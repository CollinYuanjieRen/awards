import MerLeanExperiment.Certificates.FixedCore0.Steps1200_1299

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8851 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8851 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8847, some c8686, some c8848, some c8724, some c8849, some c8850, some c8593, some c5895, some c5894, some c5893, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8851 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8851 : lratChecker f8851 p8851 = .success := by decide +kernel
theorem unsat8851 : Unsatisfiable (PosFin 65) f8851 := by
  apply lratCheckerSound f8851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8851
  · intro a ha; simp [p8851] at ha; subst a; trivial
  · exact checked8851
theorem derived8851 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8851 := by
  apply localUnsat_implies_entails f8851 [c8269, c8847, c8686, c8848, c8724, c8849, c8850, c8593, c5895, c5894, c5893] c8851 unsat8851 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8848 := derived8848 a h
  have h4 : Entails.eval a c8724 := derived8724 a h
  have h5 : Entails.eval a c8849 := derived8849 a h
  have h6 : Entails.eval a c8850 := derived8850 a h
  have h7 : Entails.eval a c8593 := derived8593 a h
  have h8 : Entails.eval a c5895 := h 5894 (by decide)
  have h9 : Entails.eval a c5894 := h 5893 (by decide)
  have h10 : Entails.eval a c5893 := h 5892 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8852 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8852 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6222, some c8815, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8852 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8852 : lratChecker f8852 p8852 = .success := by decide +kernel
theorem unsat8852 : Unsatisfiable (PosFin 65) f8852 := by
  apply lratCheckerSound f8852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8852
  · intro a ha; simp [p8852] at ha; subst a; trivial
  · exact checked8852
theorem derived8852 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8852 := by
  apply localUnsat_implies_entails f8852 [c6222, c8815] c8852 unsat8852 (by rfl) a
  have h0 : Entails.eval a c6222 := h 6221 (by decide)
  have h1 : Entails.eval a c8815 := derived8815 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8853 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8853 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5991, some c5990, some c5989, some c6003, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p8853 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8853 : lratChecker f8853 p8853 = .success := by decide +kernel
theorem unsat8853 : Unsatisfiable (PosFin 65) f8853 := by
  apply lratCheckerSound f8853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8853
  · intro a ha; simp [p8853] at ha; subst a; trivial
  · exact checked8853
theorem derived8853 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8853 := by
  apply localUnsat_implies_entails f8853 [c5991, c5990, c5989, c6003] c8853 unsat8853 (by rfl) a
  have h0 : Entails.eval a c5991 := h 5990 (by decide)
  have h1 : Entails.eval a c5990 := h 5989 (by decide)
  have h2 : Entails.eval a c5989 := h 5988 (by decide)
  have h3 : Entails.eval a c6003 := h 6002 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8854 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8854 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8590, some c8853, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p8854 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8854 : lratChecker f8854 p8854 = .success := by decide +kernel
theorem unsat8854 : Unsatisfiable (PosFin 65) f8854 := by
  apply lratCheckerSound f8854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8854
  · intro a ha; simp [p8854] at ha; subst a; trivial
  · exact checked8854
theorem derived8854 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8854 := by
  apply localUnsat_implies_entails f8854 [c8590, c8853] c8854 unsat8854 (by rfl) a
  have h0 : Entails.eval a c8590 := derived8590 a h
  have h1 : Entails.eval a c8853 := derived8853 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8855 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8855 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8851, some c8847, some c8686, some c1076, some c1131, some c4601, some c8852, some c8854, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8855 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8855 : lratChecker f8855 p8855 = .success := by decide +kernel
theorem unsat8855 : Unsatisfiable (PosFin 65) f8855 := by
  apply lratCheckerSound f8855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8855
  · intro a ha; simp [p8855] at ha; subst a; trivial
  · exact checked8855
theorem derived8855 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8855 := by
  apply localUnsat_implies_entails f8855 [c8851, c8847, c8686, c1076, c1131, c4601, c8852, c8854] c8855 unsat8855 (by rfl) a
  have h0 : Entails.eval a c8851 := derived8851 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c1076 := h 1075 (by decide)
  have h4 : Entails.eval a c1131 := h 1130 (by decide)
  have h5 : Entails.eval a c4601 := h 4600 (by decide)
  have h6 : Entails.eval a c8852 := derived8852 a h
  have h7 : Entails.eval a c8854 := derived8854 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8856 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8856 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c1267, some c1210, some c4902, some c295, some c4719, some c6139, some c288, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8856 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8856 : lratChecker f8856 p8856 = .success := by decide +kernel
theorem unsat8856 : Unsatisfiable (PosFin 65) f8856 := by
  apply lratCheckerSound f8856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8856
  · intro a ha; simp [p8856] at ha; subst a; trivial
  · exact checked8856
theorem derived8856 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8856 := by
  apply localUnsat_implies_entails f8856 [c8269, c1267, c1210, c4902, c295, c4719, c6139, c288] c8856 unsat8856 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c1267 := h 1266 (by decide)
  have h2 : Entails.eval a c1210 := h 1209 (by decide)
  have h3 : Entails.eval a c4902 := h 4901 (by decide)
  have h4 : Entails.eval a c295 := h 294 (by decide)
  have h5 : Entails.eval a c4719 := h 4718 (by decide)
  have h6 : Entails.eval a c6139 := h 6138 (by decide)
  have h7 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8857 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8857 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5884, some c5883, some c5881, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8857 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8857 : lratChecker f8857 p8857 = .success := by decide +kernel
theorem unsat8857 : Unsatisfiable (PosFin 65) f8857 := by
  apply lratCheckerSound f8857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8857
  · intro a ha; simp [p8857] at ha; subst a; trivial
  · exact checked8857
theorem derived8857 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8857 := by
  apply localUnsat_implies_entails f8857 [c5884, c5883, c5881] c8857 unsat8857 (by rfl) a
  have h0 : Entails.eval a c5884 := h 5883 (by decide)
  have h1 : Entails.eval a c5883 := h 5882 (by decide)
  have h2 : Entails.eval a c5881 := h 5880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8858 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8858 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8847, some c8686, some c8421, some c8851, some c8855, some c8856, some c8821, some c8857, some c8593, some c5908, some c5907, some c8007, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8858 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8858 : lratChecker f8858 p8858 = .success := by decide +kernel
theorem unsat8858 : Unsatisfiable (PosFin 65) f8858 := by
  apply lratCheckerSound f8858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8858
  · intro a ha; simp [p8858] at ha; subst a; trivial
  · exact checked8858
theorem derived8858 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8858 := by
  apply localUnsat_implies_entails f8858 [c8269, c8847, c8686, c8421, c8851, c8855, c8856, c8821, c8857, c8593, c5908, c5907, c8007] c8858 unsat8858 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8851 := derived8851 a h
  have h5 : Entails.eval a c8855 := derived8855 a h
  have h6 : Entails.eval a c8856 := derived8856 a h
  have h7 : Entails.eval a c8821 := derived8821 a h
  have h8 : Entails.eval a c8857 := derived8857 a h
  have h9 : Entails.eval a c8593 := derived8593 a h
  have h10 : Entails.eval a c5908 := h 5907 (by decide)
  have h11 : Entails.eval a c5907 := h 5906 (by decide)
  have h12 : Entails.eval a c8007 := derived8007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8859 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8859 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8847, some c8686, some c8421, some c1075, some c1130, some c5967, some c5969, some c4600, some c5981, some c3181, some c4850, some c4173, some c2774, some c962, some c834, some c4494, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8859 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8859 : lratChecker f8859 p8859 = .success := by decide +kernel
theorem unsat8859 : Unsatisfiable (PosFin 65) f8859 := by
  apply lratCheckerSound f8859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8859
  · intro a ha; simp [p8859] at ha; subst a; trivial
  · exact checked8859
theorem derived8859 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8859 := by
  apply localUnsat_implies_entails f8859 [c8847, c8686, c8421, c1075, c1130, c5967, c5969, c4600, c5981, c3181, c4850, c4173, c2774, c962, c834, c4494] c8859 unsat8859 (by rfl) a
  have h0 : Entails.eval a c8847 := derived8847 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c1075 := h 1074 (by decide)
  have h4 : Entails.eval a c1130 := h 1129 (by decide)
  have h5 : Entails.eval a c5967 := h 5966 (by decide)
  have h6 : Entails.eval a c5969 := h 5968 (by decide)
  have h7 : Entails.eval a c4600 := h 4599 (by decide)
  have h8 : Entails.eval a c5981 := h 5980 (by decide)
  have h9 : Entails.eval a c3181 := h 3180 (by decide)
  have h10 : Entails.eval a c4850 := h 4849 (by decide)
  have h11 : Entails.eval a c4173 := h 4172 (by decide)
  have h12 : Entails.eval a c2774 := h 2773 (by decide)
  have h13 : Entails.eval a c962 := h 961 (by decide)
  have h14 : Entails.eval a c834 := h 833 (by decide)
  have h15 : Entails.eval a c4494 := h 4493 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8860 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8860 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c5474, some c168, some c177, some c183, some c187, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8860 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8860 : lratChecker f8860 p8860 = .success := by decide +kernel
theorem unsat8860 : Unsatisfiable (PosFin 65) f8860 := by
  apply lratCheckerSound f8860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8860
  · intro a ha; simp [p8860] at ha; subst a; trivial
  · exact checked8860
theorem derived8860 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8860 := by
  apply localUnsat_implies_entails f8860 [c8269, c5474, c168, c177, c183, c187] c8860 unsat8860 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c5474 := h 5473 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c177 := h 176 (by decide)
  have h4 : Entails.eval a c183 := h 182 (by decide)
  have h5 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8861 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8861 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5485, some c5319, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p8861 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8861 : lratChecker f8861 p8861 = .success := by decide +kernel
theorem unsat8861 : Unsatisfiable (PosFin 65) f8861 := by
  apply lratCheckerSound f8861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8861
  · intro a ha; simp [p8861] at ha; subst a; trivial
  · exact checked8861
theorem derived8861 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8861 := by
  apply localUnsat_implies_entails f8861 [c5485, c5319] c8861 unsat8861 (by rfl) a
  have h0 : Entails.eval a c5485 := h 5484 (by decide)
  have h1 : Entails.eval a c5319 := h 5318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8862 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8862 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8858, some c8269, some c8686, some c8859, some c8828, some c8860, some c8861, some c5476, some c5820, some c145, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8862 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8862 : lratChecker f8862 p8862 = .success := by decide +kernel
theorem unsat8862 : Unsatisfiable (PosFin 65) f8862 := by
  apply lratCheckerSound f8862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8862
  · intro a ha; simp [p8862] at ha; subst a; trivial
  · exact checked8862
theorem derived8862 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8862 := by
  apply localUnsat_implies_entails f8862 [c8858, c8269, c8686, c8859, c8828, c8860, c8861, c5476, c5820, c145] c8862 unsat8862 (by rfl) a
  have h0 : Entails.eval a c8858 := derived8858 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8859 := derived8859 a h
  have h4 : Entails.eval a c8828 := derived8828 a h
  have h5 : Entails.eval a c8860 := derived8860 a h
  have h6 : Entails.eval a c8861 := derived8861 a h
  have h7 : Entails.eval a c5476 := h 5475 (by decide)
  have h8 : Entails.eval a c5820 := h 5819 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8863 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8863 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5956, some c5895, some c6199, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p8863 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8863 : lratChecker f8863 p8863 = .success := by decide +kernel
theorem unsat8863 : Unsatisfiable (PosFin 65) f8863 := by
  apply lratCheckerSound f8863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8863
  · intro a ha; simp [p8863] at ha; subst a; trivial
  · exact checked8863
theorem derived8863 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8863 := by
  apply localUnsat_implies_entails f8863 [c5956, c5895, c6199] c8863 unsat8863 (by rfl) a
  have h0 : Entails.eval a c5956 := h 5955 (by decide)
  have h1 : Entails.eval a c5895 := h 5894 (by decide)
  have h2 : Entails.eval a c6199 := h 6198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8864 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨23, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8864 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1143, some c1091, some c291, some c4627, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8864 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8864 : lratChecker f8864 p8864 = .success := by decide +kernel
theorem unsat8864 : Unsatisfiable (PosFin 65) f8864 := by
  apply lratCheckerSound f8864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8864
  · intro a ha; simp [p8864] at ha; subst a; trivial
  · exact checked8864
theorem derived8864 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8864 := by
  apply localUnsat_implies_entails f8864 [c1143, c1091, c291, c4627] c8864 unsat8864 (by rfl) a
  have h0 : Entails.eval a c1143 := h 1142 (by decide)
  have h1 : Entails.eval a c1091 := h 1090 (by decide)
  have h2 : Entails.eval a c291 := h 290 (by decide)
  have h3 : Entails.eval a c4627 := h 4626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8865 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨51, by decide⟩, false), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8865 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8686, some c8847, some c8862, some c8856, some c8864, some c1268, some c1211, some c8007, some c4726, some c290, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8865 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8865 : lratChecker f8865 p8865 = .success := by decide +kernel
theorem unsat8865 : Unsatisfiable (PosFin 65) f8865 := by
  apply lratCheckerSound f8865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8865
  · intro a ha; simp [p8865] at ha; subst a; trivial
  · exact checked8865
theorem derived8865 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8865 := by
  apply localUnsat_implies_entails f8865 [c8421, c8686, c8847, c8862, c8856, c8864, c1268, c1211, c8007, c4726, c290] c8865 unsat8865 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8862 := derived8862 a h
  have h4 : Entails.eval a c8856 := derived8856 a h
  have h5 : Entails.eval a c8864 := derived8864 a h
  have h6 : Entails.eval a c1268 := h 1267 (by decide)
  have h7 : Entails.eval a c1211 := h 1210 (by decide)
  have h8 : Entails.eval a c8007 := derived8007 a h
  have h9 : Entails.eval a c4726 := h 4725 (by decide)
  have h10 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8866 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8866 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8686, some c8847, some c8862, some c8856, some c8858, some c8269, some c8825, some c8865, some c8593, some c5895, some c5894, some c5893, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8866 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8866 : lratChecker f8866 p8866 = .success := by decide +kernel
theorem unsat8866 : Unsatisfiable (PosFin 65) f8866 := by
  apply lratCheckerSound f8866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8866
  · intro a ha; simp [p8866] at ha; subst a; trivial
  · exact checked8866
theorem derived8866 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8866 := by
  apply localUnsat_implies_entails f8866 [c8421, c8686, c8847, c8862, c8856, c8858, c8269, c8825, c8865, c8593, c5895, c5894, c5893] c8866 unsat8866 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8862 := derived8862 a h
  have h4 : Entails.eval a c8856 := derived8856 a h
  have h5 : Entails.eval a c8858 := derived8858 a h
  have h6 : Entails.eval a c8269 := derived8269 a h
  have h7 : Entails.eval a c8825 := derived8825 a h
  have h8 : Entails.eval a c8865 := derived8865 a h
  have h9 : Entails.eval a c8593 := derived8593 a h
  have h10 : Entails.eval a c5895 := h 5894 (by decide)
  have h11 : Entails.eval a c5894 := h 5893 (by decide)
  have h12 : Entails.eval a c5893 := h 5892 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8867 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8867 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5485, some c175, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8867 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8867 : lratChecker f8867 p8867 = .success := by decide +kernel
theorem unsat8867 : Unsatisfiable (PosFin 65) f8867 := by
  apply lratCheckerSound f8867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8867
  · intro a ha; simp [p8867] at ha; subst a; trivial
  · exact checked8867
theorem derived8867 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8867 := by
  apply localUnsat_implies_entails f8867 [c5485, c175] c8867 unsat8867 (by rfl) a
  have h0 : Entails.eval a c5485 := h 5484 (by decide)
  have h1 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8868 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8868 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8847, some c8686, some c8421, some c8858, some c8862, some c8856, some c8866, some c8860, some c8867, some c8007, some c5476, some c174, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8868 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8868 : lratChecker f8868 p8868 = .success := by decide +kernel
theorem unsat8868 : Unsatisfiable (PosFin 65) f8868 := by
  apply lratCheckerSound f8868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8868
  · intro a ha; simp [p8868] at ha; subst a; trivial
  · exact checked8868
theorem derived8868 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8868 := by
  apply localUnsat_implies_entails f8868 [c8847, c8686, c8421, c8858, c8862, c8856, c8866, c8860, c8867, c8007, c5476, c174] c8868 unsat8868 (by rfl) a
  have h0 : Entails.eval a c8847 := derived8847 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8858 := derived8858 a h
  have h4 : Entails.eval a c8862 := derived8862 a h
  have h5 : Entails.eval a c8856 := derived8856 a h
  have h6 : Entails.eval a c8866 := derived8866 a h
  have h7 : Entails.eval a c8860 := derived8860 a h
  have h8 : Entails.eval a c8867 := derived8867 a h
  have h9 : Entails.eval a c8007 := derived8007 a h
  have h10 : Entails.eval a c5476 := h 5475 (by decide)
  have h11 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8869 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8869 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6249, some c6222, some c5920, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8869 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8869 : lratChecker f8869 p8869 = .success := by decide +kernel
theorem unsat8869 : Unsatisfiable (PosFin 65) f8869 := by
  apply lratCheckerSound f8869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8869
  · intro a ha; simp [p8869] at ha; subst a; trivial
  · exact checked8869
theorem derived8869 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8869 := by
  apply localUnsat_implies_entails f8869 [c8269, c6249, c6222, c5920] c8869 unsat8869 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6249 := h 6248 (by decide)
  have h2 : Entails.eval a c6222 := h 6221 (by decide)
  have h3 : Entails.eval a c5920 := h 5919 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8870 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨53, by decide⟩, false), (⟨51, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8870 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6252, some c6226, some c5931, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p8870 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8870 : lratChecker f8870 p8870 = .success := by decide +kernel
theorem unsat8870 : Unsatisfiable (PosFin 65) f8870 := by
  apply lratCheckerSound f8870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8870
  · intro a ha; simp [p8870] at ha; subst a; trivial
  · exact checked8870
theorem derived8870 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8870 := by
  apply localUnsat_implies_entails f8870 [c6252, c6226, c5931] c8870 unsat8870 (by rfl) a
  have h0 : Entails.eval a c6252 := h 6251 (by decide)
  have h1 : Entails.eval a c6226 := h 6225 (by decide)
  have h2 : Entails.eval a c5931 := h 5930 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8871 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8871 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8823, some c8869, some c8870, some c8007, some c6223, some c6258, some c5930, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8871 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8871 : lratChecker f8871 p8871 = .success := by decide +kernel
theorem unsat8871 : Unsatisfiable (PosFin 65) f8871 := by
  apply lratCheckerSound f8871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8871
  · intro a ha; simp [p8871] at ha; subst a; trivial
  · exact checked8871
theorem derived8871 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8871 := by
  apply localUnsat_implies_entails f8871 [c8823, c8869, c8870, c8007, c6223, c6258, c5930] c8871 unsat8871 (by rfl) a
  have h0 : Entails.eval a c8823 := derived8823 a h
  have h1 : Entails.eval a c8869 := derived8869 a h
  have h2 : Entails.eval a c8870 := derived8870 a h
  have h3 : Entails.eval a c8007 := derived8007 a h
  have h4 : Entails.eval a c6223 := h 6222 (by decide)
  have h5 : Entails.eval a c6258 := h 6257 (by decide)
  have h6 : Entails.eval a c5930 := h 5929 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8872 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8872 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c1267, some c1210, some c8852, some c4719, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8872 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8872 : lratChecker f8872 p8872 = .success := by decide +kernel
theorem unsat8872 : Unsatisfiable (PosFin 65) f8872 := by
  apply lratCheckerSound f8872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8872
  · intro a ha; simp [p8872] at ha; subst a; trivial
  · exact checked8872
theorem derived8872 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8872 := by
  apply localUnsat_implies_entails f8872 [c8269, c1267, c1210, c8852, c4719] c8872 unsat8872 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c1267 := h 1266 (by decide)
  have h2 : Entails.eval a c1210 := h 1209 (by decide)
  have h3 : Entails.eval a c8852 := derived8852 a h
  have h4 : Entails.eval a c4719 := h 4718 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8873 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8873 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6221, some c6257, some c5922, some c5935, some c5925, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8873 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8873 : lratChecker f8873 p8873 = .success := by decide +kernel
theorem unsat8873 : Unsatisfiable (PosFin 65) f8873 := by
  apply lratCheckerSound f8873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8873
  · intro a ha; simp [p8873] at ha; subst a; trivial
  · exact checked8873
theorem derived8873 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8873 := by
  apply localUnsat_implies_entails f8873 [c8269, c6221, c6257, c5922, c5935, c5925] c8873 unsat8873 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6221 := h 6220 (by decide)
  have h2 : Entails.eval a c6257 := h 6256 (by decide)
  have h3 : Entails.eval a c5922 := h 5921 (by decide)
  have h4 : Entails.eval a c5935 := h 5934 (by decide)
  have h5 : Entails.eval a c5925 := h 5924 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8874 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8874 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6226, some c6263, some c5931, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p8874 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8874 : lratChecker f8874 p8874 = .success := by decide +kernel
theorem unsat8874 : Unsatisfiable (PosFin 65) f8874 := by
  apply lratCheckerSound f8874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8874
  · intro a ha; simp [p8874] at ha; subst a; trivial
  · exact checked8874
theorem derived8874 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8874 := by
  apply localUnsat_implies_entails f8874 [c6226, c6263, c5931] c8874 unsat8874 (by rfl) a
  have h0 : Entails.eval a c6226 := h 6225 (by decide)
  have h1 : Entails.eval a c6263 := h 6262 (by decide)
  have h2 : Entails.eval a c5931 := h 5930 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8875 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨52, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8875 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8873, some c8874, some c8007, some c6223, some c6258, some c5929, some c5939, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8875 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8875 : lratChecker f8875 p8875 = .success := by decide +kernel
theorem unsat8875 : Unsatisfiable (PosFin 65) f8875 := by
  apply lratCheckerSound f8875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8875
  · intro a ha; simp [p8875] at ha; subst a; trivial
  · exact checked8875
theorem derived8875 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8875 := by
  apply localUnsat_implies_entails f8875 [c8873, c8874, c8007, c6223, c6258, c5929, c5939] c8875 unsat8875 (by rfl) a
  have h0 : Entails.eval a c8873 := derived8873 a h
  have h1 : Entails.eval a c8874 := derived8874 a h
  have h2 : Entails.eval a c8007 := derived8007 a h
  have h3 : Entails.eval a c6223 := h 6222 (by decide)
  have h4 : Entails.eval a c6258 := h 6257 (by decide)
  have h5 : Entails.eval a c5929 := h 5928 (by decide)
  have h6 : Entails.eval a c5939 := h 5938 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8876 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8876 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8871, some c8872, some c8875, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8876 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8876 : lratChecker f8876 p8876 = .success := by decide +kernel
theorem unsat8876 : Unsatisfiable (PosFin 65) f8876 := by
  apply lratCheckerSound f8876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8876
  · intro a ha; simp [p8876] at ha; subst a; trivial
  · exact checked8876
theorem derived8876 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8876 := by
  apply localUnsat_implies_entails f8876 [c8871, c8872, c8875] c8876 unsat8876 (by rfl) a
  have h0 : Entails.eval a c8871 := derived8871 a h
  have h1 : Entails.eval a c8872 := derived8872 a h
  have h2 : Entails.eval a c8875 := derived8875 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8877 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8877 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6011, some c5920, some c6232, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8877 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8877 : lratChecker f8877 p8877 = .success := by decide +kernel
theorem unsat8877 : Unsatisfiable (PosFin 65) f8877 := by
  apply lratCheckerSound f8877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8877
  · intro a ha; simp [p8877] at ha; subst a; trivial
  · exact checked8877
theorem derived8877 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8877 := by
  apply localUnsat_implies_entails f8877 [c8269, c6011, c5920, c6232] c8877 unsat8877 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6011 := h 6010 (by decide)
  have h2 : Entails.eval a c5920 := h 5919 (by decide)
  have h3 : Entails.eval a c6232 := h 6231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8878 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨31, by decide⟩, false), (⟨53, by decide⟩, true), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8878 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c6270, some c6126, some c5854, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8878 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8878 : lratChecker f8878 p8878 = .success := by decide +kernel
theorem unsat8878 : Unsatisfiable (PosFin 65) f8878 := by
  apply lratCheckerSound f8878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8878
  · intro a ha; simp [p8878] at ha; subst a; trivial
  · exact checked8878
theorem derived8878 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8878 := by
  apply localUnsat_implies_entails f8878 [c8269, c6270, c6126, c5854] c8878 unsat8878 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c6270 := h 6269 (by decide)
  have h2 : Entails.eval a c6126 := h 6125 (by decide)
  have h3 : Entails.eval a c5854 := h 5853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8879 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8879 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8877, some c6174, some c8878, some c5636, some c6167, some c5681, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8879 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8879 : lratChecker f8879 p8879 = .success := by decide +kernel
theorem unsat8879 : Unsatisfiable (PosFin 65) f8879 := by
  apply lratCheckerSound f8879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8879
  · intro a ha; simp [p8879] at ha; subst a; trivial
  · exact checked8879
theorem derived8879 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8879 := by
  apply localUnsat_implies_entails f8879 [c8269, c8877, c6174, c8878, c5636, c6167, c5681] c8879 unsat8879 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8877 := derived8877 a h
  have h2 : Entails.eval a c6174 := h 6173 (by decide)
  have h3 : Entails.eval a c8878 := derived8878 a h
  have h4 : Entails.eval a c5636 := h 5635 (by decide)
  have h5 : Entails.eval a c6167 := h 6166 (by decide)
  have h6 : Entails.eval a c5681 := h 5680 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8880 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8880 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1428, some c1143, some c1091, some c5931, some c4627, some c4462, some c5655, some c5629, some c5667, some c350, some c6241, some c6111, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8880 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8880 : lratChecker f8880 p8880 = .success := by decide +kernel
theorem unsat8880 : Unsatisfiable (PosFin 65) f8880 := by
  apply lratCheckerSound f8880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8880
  · intro a ha; simp [p8880] at ha; subst a; trivial
  · exact checked8880
theorem derived8880 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8880 := by
  apply localUnsat_implies_entails f8880 [c1428, c1143, c1091, c5931, c4627, c4462, c5655, c5629, c5667, c350, c6241, c6111] c8880 unsat8880 (by rfl) a
  have h0 : Entails.eval a c1428 := h 1427 (by decide)
  have h1 : Entails.eval a c1143 := h 1142 (by decide)
  have h2 : Entails.eval a c1091 := h 1090 (by decide)
  have h3 : Entails.eval a c5931 := h 5930 (by decide)
  have h4 : Entails.eval a c4627 := h 4626 (by decide)
  have h5 : Entails.eval a c4462 := h 4461 (by decide)
  have h6 : Entails.eval a c5655 := h 5654 (by decide)
  have h7 : Entails.eval a c5629 := h 5628 (by decide)
  have h8 : Entails.eval a c5667 := h 5666 (by decide)
  have h9 : Entails.eval a c350 := h 349 (by decide)
  have h10 : Entails.eval a c6241 := h 6240 (by decide)
  have h11 : Entails.eval a c6111 := h 6110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8881 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8881 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8880, some c8007, some c6018, some c5930, some c6235, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8881 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8881 : lratChecker f8881 p8881 = .success := by decide +kernel
theorem unsat8881 : Unsatisfiable (PosFin 65) f8881 := by
  apply lratCheckerSound f8881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8881
  · intro a ha; simp [p8881] at ha; subst a; trivial
  · exact checked8881
theorem derived8881 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8881 := by
  apply localUnsat_implies_entails f8881 [c8880, c8007, c6018, c5930, c6235] c8881 unsat8881 (by rfl) a
  have h0 : Entails.eval a c8880 := derived8880 a h
  have h1 : Entails.eval a c8007 := derived8007 a h
  have h2 : Entails.eval a c6018 := h 6017 (by decide)
  have h3 : Entails.eval a c5930 := h 5929 (by decide)
  have h4 : Entails.eval a c6235 := h 6234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8882 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨31, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8882 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5689, some c6179, some c5629, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8882 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8882 : lratChecker f8882 p8882 = .success := by decide +kernel
theorem unsat8882 : Unsatisfiable (PosFin 65) f8882 := by
  apply lratCheckerSound f8882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8882
  · intro a ha; simp [p8882] at ha; subst a; trivial
  · exact checked8882
theorem derived8882 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8882 := by
  apply localUnsat_implies_entails f8882 [c5689, c6179, c5629] c8882 unsat8882 (by rfl) a
  have h0 : Entails.eval a c5689 := h 5688 (by decide)
  have h1 : Entails.eval a c6179 := h 6178 (by decide)
  have h2 : Entails.eval a c5629 := h 5628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8883 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8883 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8847, some c8868, some c8876, some c8879, some c8421, some c8724, some c8881, some c8882, some c1268, some c1211, some c4726, some c3196, some c4188, some c6271, some c6175, some c838, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8883 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8883 : lratChecker f8883 p8883 = .success := by decide +kernel
theorem unsat8883 : Unsatisfiable (PosFin 65) f8883 := by
  apply lratCheckerSound f8883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8883
  · intro a ha; simp [p8883] at ha; subst a; trivial
  · exact checked8883
theorem derived8883 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8883 := by
  apply localUnsat_implies_entails f8883 [c8686, c8847, c8868, c8876, c8879, c8421, c8724, c8881, c8882, c1268, c1211, c4726, c3196, c4188, c6271, c6175, c838] c8883 unsat8883 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8868 := derived8868 a h
  have h3 : Entails.eval a c8876 := derived8876 a h
  have h4 : Entails.eval a c8879 := derived8879 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8724 := derived8724 a h
  have h7 : Entails.eval a c8881 := derived8881 a h
  have h8 : Entails.eval a c8882 := derived8882 a h
  have h9 : Entails.eval a c1268 := h 1267 (by decide)
  have h10 : Entails.eval a c1211 := h 1210 (by decide)
  have h11 : Entails.eval a c4726 := h 4725 (by decide)
  have h12 : Entails.eval a c3196 := h 3195 (by decide)
  have h13 : Entails.eval a c4188 := h 4187 (by decide)
  have h14 : Entails.eval a c6271 := h 6270 (by decide)
  have h15 : Entails.eval a c6175 := h 6174 (by decide)
  have h16 : Entails.eval a c838 := h 837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8884 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨39, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8884 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7374, some c6449, some c7366, some c6499, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8884 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8884 : lratChecker f8884 p8884 = .success := by decide +kernel
theorem unsat8884 : Unsatisfiable (PosFin 65) f8884 := by
  apply lratCheckerSound f8884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8884
  · intro a ha; simp [p8884] at ha; subst a; trivial
  · exact checked8884
theorem derived8884 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8884 := by
  apply localUnsat_implies_entails f8884 [c7374, c6449, c7366, c6499] c8884 unsat8884 (by rfl) a
  have h0 : Entails.eval a c7374 := h 7373 (by decide)
  have h1 : Entails.eval a c6449 := h 6448 (by decide)
  have h2 : Entails.eval a c7366 := h 7365 (by decide)
  have h3 : Entails.eval a c6499 := h 6498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8885 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8885 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1428, some c1143, some c4909, some c1091, some c5931, some c4627, some c4462, some c5655, some c5639, some c350, some c78, some c6096, some c86, some c8884, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8885 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8885 : lratChecker f8885 p8885 = .success := by decide +kernel
theorem unsat8885 : Unsatisfiable (PosFin 65) f8885 := by
  apply lratCheckerSound f8885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8885
  · intro a ha; simp [p8885] at ha; subst a; trivial
  · exact checked8885
theorem derived8885 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8885 := by
  apply localUnsat_implies_entails f8885 [c1428, c1143, c4909, c1091, c5931, c4627, c4462, c5655, c5639, c350, c78, c6096, c86, c8884] c8885 unsat8885 (by rfl) a
  have h0 : Entails.eval a c1428 := h 1427 (by decide)
  have h1 : Entails.eval a c1143 := h 1142 (by decide)
  have h2 : Entails.eval a c4909 := h 4908 (by decide)
  have h3 : Entails.eval a c1091 := h 1090 (by decide)
  have h4 : Entails.eval a c5931 := h 5930 (by decide)
  have h5 : Entails.eval a c4627 := h 4626 (by decide)
  have h6 : Entails.eval a c4462 := h 4461 (by decide)
  have h7 : Entails.eval a c5655 := h 5654 (by decide)
  have h8 : Entails.eval a c5639 := h 5638 (by decide)
  have h9 : Entails.eval a c350 := h 349 (by decide)
  have h10 : Entails.eval a c78 := h 77 (by decide)
  have h11 : Entails.eval a c6096 := h 6095 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c8884 := derived8884 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8886 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8886 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8885, some c8007, some c6018, some c5930, some c6235, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8886 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8886 : lratChecker f8886 p8886 = .success := by decide +kernel
theorem unsat8886 : Unsatisfiable (PosFin 65) f8886 := by
  apply lratCheckerSound f8886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8886
  · intro a ha; simp [p8886] at ha; subst a; trivial
  · exact checked8886
theorem derived8886 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8886 := by
  apply localUnsat_implies_entails f8886 [c8885, c8007, c6018, c5930, c6235] c8886 unsat8886 (by rfl) a
  have h0 : Entails.eval a c8885 := derived8885 a h
  have h1 : Entails.eval a c8007 := derived8007 a h
  have h2 : Entails.eval a c6018 := h 6017 (by decide)
  have h3 : Entails.eval a c5930 := h 5929 (by decide)
  have h4 : Entails.eval a c6235 := h 6234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8887 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8887 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8868, some c8847, some c8686, some c8421, some c8876, some c8879, some c8883, some c8821, some c8886, some c8882, some c1268, some c1211, some c8007, some c4726, some c3196, some c4188, some c6175, some c5688, some c829, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8887 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8887 : lratChecker f8887 p8887 = .success := by decide +kernel
theorem unsat8887 : Unsatisfiable (PosFin 65) f8887 := by
  apply lratCheckerSound f8887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8887
  · intro a ha; simp [p8887] at ha; subst a; trivial
  · exact checked8887
theorem derived8887 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8887 := by
  apply localUnsat_implies_entails f8887 [c8868, c8847, c8686, c8421, c8876, c8879, c8883, c8821, c8886, c8882, c1268, c1211, c8007, c4726, c3196, c4188, c6175, c5688, c829] c8887 unsat8887 (by rfl) a
  have h0 : Entails.eval a c8868 := derived8868 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8876 := derived8876 a h
  have h5 : Entails.eval a c8879 := derived8879 a h
  have h6 : Entails.eval a c8883 := derived8883 a h
  have h7 : Entails.eval a c8821 := derived8821 a h
  have h8 : Entails.eval a c8886 := derived8886 a h
  have h9 : Entails.eval a c8882 := derived8882 a h
  have h10 : Entails.eval a c1268 := h 1267 (by decide)
  have h11 : Entails.eval a c1211 := h 1210 (by decide)
  have h12 : Entails.eval a c8007 := derived8007 a h
  have h13 : Entails.eval a c4726 := h 4725 (by decide)
  have h14 : Entails.eval a c3196 := h 3195 (by decide)
  have h15 : Entails.eval a c4188 := h 4187 (by decide)
  have h16 : Entails.eval a c6175 := h 6174 (by decide)
  have h17 : Entails.eval a c5688 := h 5687 (by decide)
  have h18 : Entails.eval a c829 := h 828 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8888 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨32, by decide⟩, true), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8888 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c1210, some c4902, some c8694, some c8828, some c144, some c33, some c8878, some c5439, some c8807, some c82, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8888 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8888 : lratChecker f8888 p8888 = .success := by decide +kernel
theorem unsat8888 : Unsatisfiable (PosFin 65) f8888 := by
  apply lratCheckerSound f8888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8888
  · intro a ha; simp [p8888] at ha; subst a; trivial
  · exact checked8888
theorem derived8888 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8888 := by
  apply localUnsat_implies_entails f8888 [c8269, c1210, c4902, c8694, c8828, c144, c33, c8878, c5439, c8807, c82] c8888 unsat8888 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c1210 := h 1209 (by decide)
  have h2 : Entails.eval a c4902 := h 4901 (by decide)
  have h3 : Entails.eval a c8694 := derived8694 a h
  have h4 : Entails.eval a c8828 := derived8828 a h
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c8878 := derived8878 a h
  have h8 : Entails.eval a c5439 := h 5438 (by decide)
  have h9 : Entails.eval a c8807 := derived8807 a h
  have h10 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8889 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, true), (⟨20, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8889 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1428, some c1143, some c4909, some c1091, some c5931, some c4627, some c4462, some c5449, some c5441, some c5399, some c86, some c65, some c8884, some c6407, some c7286, some c496, some c409, some c5261, some c6980, some c8550, some c117, some c116, some c118, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8889 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8889 : lratChecker f8889 p8889 = .success := by decide +kernel
theorem unsat8889 : Unsatisfiable (PosFin 65) f8889 := by
  apply lratCheckerSound f8889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8889
  · intro a ha; simp [p8889] at ha; subst a; trivial
  · exact checked8889
theorem derived8889 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8889 := by
  apply localUnsat_implies_entails f8889 [c1428, c1143, c4909, c1091, c5931, c4627, c4462, c5449, c5441, c5399, c86, c65, c8884, c6407, c7286, c496, c409, c5261, c6980, c8550, c117, c116, c118] c8889 unsat8889 (by rfl) a
  have h0 : Entails.eval a c1428 := h 1427 (by decide)
  have h1 : Entails.eval a c1143 := h 1142 (by decide)
  have h2 : Entails.eval a c4909 := h 4908 (by decide)
  have h3 : Entails.eval a c1091 := h 1090 (by decide)
  have h4 : Entails.eval a c5931 := h 5930 (by decide)
  have h5 : Entails.eval a c4627 := h 4626 (by decide)
  have h6 : Entails.eval a c4462 := h 4461 (by decide)
  have h7 : Entails.eval a c5449 := h 5448 (by decide)
  have h8 : Entails.eval a c5441 := h 5440 (by decide)
  have h9 : Entails.eval a c5399 := h 5398 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c8884 := derived8884 a h
  have h13 : Entails.eval a c6407 := h 6406 (by decide)
  have h14 : Entails.eval a c7286 := h 7285 (by decide)
  have h15 : Entails.eval a c496 := h 495 (by decide)
  have h16 : Entails.eval a c409 := h 408 (by decide)
  have h17 : Entails.eval a c5261 := h 5260 (by decide)
  have h18 : Entails.eval a c6980 := h 6979 (by decide)
  have h19 : Entails.eval a c8550 := derived8550 a h
  have h20 : Entails.eval a c117 := h 116 (by decide)
  have h21 : Entails.eval a c116 := h 115 (by decide)
  have h22 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8890 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨51, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8890 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1268, some c1211, some c6069, some c4726, some c3196, some c4188, some c6075, some c6063, some c842, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8890 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8890 : lratChecker f8890 p8890 = .success := by decide +kernel
theorem unsat8890 : Unsatisfiable (PosFin 65) f8890 := by
  apply lratCheckerSound f8890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8890
  · intro a ha; simp [p8890] at ha; subst a; trivial
  · exact checked8890
theorem derived8890 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8890 := by
  apply localUnsat_implies_entails f8890 [c1268, c1211, c6069, c4726, c3196, c4188, c6075, c6063, c842] c8890 unsat8890 (by rfl) a
  have h0 : Entails.eval a c1268 := h 1267 (by decide)
  have h1 : Entails.eval a c1211 := h 1210 (by decide)
  have h2 : Entails.eval a c6069 := h 6068 (by decide)
  have h3 : Entails.eval a c4726 := h 4725 (by decide)
  have h4 : Entails.eval a c3196 := h 3195 (by decide)
  have h5 : Entails.eval a c4188 := h 4187 (by decide)
  have h6 : Entails.eval a c6075 := h 6074 (by decide)
  have h7 : Entails.eval a c6063 := h 6062 (by decide)
  have h8 : Entails.eval a c842 := h 841 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8891 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8891 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8686, some c8847, some c8868, some c8887, some c8888, some c8269, some c8823, some c8890, some c6252, some c8889, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8891 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8891 : lratChecker f8891 p8891 = .success := by decide +kernel
theorem unsat8891 : Unsatisfiable (PosFin 65) f8891 := by
  apply lratCheckerSound f8891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8891
  · intro a ha; simp [p8891] at ha; subst a; trivial
  · exact checked8891
theorem derived8891 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8891 := by
  apply localUnsat_implies_entails f8891 [c8421, c8686, c8847, c8868, c8887, c8888, c8269, c8823, c8890, c6252, c8889] c8891 unsat8891 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8868 := derived8868 a h
  have h4 : Entails.eval a c8887 := derived8887 a h
  have h5 : Entails.eval a c8888 := derived8888 a h
  have h6 : Entails.eval a c8269 := derived8269 a h
  have h7 : Entails.eval a c8823 := derived8823 a h
  have h8 : Entails.eval a c8890 := derived8890 a h
  have h9 : Entails.eval a c6252 := h 6251 (by decide)
  have h10 : Entails.eval a c8889 := derived8889 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8892 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8892 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6111, some c6096, some c6203, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8892 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8892 : lratChecker f8892 p8892 = .success := by decide +kernel
theorem unsat8892 : Unsatisfiable (PosFin 65) f8892 := by
  apply lratCheckerSound f8892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8892
  · intro a ha; simp [p8892] at ha; subst a; trivial
  · exact checked8892
theorem derived8892 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8892 := by
  apply localUnsat_implies_entails f8892 [c6111, c6096, c6203] c8892 unsat8892 (by rfl) a
  have h0 : Entails.eval a c6111 := h 6110 (by decide)
  have h1 : Entails.eval a c6096 := h 6095 (by decide)
  have h2 : Entails.eval a c6203 := h 6202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8893 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8893 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1428, some c1143, some c1091, some c4627, some c4462, some c8892, some c350, some c216, some c5629, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8893 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8893 : lratChecker f8893 p8893 = .success := by decide +kernel
theorem unsat8893 : Unsatisfiable (PosFin 65) f8893 := by
  apply lratCheckerSound f8893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8893
  · intro a ha; simp [p8893] at ha; subst a; trivial
  · exact checked8893
theorem derived8893 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8893 := by
  apply localUnsat_implies_entails f8893 [c1428, c1143, c1091, c4627, c4462, c8892, c350, c216, c5629] c8893 unsat8893 (by rfl) a
  have h0 : Entails.eval a c1428 := h 1427 (by decide)
  have h1 : Entails.eval a c1143 := h 1142 (by decide)
  have h2 : Entails.eval a c1091 := h 1090 (by decide)
  have h3 : Entails.eval a c4627 := h 4626 (by decide)
  have h4 : Entails.eval a c4462 := h 4461 (by decide)
  have h5 : Entails.eval a c8892 := derived8892 a h
  have h6 : Entails.eval a c350 := h 349 (by decide)
  have h7 : Entails.eval a c216 := h 215 (by decide)
  have h8 : Entails.eval a c5629 := h 5628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8894 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨62, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, true), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8894 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c6018, some c5930, some c841, some c5791, some c6058, some c258, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8894 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8894 : lratChecker f8894 p8894 = .success := by decide +kernel
theorem unsat8894 : Unsatisfiable (PosFin 65) f8894 := by
  apply lratCheckerSound f8894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8894
  · intro a ha; simp [p8894] at ha; subst a; trivial
  · exact checked8894
theorem derived8894 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8894 := by
  apply localUnsat_implies_entails f8894 [c8007, c6018, c5930, c841, c5791, c6058, c258] c8894 unsat8894 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c6018 := h 6017 (by decide)
  have h2 : Entails.eval a c5930 := h 5929 (by decide)
  have h3 : Entails.eval a c841 := h 840 (by decide)
  have h4 : Entails.eval a c5791 := h 5790 (by decide)
  have h5 : Entails.eval a c6058 := h 6057 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8895 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8895 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8686, some c8847, some c8868, some c8887, some c8888, some c8891, some c8825, some c8893, some c1268, some c1211, some c4726, some c3196, some c4188, some c8894, some c6128, some c6271, some c836, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8895 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8895 : lratChecker f8895 p8895 = .success := by decide +kernel
theorem unsat8895 : Unsatisfiable (PosFin 65) f8895 := by
  apply lratCheckerSound f8895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8895
  · intro a ha; simp [p8895] at ha; subst a; trivial
  · exact checked8895
theorem derived8895 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8895 := by
  apply localUnsat_implies_entails f8895 [c8421, c8686, c8847, c8868, c8887, c8888, c8891, c8825, c8893, c1268, c1211, c4726, c3196, c4188, c8894, c6128, c6271, c836] c8895 unsat8895 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8868 := derived8868 a h
  have h4 : Entails.eval a c8887 := derived8887 a h
  have h5 : Entails.eval a c8888 := derived8888 a h
  have h6 : Entails.eval a c8891 := derived8891 a h
  have h7 : Entails.eval a c8825 := derived8825 a h
  have h8 : Entails.eval a c8893 := derived8893 a h
  have h9 : Entails.eval a c1268 := h 1267 (by decide)
  have h10 : Entails.eval a c1211 := h 1210 (by decide)
  have h11 : Entails.eval a c4726 := h 4725 (by decide)
  have h12 : Entails.eval a c3196 := h 3195 (by decide)
  have h13 : Entails.eval a c4188 := h 4187 (by decide)
  have h14 : Entails.eval a c8894 := derived8894 a h
  have h15 : Entails.eval a c6128 := h 6127 (by decide)
  have h16 : Entails.eval a c6271 := h 6270 (by decide)
  have h17 : Entails.eval a c836 := h 835 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8896 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨25, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8896 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c5927, some c5933, some c5935, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p8896 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8896 : lratChecker f8896 p8896 = .success := by decide +kernel
theorem unsat8896 : Unsatisfiable (PosFin 65) f8896 := by
  apply lratCheckerSound f8896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8896
  · intro a ha; simp [p8896] at ha; subst a; trivial
  · exact checked8896
theorem derived8896 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8896 := by
  apply localUnsat_implies_entails f8896 [c8269, c5927, c5933, c5935] c8896 unsat8896 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c5927 := h 5926 (by decide)
  have h2 : Entails.eval a c5933 := h 5932 (by decide)
  have h3 : Entails.eval a c5935 := h 5934 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8897 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8897 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6447, some c6460, some c6359, some c7160, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p8897 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8897 : lratChecker f8897 p8897 = .success := by decide +kernel
theorem unsat8897 : Unsatisfiable (PosFin 65) f8897 := by
  apply lratCheckerSound f8897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8897
  · intro a ha; simp [p8897] at ha; subst a; trivial
  · exact checked8897
theorem derived8897 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8897 := by
  apply localUnsat_implies_entails f8897 [c6447, c6460, c6359, c7160] c8897 unsat8897 (by rfl) a
  have h0 : Entails.eval a c6447 := h 6446 (by decide)
  have h1 : Entails.eval a c6460 := h 6459 (by decide)
  have h2 : Entails.eval a c6359 := h 6358 (by decide)
  have h3 : Entails.eval a c7160 := h 7159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8898 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, true), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8898 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5474, some c1, some c193, some c5447, some c6150, some c8896, some c6086, some c6123, some c199, some c4724, some c72, some c8897, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8898 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8898 : lratChecker f8898 p8898 = .success := by decide +kernel
theorem unsat8898 : Unsatisfiable (PosFin 65) f8898 := by
  apply lratCheckerSound f8898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8898
  · intro a ha; simp [p8898] at ha; subst a; trivial
  · exact checked8898
theorem derived8898 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8898 := by
  apply localUnsat_implies_entails f8898 [c5474, c1, c193, c5447, c6150, c8896, c6086, c6123, c199, c4724, c72, c8897] c8898 unsat8898 (by rfl) a
  have h0 : Entails.eval a c5474 := h 5473 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c5447 := h 5446 (by decide)
  have h4 : Entails.eval a c6150 := h 6149 (by decide)
  have h5 : Entails.eval a c8896 := derived8896 a h
  have h6 : Entails.eval a c6086 := h 6085 (by decide)
  have h7 : Entails.eval a c6123 := h 6122 (by decide)
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c4724 := h 4723 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c8897 := derived8897 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8899 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨31, by decide⟩, true), (⟨27, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8899 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8868, some c8887, some c8421, some c8847, some c8888, some c8895, some c8898, some c1428, some c4909, some c5485, some c2782, some c5931, some c826, some c4203, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8899 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8899 : lratChecker f8899 p8899 = .success := by decide +kernel
theorem unsat8899 : Unsatisfiable (PosFin 65) f8899 := by
  apply lratCheckerSound f8899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8899
  · intro a ha; simp [p8899] at ha; subst a; trivial
  · exact checked8899
theorem derived8899 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8899 := by
  apply localUnsat_implies_entails f8899 [c8686, c8868, c8887, c8421, c8847, c8888, c8895, c8898, c1428, c4909, c5485, c2782, c5931, c826, c4203] c8899 unsat8899 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8868 := derived8868 a h
  have h2 : Entails.eval a c8887 := derived8887 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8847 := derived8847 a h
  have h5 : Entails.eval a c8888 := derived8888 a h
  have h6 : Entails.eval a c8895 := derived8895 a h
  have h7 : Entails.eval a c8898 := derived8898 a h
  have h8 : Entails.eval a c1428 := h 1427 (by decide)
  have h9 : Entails.eval a c4909 := h 4908 (by decide)
  have h10 : Entails.eval a c5485 := h 5484 (by decide)
  have h11 : Entails.eval a c2782 := h 2781 (by decide)
  have h12 : Entails.eval a c5931 := h 5930 (by decide)
  have h13 : Entails.eval a c826 := h 825 (by decide)
  have h14 : Entails.eval a c4203 := h 4202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8900 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8900 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5476, some c5820, some c5303, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8900 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8900 : lratChecker f8900 p8900 = .success := by decide +kernel
theorem unsat8900 : Unsatisfiable (PosFin 65) f8900 := by
  apply lratCheckerSound f8900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8900
  · intro a ha; simp [p8900] at ha; subst a; trivial
  · exact checked8900
theorem derived8900 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8900 := by
  apply localUnsat_implies_entails f8900 [c5476, c5820, c5303] c8900 unsat8900 (by rfl) a
  have h0 : Entails.eval a c5476 := h 5475 (by decide)
  have h1 : Entails.eval a c5820 := h 5819 (by decide)
  have h2 : Entails.eval a c5303 := h 5302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8901 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8901 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8895, some c8421, some c8686, some c8847, some c8868, some c8887, some c8888, some c8269, some c8898, some c8900, some c1428, some c1143, some c4909, some c1091, some c5485, some c123, some c8899, some c4627, some c4462, some c7, some c5639, some c78, some c8884, some c6464, some c504, some c455, some c7484, some c8550, some c6980, some c397, some c402, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8901 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked8901 : lratChecker f8901 p8901 = .success := by decide +kernel
theorem unsat8901 : Unsatisfiable (PosFin 65) f8901 := by
  apply lratCheckerSound f8901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8901
  · intro a ha; simp [p8901] at ha; subst a; trivial
  · exact checked8901
theorem derived8901 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8901 := by
  apply localUnsat_implies_entails f8901 [c8895, c8421, c8686, c8847, c8868, c8887, c8888, c8269, c8898, c8900, c1428, c1143, c4909, c1091, c5485, c123, c8899, c4627, c4462, c7, c5639, c78, c8884, c6464, c504, c455, c7484, c8550, c6980, c397, c402] c8901 unsat8901 (by rfl) a
  have h0 : Entails.eval a c8895 := derived8895 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8868 := derived8868 a h
  have h5 : Entails.eval a c8887 := derived8887 a h
  have h6 : Entails.eval a c8888 := derived8888 a h
  have h7 : Entails.eval a c8269 := derived8269 a h
  have h8 : Entails.eval a c8898 := derived8898 a h
  have h9 : Entails.eval a c8900 := derived8900 a h
  have h10 : Entails.eval a c1428 := h 1427 (by decide)
  have h11 : Entails.eval a c1143 := h 1142 (by decide)
  have h12 : Entails.eval a c4909 := h 4908 (by decide)
  have h13 : Entails.eval a c1091 := h 1090 (by decide)
  have h14 : Entails.eval a c5485 := h 5484 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c8899 := derived8899 a h
  have h17 : Entails.eval a c4627 := h 4626 (by decide)
  have h18 : Entails.eval a c4462 := h 4461 (by decide)
  have h19 : Entails.eval a c7 := h 6 (by decide)
  have h20 : Entails.eval a c5639 := h 5638 (by decide)
  have h21 : Entails.eval a c78 := h 77 (by decide)
  have h22 : Entails.eval a c8884 := derived8884 a h
  have h23 : Entails.eval a c6464 := h 6463 (by decide)
  have h24 : Entails.eval a c504 := h 503 (by decide)
  have h25 : Entails.eval a c455 := h 454 (by decide)
  have h26 : Entails.eval a c7484 := h 7483 (by decide)
  have h27 : Entails.eval a c8550 := derived8550 a h
  have h28 : Entails.eval a c6980 := h 6979 (by decide)
  have h29 : Entails.eval a c397 := h 396 (by decide)
  have h30 : Entails.eval a c402 := h 401 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8902 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8902 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8901, some c8895, some c8421, some c8686, some c8847, some c8868, some c8887, some c8888, some c5474, some c8833, some c1, some c8897, some c1128, some c1074, some c8799, some c5815, some c4598, some c405, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8902 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8902 : lratChecker f8902 p8902 = .success := by decide +kernel
theorem unsat8902 : Unsatisfiable (PosFin 65) f8902 := by
  apply lratCheckerSound f8902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8902
  · intro a ha; simp [p8902] at ha; subst a; trivial
  · exact checked8902
theorem derived8902 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8902 := by
  apply localUnsat_implies_entails f8902 [c8901, c8895, c8421, c8686, c8847, c8868, c8887, c8888, c5474, c8833, c1, c8897, c1128, c1074, c8799, c5815, c4598, c405] c8902 unsat8902 (by rfl) a
  have h0 : Entails.eval a c8901 := derived8901 a h
  have h1 : Entails.eval a c8895 := derived8895 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c8847 := derived8847 a h
  have h5 : Entails.eval a c8868 := derived8868 a h
  have h6 : Entails.eval a c8887 := derived8887 a h
  have h7 : Entails.eval a c8888 := derived8888 a h
  have h8 : Entails.eval a c5474 := h 5473 (by decide)
  have h9 : Entails.eval a c8833 := derived8833 a h
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c8897 := derived8897 a h
  have h12 : Entails.eval a c1128 := h 1127 (by decide)
  have h13 : Entails.eval a c1074 := h 1073 (by decide)
  have h14 : Entails.eval a c8799 := derived8799 a h
  have h15 : Entails.eval a c5815 := h 5814 (by decide)
  have h16 : Entails.eval a c4598 := h 4597 (by decide)
  have h17 : Entails.eval a c405 := h 404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8903 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8903 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5485, some c123, some c5931, some c5667, some c5445, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8903 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8903 : lratChecker f8903 p8903 = .success := by decide +kernel
theorem unsat8903 : Unsatisfiable (PosFin 65) f8903 := by
  apply lratCheckerSound f8903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8903
  · intro a ha; simp [p8903] at ha; subst a; trivial
  · exact checked8903
theorem derived8903 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8903 := by
  apply localUnsat_implies_entails f8903 [c5485, c123, c5931, c5667, c5445] c8903 unsat8903 (by rfl) a
  have h0 : Entails.eval a c5485 := h 5484 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c5931 := h 5930 (by decide)
  have h3 : Entails.eval a c5667 := h 5666 (by decide)
  have h4 : Entails.eval a c5445 := h 5444 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8904 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8904 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5476, some c5820, some c145, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8904 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8904 : lratChecker f8904 p8904 = .success := by decide +kernel
theorem unsat8904 : Unsatisfiable (PosFin 65) f8904 := by
  apply lratCheckerSound f8904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8904
  · intro a ha; simp [p8904] at ha; subst a; trivial
  · exact checked8904
theorem derived8904 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8904 := by
  apply localUnsat_implies_entails f8904 [c5476, c5820, c145] c8904 unsat8904 (by rfl) a
  have h0 : Entails.eval a c5476 := h 5475 (by decide)
  have h1 : Entails.eval a c5820 := h 5819 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8905 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8905 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8847, some c8686, some c8421, some c8868, some c8887, some c8888, some c8895, some c8901, some c8902, some c8904, some c5485, some c123, some c8903, some c5639, some c5667, some c6088, some c5456, some c6111, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8905 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8905 : lratChecker f8905 p8905 = .success := by decide +kernel
theorem unsat8905 : Unsatisfiable (PosFin 65) f8905 := by
  apply lratCheckerSound f8905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8905
  · intro a ha; simp [p8905] at ha; subst a; trivial
  · exact checked8905
theorem derived8905 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8905 := by
  apply localUnsat_implies_entails f8905 [c8847, c8686, c8421, c8868, c8887, c8888, c8895, c8901, c8902, c8904, c5485, c123, c8903, c5639, c5667, c6088, c5456, c6111] c8905 unsat8905 (by rfl) a
  have h0 : Entails.eval a c8847 := derived8847 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8868 := derived8868 a h
  have h4 : Entails.eval a c8887 := derived8887 a h
  have h5 : Entails.eval a c8888 := derived8888 a h
  have h6 : Entails.eval a c8895 := derived8895 a h
  have h7 : Entails.eval a c8901 := derived8901 a h
  have h8 : Entails.eval a c8902 := derived8902 a h
  have h9 : Entails.eval a c8904 := derived8904 a h
  have h10 : Entails.eval a c5485 := h 5484 (by decide)
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c8903 := derived8903 a h
  have h13 : Entails.eval a c5639 := h 5638 (by decide)
  have h14 : Entails.eval a c5667 := h 5666 (by decide)
  have h15 : Entails.eval a c6088 := h 6087 (by decide)
  have h16 : Entails.eval a c5456 := h 5455 (by decide)
  have h17 : Entails.eval a c6111 := h 6110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8906 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8906 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8848, some c5966, some c7994, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8906 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8906 : lratChecker f8906 p8906 = .success := by decide +kernel
theorem unsat8906 : Unsatisfiable (PosFin 65) f8906 := by
  apply lratCheckerSound f8906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8906
  · intro a ha; simp [p8906] at ha; subst a; trivial
  · exact checked8906
theorem derived8906 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8906 := by
  apply localUnsat_implies_entails f8906 [c8848, c5966, c7994] c8906 unsat8906 (by rfl) a
  have h0 : Entails.eval a c8848 := derived8848 a h
  have h1 : Entails.eval a c5966 := h 5965 (by decide)
  have h2 : Entails.eval a c7994 := derived7994 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8907 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8907 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1196, some c1194, some c1205, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8907 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8907 : lratChecker f8907 p8907 = .success := by decide +kernel
theorem unsat8907 : Unsatisfiable (PosFin 65) f8907 := by
  apply lratCheckerSound f8907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8907
  · intro a ha; simp [p8907] at ha; subst a; trivial
  · exact checked8907
theorem derived8907 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8907 := by
  apply localUnsat_implies_entails f8907 [c1196, c1194, c1205] c8907 unsat8907 (by rfl) a
  have h0 : Entails.eval a c1196 := h 1195 (by decide)
  have h1 : Entails.eval a c1194 := h 1193 (by decide)
  have h2 : Entails.eval a c1205 := h 1204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8908 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨62, by decide⟩, false), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8908 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5920, some c5919, some c5940, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8908 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8908 : lratChecker f8908 p8908 = .success := by decide +kernel
theorem unsat8908 : Unsatisfiable (PosFin 65) f8908 := by
  apply lratCheckerSound f8908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8908
  · intro a ha; simp [p8908] at ha; subst a; trivial
  · exact checked8908
theorem derived8908 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8908 := by
  apply localUnsat_implies_entails f8908 [c5920, c5919, c5940] c8908 unsat8908 (by rfl) a
  have h0 : Entails.eval a c5920 := h 5919 (by decide)
  have h1 : Entails.eval a c5919 := h 5918 (by decide)
  have h2 : Entails.eval a c5940 := h 5939 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8909 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8909 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6217, some c6225, some c6224, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8909 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8909 : lratChecker f8909 p8909 = .success := by decide +kernel
theorem unsat8909 : Unsatisfiable (PosFin 65) f8909 := by
  apply lratCheckerSound f8909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8909
  · intro a ha; simp [p8909] at ha; subst a; trivial
  · exact checked8909
theorem derived8909 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8909 := by
  apply localUnsat_implies_entails f8909 [c6217, c6225, c6224] c8909 unsat8909 (by rfl) a
  have h0 : Entails.eval a c6217 := h 6216 (by decide)
  have h1 : Entails.eval a c6225 := h 6224 (by decide)
  have h2 : Entails.eval a c6224 := h 6223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8910 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨25, by decide⟩, true), (⟨51, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8910 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8905, some c8686, some c8421, some c8907, some c8689, some c791, some c1259, some c4439, some c5932, some c749, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8910 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8910 : lratChecker f8910 p8910 = .success := by decide +kernel
theorem unsat8910 : Unsatisfiable (PosFin 65) f8910 := by
  apply lratCheckerSound f8910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8910
  · intro a ha; simp [p8910] at ha; subst a; trivial
  · exact checked8910
theorem derived8910 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8910 := by
  apply localUnsat_implies_entails f8910 [c8905, c8686, c8421, c8907, c8689, c791, c1259, c4439, c5932, c749] c8910 unsat8910 (by rfl) a
  have h0 : Entails.eval a c8905 := derived8905 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8907 := derived8907 a h
  have h4 : Entails.eval a c8689 := derived8689 a h
  have h5 : Entails.eval a c791 := h 790 (by decide)
  have h6 : Entails.eval a c1259 := h 1258 (by decide)
  have h7 : Entails.eval a c4439 := h 4438 (by decide)
  have h8 : Entails.eval a c5932 := h 5931 (by decide)
  have h9 : Entails.eval a c749 := h 748 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8911 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8911 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8847, some c8906, some c8905, some c8686, some c8909, some c8910, some c6245, some c6251, some c6250, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8911 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8911 : lratChecker f8911 p8911 = .success := by decide +kernel
theorem unsat8911 : Unsatisfiable (PosFin 65) f8911 := by
  apply lratCheckerSound f8911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8911
  · intro a ha; simp [p8911] at ha; subst a; trivial
  · exact checked8911
theorem derived8911 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8911 := by
  apply localUnsat_implies_entails f8911 [c8847, c8906, c8905, c8686, c8909, c8910, c6245, c6251, c6250] c8911 unsat8911 (by rfl) a
  have h0 : Entails.eval a c8847 := derived8847 a h
  have h1 : Entails.eval a c8906 := derived8906 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c8909 := derived8909 a h
  have h5 : Entails.eval a c8910 := derived8910 a h
  have h6 : Entails.eval a c6245 := h 6244 (by decide)
  have h7 : Entails.eval a c6251 := h 6250 (by decide)
  have h8 : Entails.eval a c6250 := h 6249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8912 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8912 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8908, some c6216, some c6227, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8912 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8912 : lratChecker f8912 p8912 = .success := by decide +kernel
theorem unsat8912 : Unsatisfiable (PosFin 65) f8912 := by
  apply lratCheckerSound f8912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8912
  · intro a ha; simp [p8912] at ha; subst a; trivial
  · exact checked8912
theorem derived8912 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8912 := by
  apply localUnsat_implies_entails f8912 [c8908, c6216, c6227] c8912 unsat8912 (by rfl) a
  have h0 : Entails.eval a c8908 := derived8908 a h
  have h1 : Entails.eval a c6216 := h 6215 (by decide)
  have h2 : Entails.eval a c6227 := h 6226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8913 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8913 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5919, some c1259, some c860, some c4710, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8913 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8913 : lratChecker f8913 p8913 = .success := by decide +kernel
theorem unsat8913 : Unsatisfiable (PosFin 65) f8913 := by
  apply lratCheckerSound f8913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8913
  · intro a ha; simp [p8913] at ha; subst a; trivial
  · exact checked8913
theorem derived8913 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8913 := by
  apply localUnsat_implies_entails f8913 [c5919, c1259, c860, c4710] c8913 unsat8913 (by rfl) a
  have h0 : Entails.eval a c5919 := h 5918 (by decide)
  have h1 : Entails.eval a c1259 := h 1258 (by decide)
  have h2 : Entails.eval a c860 := h 859 (by decide)
  have h3 : Entails.eval a c4710 := h 4709 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8914 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8914 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8907, some c8912, some c8913, some c6217, some c6218, some c6224, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8914 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8914 : lratChecker f8914 p8914 = .success := by decide +kernel
theorem unsat8914 : Unsatisfiable (PosFin 65) f8914 := by
  apply lratCheckerSound f8914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8914
  · intro a ha; simp [p8914] at ha; subst a; trivial
  · exact checked8914
theorem derived8914 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8914 := by
  apply localUnsat_implies_entails f8914 [c8907, c8912, c8913, c6217, c6218, c6224] c8914 unsat8914 (by rfl) a
  have h0 : Entails.eval a c8907 := derived8907 a h
  have h1 : Entails.eval a c8912 := derived8912 a h
  have h2 : Entails.eval a c8913 := derived8913 a h
  have h3 : Entails.eval a c6217 := h 6216 (by decide)
  have h4 : Entails.eval a c6218 := h 6217 (by decide)
  have h5 : Entails.eval a c6224 := h 6223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8915 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8915 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8905, some c8847, some c8906, some c8911, some c8914, some c6244, some c1134, some c1082, some c868, some c4605, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8915 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8915 : lratChecker f8915 p8915 = .success := by decide +kernel
theorem unsat8915 : Unsatisfiable (PosFin 65) f8915 := by
  apply lratCheckerSound f8915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8915
  · intro a ha; simp [p8915] at ha; subst a; trivial
  · exact checked8915
theorem derived8915 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8915 := by
  apply localUnsat_implies_entails f8915 [c8905, c8847, c8906, c8911, c8914, c6244, c1134, c1082, c868, c4605] c8915 unsat8915 (by rfl) a
  have h0 : Entails.eval a c8905 := derived8905 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8906 := derived8906 a h
  have h3 : Entails.eval a c8911 := derived8911 a h
  have h4 : Entails.eval a c8914 := derived8914 a h
  have h5 : Entails.eval a c6244 := h 6243 (by decide)
  have h6 : Entails.eval a c1134 := h 1133 (by decide)
  have h7 : Entails.eval a c1082 := h 1081 (by decide)
  have h8 : Entails.eval a c868 := h 867 (by decide)
  have h9 : Entails.eval a c4605 := h 4604 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8916 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨62, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8916 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1259, some c5937, some c4710, some c4439, some c5923, some c5932, some c1009, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8916 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8916 : lratChecker f8916 p8916 = .success := by decide +kernel
theorem unsat8916 : Unsatisfiable (PosFin 65) f8916 := by
  apply lratCheckerSound f8916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8916
  · intro a ha; simp [p8916] at ha; subst a; trivial
  · exact checked8916
theorem derived8916 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8916 := by
  apply localUnsat_implies_entails f8916 [c1259, c5937, c4710, c4439, c5923, c5932, c1009] c8916 unsat8916 (by rfl) a
  have h0 : Entails.eval a c1259 := h 1258 (by decide)
  have h1 : Entails.eval a c5937 := h 5936 (by decide)
  have h2 : Entails.eval a c4710 := h 4709 (by decide)
  have h3 : Entails.eval a c4439 := h 4438 (by decide)
  have h4 : Entails.eval a c5923 := h 5922 (by decide)
  have h5 : Entails.eval a c5932 := h 5931 (by decide)
  have h6 : Entails.eval a c1009 := h 1008 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8917 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8917 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8854, some c8907, some c8916, some c6228, some c6225, some c6219, some c6224, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8917 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8917 : lratChecker f8917 p8917 = .success := by decide +kernel
theorem unsat8917 : Unsatisfiable (PosFin 65) f8917 := by
  apply lratCheckerSound f8917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8917
  · intro a ha; simp [p8917] at ha; subst a; trivial
  · exact checked8917
theorem derived8917 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8917 := by
  apply localUnsat_implies_entails f8917 [c8854, c8907, c8916, c6228, c6225, c6219, c6224] c8917 unsat8917 (by rfl) a
  have h0 : Entails.eval a c8854 := derived8854 a h
  have h1 : Entails.eval a c8907 := derived8907 a h
  have h2 : Entails.eval a c8916 := derived8916 a h
  have h3 : Entails.eval a c6228 := h 6227 (by decide)
  have h4 : Entails.eval a c6225 := h 6224 (by decide)
  have h5 : Entails.eval a c6219 := h 6218 (by decide)
  have h6 : Entails.eval a c6224 := h 6223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8918 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨62, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8918 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5924, some c5921, some c5935, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8918 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8918 : lratChecker f8918 p8918 = .success := by decide +kernel
theorem unsat8918 : Unsatisfiable (PosFin 65) f8918 := by
  apply lratCheckerSound f8918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8918
  · intro a ha; simp [p8918] at ha; subst a; trivial
  · exact checked8918
theorem derived8918 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8918 := by
  apply localUnsat_implies_entails f8918 [c5924, c5921, c5935] c8918 unsat8918 (by rfl) a
  have h0 : Entails.eval a c5924 := h 5923 (by decide)
  have h1 : Entails.eval a c5921 := h 5920 (by decide)
  have h2 : Entails.eval a c5935 := h 5934 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8919 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8919 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8854, some c8917, some c8918, some c6225, some c6220, some c6224, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8919 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8919 : lratChecker f8919 p8919 = .success := by decide +kernel
theorem unsat8919 : Unsatisfiable (PosFin 65) f8919 := by
  apply lratCheckerSound f8919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8919
  · intro a ha; simp [p8919] at ha; subst a; trivial
  · exact checked8919
theorem derived8919 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8919 := by
  apply localUnsat_implies_entails f8919 [c8854, c8917, c8918, c6225, c6220, c6224] c8919 unsat8919 (by rfl) a
  have h0 : Entails.eval a c8854 := derived8854 a h
  have h1 : Entails.eval a c8917 := derived8917 a h
  have h2 : Entails.eval a c8918 := derived8918 a h
  have h3 : Entails.eval a c6225 := h 6224 (by decide)
  have h4 : Entails.eval a c6220 := h 6219 (by decide)
  have h5 : Entails.eval a c6224 := h 6223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8920 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8920 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8854, some c8919, some c8874, some c8918, some c6220, some c6218, some c6224, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8920 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8920 : lratChecker f8920 p8920 = .success := by decide +kernel
theorem unsat8920 : Unsatisfiable (PosFin 65) f8920 := by
  apply lratCheckerSound f8920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8920
  · intro a ha; simp [p8920] at ha; subst a; trivial
  · exact checked8920
theorem derived8920 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8920 := by
  apply localUnsat_implies_entails f8920 [c8854, c8919, c8874, c8918, c6220, c6218, c6224] c8920 unsat8920 (by rfl) a
  have h0 : Entails.eval a c8854 := derived8854 a h
  have h1 : Entails.eval a c8919 := derived8919 a h
  have h2 : Entails.eval a c8874 := derived8874 a h
  have h3 : Entails.eval a c8918 := derived8918 a h
  have h4 : Entails.eval a c6220 := h 6219 (by decide)
  have h5 : Entails.eval a c6218 := h 6217 (by decide)
  have h6 : Entails.eval a c6224 := h 6223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8921 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8921 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8905, some c8847, some c8686, some c8421, some c8915, some c8920, some c1134, some c1082, some c4605, some c3608, some c4486, some c4211, some c763, some c843, some c6261, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8921 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8921 : lratChecker f8921 p8921 = .success := by decide +kernel
theorem unsat8921 : Unsatisfiable (PosFin 65) f8921 := by
  apply lratCheckerSound f8921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8921
  · intro a ha; simp [p8921] at ha; subst a; trivial
  · exact checked8921
theorem derived8921 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8921 := by
  apply localUnsat_implies_entails f8921 [c8905, c8847, c8686, c8421, c8915, c8920, c1134, c1082, c4605, c3608, c4486, c4211, c763, c843, c6261] c8921 unsat8921 (by rfl) a
  have h0 : Entails.eval a c8905 := derived8905 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8915 := derived8915 a h
  have h5 : Entails.eval a c8920 := derived8920 a h
  have h6 : Entails.eval a c1134 := h 1133 (by decide)
  have h7 : Entails.eval a c1082 := h 1081 (by decide)
  have h8 : Entails.eval a c4605 := h 4604 (by decide)
  have h9 : Entails.eval a c3608 := h 3607 (by decide)
  have h10 : Entails.eval a c4486 := h 4485 (by decide)
  have h11 : Entails.eval a c4211 := h 4210 (by decide)
  have h12 : Entails.eval a c763 := h 762 (by decide)
  have h13 : Entails.eval a c843 := h 842 (by decide)
  have h14 : Entails.eval a c6261 := h 6260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8922 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8922 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8849, some c7994, some c5943, some c5902, some c6191, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8922 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8922 : lratChecker f8922 p8922 = .success := by decide +kernel
theorem unsat8922 : Unsatisfiable (PosFin 65) f8922 := by
  apply lratCheckerSound f8922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8922
  · intro a ha; simp [p8922] at ha; subst a; trivial
  · exact checked8922
theorem derived8922 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8922 := by
  apply localUnsat_implies_entails f8922 [c8849, c7994, c5943, c5902, c6191] c8922 unsat8922 (by rfl) a
  have h0 : Entails.eval a c8849 := derived8849 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c5943 := h 5942 (by decide)
  have h3 : Entails.eval a c5902 := h 5901 (by decide)
  have h4 : Entails.eval a c6191 := h 6190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8923 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨12, by decide⟩, true), (⟨25, by decide⟩, false), (⟨11, by decide⟩, true), (⟨20, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8923 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4708, some c4706, some c4713, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8923 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8923 : lratChecker f8923 p8923 = .success := by decide +kernel
theorem unsat8923 : Unsatisfiable (PosFin 65) f8923 := by
  apply lratCheckerSound f8923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8923
  · intro a ha; simp [p8923] at ha; subst a; trivial
  · exact checked8923
theorem derived8923 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8923 := by
  apply localUnsat_implies_entails f8923 [c4708, c4706, c4713] c8923 unsat8923 (by rfl) a
  have h0 : Entails.eval a c4708 := h 4707 (by decide)
  have h1 : Entails.eval a c4706 := h 4705 (by decide)
  have h2 : Entails.eval a c4713 := h 4712 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8924 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨12, by decide⟩, true), (⟨54, by decide⟩, false), (⟨25, by decide⟩, false), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8924 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4449, some c6236, some c752, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8924 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8924 : lratChecker f8924 p8924 = .success := by decide +kernel
theorem unsat8924 : Unsatisfiable (PosFin 65) f8924 := by
  apply lratCheckerSound f8924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8924
  · intro a ha; simp [p8924] at ha; subst a; trivial
  · exact checked8924
theorem derived8924 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8924 := by
  apply localUnsat_implies_entails f8924 [c4449, c6236, c752] c8924 unsat8924 (by rfl) a
  have h0 : Entails.eval a c4449 := h 4448 (by decide)
  have h1 : Entails.eval a c6236 := h 6235 (by decide)
  have h2 : Entails.eval a c752 := h 751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8925 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨54, by decide⟩, false), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8925 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c6233, some c6011, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8925 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8925 : lratChecker f8925 p8925 = .success := by decide +kernel
theorem unsat8925 : Unsatisfiable (PosFin 65) f8925 := by
  apply lratCheckerSound f8925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8925
  · intro a ha; simp [p8925] at ha; subst a; trivial
  · exact checked8925
theorem derived8925 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8925 := by
  apply localUnsat_implies_entails f8925 [c7994, c6233, c6011] c8925 unsat8925 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c6233 := h 6232 (by decide)
  have h2 : Entails.eval a c6011 := h 6010 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8926 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨25, by decide⟩, false), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8926 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8925, some c1151, some c8924, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8926 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8926 : lratChecker f8926 p8926 = .success := by decide +kernel
theorem unsat8926 : Unsatisfiable (PosFin 65) f8926 := by
  apply lratCheckerSound f8926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8926
  · intro a ha; simp [p8926] at ha; subst a; trivial
  · exact checked8926
theorem derived8926 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8926 := by
  apply localUnsat_implies_entails f8926 [c8925, c1151, c8924] c8926 unsat8926 (by rfl) a
  have h0 : Entails.eval a c8925 := derived8925 a h
  have h1 : Entails.eval a c1151 := h 1150 (by decide)
  have h2 : Entails.eval a c8924 := derived8924 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8927 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8927 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8907, some c8905, some c8847, some c8686, some c8910, some c8926, some c5654, some c5673, some c6234, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8927 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8927 : lratChecker f8927 p8927 = .success := by decide +kernel
theorem unsat8927 : Unsatisfiable (PosFin 65) f8927 := by
  apply lratCheckerSound f8927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8927
  · intro a ha; simp [p8927] at ha; subst a; trivial
  · exact checked8927
theorem derived8927 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8927 := by
  apply localUnsat_implies_entails f8927 [c8907, c8905, c8847, c8686, c8910, c8926, c5654, c5673, c6234] c8927 unsat8927 (by rfl) a
  have h0 : Entails.eval a c8907 := derived8907 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c8910 := derived8910 a h
  have h5 : Entails.eval a c8926 := derived8926 a h
  have h6 : Entails.eval a c5654 := h 5653 (by decide)
  have h7 : Entails.eval a c5673 := h 5672 (by decide)
  have h8 : Entails.eval a c6234 := h 6233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8928 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨25, by decide⟩, false), (⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8928 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6236, some c5657, some c5669, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8928 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8928 : lratChecker f8928 p8928 = .success := by decide +kernel
theorem unsat8928 : Unsatisfiable (PosFin 65) f8928 := by
  apply lratCheckerSound f8928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8928
  · intro a ha; simp [p8928] at ha; subst a; trivial
  · exact checked8928
theorem derived8928 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8928 := by
  apply localUnsat_implies_entails f8928 [c6236, c5657, c5669] c8928 unsat8928 (by rfl) a
  have h0 : Entails.eval a c6236 := h 6235 (by decide)
  have h1 : Entails.eval a c5657 := h 5656 (by decide)
  have h2 : Entails.eval a c5669 := h 5668 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8929 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8929 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8905, some c8847, some c8686, some c8907, some c8927, some c8913, some c8926, some c8928, some c7994, some c6011, some c5842, some c6048, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8929 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8929 : lratChecker f8929 p8929 = .success := by decide +kernel
theorem unsat8929 : Unsatisfiable (PosFin 65) f8929 := by
  apply lratCheckerSound f8929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8929
  · intro a ha; simp [p8929] at ha; subst a; trivial
  · exact checked8929
theorem derived8929 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8929 := by
  apply localUnsat_implies_entails f8929 [c8905, c8847, c8686, c8907, c8927, c8913, c8926, c8928, c7994, c6011, c5842, c6048] c8929 unsat8929 (by rfl) a
  have h0 : Entails.eval a c8905 := derived8905 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8907 := derived8907 a h
  have h4 : Entails.eval a c8927 := derived8927 a h
  have h5 : Entails.eval a c8913 := derived8913 a h
  have h6 : Entails.eval a c8926 := derived8926 a h
  have h7 : Entails.eval a c8928 := derived8928 a h
  have h8 : Entails.eval a c7994 := derived7994 a h
  have h9 : Entails.eval a c6011 := h 6010 (by decide)
  have h10 : Entails.eval a c5842 := h 5841 (by decide)
  have h11 : Entails.eval a c6048 := h 6047 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8930 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8930 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1219, some c1220, some c1426, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8930 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8930 : lratChecker f8930 p8930 = .success := by decide +kernel
theorem unsat8930 : Unsatisfiable (PosFin 65) f8930 := by
  apply lratCheckerSound f8930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8930
  · intro a ha; simp [p8930] at ha; subst a; trivial
  · exact checked8930
theorem derived8930 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8930 := by
  apply localUnsat_implies_entails f8930 [c1219, c1220, c1426] c8930 unsat8930 (by rfl) a
  have h0 : Entails.eval a c1219 := h 1218 (by decide)
  have h1 : Entails.eval a c1220 := h 1219 (by decide)
  have h2 : Entails.eval a c1426 := h 1425 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8931 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨25, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8931 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5725, some c1151, some c4465, some c5912, some c743, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8931 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8931 : lratChecker f8931 p8931 = .success := by decide +kernel
theorem unsat8931 : Unsatisfiable (PosFin 65) f8931 := by
  apply lratCheckerSound f8931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8931
  · intro a ha; simp [p8931] at ha; subst a; trivial
  · exact checked8931
theorem derived8931 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8931 := by
  apply localUnsat_implies_entails f8931 [c5725, c1151, c4465, c5912, c743] c8931 unsat8931 (by rfl) a
  have h0 : Entails.eval a c5725 := h 5724 (by decide)
  have h1 : Entails.eval a c1151 := h 1150 (by decide)
  have h2 : Entails.eval a c4465 := h 4464 (by decide)
  have h3 : Entails.eval a c5912 := h 5911 (by decide)
  have h4 : Entails.eval a c743 := h 742 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8932 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨25, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8932 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8931, some c7994, some c5915, some c6268, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8932 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8932 : lratChecker f8932 p8932 = .success := by decide +kernel
theorem unsat8932 : Unsatisfiable (PosFin 65) f8932 := by
  apply lratCheckerSound f8932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8932
  · intro a ha; simp [p8932] at ha; subst a; trivial
  · exact checked8932
theorem derived8932 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8932 := by
  apply localUnsat_implies_entails f8932 [c8931, c7994, c5915, c6268] c8932 unsat8932 (by rfl) a
  have h0 : Entails.eval a c8931 := derived8931 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c5915 := h 5914 (by decide)
  have h3 : Entails.eval a c6268 := h 6267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8933 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨31, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8933 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5687, some c6177, some c5628, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8933 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8933 : lratChecker f8933 p8933 = .success := by decide +kernel
theorem unsat8933 : Unsatisfiable (PosFin 65) f8933 := by
  apply lratCheckerSound f8933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8933
  · intro a ha; simp [p8933] at ha; subst a; trivial
  · exact checked8933
theorem derived8933 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8933 := by
  apply localUnsat_implies_entails f8933 [c5687, c6177, c5628] c8933 unsat8933 (by rfl) a
  have h0 : Entails.eval a c5687 := h 5686 (by decide)
  have h1 : Entails.eval a c6177 := h 6176 (by decide)
  have h2 : Entails.eval a c5628 := h 5627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8934 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨31, by decide⟩, false), (⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8934 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8922, some c8932, some c8928, some c7994, some c6233, some c6126, some c5865, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8934 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8934 : lratChecker f8934 p8934 = .success := by decide +kernel
theorem unsat8934 : Unsatisfiable (PosFin 65) f8934 := by
  apply lratCheckerSound f8934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8934
  · intro a ha; simp [p8934] at ha; subst a; trivial
  · exact checked8934
theorem derived8934 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8934 := by
  apply localUnsat_implies_entails f8934 [c8922, c8932, c8928, c7994, c6233, c6126, c5865] c8934 unsat8934 (by rfl) a
  have h0 : Entails.eval a c8922 := derived8922 a h
  have h1 : Entails.eval a c8932 := derived8932 a h
  have h2 : Entails.eval a c8928 := derived8928 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c6233 := h 6232 (by decide)
  have h5 : Entails.eval a c6126 := h 6125 (by decide)
  have h6 : Entails.eval a c5865 := h 5864 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8935 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨25, by decide⟩, true), (⟨51, by decide⟩, false), (⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8935 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8905, some c8930, some c8847, some c5725, some c1151, some c4718, some c5912, some c5805, some c870, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8935 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8935 : lratChecker f8935 p8935 = .success := by decide +kernel
theorem unsat8935 : Unsatisfiable (PosFin 65) f8935 := by
  apply lratCheckerSound f8935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8935
  · intro a ha; simp [p8935] at ha; subst a; trivial
  · exact checked8935
theorem derived8935 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8935 := by
  apply localUnsat_implies_entails f8935 [c8686, c8905, c8930, c8847, c5725, c1151, c4718, c5912, c5805, c870] c8935 unsat8935 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8930 := derived8930 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c5725 := h 5724 (by decide)
  have h5 : Entails.eval a c1151 := h 1150 (by decide)
  have h6 : Entails.eval a c4718 := h 4717 (by decide)
  have h7 : Entails.eval a c5912 := h 5911 (by decide)
  have h8 : Entails.eval a c5805 := h 5804 (by decide)
  have h9 : Entails.eval a c870 := h 869 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8936 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨51, by decide⟩, false), (⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8936 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8847, some c8935, some c7994, some c5913, some c6268, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8936 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8936 : lratChecker f8936 p8936 = .success := by decide +kernel
theorem unsat8936 : Unsatisfiable (PosFin 65) f8936 := by
  apply lratCheckerSound f8936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8936
  · intro a ha; simp [p8936] at ha; subst a; trivial
  · exact checked8936
theorem derived8936 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8936 := by
  apply localUnsat_implies_entails f8936 [c8847, c8935, c7994, c5913, c6268] c8936 unsat8936 (by rfl) a
  have h0 : Entails.eval a c8847 := derived8847 a h
  have h1 : Entails.eval a c8935 := derived8935 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c5913 := h 5912 (by decide)
  have h4 : Entails.eval a c6268 := h 6267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8937 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8937 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8921, some c8905, some c8847, some c8686, some c8922, some c8929, some c8930, some c8934, some c8933, some c8936, some c8928, some c7994, some c6126, some c6268, some c5854, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8937 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8937 : lratChecker f8937 p8937 = .success := by decide +kernel
theorem unsat8937 : Unsatisfiable (PosFin 65) f8937 := by
  apply lratCheckerSound f8937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8937
  · intro a ha; simp [p8937] at ha; subst a; trivial
  · exact checked8937
theorem derived8937 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8937 := by
  apply localUnsat_implies_entails f8937 [c8921, c8905, c8847, c8686, c8922, c8929, c8930, c8934, c8933, c8936, c8928, c7994, c6126, c6268, c5854] c8937 unsat8937 (by rfl) a
  have h0 : Entails.eval a c8921 := derived8921 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c8922 := derived8922 a h
  have h5 : Entails.eval a c8929 := derived8929 a h
  have h6 : Entails.eval a c8930 := derived8930 a h
  have h7 : Entails.eval a c8934 := derived8934 a h
  have h8 : Entails.eval a c8933 := derived8933 a h
  have h9 : Entails.eval a c8936 := derived8936 a h
  have h10 : Entails.eval a c8928 := derived8928 a h
  have h11 : Entails.eval a c7994 := derived7994 a h
  have h12 : Entails.eval a c6126 := h 6125 (by decide)
  have h13 : Entails.eval a c6268 := h 6267 (by decide)
  have h14 : Entails.eval a c5854 := h 5853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8938 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8938 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1192, some c1203, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8938 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8938 : lratChecker f8938 p8938 = .success := by decide +kernel
theorem unsat8938 : Unsatisfiable (PosFin 65) f8938 := by
  apply lratCheckerSound f8938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8938
  · intro a ha; simp [p8938] at ha; subst a; trivial
  · exact checked8938
theorem derived8938 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8938 := by
  apply localUnsat_implies_entails f8938 [c1192, c1203] c8938 unsat8938 (by rfl) a
  have h0 : Entails.eval a c1192 := h 1191 (by decide)
  have h1 : Entails.eval a c1203 := h 1202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8939 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨30, by decide⟩, true), (⟨8, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨49, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8939 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3672, some c4208, some c979, some c5670, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8939 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8939 : lratChecker f8939 p8939 = .success := by decide +kernel
theorem unsat8939 : Unsatisfiable (PosFin 65) f8939 := by
  apply lratCheckerSound f8939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8939
  · intro a ha; simp [p8939] at ha; subst a; trivial
  · exact checked8939
theorem derived8939 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8939 := by
  apply localUnsat_implies_entails f8939 [c3672, c4208, c979, c5670] c8939 unsat8939 (by rfl) a
  have h0 : Entails.eval a c3672 := h 3671 (by decide)
  have h1 : Entails.eval a c4208 := h 4207 (by decide)
  have h2 : Entails.eval a c979 := h 978 (by decide)
  have h3 : Entails.eval a c5670 := h 5669 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8940 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨8, by decide⟩, false), (⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8940 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8939, some c8624, some c5502, some c132, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8940 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8940 : lratChecker f8940 p8940 = .success := by decide +kernel
theorem unsat8940 : Unsatisfiable (PosFin 65) f8940 := by
  apply lratCheckerSound f8940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8940
  · intro a ha; simp [p8940] at ha; subst a; trivial
  · exact checked8940
theorem derived8940 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8940 := by
  apply localUnsat_implies_entails f8940 [c8939, c8624, c5502, c132] c8940 unsat8940 (by rfl) a
  have h0 : Entails.eval a c8939 := derived8939 a h
  have h1 : Entails.eval a c8624 := derived8624 a h
  have h2 : Entails.eval a c5502 := h 5501 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8941 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨63, by decide⟩, true), (⟨20, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8941 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5948, some c5950, some c5959, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8941 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8941 : lratChecker f8941 p8941 = .success := by decide +kernel
theorem unsat8941 : Unsatisfiable (PosFin 65) f8941 := by
  apply lratCheckerSound f8941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8941
  · intro a ha; simp [p8941] at ha; subst a; trivial
  · exact checked8941
theorem derived8941 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8941 := by
  apply localUnsat_implies_entails f8941 [c5948, c5950, c5959] c8941 unsat8941 (by rfl) a
  have h0 : Entails.eval a c5948 := h 5947 (by decide)
  have h1 : Entails.eval a c5950 := h 5949 (by decide)
  have h2 : Entails.eval a c5959 := h 5958 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8942 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨28, by decide⟩, true), (⟨63, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8942 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5879, some c6164, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8942 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8942 : lratChecker f8942 p8942 = .success := by decide +kernel
theorem unsat8942 : Unsatisfiable (PosFin 65) f8942 := by
  apply lratCheckerSound f8942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8942
  · intro a ha; simp [p8942] at ha; subst a; trivial
  · exact checked8942
theorem derived8942 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8942 := by
  apply localUnsat_implies_entails f8942 [c5879, c6164] c8942 unsat8942 (by rfl) a
  have h0 : Entails.eval a c5879 := h 5878 (by decide)
  have h1 : Entails.eval a c6164 := h 6163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8943 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨8, by decide⟩, false), (⟨63, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8943 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8942, some c804, some c790, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8943 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8943 : lratChecker f8943 p8943 = .success := by decide +kernel
theorem unsat8943 : Unsatisfiable (PosFin 65) f8943 := by
  apply lratCheckerSound f8943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8943
  · intro a ha; simp [p8943] at ha; subst a; trivial
  · exact checked8943
theorem derived8943 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8943 := by
  apply localUnsat_implies_entails f8943 [c8942, c804, c790] c8943 unsat8943 (by rfl) a
  have h0 : Entails.eval a c8942 := derived8942 a h
  have h1 : Entails.eval a c804 := h 803 (by decide)
  have h2 : Entails.eval a c790 := h 789 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8944 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨12, by decide⟩, true), (⟨64, by decide⟩, true), (⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8944 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5879, some c4451, some c8593, some c748, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8944 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8944 : lratChecker f8944 p8944 = .success := by decide +kernel
theorem unsat8944 : Unsatisfiable (PosFin 65) f8944 := by
  apply lratCheckerSound f8944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8944
  · intro a ha; simp [p8944] at ha; subst a; trivial
  · exact checked8944
theorem derived8944 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8944 := by
  apply localUnsat_implies_entails f8944 [c5879, c4451, c8593, c748] c8944 unsat8944 (by rfl) a
  have h0 : Entails.eval a c5879 := h 5878 (by decide)
  have h1 : Entails.eval a c4451 := h 4450 (by decide)
  have h2 : Entails.eval a c8593 := derived8593 a h
  have h3 : Entails.eval a c748 := h 747 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8945 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨8, by decide⟩, false), (⟨64, by decide⟩, true), (⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8945 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8941, some c8944, some c790, some c798, some c8593, some c753, some c4430, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8945 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8945 : lratChecker f8945 p8945 = .success := by decide +kernel
theorem unsat8945 : Unsatisfiable (PosFin 65) f8945 := by
  apply lratCheckerSound f8945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8945
  · intro a ha; simp [p8945] at ha; subst a; trivial
  · exact checked8945
theorem derived8945 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8945 := by
  apply localUnsat_implies_entails f8945 [c8941, c8944, c790, c798, c8593, c753, c4430] c8945 unsat8945 (by rfl) a
  have h0 : Entails.eval a c8941 := derived8941 a h
  have h1 : Entails.eval a c8944 := derived8944 a h
  have h2 : Entails.eval a c790 := h 789 (by decide)
  have h3 : Entails.eval a c798 := h 797 (by decide)
  have h4 : Entails.eval a c8593 := derived8593 a h
  have h5 : Entails.eval a c753 := h 752 (by decide)
  have h6 : Entails.eval a c4430 := h 4429 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8946 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨18, by decide⟩, false), (⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8946 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8604, some c8943, some c8945, some c251, some c250, some c2753, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8946 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8946 : lratChecker f8946 p8946 = .success := by decide +kernel
theorem unsat8946 : Unsatisfiable (PosFin 65) f8946 := by
  apply lratCheckerSound f8946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8946
  · intro a ha; simp [p8946] at ha; subst a; trivial
  · exact checked8946
theorem derived8946 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8946 := by
  apply localUnsat_implies_entails f8946 [c8604, c8943, c8945, c251, c250, c2753] c8946 unsat8946 (by rfl) a
  have h0 : Entails.eval a c8604 := derived8604 a h
  have h1 : Entails.eval a c8943 := derived8943 a h
  have h2 : Entails.eval a c8945 := derived8945 a h
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c250 := h 249 (by decide)
  have h5 : Entails.eval a c2753 := h 2752 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8947 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8947 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c759, some c748, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8947 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8947 : lratChecker f8947 p8947 = .success := by decide +kernel
theorem unsat8947 : Unsatisfiable (PosFin 65) f8947 := by
  apply lratCheckerSound f8947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8947
  · intro a ha; simp [p8947] at ha; subst a; trivial
  · exact checked8947
theorem derived8947 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8947 := by
  apply localUnsat_implies_entails f8947 [c759, c748] c8947 unsat8947 (by rfl) a
  have h0 : Entails.eval a c759 := h 758 (by decide)
  have h1 : Entails.eval a c748 := h 747 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8948 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8948 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8937, some c8921, some c8905, some c8847, some c8686, some c8421, some c8941, some c8708, some c8946, some c4426, some c1248, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8948 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8948 : lratChecker f8948 p8948 = .success := by decide +kernel
theorem unsat8948 : Unsatisfiable (PosFin 65) f8948 := by
  apply lratCheckerSound f8948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8948
  · intro a ha; simp [p8948] at ha; subst a; trivial
  · exact checked8948
theorem derived8948 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8948 := by
  apply localUnsat_implies_entails f8948 [c8937, c8921, c8905, c8847, c8686, c8421, c8941, c8708, c8946, c4426, c1248] c8948 unsat8948 (by rfl) a
  have h0 : Entails.eval a c8937 := derived8937 a h
  have h1 : Entails.eval a c8921 := derived8921 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8941 := derived8941 a h
  have h7 : Entails.eval a c8708 := derived8708 a h
  have h8 : Entails.eval a c8946 := derived8946 a h
  have h9 : Entails.eval a c4426 := h 4425 (by decide)
  have h10 : Entails.eval a c1248 := h 1247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8949 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨25, by decide⟩, true), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8949 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8938, some c8905, some c8421, some c8947, some c8948, some c1272, some c4905, some c299, some c5953, some c313, some c4485, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8949 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8949 : lratChecker f8949 p8949 = .success := by decide +kernel
theorem unsat8949 : Unsatisfiable (PosFin 65) f8949 := by
  apply lratCheckerSound f8949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8949
  · intro a ha; simp [p8949] at ha; subst a; trivial
  · exact checked8949
theorem derived8949 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8949 := by
  apply localUnsat_implies_entails f8949 [c8938, c8905, c8421, c8947, c8948, c1272, c4905, c299, c5953, c313, c4485] c8949 unsat8949 (by rfl) a
  have h0 : Entails.eval a c8938 := derived8938 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8947 := derived8947 a h
  have h4 : Entails.eval a c8948 := derived8948 a h
  have h5 : Entails.eval a c1272 := h 1271 (by decide)
  have h6 : Entails.eval a c4905 := h 4904 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c5953 := h 5952 (by decide)
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c4485 := h 4484 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8950 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8950 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8921, some c8686, some c8949, some c6184, some c5646, some c6210, some c5673, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8950 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8950 : lratChecker f8950 p8950 = .success := by decide +kernel
theorem unsat8950 : Unsatisfiable (PosFin 65) f8950 := by
  apply lratCheckerSound f8950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8950
  · intro a ha; simp [p8950] at ha; subst a; trivial
  · exact checked8950
theorem derived8950 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8950 := by
  apply localUnsat_implies_entails f8950 [c8921, c8686, c8949, c6184, c5646, c6210, c5673] c8950 unsat8950 (by rfl) a
  have h0 : Entails.eval a c8921 := derived8921 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8949 := derived8949 a h
  have h3 : Entails.eval a c6184 := h 6183 (by decide)
  have h4 : Entails.eval a c5646 := h 5645 (by decide)
  have h5 : Entails.eval a c6210 := h 6209 (by decide)
  have h6 : Entails.eval a c5673 := h 5672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8950

end CochromaticTwenty.Certificates.FixedCore0
