import MerLeanExperiment.Certificates.FixedCore0.Steps0200_0299

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7851 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨57, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7851 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7848, some c7826, some c7830, some c7712, some c6794, some c7067, some c6826, some c6324, some c6944, some c6553, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7851 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7851 : lratChecker f7851 p7851 = .success := by decide +kernel
theorem unsat7851 : Unsatisfiable (PosFin 65) f7851 := by
  apply lratCheckerSound f7851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7851
  · intro a ha; simp [p7851] at ha; subst a; trivial
  · exact checked7851
theorem derived7851 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7851 := by
  apply localUnsat_implies_entails f7851 [c7848, c7826, c7830, c7712, c6794, c7067, c6826, c6324, c6944, c6553] c7851 unsat7851 (by rfl) a
  have h0 : Entails.eval a c7848 := derived7848 a h
  have h1 : Entails.eval a c7826 := derived7826 a h
  have h2 : Entails.eval a c7830 := derived7830 a h
  have h3 : Entails.eval a c7712 := derived7712 a h
  have h4 : Entails.eval a c6794 := h 6793 (by decide)
  have h5 : Entails.eval a c7067 := h 7066 (by decide)
  have h6 : Entails.eval a c6826 := h 6825 (by decide)
  have h7 : Entails.eval a c6324 := h 6323 (by decide)
  have h8 : Entails.eval a c6944 := h 6943 (by decide)
  have h9 : Entails.eval a c6553 := h 6552 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7852 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7852 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7848, some c7826, some c7830, some c7712, some c7850, some c7851, some c7833, some c7000, some c6826, some c6801, some c7801, some c7326, some c7145, some c7797, some c6517, some c7796, some c434, some c427, some c415, some c2440, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7852 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7852 : lratChecker f7852 p7852 = .success := by decide +kernel
theorem unsat7852 : Unsatisfiable (PosFin 65) f7852 := by
  apply lratCheckerSound f7852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7852
  · intro a ha; simp [p7852] at ha; subst a; trivial
  · exact checked7852
theorem derived7852 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7852 := by
  apply localUnsat_implies_entails f7852 [c7848, c7826, c7830, c7712, c7850, c7851, c7833, c7000, c6826, c6801, c7801, c7326, c7145, c7797, c6517, c7796, c434, c427, c415, c2440] c7852 unsat7852 (by rfl) a
  have h0 : Entails.eval a c7848 := derived7848 a h
  have h1 : Entails.eval a c7826 := derived7826 a h
  have h2 : Entails.eval a c7830 := derived7830 a h
  have h3 : Entails.eval a c7712 := derived7712 a h
  have h4 : Entails.eval a c7850 := derived7850 a h
  have h5 : Entails.eval a c7851 := derived7851 a h
  have h6 : Entails.eval a c7833 := derived7833 a h
  have h7 : Entails.eval a c7000 := h 6999 (by decide)
  have h8 : Entails.eval a c6826 := h 6825 (by decide)
  have h9 : Entails.eval a c6801 := h 6800 (by decide)
  have h10 : Entails.eval a c7801 := derived7801 a h
  have h11 : Entails.eval a c7326 := h 7325 (by decide)
  have h12 : Entails.eval a c7145 := h 7144 (by decide)
  have h13 : Entails.eval a c7797 := derived7797 a h
  have h14 : Entails.eval a c6517 := h 6516 (by decide)
  have h15 : Entails.eval a c7796 := derived7796 a h
  have h16 : Entails.eval a c434 := h 433 (by decide)
  have h17 : Entails.eval a c427 := h 426 (by decide)
  have h18 : Entails.eval a c415 := h 414 (by decide)
  have h19 : Entails.eval a c2440 := h 2439 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7853 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨41, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7853 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7398, some c7371, some c7172, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7853 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7853 : lratChecker f7853 p7853 = .success := by decide +kernel
theorem unsat7853 : Unsatisfiable (PosFin 65) f7853 := by
  apply lratCheckerSound f7853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7853
  · intro a ha; simp [p7853] at ha; subst a; trivial
  · exact checked7853
theorem derived7853 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7853 := by
  apply localUnsat_implies_entails f7853 [c7398, c7371, c7172] c7853 unsat7853 (by rfl) a
  have h0 : Entails.eval a c7398 := h 7397 (by decide)
  have h1 : Entails.eval a c7371 := h 7370 (by decide)
  have h2 : Entails.eval a c7172 := h 7171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7854 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7854 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7848, some c7826, some c7853, some c7852, some c7172, some c7145, some c7245, some c7290, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7854 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7854 : lratChecker f7854 p7854 = .success := by decide +kernel
theorem unsat7854 : Unsatisfiable (PosFin 65) f7854 := by
  apply lratCheckerSound f7854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7854
  · intro a ha; simp [p7854] at ha; subst a; trivial
  · exact checked7854
theorem derived7854 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7854 := by
  apply localUnsat_implies_entails f7854 [c7830, c7848, c7826, c7853, c7852, c7172, c7145, c7245, c7290] c7854 unsat7854 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7848 := derived7848 a h
  have h2 : Entails.eval a c7826 := derived7826 a h
  have h3 : Entails.eval a c7853 := derived7853 a h
  have h4 : Entails.eval a c7852 := derived7852 a h
  have h5 : Entails.eval a c7172 := h 7171 (by decide)
  have h6 : Entails.eval a c7145 := h 7144 (by decide)
  have h7 : Entails.eval a c7245 := h 7244 (by decide)
  have h8 : Entails.eval a c7290 := h 7289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7855 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7855 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7848, some c7826, some c7853, some c7852, some c7854, some c6916, some c6826, some c6756, some c7718, some c6293, some c7789, some c7072, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7855 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7855 : lratChecker f7855 p7855 = .success := by decide +kernel
theorem unsat7855 : Unsatisfiable (PosFin 65) f7855 := by
  apply lratCheckerSound f7855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7855
  · intro a ha; simp [p7855] at ha; subst a; trivial
  · exact checked7855
theorem derived7855 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7855 := by
  apply localUnsat_implies_entails f7855 [c7830, c7848, c7826, c7853, c7852, c7854, c6916, c6826, c6756, c7718, c6293, c7789, c7072] c7855 unsat7855 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7848 := derived7848 a h
  have h2 : Entails.eval a c7826 := derived7826 a h
  have h3 : Entails.eval a c7853 := derived7853 a h
  have h4 : Entails.eval a c7852 := derived7852 a h
  have h5 : Entails.eval a c7854 := derived7854 a h
  have h6 : Entails.eval a c6916 := h 6915 (by decide)
  have h7 : Entails.eval a c6826 := h 6825 (by decide)
  have h8 : Entails.eval a c6756 := h 6755 (by decide)
  have h9 : Entails.eval a c7718 := derived7718 a h
  have h10 : Entails.eval a c6293 := h 6292 (by decide)
  have h11 : Entails.eval a c7789 := derived7789 a h
  have h12 : Entails.eval a c7072 := h 7071 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7856 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨36, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨35, by decide⟩, false), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7856 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c437, some c427, some c415, some c2443, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7856 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7856 : lratChecker f7856 p7856 = .success := by decide +kernel
theorem unsat7856 : Unsatisfiable (PosFin 65) f7856 := by
  apply lratCheckerSound f7856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7856
  · intro a ha; simp [p7856] at ha; subst a; trivial
  · exact checked7856
theorem derived7856 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7856 := by
  apply localUnsat_implies_entails f7856 [c7830, c437, c427, c415, c2443] c7856 unsat7856 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c437 := h 436 (by decide)
  have h2 : Entails.eval a c427 := h 426 (by decide)
  have h3 : Entails.eval a c415 := h 414 (by decide)
  have h4 : Entails.eval a c2443 := h 2442 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7857 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7857 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c2967, some c2443, some c453, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7857 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7857 : lratChecker f7857 p7857 = .success := by decide +kernel
theorem unsat7857 : Unsatisfiable (PosFin 65) f7857 := by
  apply lratCheckerSound f7857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7857
  · intro a ha; simp [p7857] at ha; subst a; trivial
  · exact checked7857
theorem derived7857 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7857 := by
  apply localUnsat_implies_entails f7857 [c7830, c2967, c2443, c453] c7857 unsat7857 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c2967 := h 2966 (by decide)
  have h2 : Entails.eval a c2443 := h 2442 (by decide)
  have h3 : Entails.eval a c453 := h 452 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7858 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨35, by decide⟩, false), (⟨39, by decide⟩, false), (⟨55, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7858 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c482, some c473, some c1535, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7858 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7858 : lratChecker f7858 p7858 = .success := by decide +kernel
theorem unsat7858 : Unsatisfiable (PosFin 65) f7858 := by
  apply lratCheckerSound f7858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7858
  · intro a ha; simp [p7858] at ha; subst a; trivial
  · exact checked7858
theorem derived7858 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7858 := by
  apply localUnsat_implies_entails f7858 [c7830, c482, c473, c1535] c7858 unsat7858 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c482 := h 481 (by decide)
  have h2 : Entails.eval a c473 := h 472 (by decide)
  have h3 : Entails.eval a c1535 := h 1534 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7859 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true), (⟨55, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7859 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c6916, some c6826, some c6808, some c6756, some c7718, some c7333, some c6293, some c6664, some c7271, some c7072, some c7480, some c7856, some c7858, some c7857, some c500, some c506, some c1968, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7859 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7859 : lratChecker f7859 p7859 = .success := by decide +kernel
theorem unsat7859 : Unsatisfiable (PosFin 65) f7859 := by
  apply lratCheckerSound f7859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7859
  · intro a ha; simp [p7859] at ha; subst a; trivial
  · exact checked7859
theorem derived7859 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7859 := by
  apply localUnsat_implies_entails f7859 [c7830, c6916, c6826, c6808, c6756, c7718, c7333, c6293, c6664, c7271, c7072, c7480, c7856, c7858, c7857, c500, c506, c1968] c7859 unsat7859 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c6916 := h 6915 (by decide)
  have h2 : Entails.eval a c6826 := h 6825 (by decide)
  have h3 : Entails.eval a c6808 := h 6807 (by decide)
  have h4 : Entails.eval a c6756 := h 6755 (by decide)
  have h5 : Entails.eval a c7718 := derived7718 a h
  have h6 : Entails.eval a c7333 := h 7332 (by decide)
  have h7 : Entails.eval a c6293 := h 6292 (by decide)
  have h8 : Entails.eval a c6664 := h 6663 (by decide)
  have h9 : Entails.eval a c7271 := h 7270 (by decide)
  have h10 : Entails.eval a c7072 := h 7071 (by decide)
  have h11 : Entails.eval a c7480 := h 7479 (by decide)
  have h12 : Entails.eval a c7856 := derived7856 a h
  have h13 : Entails.eval a c7858 := derived7858 a h
  have h14 : Entails.eval a c7857 := derived7857 a h
  have h15 : Entails.eval a c500 := h 499 (by decide)
  have h16 : Entails.eval a c506 := h 505 (by decide)
  have h17 : Entails.eval a c1968 := h 1967 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7860 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨55, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7860 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7209, some c7127, some c7194, some c7333, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7860 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7860 : lratChecker f7860 p7860 = .success := by decide +kernel
theorem unsat7860 : Unsatisfiable (PosFin 65) f7860 := by
  apply lratCheckerSound f7860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7860
  · intro a ha; simp [p7860] at ha; subst a; trivial
  · exact checked7860
theorem derived7860 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7860 := by
  apply localUnsat_implies_entails f7860 [c7209, c7127, c7194, c7333] c7860 unsat7860 (by rfl) a
  have h0 : Entails.eval a c7209 := h 7208 (by decide)
  have h1 : Entails.eval a c7127 := h 7126 (by decide)
  have h2 : Entails.eval a c7194 := h 7193 (by decide)
  have h3 : Entails.eval a c7333 := h 7332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7861 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7861 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7860, some c7853, some c7859, some c7172, some c7145, some c7245, some c7290, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7861 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7861 : lratChecker f7861 p7861 = .success := by decide +kernel
theorem unsat7861 : Unsatisfiable (PosFin 65) f7861 := by
  apply lratCheckerSound f7861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7861
  · intro a ha; simp [p7861] at ha; subst a; trivial
  · exact checked7861
theorem derived7861 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7861 := by
  apply localUnsat_implies_entails f7861 [c7830, c7860, c7853, c7859, c7172, c7145, c7245, c7290] c7861 unsat7861 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7860 := derived7860 a h
  have h2 : Entails.eval a c7853 := derived7853 a h
  have h3 : Entails.eval a c7859 := derived7859 a h
  have h4 : Entails.eval a c7172 := h 7171 (by decide)
  have h5 : Entails.eval a c7145 := h 7144 (by decide)
  have h6 : Entails.eval a c7245 := h 7244 (by decide)
  have h7 : Entails.eval a c7290 := h 7289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7862 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7862 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7861, some c7855, some c7830, some c7712, some c7172, some c7145, some c6419, some c7285, some c6829, some c6301, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7862 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7862 : lratChecker f7862 p7862 = .success := by decide +kernel
theorem unsat7862 : Unsatisfiable (PosFin 65) f7862 := by
  apply lratCheckerSound f7862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7862
  · intro a ha; simp [p7862] at ha; subst a; trivial
  · exact checked7862
theorem derived7862 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7862 := by
  apply localUnsat_implies_entails f7862 [c7861, c7855, c7830, c7712, c7172, c7145, c6419, c7285, c6829, c6301] c7862 unsat7862 (by rfl) a
  have h0 : Entails.eval a c7861 := derived7861 a h
  have h1 : Entails.eval a c7855 := derived7855 a h
  have h2 : Entails.eval a c7830 := derived7830 a h
  have h3 : Entails.eval a c7712 := derived7712 a h
  have h4 : Entails.eval a c7172 := h 7171 (by decide)
  have h5 : Entails.eval a c7145 := h 7144 (by decide)
  have h6 : Entails.eval a c6419 := h 6418 (by decide)
  have h7 : Entails.eval a c7285 := h 7284 (by decide)
  have h8 : Entails.eval a c6829 := h 6828 (by decide)
  have h9 : Entails.eval a c6301 := h 6300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7863 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7863 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7862, some c7861, some c7855, some c7830, some c7712, some c6797, some c7190, some c6916, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7863 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7863 : lratChecker f7863 p7863 = .success := by decide +kernel
theorem unsat7863 : Unsatisfiable (PosFin 65) f7863 := by
  apply lratCheckerSound f7863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7863
  · intro a ha; simp [p7863] at ha; subst a; trivial
  · exact checked7863
theorem derived7863 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7863 := by
  apply localUnsat_implies_entails f7863 [c7862, c7861, c7855, c7830, c7712, c6797, c7190, c6916] c7863 unsat7863 (by rfl) a
  have h0 : Entails.eval a c7862 := derived7862 a h
  have h1 : Entails.eval a c7861 := derived7861 a h
  have h2 : Entails.eval a c7855 := derived7855 a h
  have h3 : Entails.eval a c7830 := derived7830 a h
  have h4 : Entails.eval a c7712 := derived7712 a h
  have h5 : Entails.eval a c6797 := h 6796 (by decide)
  have h6 : Entails.eval a c7190 := h 7189 (by decide)
  have h7 : Entails.eval a c6916 := h 6915 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7864 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7864 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7863, some c7861, some c7855, some c7830, some c7712, some c7307, some c7285, some c7324, some c7502, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7864 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7864 : lratChecker f7864 p7864 = .success := by decide +kernel
theorem unsat7864 : Unsatisfiable (PosFin 65) f7864 := by
  apply lratCheckerSound f7864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7864
  · intro a ha; simp [p7864] at ha; subst a; trivial
  · exact checked7864
theorem derived7864 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7864 := by
  apply localUnsat_implies_entails f7864 [c7863, c7861, c7855, c7830, c7712, c7307, c7285, c7324, c7502] c7864 unsat7864 (by rfl) a
  have h0 : Entails.eval a c7863 := derived7863 a h
  have h1 : Entails.eval a c7861 := derived7861 a h
  have h2 : Entails.eval a c7855 := derived7855 a h
  have h3 : Entails.eval a c7830 := derived7830 a h
  have h4 : Entails.eval a c7712 := derived7712 a h
  have h5 : Entails.eval a c7307 := h 7306 (by decide)
  have h6 : Entails.eval a c7285 := h 7284 (by decide)
  have h7 : Entails.eval a c7324 := h 7323 (by decide)
  have h8 : Entails.eval a c7502 := h 7501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7865 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7865 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7864, some c7130, some c7712, some c7863, some c7853, some c7271, some c7801, some c7861, some c7855, some c7458, some c6690, some c7072, some c7862, some c6916, some c6816, some c6528, some c431, some c503, some c500, some c1968, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7865 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked7865 : lratChecker f7865 p7865 = .success := by decide +kernel
theorem unsat7865 : Unsatisfiable (PosFin 65) f7865 := by
  apply lratCheckerSound f7865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7865
  · intro a ha; simp [p7865] at ha; subst a; trivial
  · exact checked7865
theorem derived7865 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7865 := by
  apply localUnsat_implies_entails f7865 [c7830, c7864, c7130, c7712, c7863, c7853, c7271, c7801, c7861, c7855, c7458, c6690, c7072, c7862, c6916, c6816, c6528, c431, c503, c500, c1968] c7865 unsat7865 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7864 := derived7864 a h
  have h2 : Entails.eval a c7130 := h 7129 (by decide)
  have h3 : Entails.eval a c7712 := derived7712 a h
  have h4 : Entails.eval a c7863 := derived7863 a h
  have h5 : Entails.eval a c7853 := derived7853 a h
  have h6 : Entails.eval a c7271 := h 7270 (by decide)
  have h7 : Entails.eval a c7801 := derived7801 a h
  have h8 : Entails.eval a c7861 := derived7861 a h
  have h9 : Entails.eval a c7855 := derived7855 a h
  have h10 : Entails.eval a c7458 := h 7457 (by decide)
  have h11 : Entails.eval a c6690 := h 6689 (by decide)
  have h12 : Entails.eval a c7072 := h 7071 (by decide)
  have h13 : Entails.eval a c7862 := derived7862 a h
  have h14 : Entails.eval a c6916 := h 6915 (by decide)
  have h15 : Entails.eval a c6816 := h 6815 (by decide)
  have h16 : Entails.eval a c6528 := h 6527 (by decide)
  have h17 : Entails.eval a c431 := h 430 (by decide)
  have h18 : Entails.eval a c503 := h 502 (by decide)
  have h19 : Entails.eval a c500 := h 499 (by decide)
  have h20 : Entails.eval a c1968 := h 1967 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7866 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7866 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1535, some c1968, some c2034, some c4053, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7866 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7866 : lratChecker f7866 p7866 = .success := by decide +kernel
theorem unsat7866 : Unsatisfiable (PosFin 65) f7866 := by
  apply lratCheckerSound f7866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7866
  · intro a ha; simp [p7866] at ha; subst a; trivial
  · exact checked7866
theorem derived7866 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7866 := by
  apply localUnsat_implies_entails f7866 [c1535, c1968, c2034, c4053] c7866 unsat7866 (by rfl) a
  have h0 : Entails.eval a c1535 := h 1534 (by decide)
  have h1 : Entails.eval a c1968 := h 1967 (by decide)
  have h2 : Entails.eval a c2034 := h 2033 (by decide)
  have h3 : Entails.eval a c4053 := h 4052 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7867 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7867 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7865, some c7830, some c7862, some c7864, some c7130, some c6916, some c7853, some c7861, some c7855, some c7712, some c539, some c482, some c2948, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7867 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7867 : lratChecker f7867 p7867 = .success := by decide +kernel
theorem unsat7867 : Unsatisfiable (PosFin 65) f7867 := by
  apply lratCheckerSound f7867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7867
  · intro a ha; simp [p7867] at ha; subst a; trivial
  · exact checked7867
theorem derived7867 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7867 := by
  apply localUnsat_implies_entails f7867 [c7865, c7830, c7862, c7864, c7130, c6916, c7853, c7861, c7855, c7712, c539, c482, c2948] c7867 unsat7867 (by rfl) a
  have h0 : Entails.eval a c7865 := derived7865 a h
  have h1 : Entails.eval a c7830 := derived7830 a h
  have h2 : Entails.eval a c7862 := derived7862 a h
  have h3 : Entails.eval a c7864 := derived7864 a h
  have h4 : Entails.eval a c7130 := h 7129 (by decide)
  have h5 : Entails.eval a c6916 := h 6915 (by decide)
  have h6 : Entails.eval a c7853 := derived7853 a h
  have h7 : Entails.eval a c7861 := derived7861 a h
  have h8 : Entails.eval a c7855 := derived7855 a h
  have h9 : Entails.eval a c7712 := derived7712 a h
  have h10 : Entails.eval a c539 := h 538 (by decide)
  have h11 : Entails.eval a c482 := h 481 (by decide)
  have h12 : Entails.eval a c2948 := h 2947 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7868 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7868 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7855, some c7830, some c7712, some c7861, some c7862, some c7863, some c7864, some c7130, some c7853, some c6916, some c7271, some c6816, some c7801, some c6528, some c7865, some c7867, some c7866, some c427, some c415, some c2448, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7868 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7868 : lratChecker f7868 p7868 = .success := by decide +kernel
theorem unsat7868 : Unsatisfiable (PosFin 65) f7868 := by
  apply lratCheckerSound f7868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7868
  · intro a ha; simp [p7868] at ha; subst a; trivial
  · exact checked7868
theorem derived7868 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7868 := by
  apply localUnsat_implies_entails f7868 [c7855, c7830, c7712, c7861, c7862, c7863, c7864, c7130, c7853, c6916, c7271, c6816, c7801, c6528, c7865, c7867, c7866, c427, c415, c2448] c7868 unsat7868 (by rfl) a
  have h0 : Entails.eval a c7855 := derived7855 a h
  have h1 : Entails.eval a c7830 := derived7830 a h
  have h2 : Entails.eval a c7712 := derived7712 a h
  have h3 : Entails.eval a c7861 := derived7861 a h
  have h4 : Entails.eval a c7862 := derived7862 a h
  have h5 : Entails.eval a c7863 := derived7863 a h
  have h6 : Entails.eval a c7864 := derived7864 a h
  have h7 : Entails.eval a c7130 := h 7129 (by decide)
  have h8 : Entails.eval a c7853 := derived7853 a h
  have h9 : Entails.eval a c6916 := h 6915 (by decide)
  have h10 : Entails.eval a c7271 := h 7270 (by decide)
  have h11 : Entails.eval a c6816 := h 6815 (by decide)
  have h12 : Entails.eval a c7801 := derived7801 a h
  have h13 : Entails.eval a c6528 := h 6527 (by decide)
  have h14 : Entails.eval a c7865 := derived7865 a h
  have h15 : Entails.eval a c7867 := derived7867 a h
  have h16 : Entails.eval a c7866 := derived7866 a h
  have h17 : Entails.eval a c427 := h 426 (by decide)
  have h18 : Entails.eval a c415 := h 414 (by decide)
  have h19 : Entails.eval a c2448 := h 2447 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7869 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨55, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7869 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7868, some c7855, some c7830, some c7712, some c7271, some c6642, some c7214, some c6667, some c6662, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7869 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7869 : lratChecker f7869 p7869 = .success := by decide +kernel
theorem unsat7869 : Unsatisfiable (PosFin 65) f7869 := by
  apply lratCheckerSound f7869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7869
  · intro a ha; simp [p7869] at ha; subst a; trivial
  · exact checked7869
theorem derived7869 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7869 := by
  apply localUnsat_implies_entails f7869 [c7868, c7855, c7830, c7712, c7271, c6642, c7214, c6667, c6662] c7869 unsat7869 (by rfl) a
  have h0 : Entails.eval a c7868 := derived7868 a h
  have h1 : Entails.eval a c7855 := derived7855 a h
  have h2 : Entails.eval a c7830 := derived7830 a h
  have h3 : Entails.eval a c7712 := derived7712 a h
  have h4 : Entails.eval a c7271 := h 7270 (by decide)
  have h5 : Entails.eval a c6642 := h 6641 (by decide)
  have h6 : Entails.eval a c7214 := h 7213 (by decide)
  have h7 : Entails.eval a c6667 := h 6666 (by decide)
  have h8 : Entails.eval a c6662 := h 6661 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7870 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨34, by decide⟩, false), (⟨55, by decide⟩, true), (⟨37, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7870 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7214, some c7231, some c6757, some c6764, some c6758, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p7870 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7870 : lratChecker f7870 p7870 = .success := by decide +kernel
theorem unsat7870 : Unsatisfiable (PosFin 65) f7870 := by
  apply lratCheckerSound f7870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7870
  · intro a ha; simp [p7870] at ha; subst a; trivial
  · exact checked7870
theorem derived7870 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7870 := by
  apply localUnsat_implies_entails f7870 [c7214, c7231, c6757, c6764, c6758] c7870 unsat7870 (by rfl) a
  have h0 : Entails.eval a c7214 := h 7213 (by decide)
  have h1 : Entails.eval a c7231 := h 7230 (by decide)
  have h2 : Entails.eval a c6757 := h 6756 (by decide)
  have h3 : Entails.eval a c6764 := h 6763 (by decide)
  have h4 : Entails.eval a c6758 := h 6757 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7871 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨38, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7871 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7000, some c7405, some c6992, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7871 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7871 : lratChecker f7871 p7871 = .success := by decide +kernel
theorem unsat7871 : Unsatisfiable (PosFin 65) f7871 := by
  apply lratCheckerSound f7871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7871
  · intro a ha; simp [p7871] at ha; subst a; trivial
  · exact checked7871
theorem derived7871 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7871 := by
  apply localUnsat_implies_entails f7871 [c7000, c7405, c6992] c7871 unsat7871 (by rfl) a
  have h0 : Entails.eval a c7000 := h 6999 (by decide)
  have h1 : Entails.eval a c7405 := h 7404 (by decide)
  have h2 : Entails.eval a c6992 := h 6991 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7872 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨55, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7872 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7868, some c7855, some c7830, some c7712, some c6642, some c7870, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7872 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7872 : lratChecker f7872 p7872 = .success := by decide +kernel
theorem unsat7872 : Unsatisfiable (PosFin 65) f7872 := by
  apply lratCheckerSound f7872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7872
  · intro a ha; simp [p7872] at ha; subst a; trivial
  · exact checked7872
theorem derived7872 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7872 := by
  apply localUnsat_implies_entails f7872 [c7868, c7855, c7830, c7712, c6642, c7870] c7872 unsat7872 (by rfl) a
  have h0 : Entails.eval a c7868 := derived7868 a h
  have h1 : Entails.eval a c7855 := derived7855 a h
  have h2 : Entails.eval a c7830 := derived7830 a h
  have h3 : Entails.eval a c7712 := derived7712 a h
  have h4 : Entails.eval a c6642 := h 6641 (by decide)
  have h5 : Entails.eval a c7870 := derived7870 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7873 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨55, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7873 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7872, some c7830, some c7869, some c7871, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7873 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7873 : lratChecker f7873 p7873 = .success := by decide +kernel
theorem unsat7873 : Unsatisfiable (PosFin 65) f7873 := by
  apply lratCheckerSound f7873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7873
  · intro a ha; simp [p7873] at ha; subst a; trivial
  · exact checked7873
theorem derived7873 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7873 := by
  apply localUnsat_implies_entails f7873 [c7872, c7830, c7869, c7871] c7873 unsat7873 (by rfl) a
  have h0 : Entails.eval a c7872 := derived7872 a h
  have h1 : Entails.eval a c7830 := derived7830 a h
  have h2 : Entails.eval a c7869 := derived7869 a h
  have h3 : Entails.eval a c7871 := derived7871 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7874 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨64, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7874 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6367, some c7157, some c6298, some c6630, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7874 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7874 : lratChecker f7874 p7874 = .success := by decide +kernel
theorem unsat7874 : Unsatisfiable (PosFin 65) f7874 := by
  apply lratCheckerSound f7874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7874
  · intro a ha; simp [p7874] at ha; subst a; trivial
  · exact checked7874
theorem derived7874 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7874 := by
  apply localUnsat_implies_entails f7874 [c6367, c7157, c6298, c6630] c7874 unsat7874 (by rfl) a
  have h0 : Entails.eval a c6367 := h 6366 (by decide)
  have h1 : Entails.eval a c7157 := h 7156 (by decide)
  have h2 : Entails.eval a c6298 := h 6297 (by decide)
  have h3 : Entails.eval a c6630 := h 6629 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7875 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7875 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c7868, some c7874, some c7873, some c6612, some c6636, some c7000, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7875 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7875 : lratChecker f7875 p7875 = .success := by decide +kernel
theorem unsat7875 : Unsatisfiable (PosFin 65) f7875 := by
  apply lratCheckerSound f7875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7875
  · intro a ha; simp [p7875] at ha; subst a; trivial
  · exact checked7875
theorem derived7875 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7875 := by
  apply localUnsat_implies_entails f7875 [c7830, c7868, c7874, c7873, c6612, c6636, c7000] c7875 unsat7875 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c7868 := derived7868 a h
  have h2 : Entails.eval a c7874 := derived7874 a h
  have h3 : Entails.eval a c7873 := derived7873 a h
  have h4 : Entails.eval a c6612 := h 6611 (by decide)
  have h5 : Entails.eval a c6636 := h 6635 (by decide)
  have h6 : Entails.eval a c7000 := h 6999 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7876 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7876 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7271, some c7871, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7876 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7876 : lratChecker f7876 p7876 = .success := by decide +kernel
theorem unsat7876 : Unsatisfiable (PosFin 65) f7876 := by
  apply lratCheckerSound f7876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7876
  · intro a ha; simp [p7876] at ha; subst a; trivial
  · exact checked7876
theorem derived7876 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7876 := by
  apply localUnsat_implies_entails f7876 [c7271, c7871] c7876 unsat7876 (by rfl) a
  have h0 : Entails.eval a c7271 := h 7270 (by decide)
  have h1 : Entails.eval a c7871 := derived7871 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7877 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7877 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7712, some c7830, some c7855, some c7868, some c7874, some c7873, some c7875, some c7876, some c7223, some c6743, some c6664, some c6970, some c7839, some c7228, some c7434, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7877 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7877 : lratChecker f7877 p7877 = .success := by decide +kernel
theorem unsat7877 : Unsatisfiable (PosFin 65) f7877 := by
  apply lratCheckerSound f7877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7877
  · intro a ha; simp [p7877] at ha; subst a; trivial
  · exact checked7877
theorem derived7877 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7877 := by
  apply localUnsat_implies_entails f7877 [c7712, c7830, c7855, c7868, c7874, c7873, c7875, c7876, c7223, c6743, c6664, c6970, c7839, c7228, c7434] c7877 unsat7877 (by rfl) a
  have h0 : Entails.eval a c7712 := derived7712 a h
  have h1 : Entails.eval a c7830 := derived7830 a h
  have h2 : Entails.eval a c7855 := derived7855 a h
  have h3 : Entails.eval a c7868 := derived7868 a h
  have h4 : Entails.eval a c7874 := derived7874 a h
  have h5 : Entails.eval a c7873 := derived7873 a h
  have h6 : Entails.eval a c7875 := derived7875 a h
  have h7 : Entails.eval a c7876 := derived7876 a h
  have h8 : Entails.eval a c7223 := h 7222 (by decide)
  have h9 : Entails.eval a c6743 := h 6742 (by decide)
  have h10 : Entails.eval a c6664 := h 6663 (by decide)
  have h11 : Entails.eval a c6970 := h 6969 (by decide)
  have h12 : Entails.eval a c7839 := derived7839 a h
  have h13 : Entails.eval a c7228 := h 7227 (by decide)
  have h14 : Entails.eval a c7434 := h 7433 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7878 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨50, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7878 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7228, some c6369, some c7539, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p7878 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7878 : lratChecker f7878 p7878 = .success := by decide +kernel
theorem unsat7878 : Unsatisfiable (PosFin 65) f7878 := by
  apply lratCheckerSound f7878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7878
  · intro a ha; simp [p7878] at ha; subst a; trivial
  · exact checked7878
theorem derived7878 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7878 := by
  apply localUnsat_implies_entails f7878 [c7228, c6369, c7539] c7878 unsat7878 (by rfl) a
  have h0 : Entails.eval a c7228 := h 7227 (by decide)
  have h1 : Entails.eval a c6369 := h 6368 (by decide)
  have h2 : Entails.eval a c7539 := h 7538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7879 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨36, by decide⟩, false), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7879 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7023, some c7240, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7879 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7879 : lratChecker f7879 p7879 = .success := by decide +kernel
theorem unsat7879 : Unsatisfiable (PosFin 65) f7879 := by
  apply lratCheckerSound f7879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7879
  · intro a ha; simp [p7879] at ha; subst a; trivial
  · exact checked7879
theorem derived7879 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7879 := by
  apply localUnsat_implies_entails f7879 [c7023, c7240] c7879 unsat7879 (by rfl) a
  have h0 : Entails.eval a c7023 := h 7022 (by decide)
  have h1 : Entails.eval a c7240 := h 7239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7880 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨35, by decide⟩, true), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨38, by decide⟩, true), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true), (⟨59, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7880 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6840, some c7234, some c6918, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7880 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7880 : lratChecker f7880 p7880 = .success := by decide +kernel
theorem unsat7880 : Unsatisfiable (PosFin 65) f7880 := by
  apply lratCheckerSound f7880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7880
  · intro a ha; simp [p7880] at ha; subst a; trivial
  · exact checked7880
theorem derived7880 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7880 := by
  apply localUnsat_implies_entails f7880 [c6840, c7234, c6918] c7880 unsat7880 (by rfl) a
  have h0 : Entails.eval a c6840 := h 6839 (by decide)
  have h1 : Entails.eval a c7234 := h 7233 (by decide)
  have h2 : Entails.eval a c6918 := h 6917 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7881 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨36, by decide⟩, false), (⟨55, by decide⟩, false), (⟨38, by decide⟩, true), (⟨37, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7881 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7876, some c7879, some c6642, some c7877, some c7317, some c7839, some c6353, some c6431, some c6419, some c6855, some c7878, some c7880, some c6694, some c7051, some c7100, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7881 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7881 : lratChecker f7881 p7881 = .success := by decide +kernel
theorem unsat7881 : Unsatisfiable (PosFin 65) f7881 := by
  apply lratCheckerSound f7881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7881
  · intro a ha; simp [p7881] at ha; subst a; trivial
  · exact checked7881
theorem derived7881 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7881 := by
  apply localUnsat_implies_entails f7881 [c7876, c7879, c6642, c7877, c7317, c7839, c6353, c6431, c6419, c6855, c7878, c7880, c6694, c7051, c7100] c7881 unsat7881 (by rfl) a
  have h0 : Entails.eval a c7876 := derived7876 a h
  have h1 : Entails.eval a c7879 := derived7879 a h
  have h2 : Entails.eval a c6642 := h 6641 (by decide)
  have h3 : Entails.eval a c7877 := derived7877 a h
  have h4 : Entails.eval a c7317 := h 7316 (by decide)
  have h5 : Entails.eval a c7839 := derived7839 a h
  have h6 : Entails.eval a c6353 := h 6352 (by decide)
  have h7 : Entails.eval a c6431 := h 6430 (by decide)
  have h8 : Entails.eval a c6419 := h 6418 (by decide)
  have h9 : Entails.eval a c6855 := h 6854 (by decide)
  have h10 : Entails.eval a c7878 := derived7878 a h
  have h11 : Entails.eval a c7880 := derived7880 a h
  have h12 : Entails.eval a c6694 := h 6693 (by decide)
  have h13 : Entails.eval a c7051 := h 7050 (by decide)
  have h14 : Entails.eval a c7100 := h 7099 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7882 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨55, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7882 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6686, some c6294, some c6415, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7882 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7882 : lratChecker f7882 p7882 = .success := by decide +kernel
theorem unsat7882 : Unsatisfiable (PosFin 65) f7882 := by
  apply lratCheckerSound f7882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7882
  · intro a ha; simp [p7882] at ha; subst a; trivial
  · exact checked7882
theorem derived7882 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7882 := by
  apply localUnsat_implies_entails f7882 [c6686, c6294, c6415] c7882 unsat7882 (by rfl) a
  have h0 : Entails.eval a c6686 := h 6685 (by decide)
  have h1 : Entails.eval a c6294 := h 6293 (by decide)
  have h2 : Entails.eval a c6415 := h 6414 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7883 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨38, by decide⟩, true), (⟨37, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7883 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7876, some c6642, some c7882, some c6970, some c7881, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7883 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7883 : lratChecker f7883 p7883 = .success := by decide +kernel
theorem unsat7883 : Unsatisfiable (PosFin 65) f7883 := by
  apply lratCheckerSound f7883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7883
  · intro a ha; simp [p7883] at ha; subst a; trivial
  · exact checked7883
theorem derived7883 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7883 := by
  apply localUnsat_implies_entails f7883 [c7876, c6642, c7882, c6970, c7881] c7883 unsat7883 (by rfl) a
  have h0 : Entails.eval a c7876 := derived7876 a h
  have h1 : Entails.eval a c6642 := h 6641 (by decide)
  have h2 : Entails.eval a c7882 := derived7882 a h
  have h3 : Entails.eval a c6970 := h 6969 (by decide)
  have h4 : Entails.eval a c7881 := derived7881 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7884 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨36, by decide⟩, false), (⟨38, by decide⟩, true), (⟨37, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7884 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7883, some c7876, some c6642, some c7879, some c7870, some c7877, some c7310, some c7839, some c6349, some c6431, some c6419, some c6855, some c7880, some c6694, some c7051, some c7100, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7884 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7884 : lratChecker f7884 p7884 = .success := by decide +kernel
theorem unsat7884 : Unsatisfiable (PosFin 65) f7884 := by
  apply lratCheckerSound f7884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7884
  · intro a ha; simp [p7884] at ha; subst a; trivial
  · exact checked7884
theorem derived7884 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7884 := by
  apply localUnsat_implies_entails f7884 [c7883, c7876, c6642, c7879, c7870, c7877, c7310, c7839, c6349, c6431, c6419, c6855, c7880, c6694, c7051, c7100] c7884 unsat7884 (by rfl) a
  have h0 : Entails.eval a c7883 := derived7883 a h
  have h1 : Entails.eval a c7876 := derived7876 a h
  have h2 : Entails.eval a c6642 := h 6641 (by decide)
  have h3 : Entails.eval a c7879 := derived7879 a h
  have h4 : Entails.eval a c7870 := derived7870 a h
  have h5 : Entails.eval a c7877 := derived7877 a h
  have h6 : Entails.eval a c7310 := h 7309 (by decide)
  have h7 : Entails.eval a c7839 := derived7839 a h
  have h8 : Entails.eval a c6349 := h 6348 (by decide)
  have h9 : Entails.eval a c6431 := h 6430 (by decide)
  have h10 : Entails.eval a c6419 := h 6418 (by decide)
  have h11 : Entails.eval a c6855 := h 6854 (by decide)
  have h12 : Entails.eval a c7880 := derived7880 a h
  have h13 : Entails.eval a c6694 := h 6693 (by decide)
  have h14 : Entails.eval a c7051 := h 7050 (by decide)
  have h15 : Entails.eval a c7100 := h 7099 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7885 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7885 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6298, some c6690, some c6419, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7885 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7885 : lratChecker f7885 p7885 = .success := by decide +kernel
theorem unsat7885 : Unsatisfiable (PosFin 65) f7885 := by
  apply lratCheckerSound f7885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7885
  · intro a ha; simp [p7885] at ha; subst a; trivial
  · exact checked7885
theorem derived7885 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7885 := by
  apply localUnsat_implies_entails f7885 [c6298, c6690, c6419] c7885 unsat7885 (by rfl) a
  have h0 : Entails.eval a c6298 := h 6297 (by decide)
  have h1 : Entails.eval a c6690 := h 6689 (by decide)
  have h2 : Entails.eval a c6419 := h 6418 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7886 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨37, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7886 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7876, some c6642, some c7885, some c6970, some c7884, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7886 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7886 : lratChecker f7886 p7886 = .success := by decide +kernel
theorem unsat7886 : Unsatisfiable (PosFin 65) f7886 := by
  apply lratCheckerSound f7886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7886
  · intro a ha; simp [p7886] at ha; subst a; trivial
  · exact checked7886
theorem derived7886 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7886 := by
  apply localUnsat_implies_entails f7886 [c7876, c6642, c7885, c6970, c7884] c7886 unsat7886 (by rfl) a
  have h0 : Entails.eval a c7876 := derived7876 a h
  have h1 : Entails.eval a c6642 := h 6641 (by decide)
  have h2 : Entails.eval a c7885 := derived7885 a h
  have h3 : Entails.eval a c6970 := h 6969 (by decide)
  have h4 : Entails.eval a c7884 := derived7884 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7887 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨35, by decide⟩, false), (⟨36, by decide⟩, false), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7887 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7879, some c7005, some c7011, some c7013, some c7012, some c6856, some c7212, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7887 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7887 : lratChecker f7887 p7887 = .success := by decide +kernel
theorem unsat7887 : Unsatisfiable (PosFin 65) f7887 := by
  apply lratCheckerSound f7887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7887
  · intro a ha; simp [p7887] at ha; subst a; trivial
  · exact checked7887
theorem derived7887 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7887 := by
  apply localUnsat_implies_entails f7887 [c7879, c7005, c7011, c7013, c7012, c6856, c7212] c7887 unsat7887 (by rfl) a
  have h0 : Entails.eval a c7879 := derived7879 a h
  have h1 : Entails.eval a c7005 := h 7004 (by decide)
  have h2 : Entails.eval a c7011 := h 7010 (by decide)
  have h3 : Entails.eval a c7013 := h 7012 (by decide)
  have h4 : Entails.eval a c7012 := h 7011 (by decide)
  have h5 : Entails.eval a c6856 := h 6855 (by decide)
  have h6 : Entails.eval a c7212 := h 7211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7888 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨37, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7888 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7876, some c7879, some c6642, some c7886, some c6652, some c7877, some c6888, some c6855, some c6528, some c7887, some c6391, some c7461, some c7096, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7888 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7888 : lratChecker f7888 p7888 = .success := by decide +kernel
theorem unsat7888 : Unsatisfiable (PosFin 65) f7888 := by
  apply lratCheckerSound f7888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7888
  · intro a ha; simp [p7888] at ha; subst a; trivial
  · exact checked7888
theorem derived7888 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7888 := by
  apply localUnsat_implies_entails f7888 [c7876, c7879, c6642, c7886, c6652, c7877, c6888, c6855, c6528, c7887, c6391, c7461, c7096] c7888 unsat7888 (by rfl) a
  have h0 : Entails.eval a c7876 := derived7876 a h
  have h1 : Entails.eval a c7879 := derived7879 a h
  have h2 : Entails.eval a c6642 := h 6641 (by decide)
  have h3 : Entails.eval a c7886 := derived7886 a h
  have h4 : Entails.eval a c6652 := h 6651 (by decide)
  have h5 : Entails.eval a c7877 := derived7877 a h
  have h6 : Entails.eval a c6888 := h 6887 (by decide)
  have h7 : Entails.eval a c6855 := h 6854 (by decide)
  have h8 : Entails.eval a c6528 := h 6527 (by decide)
  have h9 : Entails.eval a c7887 := derived7887 a h
  have h10 : Entails.eval a c6391 := h 6390 (by decide)
  have h11 : Entails.eval a c7461 := h 7460 (by decide)
  have h12 : Entails.eval a c7096 := h 7095 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7889 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨37, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7889 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7876, some c6642, some c7886, some c6652, some c7888, some c7038, some c6916, some c6528, some c6855, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7889 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7889 : lratChecker f7889 p7889 = .success := by decide +kernel
theorem unsat7889 : Unsatisfiable (PosFin 65) f7889 := by
  apply lratCheckerSound f7889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7889
  · intro a ha; simp [p7889] at ha; subst a; trivial
  · exact checked7889
theorem derived7889 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7889 := by
  apply localUnsat_implies_entails f7889 [c7876, c6642, c7886, c6652, c7888, c7038, c6916, c6528, c6855] c7889 unsat7889 (by rfl) a
  have h0 : Entails.eval a c7876 := derived7876 a h
  have h1 : Entails.eval a c6642 := h 6641 (by decide)
  have h2 : Entails.eval a c7886 := derived7886 a h
  have h3 : Entails.eval a c6652 := h 6651 (by decide)
  have h4 : Entails.eval a c7888 := derived7888 a h
  have h5 : Entails.eval a c7038 := h 7037 (by decide)
  have h6 : Entails.eval a c6916 := h 6915 (by decide)
  have h7 : Entails.eval a c6528 := h 6527 (by decide)
  have h8 : Entails.eval a c6855 := h 6854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7890 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨44, by decide⟩, true), (⟨36, by decide⟩, false), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7890 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7879, some c7887, some c7253, some c7235, some c7227, some c7234, some c6856, some c7212, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7890 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7890 : lratChecker f7890 p7890 = .success := by decide +kernel
theorem unsat7890 : Unsatisfiable (PosFin 65) f7890 := by
  apply lratCheckerSound f7890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7890
  · intro a ha; simp [p7890] at ha; subst a; trivial
  · exact checked7890
theorem derived7890 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7890 := by
  apply localUnsat_implies_entails f7890 [c7879, c7887, c7253, c7235, c7227, c7234, c6856, c7212] c7890 unsat7890 (by rfl) a
  have h0 : Entails.eval a c7879 := derived7879 a h
  have h1 : Entails.eval a c7887 := derived7887 a h
  have h2 : Entails.eval a c7253 := h 7252 (by decide)
  have h3 : Entails.eval a c7235 := h 7234 (by decide)
  have h4 : Entails.eval a c7227 := h 7226 (by decide)
  have h5 : Entails.eval a c7234 := h 7233 (by decide)
  have h6 : Entails.eval a c6856 := h 6855 (by decide)
  have h7 : Entails.eval a c7212 := h 7211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7891 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨36, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, true), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7891 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6916, some c6902, some c7038, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7891 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7891 : lratChecker f7891 p7891 = .success := by decide +kernel
theorem unsat7891 : Unsatisfiable (PosFin 65) f7891 := by
  apply lratCheckerSound f7891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7891
  · intro a ha; simp [p7891] at ha; subst a; trivial
  · exact checked7891
theorem derived7891 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7891 := by
  apply localUnsat_implies_entails f7891 [c6916, c6902, c7038] c7891 unsat7891 (by rfl) a
  have h0 : Entails.eval a c6916 := h 6915 (by decide)
  have h1 : Entails.eval a c6902 := h 6901 (by decide)
  have h2 : Entails.eval a c7038 := h 7037 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7892 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨37, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7892 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7876, some c6642, some c7886, some c6652, some c7877, some c7889, some c7891, some c6298, some c7890, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7892 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7892 : lratChecker f7892 p7892 = .success := by decide +kernel
theorem unsat7892 : Unsatisfiable (PosFin 65) f7892 := by
  apply lratCheckerSound f7892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7892
  · intro a ha; simp [p7892] at ha; subst a; trivial
  · exact checked7892
theorem derived7892 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7892 := by
  apply localUnsat_implies_entails f7892 [c7876, c6642, c7886, c6652, c7877, c7889, c7891, c6298, c7890] c7892 unsat7892 (by rfl) a
  have h0 : Entails.eval a c7876 := derived7876 a h
  have h1 : Entails.eval a c6642 := h 6641 (by decide)
  have h2 : Entails.eval a c7886 := derived7886 a h
  have h3 : Entails.eval a c6652 := h 6651 (by decide)
  have h4 : Entails.eval a c7877 := derived7877 a h
  have h5 : Entails.eval a c7889 := derived7889 a h
  have h6 : Entails.eval a c7891 := derived7891 a h
  have h7 : Entails.eval a c6298 := h 6297 (by decide)
  have h8 : Entails.eval a c7890 := derived7890 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7893 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7893 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6391, some c7235, some c7227, some c7234, some c6856, some c7212, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7893 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7893 : lratChecker f7893 p7893 = .success := by decide +kernel
theorem unsat7893 : Unsatisfiable (PosFin 65) f7893 := by
  apply lratCheckerSound f7893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7893
  · intro a ha; simp [p7893] at ha; subst a; trivial
  · exact checked7893
theorem derived7893 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7893 := by
  apply localUnsat_implies_entails f7893 [c6391, c7235, c7227, c7234, c6856, c7212] c7893 unsat7893 (by rfl) a
  have h0 : Entails.eval a c6391 := h 6390 (by decide)
  have h1 : Entails.eval a c7235 := h 7234 (by decide)
  have h2 : Entails.eval a c7227 := h 7226 (by decide)
  have h3 : Entails.eval a c7234 := h 7233 (by decide)
  have h4 : Entails.eval a c6856 := h 6855 (by decide)
  have h5 : Entails.eval a c7212 := h 7211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7894 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7894 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7224, some c6744, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7894 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7894 : lratChecker f7894 p7894 = .success := by decide +kernel
theorem unsat7894 : Unsatisfiable (PosFin 65) f7894 := by
  apply lratCheckerSound f7894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7894
  · intro a ha; simp [p7894] at ha; subst a; trivial
  · exact checked7894
theorem derived7894 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7894 := by
  apply localUnsat_implies_entails f7894 [c7224, c6744] c7894 unsat7894 (by rfl) a
  have h0 : Entails.eval a c7224 := h 7223 (by decide)
  have h1 : Entails.eval a c6744 := h 6743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7895 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨48, by decide⟩, false), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7895 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6374, some c7440, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p7895 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7895 : lratChecker f7895 p7895 = .success := by decide +kernel
theorem unsat7895 : Unsatisfiable (PosFin 65) f7895 := by
  apply lratCheckerSound f7895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7895
  · intro a ha; simp [p7895] at ha; subst a; trivial
  · exact checked7895
theorem derived7895 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7895 := by
  apply localUnsat_implies_entails f7895 [c6374, c7440] c7895 unsat7895 (by rfl) a
  have h0 : Entails.eval a c6374 := h 6373 (by decide)
  have h1 : Entails.eval a c7440 := h 7439 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7896 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨51, by decide⟩, false), (⟨48, by decide⟩, false), (⟨61, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7896 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7433, some c6654, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7896 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7896 : lratChecker f7896 p7896 = .success := by decide +kernel
theorem unsat7896 : Unsatisfiable (PosFin 65) f7896 := by
  apply lratCheckerSound f7896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7896
  · intro a ha; simp [p7896] at ha; subst a; trivial
  · exact checked7896
theorem derived7896 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7896 := by
  apply localUnsat_implies_entails f7896 [c7433, c6654] c7896 unsat7896 (by rfl) a
  have h0 : Entails.eval a c7433 := h 7432 (by decide)
  have h1 : Entails.eval a c6654 := h 6653 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7897 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨36, by decide⟩, true), (⟨41, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7897 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7893, some c7895, some c7896, some c6971, some c7073, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7897 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7897 : lratChecker f7897 p7897 = .success := by decide +kernel
theorem unsat7897 : Unsatisfiable (PosFin 65) f7897 := by
  apply lratCheckerSound f7897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7897
  · intro a ha; simp [p7897] at ha; subst a; trivial
  · exact checked7897
theorem derived7897 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7897 := by
  apply localUnsat_implies_entails f7897 [c7893, c7895, c7896, c6971, c7073] c7897 unsat7897 (by rfl) a
  have h0 : Entails.eval a c7893 := derived7893 a h
  have h1 : Entails.eval a c7895 := derived7895 a h
  have h2 : Entails.eval a c7896 := derived7896 a h
  have h3 : Entails.eval a c6971 := h 6970 (by decide)
  have h4 : Entails.eval a c7073 := h 7072 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7898 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨46, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨41, by decide⟩, true), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7898 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7110, some c6549, some c7449, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p7898 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7898 : lratChecker f7898 p7898 = .success := by decide +kernel
theorem unsat7898 : Unsatisfiable (PosFin 65) f7898 := by
  apply lratCheckerSound f7898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7898
  · intro a ha; simp [p7898] at ha; subst a; trivial
  · exact checked7898
theorem derived7898 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7898 := by
  apply localUnsat_implies_entails f7898 [c7110, c6549, c7449] c7898 unsat7898 (by rfl) a
  have h0 : Entails.eval a c7110 := h 7109 (by decide)
  have h1 : Entails.eval a c6549 := h 6548 (by decide)
  have h2 : Entails.eval a c7449 := h 7448 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7899 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7899 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7876, some c7877, some c6642, some c7886, some c6652, some c7892, some c6970, some c6794, some c6298, some c6690, some c6855, some c6528, some c7894, some c7897, some c7592, some c7898, some c6862, some c7359, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7899 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7899 : lratChecker f7899 p7899 = .success := by decide +kernel
theorem unsat7899 : Unsatisfiable (PosFin 65) f7899 := by
  apply lratCheckerSound f7899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7899
  · intro a ha; simp [p7899] at ha; subst a; trivial
  · exact checked7899
theorem derived7899 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7899 := by
  apply localUnsat_implies_entails f7899 [c7876, c7877, c6642, c7886, c6652, c7892, c6970, c6794, c6298, c6690, c6855, c6528, c7894, c7897, c7592, c7898, c6862, c7359] c7899 unsat7899 (by rfl) a
  have h0 : Entails.eval a c7876 := derived7876 a h
  have h1 : Entails.eval a c7877 := derived7877 a h
  have h2 : Entails.eval a c6642 := h 6641 (by decide)
  have h3 : Entails.eval a c7886 := derived7886 a h
  have h4 : Entails.eval a c6652 := h 6651 (by decide)
  have h5 : Entails.eval a c7892 := derived7892 a h
  have h6 : Entails.eval a c6970 := h 6969 (by decide)
  have h7 : Entails.eval a c6794 := h 6793 (by decide)
  have h8 : Entails.eval a c6298 := h 6297 (by decide)
  have h9 : Entails.eval a c6690 := h 6689 (by decide)
  have h10 : Entails.eval a c6855 := h 6854 (by decide)
  have h11 : Entails.eval a c6528 := h 6527 (by decide)
  have h12 : Entails.eval a c7894 := derived7894 a h
  have h13 : Entails.eval a c7897 := derived7897 a h
  have h14 : Entails.eval a c7592 := derived7592 a h
  have h15 : Entails.eval a c7898 := derived7898 a h
  have h16 : Entails.eval a c6862 := h 6861 (by decide)
  have h17 : Entails.eval a c7359 := h 7358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7900 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7900 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7899, some c7876, some c7877, some c6826, some c6863, some c6861, some c6858, some c6800, some c6857, some c7461, some c7326, some c6655, some c6690, some c6870, some c7597, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7900 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7900 : lratChecker f7900 p7900 = .success := by decide +kernel
theorem unsat7900 : Unsatisfiable (PosFin 65) f7900 := by
  apply lratCheckerSound f7900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7900
  · intro a ha; simp [p7900] at ha; subst a; trivial
  · exact checked7900
theorem derived7900 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7900 := by
  apply localUnsat_implies_entails f7900 [c7899, c7876, c7877, c6826, c6863, c6861, c6858, c6800, c6857, c7461, c7326, c6655, c6690, c6870, c7597] c7900 unsat7900 (by rfl) a
  have h0 : Entails.eval a c7899 := derived7899 a h
  have h1 : Entails.eval a c7876 := derived7876 a h
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c6826 := h 6825 (by decide)
  have h4 : Entails.eval a c6863 := h 6862 (by decide)
  have h5 : Entails.eval a c6861 := h 6860 (by decide)
  have h6 : Entails.eval a c6858 := h 6857 (by decide)
  have h7 : Entails.eval a c6800 := h 6799 (by decide)
  have h8 : Entails.eval a c6857 := h 6856 (by decide)
  have h9 : Entails.eval a c7461 := h 7460 (by decide)
  have h10 : Entails.eval a c7326 := h 7325 (by decide)
  have h11 : Entails.eval a c6655 := h 6654 (by decide)
  have h12 : Entails.eval a c6690 := h 6689 (by decide)
  have h13 : Entails.eval a c6870 := h 6869 (by decide)
  have h14 : Entails.eval a c7597 := derived7597 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7901 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7901 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7899, some c7876, some c6902, some c7187, some c7172, some c6916, some c6528, some c6286, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7901 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7901 : lratChecker f7901 p7901 = .success := by decide +kernel
theorem unsat7901 : Unsatisfiable (PosFin 65) f7901 := by
  apply lratCheckerSound f7901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7901
  · intro a ha; simp [p7901] at ha; subst a; trivial
  · exact checked7901
theorem derived7901 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7901 := by
  apply localUnsat_implies_entails f7901 [c7899, c7876, c6902, c7187, c7172, c6916, c6528, c6286] c7901 unsat7901 (by rfl) a
  have h0 : Entails.eval a c7899 := derived7899 a h
  have h1 : Entails.eval a c7876 := derived7876 a h
  have h2 : Entails.eval a c6902 := h 6901 (by decide)
  have h3 : Entails.eval a c7187 := h 7186 (by decide)
  have h4 : Entails.eval a c7172 := h 7171 (by decide)
  have h5 : Entails.eval a c6916 := h 6915 (by decide)
  have h6 : Entails.eval a c6528 := h 6527 (by decide)
  have h7 : Entails.eval a c6286 := h 6285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7902 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7902 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6690, some c7899, some c7901, some c6826, some c7172, some c6528, some c6286, some c7072, some c6702, some c7356, some c7664, some c7663, some c5161, some c5148, some c5135, some c5537, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7902 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7902 : lratChecker f7902 p7902 = .success := by decide +kernel
theorem unsat7902 : Unsatisfiable (PosFin 65) f7902 := by
  apply lratCheckerSound f7902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7902
  · intro a ha; simp [p7902] at ha; subst a; trivial
  · exact checked7902
theorem derived7902 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7902 := by
  apply localUnsat_implies_entails f7902 [c6690, c7899, c7901, c6826, c7172, c6528, c6286, c7072, c6702, c7356, c7664, c7663, c5161, c5148, c5135, c5537] c7902 unsat7902 (by rfl) a
  have h0 : Entails.eval a c6690 := h 6689 (by decide)
  have h1 : Entails.eval a c7899 := derived7899 a h
  have h2 : Entails.eval a c7901 := derived7901 a h
  have h3 : Entails.eval a c6826 := h 6825 (by decide)
  have h4 : Entails.eval a c7172 := h 7171 (by decide)
  have h5 : Entails.eval a c6528 := h 6527 (by decide)
  have h6 : Entails.eval a c6286 := h 6285 (by decide)
  have h7 : Entails.eval a c7072 := h 7071 (by decide)
  have h8 : Entails.eval a c6702 := h 6701 (by decide)
  have h9 : Entails.eval a c7356 := h 7355 (by decide)
  have h10 : Entails.eval a c7664 := derived7664 a h
  have h11 : Entails.eval a c7663 := derived7663 a h
  have h12 : Entails.eval a c5161 := h 5160 (by decide)
  have h13 : Entails.eval a c5148 := h 5147 (by decide)
  have h14 : Entails.eval a c5135 := h 5134 (by decide)
  have h15 : Entails.eval a c5537 := h 5536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7903 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨20, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7903 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5149, some c5136, some c5538, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7903 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7903 : lratChecker f7903 p7903 = .success := by decide +kernel
theorem unsat7903 : Unsatisfiable (PosFin 65) f7903 := by
  apply lratCheckerSound f7903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7903
  · intro a ha; simp [p7903] at ha; subst a; trivial
  · exact checked7903
theorem derived7903 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7903 := by
  apply localUnsat_implies_entails f7903 [c5149, c5136, c5538] c7903 unsat7903 (by rfl) a
  have h0 : Entails.eval a c5149 := h 5148 (by decide)
  have h1 : Entails.eval a c5136 := h 5135 (by decide)
  have h2 : Entails.eval a c5538 := h 5537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7904 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨61, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7904 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7790, some c5413, some c5346, some c5247, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7904 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7904 : lratChecker f7904 p7904 = .success := by decide +kernel
theorem unsat7904 : Unsatisfiable (PosFin 65) f7904 := by
  apply lratCheckerSound f7904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7904
  · intro a ha; simp [p7904] at ha; subst a; trivial
  · exact checked7904
theorem derived7904 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7904 := by
  apply localUnsat_implies_entails f7904 [c7877, c7790, c5413, c5346, c5247] c7904 unsat7904 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7790 := derived7790 a h
  have h2 : Entails.eval a c5413 := h 5412 (by decide)
  have h3 : Entails.eval a c5346 := h 5345 (by decide)
  have h4 : Entails.eval a c5247 := h 5246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7905 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨36, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7905 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5162, some c7903, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7905 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7905 : lratChecker f7905 p7905 = .success := by decide +kernel
theorem unsat7905 : Unsatisfiable (PosFin 65) f7905 := by
  apply lratCheckerSound f7905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7905
  · intro a ha; simp [p7905] at ha; subst a; trivial
  · exact checked7905
theorem derived7905 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7905 := by
  apply localUnsat_implies_entails f7905 [c5162, c7903] c7905 unsat7905 (by rfl) a
  have h0 : Entails.eval a c5162 := h 5161 (by decide)
  have h1 : Entails.eval a c7903 := derived7903 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7906 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7906 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5538, some c5719, some c5739, some c5619, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7906 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7906 : lratChecker f7906 p7906 = .success := by decide +kernel
theorem unsat7906 : Unsatisfiable (PosFin 65) f7906 := by
  apply lratCheckerSound f7906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7906
  · intro a ha; simp [p7906] at ha; subst a; trivial
  · exact checked7906
theorem derived7906 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7906 := by
  apply localUnsat_implies_entails f7906 [c5538, c5719, c5739, c5619] c7906 unsat7906 (by rfl) a
  have h0 : Entails.eval a c5538 := h 5537 (by decide)
  have h1 : Entails.eval a c5719 := h 5718 (by decide)
  have h2 : Entails.eval a c5739 := h 5738 (by decide)
  have h3 : Entails.eval a c5619 := h 5618 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7907 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7907 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7899, some c7901, some c6826, some c6690, some c7172, some c6528, some c6286, some c7072, some c7902, some c7905, some c7904, some c5220, some c5199, some c7906, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7907 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7907 : lratChecker f7907 p7907 = .success := by decide +kernel
theorem unsat7907 : Unsatisfiable (PosFin 65) f7907 := by
  apply lratCheckerSound f7907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7907
  · intro a ha; simp [p7907] at ha; subst a; trivial
  · exact checked7907
theorem derived7907 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7907 := by
  apply localUnsat_implies_entails f7907 [c7899, c7901, c6826, c6690, c7172, c6528, c6286, c7072, c7902, c7905, c7904, c5220, c5199, c7906] c7907 unsat7907 (by rfl) a
  have h0 : Entails.eval a c7899 := derived7899 a h
  have h1 : Entails.eval a c7901 := derived7901 a h
  have h2 : Entails.eval a c6826 := h 6825 (by decide)
  have h3 : Entails.eval a c6690 := h 6689 (by decide)
  have h4 : Entails.eval a c7172 := h 7171 (by decide)
  have h5 : Entails.eval a c6528 := h 6527 (by decide)
  have h6 : Entails.eval a c6286 := h 6285 (by decide)
  have h7 : Entails.eval a c7072 := h 7071 (by decide)
  have h8 : Entails.eval a c7902 := derived7902 a h
  have h9 : Entails.eval a c7905 := derived7905 a h
  have h10 : Entails.eval a c7904 := derived7904 a h
  have h11 : Entails.eval a c5220 := h 5219 (by decide)
  have h12 : Entails.eval a c5199 := h 5198 (by decide)
  have h13 : Entails.eval a c7906 := derived7906 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7908 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7908 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7907, some c7901, some c7899, some c7876, some c7877, some c7478, some c7476, some c7472, some c6796, some c7457, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7908 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7908 : lratChecker f7908 p7908 = .success := by decide +kernel
theorem unsat7908 : Unsatisfiable (PosFin 65) f7908 := by
  apply lratCheckerSound f7908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7908
  · intro a ha; simp [p7908] at ha; subst a; trivial
  · exact checked7908
theorem derived7908 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7908 := by
  apply localUnsat_implies_entails f7908 [c7907, c7901, c7899, c7876, c7877, c7478, c7476, c7472, c6796, c7457] c7908 unsat7908 (by rfl) a
  have h0 : Entails.eval a c7907 := derived7907 a h
  have h1 : Entails.eval a c7901 := derived7901 a h
  have h2 : Entails.eval a c7899 := derived7899 a h
  have h3 : Entails.eval a c7876 := derived7876 a h
  have h4 : Entails.eval a c7877 := derived7877 a h
  have h5 : Entails.eval a c7478 := h 7477 (by decide)
  have h6 : Entails.eval a c7476 := h 7475 (by decide)
  have h7 : Entails.eval a c7472 := h 7471 (by decide)
  have h8 : Entails.eval a c6796 := h 6795 (by decide)
  have h9 : Entails.eval a c7457 := h 7456 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7909 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7909 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7901, some c7908, some c6868, some c7900, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7909 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7909 : lratChecker f7909 p7909 = .success := by decide +kernel
theorem unsat7909 : Unsatisfiable (PosFin 65) f7909 := by
  apply lratCheckerSound f7909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7909
  · intro a ha; simp [p7909] at ha; subst a; trivial
  · exact checked7909
theorem derived7909 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7909 := by
  apply localUnsat_implies_entails f7909 [c7901, c7908, c6868, c7900] c7909 unsat7909 (by rfl) a
  have h0 : Entails.eval a c7901 := derived7901 a h
  have h1 : Entails.eval a c7908 := derived7908 a h
  have h2 : Entails.eval a c6868 := h 6867 (by decide)
  have h3 : Entails.eval a c7900 := derived7900 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7910 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7910 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6863, some c6731, some c7536, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7910 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7910 : lratChecker f7910 p7910 = .success := by decide +kernel
theorem unsat7910 : Unsatisfiable (PosFin 65) f7910 := by
  apply lratCheckerSound f7910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7910
  · intro a ha; simp [p7910] at ha; subst a; trivial
  · exact checked7910
theorem derived7910 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7910 := by
  apply localUnsat_implies_entails f7910 [c6863, c6731, c7536] c7910 unsat7910 (by rfl) a
  have h0 : Entails.eval a c6863 := h 6862 (by decide)
  have h1 : Entails.eval a c6731 := h 6730 (by decide)
  have h2 : Entails.eval a c7536 := h 7535 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7911 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7911 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7910, some c7478, some c7475, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7911 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7911 : lratChecker f7911 p7911 = .success := by decide +kernel
theorem unsat7911 : Unsatisfiable (PosFin 65) f7911 := by
  apply lratCheckerSound f7911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7911
  · intro a ha; simp [p7911] at ha; subst a; trivial
  · exact checked7911
theorem derived7911 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7911 := by
  apply localUnsat_implies_entails f7911 [c7910, c7478, c7475] c7911 unsat7911 (by rfl) a
  have h0 : Entails.eval a c7910 := derived7910 a h
  have h1 : Entails.eval a c7478 := h 7477 (by decide)
  have h2 : Entails.eval a c7475 := h 7474 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7912 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨40, by decide⟩, true), (⟨64, by decide⟩, false), (⟨45, by decide⟩, false), (⟨46, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7912 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7911, some c6868, some c7481, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p7912 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7912 : lratChecker f7912 p7912 = .success := by decide +kernel
theorem unsat7912 : Unsatisfiable (PosFin 65) f7912 := by
  apply lratCheckerSound f7912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7912
  · intro a ha; simp [p7912] at ha; subst a; trivial
  · exact checked7912
theorem derived7912 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7912 := by
  apply localUnsat_implies_entails f7912 [c7911, c6868, c7481] c7912 unsat7912 (by rfl) a
  have h0 : Entails.eval a c7911 := derived7911 a h
  have h1 : Entails.eval a c6868 := h 6867 (by decide)
  have h2 : Entails.eval a c7481 := h 7480 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7913 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7913 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7876, some c7899, some c7909, some c6592, some c6826, some c6756, some c6625, some c7172, some c7145, some c6431, some c6327, some c7839, some c7912, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7913 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7913 : lratChecker f7913 p7913 = .success := by decide +kernel
theorem unsat7913 : Unsatisfiable (PosFin 65) f7913 := by
  apply lratCheckerSound f7913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7913
  · intro a ha; simp [p7913] at ha; subst a; trivial
  · exact checked7913
theorem derived7913 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7913 := by
  apply localUnsat_implies_entails f7913 [c7876, c7899, c7909, c6592, c6826, c6756, c6625, c7172, c7145, c6431, c6327, c7839, c7912] c7913 unsat7913 (by rfl) a
  have h0 : Entails.eval a c7876 := derived7876 a h
  have h1 : Entails.eval a c7899 := derived7899 a h
  have h2 : Entails.eval a c7909 := derived7909 a h
  have h3 : Entails.eval a c6592 := h 6591 (by decide)
  have h4 : Entails.eval a c6826 := h 6825 (by decide)
  have h5 : Entails.eval a c6756 := h 6755 (by decide)
  have h6 : Entails.eval a c6625 := h 6624 (by decide)
  have h7 : Entails.eval a c7172 := h 7171 (by decide)
  have h8 : Entails.eval a c7145 := h 7144 (by decide)
  have h9 : Entails.eval a c6431 := h 6430 (by decide)
  have h10 : Entails.eval a c6327 := h 6326 (by decide)
  have h11 : Entails.eval a c7839 := derived7839 a h
  have h12 : Entails.eval a c7912 := derived7912 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7914 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨50, by decide⟩, true), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7914 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7407, some c7189, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p7914 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7914 : lratChecker f7914 p7914 = .success := by decide +kernel
theorem unsat7914 : Unsatisfiable (PosFin 65) f7914 := by
  apply lratCheckerSound f7914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7914
  · intro a ha; simp [p7914] at ha; subst a; trivial
  · exact checked7914
theorem derived7914 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7914 := by
  apply localUnsat_implies_entails f7914 [c7407, c7189] c7914 unsat7914 (by rfl) a
  have h0 : Entails.eval a c7407 := h 7406 (by decide)
  have h1 : Entails.eval a c7189 := h 7188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7915 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7915 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6348, some c7242, some c6804, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7915 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7915 : lratChecker f7915 p7915 = .success := by decide +kernel
theorem unsat7915 : Unsatisfiable (PosFin 65) f7915 := by
  apply lratCheckerSound f7915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7915
  · intro a ha; simp [p7915] at ha; subst a; trivial
  · exact checked7915
theorem derived7915 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7915 := by
  apply localUnsat_implies_entails f7915 [c6348, c7242, c6804] c7915 unsat7915 (by rfl) a
  have h0 : Entails.eval a c6348 := h 6347 (by decide)
  have h1 : Entails.eval a c7242 := h 7241 (by decide)
  have h2 : Entails.eval a c6804 := h 6803 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7916 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨40, by decide⟩, true), (⟨44, by decide⟩, true), (⟨45, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨38, by decide⟩, true), (⟨46, by decide⟩, true), (⟨50, by decide⟩, true), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7916 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7914, some c7915, some c7373, some c7321, some c7331, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7916 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7916 : lratChecker f7916 p7916 = .success := by decide +kernel
theorem unsat7916 : Unsatisfiable (PosFin 65) f7916 := by
  apply lratCheckerSound f7916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7916
  · intro a ha; simp [p7916] at ha; subst a; trivial
  · exact checked7916
theorem derived7916 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7916 := by
  apply localUnsat_implies_entails f7916 [c7914, c7915, c7373, c7321, c7331] c7916 unsat7916 (by rfl) a
  have h0 : Entails.eval a c7914 := derived7914 a h
  have h1 : Entails.eval a c7915 := derived7915 a h
  have h2 : Entails.eval a c7373 := h 7372 (by decide)
  have h3 : Entails.eval a c7321 := h 7320 (by decide)
  have h4 : Entails.eval a c7331 := h 7330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7917 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7917 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7913, some c7874, some c7853, some c7211, some c7130, some c6431, some c6286, some c6679, some c7172, some c7826, some c6992, some c6343, some c7460, some c6592, some c6327, some c7916, some c7906, some c5274, some c5187, some c5838, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7917 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked7917 : lratChecker f7917 p7917 = .success := by decide +kernel
theorem unsat7917 : Unsatisfiable (PosFin 65) f7917 := by
  apply lratCheckerSound f7917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7917
  · intro a ha; simp [p7917] at ha; subst a; trivial
  · exact checked7917
theorem derived7917 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7917 := by
  apply localUnsat_implies_entails f7917 [c7877, c7913, c7874, c7853, c7211, c7130, c6431, c6286, c6679, c7172, c7826, c6992, c6343, c7460, c6592, c6327, c7916, c7906, c5274, c5187, c5838] c7917 unsat7917 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7913 := derived7913 a h
  have h2 : Entails.eval a c7874 := derived7874 a h
  have h3 : Entails.eval a c7853 := derived7853 a h
  have h4 : Entails.eval a c7211 := h 7210 (by decide)
  have h5 : Entails.eval a c7130 := h 7129 (by decide)
  have h6 : Entails.eval a c6431 := h 6430 (by decide)
  have h7 : Entails.eval a c6286 := h 6285 (by decide)
  have h8 : Entails.eval a c6679 := h 6678 (by decide)
  have h9 : Entails.eval a c7172 := h 7171 (by decide)
  have h10 : Entails.eval a c7826 := derived7826 a h
  have h11 : Entails.eval a c6992 := h 6991 (by decide)
  have h12 : Entails.eval a c6343 := h 6342 (by decide)
  have h13 : Entails.eval a c7460 := h 7459 (by decide)
  have h14 : Entails.eval a c6592 := h 6591 (by decide)
  have h15 : Entails.eval a c6327 := h 6326 (by decide)
  have h16 : Entails.eval a c7916 := derived7916 a h
  have h17 : Entails.eval a c7906 := derived7906 a h
  have h18 : Entails.eval a c5274 := h 5273 (by decide)
  have h19 : Entails.eval a c5187 := h 5186 (by decide)
  have h20 : Entails.eval a c5838 := h 5837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7918 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨52, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7918 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7913, some c7874, some c7853, some c7211, some c7130, some c6431, some c6992, some c6343, some c6286, some c6592, some c6327, some c7877, some c7826, some c6679, some c7172, some c7916, some c7345, some c6715, some c7460, some c7456, some c7329, some c6721, some c6730, some c7917, some c5238, some c5280, some c5161, some c5470, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7918 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked7918 : lratChecker f7918 p7918 = .success := by decide +kernel
theorem unsat7918 : Unsatisfiable (PosFin 65) f7918 := by
  apply lratCheckerSound f7918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7918
  · intro a ha; simp [p7918] at ha; subst a; trivial
  · exact checked7918
theorem derived7918 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7918 := by
  apply localUnsat_implies_entails f7918 [c7913, c7874, c7853, c7211, c7130, c6431, c6992, c6343, c6286, c6592, c6327, c7877, c7826, c6679, c7172, c7916, c7345, c6715, c7460, c7456, c7329, c6721, c6730, c7917, c5238, c5280, c5161, c5470] c7918 unsat7918 (by rfl) a
  have h0 : Entails.eval a c7913 := derived7913 a h
  have h1 : Entails.eval a c7874 := derived7874 a h
  have h2 : Entails.eval a c7853 := derived7853 a h
  have h3 : Entails.eval a c7211 := h 7210 (by decide)
  have h4 : Entails.eval a c7130 := h 7129 (by decide)
  have h5 : Entails.eval a c6431 := h 6430 (by decide)
  have h6 : Entails.eval a c6992 := h 6991 (by decide)
  have h7 : Entails.eval a c6343 := h 6342 (by decide)
  have h8 : Entails.eval a c6286 := h 6285 (by decide)
  have h9 : Entails.eval a c6592 := h 6591 (by decide)
  have h10 : Entails.eval a c6327 := h 6326 (by decide)
  have h11 : Entails.eval a c7877 := derived7877 a h
  have h12 : Entails.eval a c7826 := derived7826 a h
  have h13 : Entails.eval a c6679 := h 6678 (by decide)
  have h14 : Entails.eval a c7172 := h 7171 (by decide)
  have h15 : Entails.eval a c7916 := derived7916 a h
  have h16 : Entails.eval a c7345 := h 7344 (by decide)
  have h17 : Entails.eval a c6715 := h 6714 (by decide)
  have h18 : Entails.eval a c7460 := h 7459 (by decide)
  have h19 : Entails.eval a c7456 := h 7455 (by decide)
  have h20 : Entails.eval a c7329 := h 7328 (by decide)
  have h21 : Entails.eval a c6721 := h 6720 (by decide)
  have h22 : Entails.eval a c6730 := h 6729 (by decide)
  have h23 : Entails.eval a c7917 := derived7917 a h
  have h24 : Entails.eval a c5238 := h 5237 (by decide)
  have h25 : Entails.eval a c5280 := h 5279 (by decide)
  have h26 : Entails.eval a c5161 := h 5160 (by decide)
  have h27 : Entails.eval a c5470 := h 5469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7919 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨49, by decide⟩, false), (⟨53, by decide⟩, false), (⟨61, by decide⟩, false), (⟨43, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7919 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5238, some c5263, some c5279, some c5470, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7919 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7919 : lratChecker f7919 p7919 = .success := by decide +kernel
theorem unsat7919 : Unsatisfiable (PosFin 65) f7919 := by
  apply lratCheckerSound f7919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7919
  · intro a ha; simp [p7919] at ha; subst a; trivial
  · exact checked7919
theorem derived7919 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7919 := by
  apply localUnsat_implies_entails f7919 [c5238, c5263, c5279, c5470] c7919 unsat7919 (by rfl) a
  have h0 : Entails.eval a c5238 := h 5237 (by decide)
  have h1 : Entails.eval a c5263 := h 5262 (by decide)
  have h2 : Entails.eval a c5279 := h 5278 (by decide)
  have h3 : Entails.eval a c5470 := h 5469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7920 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7920 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7913, some c7874, some c7853, some c7211, some c7130, some c6431, some c6992, some c6343, some c6286, some c6592, some c6327, some c7877, some c7826, some c6679, some c7172, some c7916, some c7345, some c7478, some c7918, some c6353, some c6348, some c6300, some c6806, some c6931, some c7919, some c7906, some c5273, some c5187, some c5838, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7920 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked7920 : lratChecker f7920 p7920 = .success := by decide +kernel
theorem unsat7920 : Unsatisfiable (PosFin 65) f7920 := by
  apply lratCheckerSound f7920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7920
  · intro a ha; simp [p7920] at ha; subst a; trivial
  · exact checked7920
theorem derived7920 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7920 := by
  apply localUnsat_implies_entails f7920 [c7913, c7874, c7853, c7211, c7130, c6431, c6992, c6343, c6286, c6592, c6327, c7877, c7826, c6679, c7172, c7916, c7345, c7478, c7918, c6353, c6348, c6300, c6806, c6931, c7919, c7906, c5273, c5187, c5838] c7920 unsat7920 (by rfl) a
  have h0 : Entails.eval a c7913 := derived7913 a h
  have h1 : Entails.eval a c7874 := derived7874 a h
  have h2 : Entails.eval a c7853 := derived7853 a h
  have h3 : Entails.eval a c7211 := h 7210 (by decide)
  have h4 : Entails.eval a c7130 := h 7129 (by decide)
  have h5 : Entails.eval a c6431 := h 6430 (by decide)
  have h6 : Entails.eval a c6992 := h 6991 (by decide)
  have h7 : Entails.eval a c6343 := h 6342 (by decide)
  have h8 : Entails.eval a c6286 := h 6285 (by decide)
  have h9 : Entails.eval a c6592 := h 6591 (by decide)
  have h10 : Entails.eval a c6327 := h 6326 (by decide)
  have h11 : Entails.eval a c7877 := derived7877 a h
  have h12 : Entails.eval a c7826 := derived7826 a h
  have h13 : Entails.eval a c6679 := h 6678 (by decide)
  have h14 : Entails.eval a c7172 := h 7171 (by decide)
  have h15 : Entails.eval a c7916 := derived7916 a h
  have h16 : Entails.eval a c7345 := h 7344 (by decide)
  have h17 : Entails.eval a c7478 := h 7477 (by decide)
  have h18 : Entails.eval a c7918 := derived7918 a h
  have h19 : Entails.eval a c6353 := h 6352 (by decide)
  have h20 : Entails.eval a c6348 := h 6347 (by decide)
  have h21 : Entails.eval a c6300 := h 6299 (by decide)
  have h22 : Entails.eval a c6806 := h 6805 (by decide)
  have h23 : Entails.eval a c6931 := h 6930 (by decide)
  have h24 : Entails.eval a c7919 := derived7919 a h
  have h25 : Entails.eval a c7906 := derived7906 a h
  have h26 : Entails.eval a c5273 := h 5272 (by decide)
  have h27 : Entails.eval a c5187 := h 5186 (by decide)
  have h28 : Entails.eval a c5838 := h 5837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7921 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7921 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7913, some c7874, some c7853, some c7826, some c7211, some c7130, some c6992, some c6431, some c6286, some c6343, some c6592, some c6679, some c6327, some c7172, some c7916, some c7345, some c7920, some c7284, some c7517, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7921 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7921 : lratChecker f7921 p7921 = .success := by decide +kernel
theorem unsat7921 : Unsatisfiable (PosFin 65) f7921 := by
  apply lratCheckerSound f7921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7921
  · intro a ha; simp [p7921] at ha; subst a; trivial
  · exact checked7921
theorem derived7921 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7921 := by
  apply localUnsat_implies_entails f7921 [c7877, c7913, c7874, c7853, c7826, c7211, c7130, c6992, c6431, c6286, c6343, c6592, c6679, c6327, c7172, c7916, c7345, c7920, c7284, c7517] c7921 unsat7921 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7913 := derived7913 a h
  have h2 : Entails.eval a c7874 := derived7874 a h
  have h3 : Entails.eval a c7853 := derived7853 a h
  have h4 : Entails.eval a c7826 := derived7826 a h
  have h5 : Entails.eval a c7211 := h 7210 (by decide)
  have h6 : Entails.eval a c7130 := h 7129 (by decide)
  have h7 : Entails.eval a c6992 := h 6991 (by decide)
  have h8 : Entails.eval a c6431 := h 6430 (by decide)
  have h9 : Entails.eval a c6286 := h 6285 (by decide)
  have h10 : Entails.eval a c6343 := h 6342 (by decide)
  have h11 : Entails.eval a c6592 := h 6591 (by decide)
  have h12 : Entails.eval a c6679 := h 6678 (by decide)
  have h13 : Entails.eval a c6327 := h 6326 (by decide)
  have h14 : Entails.eval a c7172 := h 7171 (by decide)
  have h15 : Entails.eval a c7916 := derived7916 a h
  have h16 : Entails.eval a c7345 := h 7344 (by decide)
  have h17 : Entails.eval a c7920 := derived7920 a h
  have h18 : Entails.eval a c7284 := h 7283 (by decide)
  have h19 : Entails.eval a c7517 := h 7516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7922 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7922 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6303, some c6299, some c5140, some c5179, some c5273, some c5350, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7922 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7922 : lratChecker f7922 p7922 = .success := by decide +kernel
theorem unsat7922 : Unsatisfiable (PosFin 65) f7922 := by
  apply lratCheckerSound f7922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7922
  · intro a ha; simp [p7922] at ha; subst a; trivial
  · exact checked7922
theorem derived7922 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7922 := by
  apply localUnsat_implies_entails f7922 [c6303, c6299, c5140, c5179, c5273, c5350] c7922 unsat7922 (by rfl) a
  have h0 : Entails.eval a c6303 := h 6302 (by decide)
  have h1 : Entails.eval a c6299 := h 6298 (by decide)
  have h2 : Entails.eval a c5140 := h 5139 (by decide)
  have h3 : Entails.eval a c5179 := h 5178 (by decide)
  have h4 : Entails.eval a c5273 := h 5272 (by decide)
  have h5 : Entails.eval a c5350 := h 5349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7923 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨36, by decide⟩, false), (⟨42, by decide⟩, true), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7923 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c6801, some c6303, some c6809, some c6300, some c6309, some c6299, some c6804, some c6803, some c6813, some c7921, some c7479, some c7680, some c6860, some c6279, some c6678, some c7922, some c7645, some c5279, some c5282, some c5808, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7923 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked7923 : lratChecker f7923 p7923 = .success := by decide +kernel
theorem unsat7923 : Unsatisfiable (PosFin 65) f7923 := by
  apply lratCheckerSound f7923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7923
  · intro a ha; simp [p7923] at ha; subst a; trivial
  · exact checked7923
theorem derived7923 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7923 := by
  apply localUnsat_implies_entails f7923 [c7877, c6801, c6303, c6809, c6300, c6309, c6299, c6804, c6803, c6813, c7921, c7479, c7680, c6860, c6279, c6678, c7922, c7645, c5279, c5282, c5808] c7923 unsat7923 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c6801 := h 6800 (by decide)
  have h2 : Entails.eval a c6303 := h 6302 (by decide)
  have h3 : Entails.eval a c6809 := h 6808 (by decide)
  have h4 : Entails.eval a c6300 := h 6299 (by decide)
  have h5 : Entails.eval a c6309 := h 6308 (by decide)
  have h6 : Entails.eval a c6299 := h 6298 (by decide)
  have h7 : Entails.eval a c6804 := h 6803 (by decide)
  have h8 : Entails.eval a c6803 := h 6802 (by decide)
  have h9 : Entails.eval a c6813 := h 6812 (by decide)
  have h10 : Entails.eval a c7921 := derived7921 a h
  have h11 : Entails.eval a c7479 := h 7478 (by decide)
  have h12 : Entails.eval a c7680 := derived7680 a h
  have h13 : Entails.eval a c6860 := h 6859 (by decide)
  have h14 : Entails.eval a c6279 := h 6278 (by decide)
  have h15 : Entails.eval a c6678 := h 6677 (by decide)
  have h16 : Entails.eval a c7922 := derived7922 a h
  have h17 : Entails.eval a c7645 := derived7645 a h
  have h18 : Entails.eval a c5279 := h 5278 (by decide)
  have h19 : Entails.eval a c5282 := h 5281 (by decide)
  have h20 : Entails.eval a c5808 := h 5807 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7924 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨42, by decide⟩, true), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7924 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c6801, some c6303, some c6809, some c6300, some c6309, some c7921, some c6316, some c6299, some c6803, some c6813, some c7923, some c7044, some c7161, some c7340, some c7119, some c7395, some c7652, some c7648, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7924 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7924 : lratChecker f7924 p7924 = .success := by decide +kernel
theorem unsat7924 : Unsatisfiable (PosFin 65) f7924 := by
  apply lratCheckerSound f7924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7924
  · intro a ha; simp [p7924] at ha; subst a; trivial
  · exact checked7924
theorem derived7924 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7924 := by
  apply localUnsat_implies_entails f7924 [c7877, c6801, c6303, c6809, c6300, c6309, c7921, c6316, c6299, c6803, c6813, c7923, c7044, c7161, c7340, c7119, c7395, c7652, c7648] c7924 unsat7924 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c6801 := h 6800 (by decide)
  have h2 : Entails.eval a c6303 := h 6302 (by decide)
  have h3 : Entails.eval a c6809 := h 6808 (by decide)
  have h4 : Entails.eval a c6300 := h 6299 (by decide)
  have h5 : Entails.eval a c6309 := h 6308 (by decide)
  have h6 : Entails.eval a c7921 := derived7921 a h
  have h7 : Entails.eval a c6316 := h 6315 (by decide)
  have h8 : Entails.eval a c6299 := h 6298 (by decide)
  have h9 : Entails.eval a c6803 := h 6802 (by decide)
  have h10 : Entails.eval a c6813 := h 6812 (by decide)
  have h11 : Entails.eval a c7923 := derived7923 a h
  have h12 : Entails.eval a c7044 := h 7043 (by decide)
  have h13 : Entails.eval a c7161 := h 7160 (by decide)
  have h14 : Entails.eval a c7340 := h 7339 (by decide)
  have h15 : Entails.eval a c7119 := h 7118 (by decide)
  have h16 : Entails.eval a c7395 := h 7394 (by decide)
  have h17 : Entails.eval a c7652 := derived7652 a h
  have h18 : Entails.eval a c7648 := derived7648 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7925 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨46, by decide⟩, true), (⟨58, by decide⟩, true), (⟨56, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7925 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7822, some c6986, some c6621, some c6661, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7925 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7925 : lratChecker f7925 p7925 = .success := by decide +kernel
theorem unsat7925 : Unsatisfiable (PosFin 65) f7925 := by
  apply lratCheckerSound f7925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7925
  · intro a ha; simp [p7925] at ha; subst a; trivial
  · exact checked7925
theorem derived7925 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7925 := by
  apply localUnsat_implies_entails f7925 [c7822, c6986, c6621, c6661] c7925 unsat7925 (by rfl) a
  have h0 : Entails.eval a c7822 := derived7822 a h
  have h1 : Entails.eval a c6986 := h 6985 (by decide)
  have h2 : Entails.eval a c6621 := h 6620 (by decide)
  have h3 : Entails.eval a c6661 := h 6660 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7926 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7926 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c7877, some c6809, some c6801, some c6299, some c6303, some c6813, some c6803, some c6804, some c6815, some c7925, some c6337, some c7924, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7926 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7926 : lratChecker f7926 p7926 = .success := by decide +kernel
theorem unsat7926 : Unsatisfiable (PosFin 65) f7926 := by
  apply lratCheckerSound f7926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7926
  · intro a ha; simp [p7926] at ha; subst a; trivial
  · exact checked7926
theorem derived7926 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7926 := by
  apply localUnsat_implies_entails f7926 [c7921, c7877, c6809, c6801, c6299, c6303, c6813, c6803, c6804, c6815, c7925, c6337, c7924] c7926 unsat7926 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c7877 := derived7877 a h
  have h2 : Entails.eval a c6809 := h 6808 (by decide)
  have h3 : Entails.eval a c6801 := h 6800 (by decide)
  have h4 : Entails.eval a c6299 := h 6298 (by decide)
  have h5 : Entails.eval a c6303 := h 6302 (by decide)
  have h6 : Entails.eval a c6813 := h 6812 (by decide)
  have h7 : Entails.eval a c6803 := h 6802 (by decide)
  have h8 : Entails.eval a c6804 := h 6803 (by decide)
  have h9 : Entails.eval a c6815 := h 6814 (by decide)
  have h10 : Entails.eval a c7925 := derived7925 a h
  have h11 : Entails.eval a c6337 := h 6336 (by decide)
  have h12 : Entails.eval a c7924 := derived7924 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7927 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7927 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c6815, some c7877, some c7133, some c7119, some c6753, some c7392, some c6663, some c7447, some c7657, some c7652, some c7648, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7927 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7927 : lratChecker f7927 p7927 = .success := by decide +kernel
theorem unsat7927 : Unsatisfiable (PosFin 65) f7927 := by
  apply lratCheckerSound f7927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7927
  · intro a ha; simp [p7927] at ha; subst a; trivial
  · exact checked7927
theorem derived7927 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7927 := by
  apply localUnsat_implies_entails f7927 [c7921, c6815, c7877, c7133, c7119, c6753, c7392, c6663, c7447, c7657, c7652, c7648] c7927 unsat7927 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c6815 := h 6814 (by decide)
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c7133 := h 7132 (by decide)
  have h4 : Entails.eval a c7119 := h 7118 (by decide)
  have h5 : Entails.eval a c6753 := h 6752 (by decide)
  have h6 : Entails.eval a c7392 := h 7391 (by decide)
  have h7 : Entails.eval a c6663 := h 6662 (by decide)
  have h8 : Entails.eval a c7447 := h 7446 (by decide)
  have h9 : Entails.eval a c7657 := derived7657 a h
  have h10 : Entails.eval a c7652 := derived7652 a h
  have h11 : Entails.eval a c7648 := derived7648 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7928 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨45, by decide⟩, false), (⟨34, by decide⟩, true), (⟨61, by decide⟩, false), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7928 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6332, some c5140, some c5179, some c5274, some c5350, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7928 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7928 : lratChecker f7928 p7928 = .success := by decide +kernel
theorem unsat7928 : Unsatisfiable (PosFin 65) f7928 := by
  apply lratCheckerSound f7928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7928
  · intro a ha; simp [p7928] at ha; subst a; trivial
  · exact checked7928
theorem derived7928 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7928 := by
  apply localUnsat_implies_entails f7928 [c6332, c5140, c5179, c5274, c5350] c7928 unsat7928 (by rfl) a
  have h0 : Entails.eval a c6332 := h 6331 (by decide)
  have h1 : Entails.eval a c5140 := h 5139 (by decide)
  have h2 : Entails.eval a c5179 := h 5178 (by decide)
  have h3 : Entails.eval a c5274 := h 5273 (by decide)
  have h4 : Entails.eval a c5350 := h 5349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7929 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨61, by decide⟩, false), (⟨52, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7929 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c6815, some c7877, some c6332, some c6318, some c7926, some c7927, some c7340, some c7046, some c7010, some c7683, some c7479, some c6760, some c6754, some c7928, some c7645, some c5280, some c5237, some c5823, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7929 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7929 : lratChecker f7929 p7929 = .success := by decide +kernel
theorem unsat7929 : Unsatisfiable (PosFin 65) f7929 := by
  apply lratCheckerSound f7929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7929
  · intro a ha; simp [p7929] at ha; subst a; trivial
  · exact checked7929
theorem derived7929 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7929 := by
  apply localUnsat_implies_entails f7929 [c7921, c6815, c7877, c6332, c6318, c7926, c7927, c7340, c7046, c7010, c7683, c7479, c6760, c6754, c7928, c7645, c5280, c5237, c5823] c7929 unsat7929 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c6815 := h 6814 (by decide)
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c6332 := h 6331 (by decide)
  have h4 : Entails.eval a c6318 := h 6317 (by decide)
  have h5 : Entails.eval a c7926 := derived7926 a h
  have h6 : Entails.eval a c7927 := derived7927 a h
  have h7 : Entails.eval a c7340 := h 7339 (by decide)
  have h8 : Entails.eval a c7046 := h 7045 (by decide)
  have h9 : Entails.eval a c7010 := h 7009 (by decide)
  have h10 : Entails.eval a c7683 := derived7683 a h
  have h11 : Entails.eval a c7479 := h 7478 (by decide)
  have h12 : Entails.eval a c6760 := h 6759 (by decide)
  have h13 : Entails.eval a c6754 := h 6753 (by decide)
  have h14 : Entails.eval a c7928 := derived7928 a h
  have h15 : Entails.eval a c7645 := derived7645 a h
  have h16 : Entails.eval a c5280 := h 5279 (by decide)
  have h17 : Entails.eval a c5237 := h 5236 (by decide)
  have h18 : Entails.eval a c5823 := h 5822 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7930 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨52, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7930 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c6815, some c7877, some c6332, some c7926, some c7929, some c6732, some c7471, some c7327, some c7131, some c7161, some c7614, some c7392, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7930 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7930 : lratChecker f7930 p7930 = .success := by decide +kernel
theorem unsat7930 : Unsatisfiable (PosFin 65) f7930 := by
  apply lratCheckerSound f7930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7930
  · intro a ha; simp [p7930] at ha; subst a; trivial
  · exact checked7930
theorem derived7930 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7930 := by
  apply localUnsat_implies_entails f7930 [c7921, c6815, c7877, c6332, c7926, c7929, c6732, c7471, c7327, c7131, c7161, c7614, c7392] c7930 unsat7930 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c6815 := h 6814 (by decide)
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c6332 := h 6331 (by decide)
  have h4 : Entails.eval a c7926 := derived7926 a h
  have h5 : Entails.eval a c7929 := derived7929 a h
  have h6 : Entails.eval a c6732 := h 6731 (by decide)
  have h7 : Entails.eval a c7471 := h 7470 (by decide)
  have h8 : Entails.eval a c7327 := h 7326 (by decide)
  have h9 : Entails.eval a c7131 := h 7130 (by decide)
  have h10 : Entails.eval a c7161 := h 7160 (by decide)
  have h11 : Entails.eval a c7614 := derived7614 a h
  have h12 : Entails.eval a c7392 := h 7391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7931 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨39, by decide⟩, false), (⟨61, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7931 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5189, some c5139, some c5178, some c5328, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7931 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7931 : lratChecker f7931 p7931 = .success := by decide +kernel
theorem unsat7931 : Unsatisfiable (PosFin 65) f7931 := by
  apply lratCheckerSound f7931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7931
  · intro a ha; simp [p7931] at ha; subst a; trivial
  · exact checked7931
theorem derived7931 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7931 := by
  apply localUnsat_implies_entails f7931 [c5189, c5139, c5178, c5328] c7931 unsat7931 (by rfl) a
  have h0 : Entails.eval a c5189 := h 5188 (by decide)
  have h1 : Entails.eval a c5139 := h 5138 (by decide)
  have h2 : Entails.eval a c5178 := h 5177 (by decide)
  have h3 : Entails.eval a c5328 := h 5327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7932 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨60, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7932 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5704, some c5528, some c5166, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7932 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7932 : lratChecker f7932 p7932 = .success := by decide +kernel
theorem unsat7932 : Unsatisfiable (PosFin 65) f7932 := by
  apply lratCheckerSound f7932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7932
  · intro a ha; simp [p7932] at ha; subst a; trivial
  · exact checked7932
theorem derived7932 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7932 := by
  apply localUnsat_implies_entails f7932 [c5704, c5528, c5166] c7932 unsat7932 (by rfl) a
  have h0 : Entails.eval a c5704 := h 5703 (by decide)
  have h1 : Entails.eval a c5528 := h 5527 (by decide)
  have h2 : Entails.eval a c5166 := h 5165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7933 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7933 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6815, some c6332, some c6318, some c7324, some c7412, some c7460, some c7133, some c7010, some c6753, some c7771, some c7931, some c7932, some c5209, some c5153, some c5223, some c5411, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7933 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7933 : lratChecker f7933 p7933 = .success := by decide +kernel
theorem unsat7933 : Unsatisfiable (PosFin 65) f7933 := by
  apply lratCheckerSound f7933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7933
  · intro a ha; simp [p7933] at ha; subst a; trivial
  · exact checked7933
theorem derived7933 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7933 := by
  apply localUnsat_implies_entails f7933 [c6815, c6332, c6318, c7324, c7412, c7460, c7133, c7010, c6753, c7771, c7931, c7932, c5209, c5153, c5223, c5411] c7933 unsat7933 (by rfl) a
  have h0 : Entails.eval a c6815 := h 6814 (by decide)
  have h1 : Entails.eval a c6332 := h 6331 (by decide)
  have h2 : Entails.eval a c6318 := h 6317 (by decide)
  have h3 : Entails.eval a c7324 := h 7323 (by decide)
  have h4 : Entails.eval a c7412 := h 7411 (by decide)
  have h5 : Entails.eval a c7460 := h 7459 (by decide)
  have h6 : Entails.eval a c7133 := h 7132 (by decide)
  have h7 : Entails.eval a c7010 := h 7009 (by decide)
  have h8 : Entails.eval a c6753 := h 6752 (by decide)
  have h9 : Entails.eval a c7771 := derived7771 a h
  have h10 : Entails.eval a c7931 := derived7931 a h
  have h11 : Entails.eval a c7932 := derived7932 a h
  have h12 : Entails.eval a c5209 := h 5208 (by decide)
  have h13 : Entails.eval a c5153 := h 5152 (by decide)
  have h14 : Entails.eval a c5223 := h 5222 (by decide)
  have h15 : Entails.eval a c5411 := h 5410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7934 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7934 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c6815, some c7877, some c6332, some c6318, some c7926, some c7933, some c7930, some c7306, some c7409, some c7455, some c7133, some c7927, some c6753, some c7614, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7934 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7934 : lratChecker f7934 p7934 = .success := by decide +kernel
theorem unsat7934 : Unsatisfiable (PosFin 65) f7934 := by
  apply lratCheckerSound f7934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7934
  · intro a ha; simp [p7934] at ha; subst a; trivial
  · exact checked7934
theorem derived7934 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7934 := by
  apply localUnsat_implies_entails f7934 [c7921, c6815, c7877, c6332, c6318, c7926, c7933, c7930, c7306, c7409, c7455, c7133, c7927, c6753, c7614] c7934 unsat7934 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c6815 := h 6814 (by decide)
  have h2 : Entails.eval a c7877 := derived7877 a h
  have h3 : Entails.eval a c6332 := h 6331 (by decide)
  have h4 : Entails.eval a c6318 := h 6317 (by decide)
  have h5 : Entails.eval a c7926 := derived7926 a h
  have h6 : Entails.eval a c7933 := derived7933 a h
  have h7 : Entails.eval a c7930 := derived7930 a h
  have h8 : Entails.eval a c7306 := h 7305 (by decide)
  have h9 : Entails.eval a c7409 := h 7408 (by decide)
  have h10 : Entails.eval a c7455 := h 7454 (by decide)
  have h11 : Entails.eval a c7133 := h 7132 (by decide)
  have h12 : Entails.eval a c7927 := derived7927 a h
  have h13 : Entails.eval a c6753 := h 6752 (by decide)
  have h14 : Entails.eval a c7614 := derived7614 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7935 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨45, by decide⟩, true), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨61, by decide⟩, false), (⟨46, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7935 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6732, some c7614, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7935 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7935 : lratChecker f7935 p7935 = .success := by decide +kernel
theorem unsat7935 : Unsatisfiable (PosFin 65) f7935 := by
  apply lratCheckerSound f7935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7935
  · intro a ha; simp [p7935] at ha; subst a; trivial
  · exact checked7935
theorem derived7935 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7935 := by
  apply localUnsat_implies_entails f7935 [c6732, c7614] c7935 unsat7935 (by rfl) a
  have h0 : Entails.eval a c6732 := h 6731 (by decide)
  have h1 : Entails.eval a c7614 := derived7614 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7936 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨61, by decide⟩, false), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7936 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6815, some c6332, some c6318, some c7010, some c6860, some c7340, some c7474, some c7133, some c7935, some c7657, some c6754, some c7652, some c7651, some c7769, some c5704, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7936 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7936 : lratChecker f7936 p7936 = .success := by decide +kernel
theorem unsat7936 : Unsatisfiable (PosFin 65) f7936 := by
  apply lratCheckerSound f7936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7936
  · intro a ha; simp [p7936] at ha; subst a; trivial
  · exact checked7936
theorem derived7936 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7936 := by
  apply localUnsat_implies_entails f7936 [c6815, c6332, c6318, c7010, c6860, c7340, c7474, c7133, c7935, c7657, c6754, c7652, c7651, c7769, c5704] c7936 unsat7936 (by rfl) a
  have h0 : Entails.eval a c6815 := h 6814 (by decide)
  have h1 : Entails.eval a c6332 := h 6331 (by decide)
  have h2 : Entails.eval a c6318 := h 6317 (by decide)
  have h3 : Entails.eval a c7010 := h 7009 (by decide)
  have h4 : Entails.eval a c6860 := h 6859 (by decide)
  have h5 : Entails.eval a c7340 := h 7339 (by decide)
  have h6 : Entails.eval a c7474 := h 7473 (by decide)
  have h7 : Entails.eval a c7133 := h 7132 (by decide)
  have h8 : Entails.eval a c7935 := derived7935 a h
  have h9 : Entails.eval a c7657 := derived7657 a h
  have h10 : Entails.eval a c6754 := h 6753 (by decide)
  have h11 : Entails.eval a c7652 := derived7652 a h
  have h12 : Entails.eval a c7651 := derived7651 a h
  have h13 : Entails.eval a c7769 := derived7769 a h
  have h14 : Entails.eval a c5704 := h 5703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7937 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨56, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨62, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7937 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7409, some c7417, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7937 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7937 : lratChecker f7937 p7937 = .success := by decide +kernel
theorem unsat7937 : Unsatisfiable (PosFin 65) f7937 := by
  apply lratCheckerSound f7937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7937
  · intro a ha; simp [p7937] at ha; subst a; trivial
  · exact checked7937
theorem derived7937 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7937 := by
  apply localUnsat_implies_entails f7937 [c7409, c7417] c7937 unsat7937 (by rfl) a
  have h0 : Entails.eval a c7409 := h 7408 (by decide)
  have h1 : Entails.eval a c7417 := h 7416 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7938 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨61, by decide⟩, true), (⟨39, by decide⟩, false), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7938 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5209, some c5153, some c5223, some c5411, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7938 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7938 : lratChecker f7938 p7938 = .success := by decide +kernel
theorem unsat7938 : Unsatisfiable (PosFin 65) f7938 := by
  apply lratCheckerSound f7938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7938
  · intro a ha; simp [p7938] at ha; subst a; trivial
  · exact checked7938
theorem derived7938 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7938 := by
  apply localUnsat_implies_entails f7938 [c5209, c5153, c5223, c5411] c7938 unsat7938 (by rfl) a
  have h0 : Entails.eval a c5209 := h 5208 (by decide)
  have h1 : Entails.eval a c5153 := h 5152 (by decide)
  have h2 : Entails.eval a c5223 := h 5222 (by decide)
  have h3 : Entails.eval a c5411 := h 5410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7939 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7939 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7921, some c6332, some c6318, some c7926, some c6815, some c7934, some c7937, some c7010, some c6860, some c7936, some c7340, some c7771, some c7474, some c7931, some c6732, some c7938, some c5704, some c5240, some c5166, some c5572, some c5575, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7939 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked7939 : lratChecker f7939 p7939 = .success := by decide +kernel
theorem unsat7939 : Unsatisfiable (PosFin 65) f7939 := by
  apply lratCheckerSound f7939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7939
  · intro a ha; simp [p7939] at ha; subst a; trivial
  · exact checked7939
theorem derived7939 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7939 := by
  apply localUnsat_implies_entails f7939 [c7877, c7921, c6332, c6318, c7926, c6815, c7934, c7937, c7010, c6860, c7936, c7340, c7771, c7474, c7931, c6732, c7938, c5704, c5240, c5166, c5572, c5575] c7939 unsat7939 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c6332 := h 6331 (by decide)
  have h3 : Entails.eval a c6318 := h 6317 (by decide)
  have h4 : Entails.eval a c7926 := derived7926 a h
  have h5 : Entails.eval a c6815 := h 6814 (by decide)
  have h6 : Entails.eval a c7934 := derived7934 a h
  have h7 : Entails.eval a c7937 := derived7937 a h
  have h8 : Entails.eval a c7010 := h 7009 (by decide)
  have h9 : Entails.eval a c6860 := h 6859 (by decide)
  have h10 : Entails.eval a c7936 := derived7936 a h
  have h11 : Entails.eval a c7340 := h 7339 (by decide)
  have h12 : Entails.eval a c7771 := derived7771 a h
  have h13 : Entails.eval a c7474 := h 7473 (by decide)
  have h14 : Entails.eval a c7931 := derived7931 a h
  have h15 : Entails.eval a c6732 := h 6731 (by decide)
  have h16 : Entails.eval a c7938 := derived7938 a h
  have h17 : Entails.eval a c5704 := h 5703 (by decide)
  have h18 : Entails.eval a c5240 := h 5239 (by decide)
  have h19 : Entails.eval a c5166 := h 5165 (by decide)
  have h20 : Entails.eval a c5572 := h 5571 (by decide)
  have h21 : Entails.eval a c5575 := h 5574 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7940 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7940 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5714, some c5532, some c5164, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7940 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7940 : lratChecker f7940 p7940 = .success := by decide +kernel
theorem unsat7940 : Unsatisfiable (PosFin 65) f7940 := by
  apply lratCheckerSound f7940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7940
  · intro a ha; simp [p7940] at ha; subst a; trivial
  · exact checked7940
theorem derived7940 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7940 := by
  apply localUnsat_implies_entails f7940 [c5714, c5532, c5164] c7940 unsat7940 (by rfl) a
  have h0 : Entails.eval a c5714 := h 5713 (by decide)
  have h1 : Entails.eval a c5532 := h 5531 (by decide)
  have h2 : Entails.eval a c5164 := h 5163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7941 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨39, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7941 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5189, some c5140, some c5179, some c5328, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7941 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7941 : lratChecker f7941 p7941 = .success := by decide +kernel
theorem unsat7941 : Unsatisfiable (PosFin 65) f7941 := by
  apply lratCheckerSound f7941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7941
  · intro a ha; simp [p7941] at ha; subst a; trivial
  · exact checked7941
theorem derived7941 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7941 := by
  apply localUnsat_implies_entails f7941 [c5189, c5140, c5179, c5328] c7941 unsat7941 (by rfl) a
  have h0 : Entails.eval a c5189 := h 5188 (by decide)
  have h1 : Entails.eval a c5140 := h 5139 (by decide)
  have h2 : Entails.eval a c5179 := h 5178 (by decide)
  have h3 : Entails.eval a c5328 := h 5327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7942 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7942 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7921, some c6318, some c7926, some c6332, some c7939, some c6725, some c7317, some c7469, some c7170, some c6275, some c7392, some c7941, some c7940, some c5209, some c5154, some c5224, some c5411, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7942 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7942 : lratChecker f7942 p7942 = .success := by decide +kernel
theorem unsat7942 : Unsatisfiable (PosFin 65) f7942 := by
  apply lratCheckerSound f7942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7942
  · intro a ha; simp [p7942] at ha; subst a; trivial
  · exact checked7942
theorem derived7942 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7942 := by
  apply localUnsat_implies_entails f7942 [c7877, c7921, c6318, c7926, c6332, c7939, c6725, c7317, c7469, c7170, c6275, c7392, c7941, c7940, c5209, c5154, c5224, c5411] c7942 unsat7942 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c6318 := h 6317 (by decide)
  have h3 : Entails.eval a c7926 := derived7926 a h
  have h4 : Entails.eval a c6332 := h 6331 (by decide)
  have h5 : Entails.eval a c7939 := derived7939 a h
  have h6 : Entails.eval a c6725 := h 6724 (by decide)
  have h7 : Entails.eval a c7317 := h 7316 (by decide)
  have h8 : Entails.eval a c7469 := h 7468 (by decide)
  have h9 : Entails.eval a c7170 := h 7169 (by decide)
  have h10 : Entails.eval a c6275 := h 6274 (by decide)
  have h11 : Entails.eval a c7392 := h 7391 (by decide)
  have h12 : Entails.eval a c7941 := derived7941 a h
  have h13 : Entails.eval a c7940 := derived7940 a h
  have h14 : Entails.eval a c5209 := h 5208 (by decide)
  have h15 : Entails.eval a c5154 := h 5153 (by decide)
  have h16 : Entails.eval a c5224 := h 5223 (by decide)
  have h17 : Entails.eval a c5411 := h 5410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7943 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7943 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c7877, some c6318, some c7942, some c6978, some c7066, some c7121, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7943 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7943 : lratChecker f7943 p7943 = .success := by decide +kernel
theorem unsat7943 : Unsatisfiable (PosFin 65) f7943 := by
  apply lratCheckerSound f7943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7943
  · intro a ha; simp [p7943] at ha; subst a; trivial
  · exact checked7943
theorem derived7943 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7943 := by
  apply localUnsat_implies_entails f7943 [c7921, c7877, c6318, c7942, c6978, c7066, c7121] c7943 unsat7943 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c7877 := derived7877 a h
  have h2 : Entails.eval a c6318 := h 6317 (by decide)
  have h3 : Entails.eval a c7942 := derived7942 a h
  have h4 : Entails.eval a c6978 := h 6977 (by decide)
  have h5 : Entails.eval a c7066 := h 7065 (by decide)
  have h6 : Entails.eval a c7121 := h 7120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7944 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨64, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7944 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7926, some c7943, some c7826, some c6818, some c6319, some c7326, some c7385, some c7067, some c7797, some c7796, some c6, some c7790, some c7795, some c5211, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7944 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7944 : lratChecker f7944 p7944 = .success := by decide +kernel
theorem unsat7944 : Unsatisfiable (PosFin 65) f7944 := by
  apply lratCheckerSound f7944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7944
  · intro a ha; simp [p7944] at ha; subst a; trivial
  · exact checked7944
theorem derived7944 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7944 := by
  apply localUnsat_implies_entails f7944 [c7926, c7943, c7826, c6818, c6319, c7326, c7385, c7067, c7797, c7796, c6, c7790, c7795, c5211] c7944 unsat7944 (by rfl) a
  have h0 : Entails.eval a c7926 := derived7926 a h
  have h1 : Entails.eval a c7943 := derived7943 a h
  have h2 : Entails.eval a c7826 := derived7826 a h
  have h3 : Entails.eval a c6818 := h 6817 (by decide)
  have h4 : Entails.eval a c6319 := h 6318 (by decide)
  have h5 : Entails.eval a c7326 := h 7325 (by decide)
  have h6 : Entails.eval a c7385 := h 7384 (by decide)
  have h7 : Entails.eval a c7067 := h 7066 (by decide)
  have h8 : Entails.eval a c7797 := derived7797 a h
  have h9 : Entails.eval a c7796 := derived7796 a h
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c7790 := derived7790 a h
  have h12 : Entails.eval a c7795 := derived7795 a h
  have h13 : Entails.eval a c5211 := h 5210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7945 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7945 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6801, some c6818, some c6517, some c7326, some c7136, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7945 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7945 : lratChecker f7945 p7945 = .success := by decide +kernel
theorem unsat7945 : Unsatisfiable (PosFin 65) f7945 := by
  apply lratCheckerSound f7945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7945
  · intro a ha; simp [p7945] at ha; subst a; trivial
  · exact checked7945
theorem derived7945 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7945 := by
  apply localUnsat_implies_entails f7945 [c6801, c6818, c6517, c7326, c7136] c7945 unsat7945 (by rfl) a
  have h0 : Entails.eval a c6801 := h 6800 (by decide)
  have h1 : Entails.eval a c6818 := h 6817 (by decide)
  have h2 : Entails.eval a c6517 := h 6516 (by decide)
  have h3 : Entails.eval a c7326 := h 7325 (by decide)
  have h4 : Entails.eval a c7136 := h 7135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7946 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7946 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7121, some c7134, some c6463, some c6532, some c6860, some c7010, some c7076, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7946 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7946 : lratChecker f7946 p7946 = .success := by decide +kernel
theorem unsat7946 : Unsatisfiable (PosFin 65) f7946 := by
  apply lratCheckerSound f7946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7946
  · intro a ha; simp [p7946] at ha; subst a; trivial
  · exact checked7946
theorem derived7946 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7946 := by
  apply localUnsat_implies_entails f7946 [c7121, c7134, c6463, c6532, c6860, c7010, c7076] c7946 unsat7946 (by rfl) a
  have h0 : Entails.eval a c7121 := h 7120 (by decide)
  have h1 : Entails.eval a c7134 := h 7133 (by decide)
  have h2 : Entails.eval a c6463 := h 6462 (by decide)
  have h3 : Entails.eval a c6532 := h 6531 (by decide)
  have h4 : Entails.eval a c6860 := h 6859 (by decide)
  have h5 : Entails.eval a c7010 := h 7009 (by decide)
  have h6 : Entails.eval a c7076 := h 7075 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7947 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7947 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c7877, some c7944, some c7945, some c7946, some c6436, some c6406, some c7162, some c7046, some c6463, some c6860, some c7076, some c7822, some c7200, some c6525, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7947 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7947 : lratChecker f7947 p7947 = .success := by decide +kernel
theorem unsat7947 : Unsatisfiable (PosFin 65) f7947 := by
  apply lratCheckerSound f7947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7947
  · intro a ha; simp [p7947] at ha; subst a; trivial
  · exact checked7947
theorem derived7947 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7947 := by
  apply localUnsat_implies_entails f7947 [c7921, c7877, c7944, c7945, c7946, c6436, c6406, c7162, c7046, c6463, c6860, c7076, c7822, c7200, c6525] c7947 unsat7947 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c7877 := derived7877 a h
  have h2 : Entails.eval a c7944 := derived7944 a h
  have h3 : Entails.eval a c7945 := derived7945 a h
  have h4 : Entails.eval a c7946 := derived7946 a h
  have h5 : Entails.eval a c6436 := h 6435 (by decide)
  have h6 : Entails.eval a c6406 := h 6405 (by decide)
  have h7 : Entails.eval a c7162 := h 7161 (by decide)
  have h8 : Entails.eval a c7046 := h 7045 (by decide)
  have h9 : Entails.eval a c6463 := h 6462 (by decide)
  have h10 : Entails.eval a c6860 := h 6859 (by decide)
  have h11 : Entails.eval a c7076 := h 7075 (by decide)
  have h12 : Entails.eval a c7822 := derived7822 a h
  have h13 : Entails.eval a c7200 := h 7199 (by decide)
  have h14 : Entails.eval a c6525 := h 6524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7948 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7948 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6373, some c6361, some c6860, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7948 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7948 : lratChecker f7948 p7948 = .success := by decide +kernel
theorem unsat7948 : Unsatisfiable (PosFin 65) f7948 := by
  apply lratCheckerSound f7948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7948
  · intro a ha; simp [p7948] at ha; subst a; trivial
  · exact checked7948
theorem derived7948 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7948 := by
  apply localUnsat_implies_entails f7948 [c6373, c6361, c6860] c7948 unsat7948 (by rfl) a
  have h0 : Entails.eval a c6373 := h 6372 (by decide)
  have h1 : Entails.eval a c6361 := h 6360 (by decide)
  have h2 : Entails.eval a c6860 := h 6859 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7949 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7949 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7877, some c7921, some c7948, some c6362, some c6851, some c6517, some c6423, some c7733, some c6865, some c6859, some c7276, some c7442, some c7007, some c7361, some c7549, some c6965, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7949 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7949 : lratChecker f7949 p7949 = .success := by decide +kernel
theorem unsat7949 : Unsatisfiable (PosFin 65) f7949 := by
  apply lratCheckerSound f7949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7949
  · intro a ha; simp [p7949] at ha; subst a; trivial
  · exact checked7949
theorem derived7949 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7949 := by
  apply localUnsat_implies_entails f7949 [c7877, c7921, c7948, c6362, c6851, c6517, c6423, c7733, c6865, c6859, c7276, c7442, c7007, c7361, c7549, c6965] c7949 unsat7949 (by rfl) a
  have h0 : Entails.eval a c7877 := derived7877 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7948 := derived7948 a h
  have h3 : Entails.eval a c6362 := h 6361 (by decide)
  have h4 : Entails.eval a c6851 := h 6850 (by decide)
  have h5 : Entails.eval a c6517 := h 6516 (by decide)
  have h6 : Entails.eval a c6423 := h 6422 (by decide)
  have h7 : Entails.eval a c7733 := derived7733 a h
  have h8 : Entails.eval a c6865 := h 6864 (by decide)
  have h9 : Entails.eval a c6859 := h 6858 (by decide)
  have h10 : Entails.eval a c7276 := h 7275 (by decide)
  have h11 : Entails.eval a c7442 := h 7441 (by decide)
  have h12 : Entails.eval a c7007 := h 7006 (by decide)
  have h13 : Entails.eval a c7361 := h 7360 (by decide)
  have h14 : Entails.eval a c7549 := h 7548 (by decide)
  have h15 : Entails.eval a c6965 := h 6964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7950 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7950 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7921, some c7877, some c7948, some c7733, some c6362, some c6851, some c6423, some c7264, some c7949, some c6377, some c6372, some c7215, some c6555, some c7007, some c6378, some c7111, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7950 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7950 : lratChecker f7950 p7950 = .success := by decide +kernel
theorem unsat7950 : Unsatisfiable (PosFin 65) f7950 := by
  apply lratCheckerSound f7950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7950
  · intro a ha; simp [p7950] at ha; subst a; trivial
  · exact checked7950
theorem derived7950 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7950 := by
  apply localUnsat_implies_entails f7950 [c7921, c7877, c7948, c7733, c6362, c6851, c6423, c7264, c7949, c6377, c6372, c7215, c6555, c7007, c6378, c7111] c7950 unsat7950 (by rfl) a
  have h0 : Entails.eval a c7921 := derived7921 a h
  have h1 : Entails.eval a c7877 := derived7877 a h
  have h2 : Entails.eval a c7948 := derived7948 a h
  have h3 : Entails.eval a c7733 := derived7733 a h
  have h4 : Entails.eval a c6362 := h 6361 (by decide)
  have h5 : Entails.eval a c6851 := h 6850 (by decide)
  have h6 : Entails.eval a c6423 := h 6422 (by decide)
  have h7 : Entails.eval a c7264 := h 7263 (by decide)
  have h8 : Entails.eval a c7949 := derived7949 a h
  have h9 : Entails.eval a c6377 := h 6376 (by decide)
  have h10 : Entails.eval a c6372 := h 6371 (by decide)
  have h11 : Entails.eval a c7215 := h 7214 (by decide)
  have h12 : Entails.eval a c6555 := h 6554 (by decide)
  have h13 : Entails.eval a c7007 := h 7006 (by decide)
  have h14 : Entails.eval a c6378 := h 6377 (by decide)
  have h15 : Entails.eval a c7111 := h 7110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7950

end CochromaticTwenty.Certificates.FixedCore0
