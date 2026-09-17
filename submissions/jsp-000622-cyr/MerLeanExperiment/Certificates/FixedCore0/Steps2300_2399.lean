import MerLeanExperiment.Certificates.FixedCore0.Steps2200_2299

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9851 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9851 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3554, some c3551, some c911, some c3556, some c923, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9851 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9851 : lratChecker f9851 p9851 = .success := by decide +kernel
theorem unsat9851 : Unsatisfiable (PosFin 65) f9851 := by
  apply lratCheckerSound f9851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9851
  · intro a ha; simp [p9851] at ha; subst a; trivial
  · exact checked9851
theorem derived9851 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9851 := by
  apply localUnsat_implies_entails f9851 [c3554, c3551, c911, c3556, c923] c9851 unsat9851 (by rfl) a
  have h0 : Entails.eval a c3554 := h 3553 (by decide)
  have h1 : Entails.eval a c3551 := h 3550 (by decide)
  have h2 : Entails.eval a c911 := h 910 (by decide)
  have h3 : Entails.eval a c3556 := h 3555 (by decide)
  have h4 : Entails.eval a c923 := h 922 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9852 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9852 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9792, some c9830, some c9847, some c3593, some c3592, some c3591, some c3580, some c3579, some c3590, some c8003, some c3587, some c3598, some c9829, some c9828, some c9849, some c9851, some c9839, some c9850, some c3827, some c1664, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9852 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked9852 : lratChecker f9852 p9852 = .success := by decide +kernel
theorem unsat9852 : Unsatisfiable (PosFin 65) f9852 := by
  apply lratCheckerSound f9852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9852
  · intro a ha; simp [p9852] at ha; subst a; trivial
  · exact checked9852
theorem derived9852 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9852 := by
  apply localUnsat_implies_entails f9852 [c9748, c9792, c9830, c9847, c3593, c3592, c3591, c3580, c3579, c3590, c8003, c3587, c3598, c9829, c9828, c9849, c9851, c9839, c9850, c3827, c1664] c9852 unsat9852 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9792 := derived9792 a h
  have h2 : Entails.eval a c9830 := derived9830 a h
  have h3 : Entails.eval a c9847 := derived9847 a h
  have h4 : Entails.eval a c3593 := h 3592 (by decide)
  have h5 : Entails.eval a c3592 := h 3591 (by decide)
  have h6 : Entails.eval a c3591 := h 3590 (by decide)
  have h7 : Entails.eval a c3580 := h 3579 (by decide)
  have h8 : Entails.eval a c3579 := h 3578 (by decide)
  have h9 : Entails.eval a c3590 := h 3589 (by decide)
  have h10 : Entails.eval a c8003 := derived8003 a h
  have h11 : Entails.eval a c3587 := h 3586 (by decide)
  have h12 : Entails.eval a c3598 := h 3597 (by decide)
  have h13 : Entails.eval a c9829 := derived9829 a h
  have h14 : Entails.eval a c9828 := derived9828 a h
  have h15 : Entails.eval a c9849 := derived9849 a h
  have h16 : Entails.eval a c9851 := derived9851 a h
  have h17 : Entails.eval a c9839 := derived9839 a h
  have h18 : Entails.eval a c9850 := derived9850 a h
  have h19 : Entails.eval a c3827 := h 3826 (by decide)
  have h20 : Entails.eval a c1664 := h 1663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9853 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9853 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1509, some c4131, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9853 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9853 : lratChecker f9853 p9853 = .success := by decide +kernel
theorem unsat9853 : Unsatisfiable (PosFin 65) f9853 := by
  apply lratCheckerSound f9853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9853
  · intro a ha; simp [p9853] at ha; subst a; trivial
  · exact checked9853
theorem derived9853 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9853 := by
  apply localUnsat_implies_entails f9853 [c9748, c1509, c4131] c9853 unsat9853 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1509 := h 1508 (by decide)
  have h2 : Entails.eval a c4131 := h 4130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9854 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9854 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9853, some c9781, some c9789, some c1507, some c4133, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9854 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9854 : lratChecker f9854 p9854 = .success := by decide +kernel
theorem unsat9854 : Unsatisfiable (PosFin 65) f9854 := by
  apply lratCheckerSound f9854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9854
  · intro a ha; simp [p9854] at ha; subst a; trivial
  · exact checked9854
theorem derived9854 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9854 := by
  apply localUnsat_implies_entails f9854 [c9748, c9853, c9781, c9789, c1507, c4133] c9854 unsat9854 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9853 := derived9853 a h
  have h2 : Entails.eval a c9781 := derived9781 a h
  have h3 : Entails.eval a c9789 := derived9789 a h
  have h4 : Entails.eval a c1507 := h 1506 (by decide)
  have h5 : Entails.eval a c4133 := h 4132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9855 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨50, by decide⟩, true), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9855 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1945, some c1942, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p9855 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9855 : lratChecker f9855 p9855 = .success := by decide +kernel
theorem unsat9855 : Unsatisfiable (PosFin 65) f9855 := by
  apply lratCheckerSound f9855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9855
  · intro a ha; simp [p9855] at ha; subst a; trivial
  · exact checked9855
theorem derived9855 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9855 := by
  apply localUnsat_implies_entails f9855 [c9748, c1945, c1942] c9855 unsat9855 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1945 := h 1944 (by decide)
  have h2 : Entails.eval a c1942 := h 1941 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9856 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9856 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3977, some c1503, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9856 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9856 : lratChecker f9856 p9856 = .success := by decide +kernel
theorem unsat9856 : Unsatisfiable (PosFin 65) f9856 := by
  apply lratCheckerSound f9856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9856
  · intro a ha; simp [p9856] at ha; subst a; trivial
  · exact checked9856
theorem derived9856 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9856 := by
  apply localUnsat_implies_entails f9856 [c9748, c3977, c1503] c9856 unsat9856 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3977 := h 3976 (by decide)
  have h2 : Entails.eval a c1503 := h 1502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9857 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9857 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9812, some c3968, some c3966, some c1918, some c1922, some c3970, some c1455, some c3971, some c1486, some c1916, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9857 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9857 : lratChecker f9857 p9857 = .success := by decide +kernel
theorem unsat9857 : Unsatisfiable (PosFin 65) f9857 := by
  apply lratCheckerSound f9857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9857
  · intro a ha; simp [p9857] at ha; subst a; trivial
  · exact checked9857
theorem derived9857 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9857 := by
  apply localUnsat_implies_entails f9857 [c9748, c9812, c3968, c3966, c1918, c1922, c3970, c1455, c3971, c1486, c1916] c9857 unsat9857 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9812 := derived9812 a h
  have h2 : Entails.eval a c3968 := h 3967 (by decide)
  have h3 : Entails.eval a c3966 := h 3965 (by decide)
  have h4 : Entails.eval a c1918 := h 1917 (by decide)
  have h5 : Entails.eval a c1922 := h 1921 (by decide)
  have h6 : Entails.eval a c3970 := h 3969 (by decide)
  have h7 : Entails.eval a c1455 := h 1454 (by decide)
  have h8 : Entails.eval a c3971 := h 3970 (by decide)
  have h9 : Entails.eval a c1486 := h 1485 (by decide)
  have h10 : Entails.eval a c1916 := h 1915 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9858 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, true), (⟨50, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9858 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1944, some c1529, some c9857, some c1457, some c1458, some c3967, some c3971, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9858 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9858 : lratChecker f9858 p9858 = .success := by decide +kernel
theorem unsat9858 : Unsatisfiable (PosFin 65) f9858 := by
  apply lratCheckerSound f9858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9858
  · intro a ha; simp [p9858] at ha; subst a; trivial
  · exact checked9858
theorem derived9858 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9858 := by
  apply localUnsat_implies_entails f9858 [c9748, c1944, c1529, c9857, c1457, c1458, c3967, c3971] c9858 unsat9858 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1944 := h 1943 (by decide)
  have h2 : Entails.eval a c1529 := h 1528 (by decide)
  have h3 : Entails.eval a c9857 := derived9857 a h
  have h4 : Entails.eval a c1457 := h 1456 (by decide)
  have h5 : Entails.eval a c1458 := h 1457 (by decide)
  have h6 : Entails.eval a c3967 := h 3966 (by decide)
  have h7 : Entails.eval a c3971 := h 3970 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9859 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9859 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4113, some c4112, some c1921, some c4115, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9859 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9859 : lratChecker f9859 p9859 = .success := by decide +kernel
theorem unsat9859 : Unsatisfiable (PosFin 65) f9859 := by
  apply lratCheckerSound f9859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9859
  · intro a ha; simp [p9859] at ha; subst a; trivial
  · exact checked9859
theorem derived9859 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9859 := by
  apply localUnsat_implies_entails f9859 [c9748, c4113, c4112, c1921, c4115] c9859 unsat9859 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4113 := h 4112 (by decide)
  have h2 : Entails.eval a c4112 := h 4111 (by decide)
  have h3 : Entails.eval a c1921 := h 1920 (by decide)
  have h4 : Entails.eval a c4115 := h 4114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9860 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9860 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9859, some c4107, some c1918, some c4104, some c2609, some c1686, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9860 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9860 : lratChecker f9860 p9860 = .success := by decide +kernel
theorem unsat9860 : Unsatisfiable (PosFin 65) f9860 := by
  apply lratCheckerSound f9860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9860
  · intro a ha; simp [p9860] at ha; subst a; trivial
  · exact checked9860
theorem derived9860 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9860 := by
  apply localUnsat_implies_entails f9860 [c9748, c9859, c4107, c1918, c4104, c2609, c1686] c9860 unsat9860 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9859 := derived9859 a h
  have h2 : Entails.eval a c4107 := h 4106 (by decide)
  have h3 : Entails.eval a c1918 := h 1917 (by decide)
  have h4 : Entails.eval a c4104 := h 4103 (by decide)
  have h5 : Entails.eval a c2609 := h 2608 (by decide)
  have h6 : Entails.eval a c1686 := h 1685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9861 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9861 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c911, some c772, some c1618, some c2773, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9861 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9861 : lratChecker f9861 p9861 = .success := by decide +kernel
theorem unsat9861 : Unsatisfiable (PosFin 65) f9861 := by
  apply lratCheckerSound f9861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9861
  · intro a ha; simp [p9861] at ha; subst a; trivial
  · exact checked9861
theorem derived9861 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9861 := by
  apply localUnsat_implies_entails f9861 [c9748, c911, c772, c1618, c2773] c9861 unsat9861 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c911 := h 910 (by decide)
  have h2 : Entails.eval a c772 := h 771 (by decide)
  have h3 : Entails.eval a c1618 := h 1617 (by decide)
  have h4 : Entails.eval a c2773 := h 2772 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9862 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, false), (⟨12, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9862 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9818, some c3968, some c9861, some c2765, some c2607, some c4481, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9862 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9862 : lratChecker f9862 p9862 = .success := by decide +kernel
theorem unsat9862 : Unsatisfiable (PosFin 65) f9862 := by
  apply lratCheckerSound f9862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9862
  · intro a ha; simp [p9862] at ha; subst a; trivial
  · exact checked9862
theorem derived9862 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9862 := by
  apply localUnsat_implies_entails f9862 [c9818, c3968, c9861, c2765, c2607, c4481] c9862 unsat9862 (by rfl) a
  have h0 : Entails.eval a c9818 := derived9818 a h
  have h1 : Entails.eval a c3968 := h 3967 (by decide)
  have h2 : Entails.eval a c9861 := derived9861 a h
  have h3 : Entails.eval a c2765 := h 2764 (by decide)
  have h4 : Entails.eval a c2607 := h 2606 (by decide)
  have h5 : Entails.eval a c4481 := h 4480 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9863 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨8, by decide⟩, false), (⟨12, by decide⟩, true), (⟨50, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9863 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3977, some c3984, some c9862, some c1457, some c1458, some c3967, some c3971, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9863 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9863 : lratChecker f9863 p9863 = .success := by decide +kernel
theorem unsat9863 : Unsatisfiable (PosFin 65) f9863 := by
  apply lratCheckerSound f9863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9863
  · intro a ha; simp [p9863] at ha; subst a; trivial
  · exact checked9863
theorem derived9863 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9863 := by
  apply localUnsat_implies_entails f9863 [c9748, c3977, c3984, c9862, c1457, c1458, c3967, c3971] c9863 unsat9863 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3977 := h 3976 (by decide)
  have h2 : Entails.eval a c3984 := h 3983 (by decide)
  have h3 : Entails.eval a c9862 := derived9862 a h
  have h4 : Entails.eval a c1457 := h 1456 (by decide)
  have h5 : Entails.eval a c1458 := h 1457 (by decide)
  have h6 : Entails.eval a c3967 := h 3966 (by decide)
  have h7 : Entails.eval a c3971 := h 3970 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9864 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨35, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9864 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1487, some c1486, some c1484, some c1485, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p9864 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9864 : lratChecker f9864 p9864 = .success := by decide +kernel
theorem unsat9864 : Unsatisfiable (PosFin 65) f9864 := by
  apply lratCheckerSound f9864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9864
  · intro a ha; simp [p9864] at ha; subst a; trivial
  · exact checked9864
theorem derived9864 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9864 := by
  apply localUnsat_implies_entails f9864 [c9748, c1487, c1486, c1484, c1485] c9864 unsat9864 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1487 := h 1486 (by decide)
  have h2 : Entails.eval a c1486 := h 1485 (by decide)
  have h3 : Entails.eval a c1484 := h 1483 (by decide)
  have h4 : Entails.eval a c1485 := h 1484 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9865 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9865 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9812, some c1454, some c1918, some c1922, some c1455, some c9864, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p9865 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9865 : lratChecker f9865 p9865 = .success := by decide +kernel
theorem unsat9865 : Unsatisfiable (PosFin 65) f9865 := by
  apply lratCheckerSound f9865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9865
  · intro a ha; simp [p9865] at ha; subst a; trivial
  · exact checked9865
theorem derived9865 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9865 := by
  apply localUnsat_implies_entails f9865 [c9748, c9812, c1454, c1918, c1922, c1455, c9864] c9865 unsat9865 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9812 := derived9812 a h
  have h2 : Entails.eval a c1454 := h 1453 (by decide)
  have h3 : Entails.eval a c1918 := h 1917 (by decide)
  have h4 : Entails.eval a c1922 := h 1921 (by decide)
  have h5 : Entails.eval a c1455 := h 1454 (by decide)
  have h6 : Entails.eval a c9864 := derived9864 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9866 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9866 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9834, some c1500, some c1528, some c9865, some c1457, some c1458, some c1479, some c1471, some c1928, some c1454, some c1480, some c9864, some c8561, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9866 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9866 : lratChecker f9866 p9866 = .success := by decide +kernel
theorem unsat9866 : Unsatisfiable (PosFin 65) f9866 := by
  apply lratCheckerSound f9866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9866
  · intro a ha; simp [p9866] at ha; subst a; trivial
  · exact checked9866
theorem derived9866 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9866 := by
  apply localUnsat_implies_entails f9866 [c9748, c9834, c1500, c1528, c9865, c1457, c1458, c1479, c1471, c1928, c1454, c1480, c9864, c8561] c9866 unsat9866 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9834 := derived9834 a h
  have h2 : Entails.eval a c1500 := h 1499 (by decide)
  have h3 : Entails.eval a c1528 := h 1527 (by decide)
  have h4 : Entails.eval a c9865 := derived9865 a h
  have h5 : Entails.eval a c1457 := h 1456 (by decide)
  have h6 : Entails.eval a c1458 := h 1457 (by decide)
  have h7 : Entails.eval a c1479 := h 1478 (by decide)
  have h8 : Entails.eval a c1471 := h 1470 (by decide)
  have h9 : Entails.eval a c1928 := h 1927 (by decide)
  have h10 : Entails.eval a c1454 := h 1453 (by decide)
  have h11 : Entails.eval a c1480 := h 1479 (by decide)
  have h12 : Entails.eval a c9864 := derived9864 a h
  have h13 : Entails.eval a c8561 := derived8561 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9867 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨63, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9867 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1518, some c1512, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p9867 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9867 : lratChecker f9867 p9867 = .success := by decide +kernel
theorem unsat9867 : Unsatisfiable (PosFin 65) f9867 := by
  apply lratCheckerSound f9867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9867
  · intro a ha; simp [p9867] at ha; subst a; trivial
  · exact checked9867
theorem derived9867 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9867 := by
  apply localUnsat_implies_entails f9867 [c9748, c1518, c1512] c9867 unsat9867 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1518 := h 1517 (by decide)
  have h2 : Entails.eval a c1512 := h 1511 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9868 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨61, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9868 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1527, some c3981, some c1528, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9868 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9868 : lratChecker f9868 p9868 = .success := by decide +kernel
theorem unsat9868 : Unsatisfiable (PosFin 65) f9868 := by
  apply lratCheckerSound f9868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9868
  · intro a ha; simp [p9868] at ha; subst a; trivial
  · exact checked9868
theorem derived9868 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9868 := by
  apply localUnsat_implies_entails f9868 [c9748, c1527, c3981, c1528] c9868 unsat9868 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1527 := h 1526 (by decide)
  have h2 : Entails.eval a c3981 := h 3980 (by decide)
  have h3 : Entails.eval a c1528 := h 1527 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9869 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9869 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1954, some c2752, some c9868, some c4137, some c4135, some c4139, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9869 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9869 : lratChecker f9869 p9869 = .success := by decide +kernel
theorem unsat9869 : Unsatisfiable (PosFin 65) f9869 := by
  apply lratCheckerSound f9869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9869
  · intro a ha; simp [p9869] at ha; subst a; trivial
  · exact checked9869
theorem derived9869 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9869 := by
  apply localUnsat_implies_entails f9869 [c9748, c1954, c2752, c9868, c4137, c4135, c4139] c9869 unsat9869 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1954 := h 1953 (by decide)
  have h2 : Entails.eval a c2752 := h 2751 (by decide)
  have h3 : Entails.eval a c9868 := derived9868 a h
  have h4 : Entails.eval a c4137 := h 4136 (by decide)
  have h5 : Entails.eval a c4135 := h 4134 (by decide)
  have h6 : Entails.eval a c4139 := h 4138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9870 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨12, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, true), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9870 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9863, some c9858, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9870 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9870 : lratChecker f9870 p9870 = .success := by decide +kernel
theorem unsat9870 : Unsatisfiable (PosFin 65) f9870 := by
  apply lratCheckerSound f9870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9870
  · intro a ha; simp [p9870] at ha; subst a; trivial
  · exact checked9870
theorem derived9870 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9870 := by
  apply localUnsat_implies_entails f9870 [c9863, c9858] c9870 unsat9870 (by rfl) a
  have h0 : Entails.eval a c9863 := derived9863 a h
  have h1 : Entails.eval a c9858 := derived9858 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9871 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9871 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9856, some c9870, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9871 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9871 : lratChecker f9871 p9871 = .success := by decide +kernel
theorem unsat9871 : Unsatisfiable (PosFin 65) f9871 := by
  apply lratCheckerSound f9871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9871
  · intro a ha; simp [p9871] at ha; subst a; trivial
  · exact checked9871
theorem derived9871 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9871 := by
  apply localUnsat_implies_entails f9871 [c9856, c9870] c9871 unsat9871 (by rfl) a
  have h0 : Entails.eval a c9856 := derived9856 a h
  have h1 : Entails.eval a c9870 := derived9870 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9872 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9872 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9871, some c9866, some c9855, some c1503, some c2732, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9872 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9872 : lratChecker f9872 p9872 = .success := by decide +kernel
theorem unsat9872 : Unsatisfiable (PosFin 65) f9872 := by
  apply lratCheckerSound f9872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9872
  · intro a ha; simp [p9872] at ha; subst a; trivial
  · exact checked9872
theorem derived9872 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9872 := by
  apply localUnsat_implies_entails f9872 [c9748, c9871, c9866, c9855, c1503, c2732] c9872 unsat9872 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9871 := derived9871 a h
  have h2 : Entails.eval a c9866 := derived9866 a h
  have h3 : Entails.eval a c9855 := derived9855 a h
  have h4 : Entails.eval a c1503 := h 1502 (by decide)
  have h5 : Entails.eval a c2732 := h 2731 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9873 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨5, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9873 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4127, some c4126, some c4129, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9873 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9873 : lratChecker f9873 p9873 = .success := by decide +kernel
theorem unsat9873 : Unsatisfiable (PosFin 65) f9873 := by
  apply lratCheckerSound f9873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9873
  · intro a ha; simp [p9873] at ha; subst a; trivial
  · exact checked9873
theorem derived9873 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9873 := by
  apply localUnsat_implies_entails f9873 [c4127, c4126, c4129] c9873 unsat9873 (by rfl) a
  have h0 : Entails.eval a c4127 := h 4126 (by decide)
  have h1 : Entails.eval a c4126 := h 4125 (by decide)
  have h2 : Entails.eval a c4129 := h 4128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9874 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9874 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4106, some c4105, some c4103, some c4110, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9874 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9874 : lratChecker f9874 p9874 = .success := by decide +kernel
theorem unsat9874 : Unsatisfiable (PosFin 65) f9874 := by
  apply lratCheckerSound f9874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9874
  · intro a ha; simp [p9874] at ha; subst a; trivial
  · exact checked9874
theorem derived9874 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9874 := by
  apply localUnsat_implies_entails f9874 [c4106, c4105, c4103, c4110] c9874 unsat9874 (by rfl) a
  have h0 : Entails.eval a c4106 := h 4105 (by decide)
  have h1 : Entails.eval a c4105 := h 4104 (by decide)
  have h2 : Entails.eval a c4103 := h 4102 (by decide)
  have h3 : Entails.eval a c4110 := h 4109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9875 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9875 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c774, some c914, some c911, some c930, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9875 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9875 : lratChecker f9875 p9875 = .success := by decide +kernel
theorem unsat9875 : Unsatisfiable (PosFin 65) f9875 := by
  apply lratCheckerSound f9875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9875
  · intro a ha; simp [p9875] at ha; subst a; trivial
  · exact checked9875
theorem derived9875 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9875 := by
  apply localUnsat_implies_entails f9875 [c774, c914, c911, c930] c9875 unsat9875 (by rfl) a
  have h0 : Entails.eval a c774 := h 773 (by decide)
  have h1 : Entails.eval a c914 := h 913 (by decide)
  have h2 : Entails.eval a c911 := h 910 (by decide)
  have h3 : Entails.eval a c930 := h 929 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9876 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9876 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9839, some c4104, some c9875, some c785, some c923, some c780, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9876 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9876 : lratChecker f9876 p9876 = .success := by decide +kernel
theorem unsat9876 : Unsatisfiable (PosFin 65) f9876 := by
  apply lratCheckerSound f9876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9876
  · intro a ha; simp [p9876] at ha; subst a; trivial
  · exact checked9876
theorem derived9876 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9876 := by
  apply localUnsat_implies_entails f9876 [c9839, c4104, c9875, c785, c923, c780] c9876 unsat9876 (by rfl) a
  have h0 : Entails.eval a c9839 := derived9839 a h
  have h1 : Entails.eval a c4104 := h 4103 (by decide)
  have h2 : Entails.eval a c9875 := derived9875 a h
  have h3 : Entails.eval a c785 := h 784 (by decide)
  have h4 : Entails.eval a c923 := h 922 (by decide)
  have h5 : Entails.eval a c780 := h 779 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9877 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9877 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9794, some c9781, some c9869, some c9872, some c4118, some c9873, some c4125, some c4139, some c9874, some c9876, some c1944, some c9860, some c4398, some c1751, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9877 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9877 : lratChecker f9877 p9877 = .success := by decide +kernel
theorem unsat9877 : Unsatisfiable (PosFin 65) f9877 := by
  apply lratCheckerSound f9877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9877
  · intro a ha; simp [p9877] at ha; subst a; trivial
  · exact checked9877
theorem derived9877 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9877 := by
  apply localUnsat_implies_entails f9877 [c9748, c9794, c9781, c9869, c9872, c4118, c9873, c4125, c4139, c9874, c9876, c1944, c9860, c4398, c1751] c9877 unsat9877 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9794 := derived9794 a h
  have h2 : Entails.eval a c9781 := derived9781 a h
  have h3 : Entails.eval a c9869 := derived9869 a h
  have h4 : Entails.eval a c9872 := derived9872 a h
  have h5 : Entails.eval a c4118 := h 4117 (by decide)
  have h6 : Entails.eval a c9873 := derived9873 a h
  have h7 : Entails.eval a c4125 := h 4124 (by decide)
  have h8 : Entails.eval a c4139 := h 4138 (by decide)
  have h9 : Entails.eval a c9874 := derived9874 a h
  have h10 : Entails.eval a c9876 := derived9876 a h
  have h11 : Entails.eval a c1944 := h 1943 (by decide)
  have h12 : Entails.eval a c9860 := derived9860 a h
  have h13 : Entails.eval a c4398 := h 4397 (by decide)
  have h14 : Entails.eval a c1751 := h 1750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9878 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9878 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1519, some c9867, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p9878 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9878 : lratChecker f9878 p9878 = .success := by decide +kernel
theorem unsat9878 : Unsatisfiable (PosFin 65) f9878 := by
  apply lratCheckerSound f9878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9878
  · intro a ha; simp [p9878] at ha; subst a; trivial
  · exact checked9878
theorem derived9878 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9878 := by
  apply localUnsat_implies_entails f9878 [c9748, c1519, c9867] c9878 unsat9878 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1519 := h 1518 (by decide)
  have h2 : Entails.eval a c9867 := derived9867 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9879 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9879 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9852, some c9792, some c9794, some c9854, some c9877, some c9878, some c4118, some c2018, some c4245, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9879 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9879 : lratChecker f9879 p9879 = .success := by decide +kernel
theorem unsat9879 : Unsatisfiable (PosFin 65) f9879 := by
  apply lratCheckerSound f9879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9879
  · intro a ha; simp [p9879] at ha; subst a; trivial
  · exact checked9879
theorem derived9879 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9879 := by
  apply localUnsat_implies_entails f9879 [c9748, c9852, c9792, c9794, c9854, c9877, c9878, c4118, c2018, c4245] c9879 unsat9879 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9852 := derived9852 a h
  have h2 : Entails.eval a c9792 := derived9792 a h
  have h3 : Entails.eval a c9794 := derived9794 a h
  have h4 : Entails.eval a c9854 := derived9854 a h
  have h5 : Entails.eval a c9877 := derived9877 a h
  have h6 : Entails.eval a c9878 := derived9878 a h
  have h7 : Entails.eval a c4118 := h 4117 (by decide)
  have h8 : Entails.eval a c2018 := h 2017 (by decide)
  have h9 : Entails.eval a c4245 := h 4244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9880 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9880 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9259, some c2613, some c2810, some c2731, some c1906, some c1741, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9880 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9880 : lratChecker f9880 p9880 = .success := by decide +kernel
theorem unsat9880 : Unsatisfiable (PosFin 65) f9880 := by
  apply lratCheckerSound f9880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9880
  · intro a ha; simp [p9880] at ha; subst a; trivial
  · exact checked9880
theorem derived9880 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9880 := by
  apply localUnsat_implies_entails f9880 [c9748, c9259, c2613, c2810, c2731, c1906, c1741] c9880 unsat9880 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9259 := derived9259 a h
  have h2 : Entails.eval a c2613 := h 2612 (by decide)
  have h3 : Entails.eval a c2810 := h 2809 (by decide)
  have h4 : Entails.eval a c2731 := h 2730 (by decide)
  have h5 : Entails.eval a c1906 := h 1905 (by decide)
  have h6 : Entails.eval a c1741 := h 1740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9881 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨55, by decide⟩, false), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9881 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3560, some c882, some c895, some c890, some c3567, some c887, some c3559, some c894, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9881 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9881 : lratChecker f9881 p9881 = .success := by decide +kernel
theorem unsat9881 : Unsatisfiable (PosFin 65) f9881 := by
  apply lratCheckerSound f9881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9881
  · intro a ha; simp [p9881] at ha; subst a; trivial
  · exact checked9881
theorem derived9881 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9881 := by
  apply localUnsat_implies_entails f9881 [c3560, c882, c895, c890, c3567, c887, c3559, c894] c9881 unsat9881 (by rfl) a
  have h0 : Entails.eval a c3560 := h 3559 (by decide)
  have h1 : Entails.eval a c882 := h 881 (by decide)
  have h2 : Entails.eval a c895 := h 894 (by decide)
  have h3 : Entails.eval a c890 := h 889 (by decide)
  have h4 : Entails.eval a c3567 := h 3566 (by decide)
  have h5 : Entails.eval a c887 := h 886 (by decide)
  have h6 : Entails.eval a c3559 := h 3558 (by decide)
  have h7 : Entails.eval a c894 := h 893 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9882 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9882 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3105, some c1677, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p9882 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9882 : lratChecker f9882 p9882 = .success := by decide +kernel
theorem unsat9882 : Unsatisfiable (PosFin 65) f9882 := by
  apply lratCheckerSound f9882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9882
  · intro a ha; simp [p9882] at ha; subst a; trivial
  · exact checked9882
theorem derived9882 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9882 := by
  apply localUnsat_implies_entails f9882 [c9748, c3105, c1677] c9882 unsat9882 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3105 := h 3104 (by decide)
  have h2 : Entails.eval a c1677 := h 1676 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9883 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9883 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9881, some c3554, some c3556, some c3563, some c3562, some c3565, some c893, some c9882, some c4382, some c2608, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9883 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9883 : lratChecker f9883 p9883 = .success := by decide +kernel
theorem unsat9883 : Unsatisfiable (PosFin 65) f9883 := by
  apply lratCheckerSound f9883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9883
  · intro a ha; simp [p9883] at ha; subst a; trivial
  · exact checked9883
theorem derived9883 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9883 := by
  apply localUnsat_implies_entails f9883 [c9881, c3554, c3556, c3563, c3562, c3565, c893, c9882, c4382, c2608] c9883 unsat9883 (by rfl) a
  have h0 : Entails.eval a c9881 := derived9881 a h
  have h1 : Entails.eval a c3554 := h 3553 (by decide)
  have h2 : Entails.eval a c3556 := h 3555 (by decide)
  have h3 : Entails.eval a c3563 := h 3562 (by decide)
  have h4 : Entails.eval a c3562 := h 3561 (by decide)
  have h5 : Entails.eval a c3565 := h 3564 (by decide)
  have h6 : Entails.eval a c893 := h 892 (by decide)
  have h7 : Entails.eval a c9882 := derived9882 a h
  have h8 : Entails.eval a c4382 := h 4381 (by decide)
  have h9 : Entails.eval a c2608 := h 2607 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9884 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9884 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3579, some c3590, some c8003, some c3592, some c3587, some c3598, some c9828, some c3580, some c9829, some c9827, some c9883, some c3545, some c3551, some c3560, some c882, some c895, some c890, some c3567, some c887, some c3565, some c3564, some c894, some c3548, some c3568, some c3572, some c3573, some c3570, some c3571, some c3575, some c898, some c897, some c899, some c901, some c900, some c8664, some c5840, some c6008, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9884 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked9884 : lratChecker f9884 p9884 = .success := by decide +kernel
theorem unsat9884 : Unsatisfiable (PosFin 65) f9884 := by
  apply lratCheckerSound f9884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9884
  · intro a ha; simp [p9884] at ha; subst a; trivial
  · exact checked9884
theorem derived9884 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9884 := by
  apply localUnsat_implies_entails f9884 [c9748, c3579, c3590, c8003, c3592, c3587, c3598, c9828, c3580, c9829, c9827, c9883, c3545, c3551, c3560, c882, c895, c890, c3567, c887, c3565, c3564, c894, c3548, c3568, c3572, c3573, c3570, c3571, c3575, c898, c897, c899, c901, c900, c8664, c5840, c6008] c9884 unsat9884 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3579 := h 3578 (by decide)
  have h2 : Entails.eval a c3590 := h 3589 (by decide)
  have h3 : Entails.eval a c8003 := derived8003 a h
  have h4 : Entails.eval a c3592 := h 3591 (by decide)
  have h5 : Entails.eval a c3587 := h 3586 (by decide)
  have h6 : Entails.eval a c3598 := h 3597 (by decide)
  have h7 : Entails.eval a c9828 := derived9828 a h
  have h8 : Entails.eval a c3580 := h 3579 (by decide)
  have h9 : Entails.eval a c9829 := derived9829 a h
  have h10 : Entails.eval a c9827 := derived9827 a h
  have h11 : Entails.eval a c9883 := derived9883 a h
  have h12 : Entails.eval a c3545 := h 3544 (by decide)
  have h13 : Entails.eval a c3551 := h 3550 (by decide)
  have h14 : Entails.eval a c3560 := h 3559 (by decide)
  have h15 : Entails.eval a c882 := h 881 (by decide)
  have h16 : Entails.eval a c895 := h 894 (by decide)
  have h17 : Entails.eval a c890 := h 889 (by decide)
  have h18 : Entails.eval a c3567 := h 3566 (by decide)
  have h19 : Entails.eval a c887 := h 886 (by decide)
  have h20 : Entails.eval a c3565 := h 3564 (by decide)
  have h21 : Entails.eval a c3564 := h 3563 (by decide)
  have h22 : Entails.eval a c894 := h 893 (by decide)
  have h23 : Entails.eval a c3548 := h 3547 (by decide)
  have h24 : Entails.eval a c3568 := h 3567 (by decide)
  have h25 : Entails.eval a c3572 := h 3571 (by decide)
  have h26 : Entails.eval a c3573 := h 3572 (by decide)
  have h27 : Entails.eval a c3570 := h 3569 (by decide)
  have h28 : Entails.eval a c3571 := h 3570 (by decide)
  have h29 : Entails.eval a c3575 := h 3574 (by decide)
  have h30 : Entails.eval a c898 := h 897 (by decide)
  have h31 : Entails.eval a c897 := h 896 (by decide)
  have h32 : Entails.eval a c899 := h 898 (by decide)
  have h33 : Entails.eval a c901 := h 900 (by decide)
  have h34 : Entails.eval a c900 := h 899 (by decide)
  have h35 : Entails.eval a c8664 := derived8664 a h
  have h36 : Entails.eval a c5840 := h 5839 (by decide)
  have h37 : Entails.eval a c6008 := h 6007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9885 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9885 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3827, some c1664, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9885 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9885 : lratChecker f9885 p9885 = .success := by decide +kernel
theorem unsat9885 : Unsatisfiable (PosFin 65) f9885 := by
  apply lratCheckerSound f9885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9885
  · intro a ha; simp [p9885] at ha; subst a; trivial
  · exact checked9885
theorem derived9885 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9885 := by
  apply localUnsat_implies_entails f9885 [c9748, c3827, c1664] c9885 unsat9885 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3827 := h 3826 (by decide)
  have h2 : Entails.eval a c1664 := h 1663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9886 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9886 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3579, some c3590, some c8003, some c3592, some c3587, some c3598, some c9828, some c3580, some c9829, some c9884, some c9851, some c9850, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9886 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9886 : lratChecker f9886 p9886 = .success := by decide +kernel
theorem unsat9886 : Unsatisfiable (PosFin 65) f9886 := by
  apply lratCheckerSound f9886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9886
  · intro a ha; simp [p9886] at ha; subst a; trivial
  · exact checked9886
theorem derived9886 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9886 := by
  apply localUnsat_implies_entails f9886 [c9748, c3579, c3590, c8003, c3592, c3587, c3598, c9828, c3580, c9829, c9884, c9851, c9850] c9886 unsat9886 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3579 := h 3578 (by decide)
  have h2 : Entails.eval a c3590 := h 3589 (by decide)
  have h3 : Entails.eval a c8003 := derived8003 a h
  have h4 : Entails.eval a c3592 := h 3591 (by decide)
  have h5 : Entails.eval a c3587 := h 3586 (by decide)
  have h6 : Entails.eval a c3598 := h 3597 (by decide)
  have h7 : Entails.eval a c9828 := derived9828 a h
  have h8 : Entails.eval a c3580 := h 3579 (by decide)
  have h9 : Entails.eval a c9829 := derived9829 a h
  have h10 : Entails.eval a c9884 := derived9884 a h
  have h11 : Entails.eval a c9851 := derived9851 a h
  have h12 : Entails.eval a c9850 := derived9850 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9887 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9887 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9792, some c9852, some c9879, some c3593, some c3592, some c3591, some c3580, some c3579, some c9886, some c3827, some c4398, some c1906, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9887 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9887 : lratChecker f9887 p9887 = .success := by decide +kernel
theorem unsat9887 : Unsatisfiable (PosFin 65) f9887 := by
  apply lratCheckerSound f9887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9887
  · intro a ha; simp [p9887] at ha; subst a; trivial
  · exact checked9887
theorem derived9887 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9887 := by
  apply localUnsat_implies_entails f9887 [c9748, c9792, c9852, c9879, c3593, c3592, c3591, c3580, c3579, c9886, c3827, c4398, c1906] c9887 unsat9887 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9792 := derived9792 a h
  have h2 : Entails.eval a c9852 := derived9852 a h
  have h3 : Entails.eval a c9879 := derived9879 a h
  have h4 : Entails.eval a c3593 := h 3592 (by decide)
  have h5 : Entails.eval a c3592 := h 3591 (by decide)
  have h6 : Entails.eval a c3591 := h 3590 (by decide)
  have h7 : Entails.eval a c3580 := h 3579 (by decide)
  have h8 : Entails.eval a c3579 := h 3578 (by decide)
  have h9 : Entails.eval a c9886 := derived9886 a h
  have h10 : Entails.eval a c3827 := h 3826 (by decide)
  have h11 : Entails.eval a c4398 := h 4397 (by decide)
  have h12 : Entails.eval a c1906 := h 1905 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9888 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9888 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3579, some c3580, some c3592, some c3593, some c9886, some c4398, some c4480, some c5033, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9888 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9888 : lratChecker f9888 p9888 = .success := by decide +kernel
theorem unsat9888 : Unsatisfiable (PosFin 65) f9888 := by
  apply lratCheckerSound f9888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9888
  · intro a ha; simp [p9888] at ha; subst a; trivial
  · exact checked9888
theorem derived9888 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9888 := by
  apply localUnsat_implies_entails f9888 [c3579, c3580, c3592, c3593, c9886, c4398, c4480, c5033] c9888 unsat9888 (by rfl) a
  have h0 : Entails.eval a c3579 := h 3578 (by decide)
  have h1 : Entails.eval a c3580 := h 3579 (by decide)
  have h2 : Entails.eval a c3592 := h 3591 (by decide)
  have h3 : Entails.eval a c3593 := h 3592 (by decide)
  have h4 : Entails.eval a c9886 := derived9886 a h
  have h5 : Entails.eval a c4398 := h 4397 (by decide)
  have h6 : Entails.eval a c4480 := h 4479 (by decide)
  have h7 : Entails.eval a c5033 := h 5032 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9889 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9889 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3579, some c3590, some c8003, some c3592, some c3587, some c3598, some c9828, some c3580, some c9829, some c9849, some c9827, some c1750, some c2068, some c2653, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9889 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9889 : lratChecker f9889 p9889 = .success := by decide +kernel
theorem unsat9889 : Unsatisfiable (PosFin 65) f9889 := by
  apply lratCheckerSound f9889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9889
  · intro a ha; simp [p9889] at ha; subst a; trivial
  · exact checked9889
theorem derived9889 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9889 := by
  apply localUnsat_implies_entails f9889 [c9748, c3579, c3590, c8003, c3592, c3587, c3598, c9828, c3580, c9829, c9849, c9827, c1750, c2068, c2653] c9889 unsat9889 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3579 := h 3578 (by decide)
  have h2 : Entails.eval a c3590 := h 3589 (by decide)
  have h3 : Entails.eval a c8003 := derived8003 a h
  have h4 : Entails.eval a c3592 := h 3591 (by decide)
  have h5 : Entails.eval a c3587 := h 3586 (by decide)
  have h6 : Entails.eval a c3598 := h 3597 (by decide)
  have h7 : Entails.eval a c9828 := derived9828 a h
  have h8 : Entails.eval a c3580 := h 3579 (by decide)
  have h9 : Entails.eval a c9829 := derived9829 a h
  have h10 : Entails.eval a c9849 := derived9849 a h
  have h11 : Entails.eval a c9827 := derived9827 a h
  have h12 : Entails.eval a c1750 := h 1749 (by decide)
  have h13 : Entails.eval a c2068 := h 2067 (by decide)
  have h14 : Entails.eval a c2653 := h 2652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9890 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9890 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9887, some c3593, some c3592, some c3591, some c3580, some c3579, some c3590, some c8003, some c3587, some c3598, some c9829, some c9828, some c9888, some c9889, some c9851, some c3560, some c909, some c9850, some c5530, some c792, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9890 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked9890 : lratChecker f9890 p9890 = .success := by decide +kernel
theorem unsat9890 : Unsatisfiable (PosFin 65) f9890 := by
  apply lratCheckerSound f9890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9890
  · intro a ha; simp [p9890] at ha; subst a; trivial
  · exact checked9890
theorem derived9890 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9890 := by
  apply localUnsat_implies_entails f9890 [c9748, c9887, c3593, c3592, c3591, c3580, c3579, c3590, c8003, c3587, c3598, c9829, c9828, c9888, c9889, c9851, c3560, c909, c9850, c5530, c792] c9890 unsat9890 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9887 := derived9887 a h
  have h2 : Entails.eval a c3593 := h 3592 (by decide)
  have h3 : Entails.eval a c3592 := h 3591 (by decide)
  have h4 : Entails.eval a c3591 := h 3590 (by decide)
  have h5 : Entails.eval a c3580 := h 3579 (by decide)
  have h6 : Entails.eval a c3579 := h 3578 (by decide)
  have h7 : Entails.eval a c3590 := h 3589 (by decide)
  have h8 : Entails.eval a c8003 := derived8003 a h
  have h9 : Entails.eval a c3587 := h 3586 (by decide)
  have h10 : Entails.eval a c3598 := h 3597 (by decide)
  have h11 : Entails.eval a c9829 := derived9829 a h
  have h12 : Entails.eval a c9828 := derived9828 a h
  have h13 : Entails.eval a c9888 := derived9888 a h
  have h14 : Entails.eval a c9889 := derived9889 a h
  have h15 : Entails.eval a c9851 := derived9851 a h
  have h16 : Entails.eval a c3560 := h 3559 (by decide)
  have h17 : Entails.eval a c909 := h 908 (by decide)
  have h18 : Entails.eval a c9850 := derived9850 a h
  have h19 : Entails.eval a c5530 := h 5529 (by decide)
  have h20 : Entails.eval a c792 := h 791 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9891 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9891 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1659, some c1640, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9891 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9891 : lratChecker f9891 p9891 = .success := by decide +kernel
theorem unsat9891 : Unsatisfiable (PosFin 65) f9891 := by
  apply lratCheckerSound f9891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9891
  · intro a ha; simp [p9891] at ha; subst a; trivial
  · exact checked9891
theorem derived9891 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9891 := by
  apply localUnsat_implies_entails f9891 [c9748, c1659, c1640] c9891 unsat9891 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1659 := h 1658 (by decide)
  have h2 : Entails.eval a c1640 := h 1639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9892 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false), (⟨50, by decide⟩, true), (⟨60, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9892 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3615, some c3623, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9892 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9892 : lratChecker f9892 p9892 = .success := by decide +kernel
theorem unsat9892 : Unsatisfiable (PosFin 65) f9892 := by
  apply lratCheckerSound f9892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9892
  · intro a ha; simp [p9892] at ha; subst a; trivial
  · exact checked9892
theorem derived9892 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9892 := by
  apply localUnsat_implies_entails f9892 [c3615, c3623] c9892 unsat9892 (by rfl) a
  have h0 : Entails.eval a c3615 := h 3614 (by decide)
  have h1 : Entails.eval a c3623 := h 3622 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9893 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true), (⟨59, by decide⟩, true), (⟨56, by decide⟩, true), (⟨63, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9893 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2327, some c1909, some c3963, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p9893 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9893 : lratChecker f9893 p9893 = .success := by decide +kernel
theorem unsat9893 : Unsatisfiable (PosFin 65) f9893 := by
  apply lratCheckerSound f9893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9893
  · intro a ha; simp [p9893] at ha; subst a; trivial
  · exact checked9893
theorem derived9893 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9893 := by
  apply localUnsat_implies_entails f9893 [c9748, c2327, c1909, c3963] c9893 unsat9893 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2327 := h 2326 (by decide)
  have h2 : Entails.eval a c1909 := h 1908 (by decide)
  have h3 : Entails.eval a c3963 := h 3962 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9894 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9894 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9890, some c3595, some c9759, some c3578, some c3591, some c3597, some c3599, some c9764, some c3584, some c8001, some c9892, some c9891, some c9893, some c2339, some c1910, some c3945, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9894 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9894 : lratChecker f9894 p9894 = .success := by decide +kernel
theorem unsat9894 : Unsatisfiable (PosFin 65) f9894 := by
  apply lratCheckerSound f9894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9894
  · intro a ha; simp [p9894] at ha; subst a; trivial
  · exact checked9894
theorem derived9894 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9894 := by
  apply localUnsat_implies_entails f9894 [c9748, c9890, c3595, c9759, c3578, c3591, c3597, c3599, c9764, c3584, c8001, c9892, c9891, c9893, c2339, c1910, c3945] c9894 unsat9894 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9890 := derived9890 a h
  have h2 : Entails.eval a c3595 := h 3594 (by decide)
  have h3 : Entails.eval a c9759 := derived9759 a h
  have h4 : Entails.eval a c3578 := h 3577 (by decide)
  have h5 : Entails.eval a c3591 := h 3590 (by decide)
  have h6 : Entails.eval a c3597 := h 3596 (by decide)
  have h7 : Entails.eval a c3599 := h 3598 (by decide)
  have h8 : Entails.eval a c9764 := derived9764 a h
  have h9 : Entails.eval a c3584 := h 3583 (by decide)
  have h10 : Entails.eval a c8001 := derived8001 a h
  have h11 : Entails.eval a c9892 := derived9892 a h
  have h12 : Entails.eval a c9891 := derived9891 a h
  have h13 : Entails.eval a c9893 := derived9893 a h
  have h14 : Entails.eval a c2339 := h 2338 (by decide)
  have h15 : Entails.eval a c1910 := h 1909 (by decide)
  have h16 : Entails.eval a c3945 := h 3944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9895 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨9, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9895 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9878, some c9880, some c9872, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9895 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9895 : lratChecker f9895 p9895 = .success := by decide +kernel
theorem unsat9895 : Unsatisfiable (PosFin 65) f9895 := by
  apply lratCheckerSound f9895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9895
  · intro a ha; simp [p9895] at ha; subst a; trivial
  · exact checked9895
theorem derived9895 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9895 := by
  apply localUnsat_implies_entails f9895 [c9878, c9880, c9872] c9895 unsat9895 (by rfl) a
  have h0 : Entails.eval a c9878 := derived9878 a h
  have h1 : Entails.eval a c9880 := derived9880 a h
  have h2 : Entails.eval a c9872 := derived9872 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9896 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9896 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1918, some c1677, some c4368, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p9896 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9896 : lratChecker f9896 p9896 = .success := by decide +kernel
theorem unsat9896 : Unsatisfiable (PosFin 65) f9896 := by
  apply lratCheckerSound f9896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9896
  · intro a ha; simp [p9896] at ha; subst a; trivial
  · exact checked9896
theorem derived9896 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9896 := by
  apply localUnsat_implies_entails f9896 [c9748, c1918, c1677, c4368] c9896 unsat9896 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1918 := h 1917 (by decide)
  have h2 : Entails.eval a c1677 := h 1676 (by decide)
  have h3 : Entails.eval a c4368 := h 4367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9897 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9897 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9896, some c4564, some c4367, some c1920, some c1930, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p9897 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9897 : lratChecker f9897 p9897 = .success := by decide +kernel
theorem unsat9897 : Unsatisfiable (PosFin 65) f9897 := by
  apply lratCheckerSound f9897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9897
  · intro a ha; simp [p9897] at ha; subst a; trivial
  · exact checked9897
theorem derived9897 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9897 := by
  apply localUnsat_implies_entails f9897 [c9748, c9896, c4564, c4367, c1920, c1930] c9897 unsat9897 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9896 := derived9896 a h
  have h2 : Entails.eval a c4564 := h 4563 (by decide)
  have h3 : Entails.eval a c4367 := h 4366 (by decide)
  have h4 : Entails.eval a c1920 := h 1919 (by decide)
  have h5 : Entails.eval a c1930 := h 1929 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9898 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨34, by decide⟩, true), (⟨22, by decide⟩, true), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9898 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1827, some c391, some c1875, some c384, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9898 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9898 : lratChecker f9898 p9898 = .success := by decide +kernel
theorem unsat9898 : Unsatisfiable (PosFin 65) f9898 := by
  apply lratCheckerSound f9898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9898
  · intro a ha; simp [p9898] at ha; subst a; trivial
  · exact checked9898
theorem derived9898 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9898 := by
  apply localUnsat_implies_entails f9898 [c9748, c1827, c391, c1875, c384] c9898 unsat9898 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1827 := h 1826 (by decide)
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c1875 := h 1874 (by decide)
  have h4 : Entails.eval a c384 := h 383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9899 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9899 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9897, some c4559, some c4557, some c4558, some c4562, some c4563, some c9898, some c2803, some c1970, some c3781, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9899 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9899 : lratChecker f9899 p9899 = .success := by decide +kernel
theorem unsat9899 : Unsatisfiable (PosFin 65) f9899 := by
  apply lratCheckerSound f9899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9899
  · intro a ha; simp [p9899] at ha; subst a; trivial
  · exact checked9899
theorem derived9899 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9899 := by
  apply localUnsat_implies_entails f9899 [c9748, c9897, c4559, c4557, c4558, c4562, c4563, c9898, c2803, c1970, c3781] c9899 unsat9899 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9897 := derived9897 a h
  have h2 : Entails.eval a c4559 := h 4558 (by decide)
  have h3 : Entails.eval a c4557 := h 4556 (by decide)
  have h4 : Entails.eval a c4558 := h 4557 (by decide)
  have h5 : Entails.eval a c4562 := h 4561 (by decide)
  have h6 : Entails.eval a c4563 := h 4562 (by decide)
  have h7 : Entails.eval a c9898 := derived9898 a h
  have h8 : Entails.eval a c2803 := h 2802 (by decide)
  have h9 : Entails.eval a c1970 := h 1969 (by decide)
  have h10 : Entails.eval a c3781 := h 3780 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9900 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9900 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4700, some c2605, some c3846, some c4382, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9900 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9900 : lratChecker f9900 p9900 = .success := by decide +kernel
theorem unsat9900 : Unsatisfiable (PosFin 65) f9900 := by
  apply lratCheckerSound f9900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9900
  · intro a ha; simp [p9900] at ha; subst a; trivial
  · exact checked9900
theorem derived9900 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9900 := by
  apply localUnsat_implies_entails f9900 [c4700, c2605, c3846, c4382] c9900 unsat9900 (by rfl) a
  have h0 : Entails.eval a c4700 := h 4699 (by decide)
  have h1 : Entails.eval a c2605 := h 2604 (by decide)
  have h2 : Entails.eval a c3846 := h 3845 (by decide)
  have h3 : Entails.eval a c4382 := h 4381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9901 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9901 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1918, some c2605, some c3846, some c4382, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9901 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9901 : lratChecker f9901 p9901 = .success := by decide +kernel
theorem unsat9901 : Unsatisfiable (PosFin 65) f9901 := by
  apply lratCheckerSound f9901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9901
  · intro a ha; simp [p9901] at ha; subst a; trivial
  · exact checked9901
theorem derived9901 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9901 := by
  apply localUnsat_implies_entails f9901 [c9748, c1918, c2605, c3846, c4382] c9901 unsat9901 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1918 := h 1917 (by decide)
  have h2 : Entails.eval a c2605 := h 2604 (by decide)
  have h3 : Entails.eval a c3846 := h 3845 (by decide)
  have h4 : Entails.eval a c4382 := h 4381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9902 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9902 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4564, some c1920, some c1921, some c1930, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p9902 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9902 : lratChecker f9902 p9902 = .success := by decide +kernel
theorem unsat9902 : Unsatisfiable (PosFin 65) f9902 := by
  apply lratCheckerSound f9902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9902
  · intro a ha; simp [p9902] at ha; subst a; trivial
  · exact checked9902
theorem derived9902 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9902 := by
  apply localUnsat_implies_entails f9902 [c9748, c4564, c1920, c1921, c1930] c9902 unsat9902 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4564 := h 4563 (by decide)
  have h2 : Entails.eval a c1920 := h 1919 (by decide)
  have h3 : Entails.eval a c1921 := h 1920 (by decide)
  have h4 : Entails.eval a c1930 := h 1929 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9903 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9903 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9899, some c9901, some c9902, some c4559, some c4378, some c1978, some c3779, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9903 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9903 : lratChecker f9903 p9903 = .success := by decide +kernel
theorem unsat9903 : Unsatisfiable (PosFin 65) f9903 := by
  apply lratCheckerSound f9903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9903
  · intro a ha; simp [p9903] at ha; subst a; trivial
  · exact checked9903
theorem derived9903 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9903 := by
  apply localUnsat_implies_entails f9903 [c9748, c9899, c9901, c9902, c4559, c4378, c1978, c3779] c9903 unsat9903 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9899 := derived9899 a h
  have h2 : Entails.eval a c9901 := derived9901 a h
  have h3 : Entails.eval a c9902 := derived9902 a h
  have h4 : Entails.eval a c4559 := h 4558 (by decide)
  have h5 : Entails.eval a c4378 := h 4377 (by decide)
  have h6 : Entails.eval a c1978 := h 1977 (by decide)
  have h7 : Entails.eval a c3779 := h 3778 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9904 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9904 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4700, some c4427, some c911, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9904 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9904 : lratChecker f9904 p9904 = .success := by decide +kernel
theorem unsat9904 : Unsatisfiable (PosFin 65) f9904 := by
  apply lratCheckerSound f9904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9904
  · intro a ha; simp [p9904] at ha; subst a; trivial
  · exact checked9904
theorem derived9904 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9904 := by
  apply localUnsat_implies_entails f9904 [c4700, c4427, c911] c9904 unsat9904 (by rfl) a
  have h0 : Entails.eval a c4700 := h 4699 (by decide)
  have h1 : Entails.eval a c4427 := h 4426 (by decide)
  have h2 : Entails.eval a c911 := h 910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9905 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9905 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9839, some c9904, some c2720, some c2721, some c911, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9905 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9905 : lratChecker f9905 p9905 = .success := by decide +kernel
theorem unsat9905 : Unsatisfiable (PosFin 65) f9905 := by
  apply lratCheckerSound f9905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9905
  · intro a ha; simp [p9905] at ha; subst a; trivial
  · exact checked9905
theorem derived9905 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9905 := by
  apply localUnsat_implies_entails f9905 [c9839, c9904, c2720, c2721, c911] c9905 unsat9905 (by rfl) a
  have h0 : Entails.eval a c9839 := derived9839 a h
  have h1 : Entails.eval a c9904 := derived9904 a h
  have h2 : Entails.eval a c2720 := h 2719 (by decide)
  have h3 : Entails.eval a c2721 := h 2720 (by decide)
  have h4 : Entails.eval a c911 := h 910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9906 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9906 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4697, some c4698, some c4695, some c4703, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9906 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9906 : lratChecker f9906 p9906 = .success := by decide +kernel
theorem unsat9906 : Unsatisfiable (PosFin 65) f9906 := by
  apply lratCheckerSound f9906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9906
  · intro a ha; simp [p9906] at ha; subst a; trivial
  · exact checked9906
theorem derived9906 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9906 := by
  apply localUnsat_implies_entails f9906 [c4697, c4698, c4695, c4703] c9906 unsat9906 (by rfl) a
  have h0 : Entails.eval a c4697 := h 4696 (by decide)
  have h1 : Entails.eval a c4698 := h 4697 (by decide)
  have h2 : Entails.eval a c4695 := h 4694 (by decide)
  have h3 : Entails.eval a c4703 := h 4702 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9907 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9907 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2720, some c2718, some c2721, some c771, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9907 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9907 : lratChecker f9907 p9907 = .success := by decide +kernel
theorem unsat9907 : Unsatisfiable (PosFin 65) f9907 := by
  apply lratCheckerSound f9907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9907
  · intro a ha; simp [p9907] at ha; subst a; trivial
  · exact checked9907
theorem derived9907 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9907 := by
  apply localUnsat_implies_entails f9907 [c2720, c2718, c2721, c771] c9907 unsat9907 (by rfl) a
  have h0 : Entails.eval a c2720 := h 2719 (by decide)
  have h1 : Entails.eval a c2718 := h 2717 (by decide)
  have h2 : Entails.eval a c2721 := h 2720 (by decide)
  have h3 : Entails.eval a c771 := h 770 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9908 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9908 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9906, some c9907, some c9842, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9908 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9908 : lratChecker f9908 p9908 = .success := by decide +kernel
theorem unsat9908 : Unsatisfiable (PosFin 65) f9908 := by
  apply lratCheckerSound f9908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9908
  · intro a ha; simp [p9908] at ha; subst a; trivial
  · exact checked9908
theorem derived9908 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9908 := by
  apply localUnsat_implies_entails f9908 [c9906, c9907, c9842] c9908 unsat9908 (by rfl) a
  have h0 : Entails.eval a c9906 := derived9906 a h
  have h1 : Entails.eval a c9907 := derived9907 a h
  have h2 : Entails.eval a c9842 := derived9842 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9909 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9909 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9908, some c9839, some c9905, some c9900, some c9907, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9909 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9909 : lratChecker f9909 p9909 = .success := by decide +kernel
theorem unsat9909 : Unsatisfiable (PosFin 65) f9909 := by
  apply lratCheckerSound f9909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9909
  · intro a ha; simp [p9909] at ha; subst a; trivial
  · exact checked9909
theorem derived9909 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9909 := by
  apply localUnsat_implies_entails f9909 [c9908, c9839, c9905, c9900, c9907] c9909 unsat9909 (by rfl) a
  have h0 : Entails.eval a c9908 := derived9908 a h
  have h1 : Entails.eval a c9839 := derived9839 a h
  have h2 : Entails.eval a c9905 := derived9905 a h
  have h3 : Entails.eval a c9900 := derived9900 a h
  have h4 : Entails.eval a c9907 := derived9907 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9910 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, true), (⟨9, by decide⟩, false), (⟨57, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9910 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2820, some c3800, some c2337, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9910 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9910 : lratChecker f9910 p9910 = .success := by decide +kernel
theorem unsat9910 : Unsatisfiable (PosFin 65) f9910 := by
  apply lratCheckerSound f9910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9910
  · intro a ha; simp [p9910] at ha; subst a; trivial
  · exact checked9910
theorem derived9910 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9910 := by
  apply localUnsat_implies_entails f9910 [c9748, c2820, c3800, c2337] c9910 unsat9910 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2820 := h 2819 (by decide)
  have h2 : Entails.eval a c3800 := h 3799 (by decide)
  have h3 : Entails.eval a c2337 := h 2336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9911 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9911 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9794, some c1939, some c9903, some c3801, some c2030, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9911 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9911 : lratChecker f9911 p9911 = .success := by decide +kernel
theorem unsat9911 : Unsatisfiable (PosFin 65) f9911 := by
  apply lratCheckerSound f9911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9911
  · intro a ha; simp [p9911] at ha; subst a; trivial
  · exact checked9911
theorem derived9911 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9911 := by
  apply localUnsat_implies_entails f9911 [c9748, c9794, c1939, c9903, c3801, c2030] c9911 unsat9911 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9794 := derived9794 a h
  have h2 : Entails.eval a c1939 := h 1938 (by decide)
  have h3 : Entails.eval a c9903 := derived9903 a h
  have h4 : Entails.eval a c3801 := h 3800 (by decide)
  have h5 : Entails.eval a c2030 := h 2029 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9912 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨59, by decide⟩, true), (⟨2, by decide⟩, false), (⟨9, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9912 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2821, some c2637, some c1908, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p9912 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9912 : lratChecker f9912 p9912 = .success := by decide +kernel
theorem unsat9912 : Unsatisfiable (PosFin 65) f9912 := by
  apply lratCheckerSound f9912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9912
  · intro a ha; simp [p9912] at ha; subst a; trivial
  · exact checked9912
theorem derived9912 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9912 := by
  apply localUnsat_implies_entails f9912 [c9748, c2821, c2637, c1908] c9912 unsat9912 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2821 := h 2820 (by decide)
  have h2 : Entails.eval a c2637 := h 2636 (by decide)
  have h3 : Entails.eval a c1908 := h 1907 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9913 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨60, by decide⟩, true), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9913 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9794, some c9910, some c9911, some c9909, some c9912, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9913 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9913 : lratChecker f9913 p9913 = .success := by decide +kernel
theorem unsat9913 : Unsatisfiable (PosFin 65) f9913 := by
  apply lratCheckerSound f9913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9913
  · intro a ha; simp [p9913] at ha; subst a; trivial
  · exact checked9913
theorem derived9913 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9913 := by
  apply localUnsat_implies_entails f9913 [c9794, c9910, c9911, c9909, c9912] c9913 unsat9913 (by rfl) a
  have h0 : Entails.eval a c9794 := derived9794 a h
  have h1 : Entails.eval a c9910 := derived9910 a h
  have h2 : Entails.eval a c9911 := derived9911 a h
  have h3 : Entails.eval a c9909 := derived9909 a h
  have h4 : Entails.eval a c9912 := derived9912 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9914 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9914 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3786, some c2008, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9914 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9914 : lratChecker f9914 p9914 = .success := by decide +kernel
theorem unsat9914 : Unsatisfiable (PosFin 65) f9914 := by
  apply lratCheckerSound f9914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9914
  · intro a ha; simp [p9914] at ha; subst a; trivial
  · exact checked9914
theorem derived9914 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9914 := by
  apply localUnsat_implies_entails f9914 [c9748, c3786, c2008] c9914 unsat9914 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3786 := h 3785 (by decide)
  have h2 : Entails.eval a c2008 := h 2007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9915 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9915 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9914, some c9912, some c9913, some c2612, some c2809, some c1886, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9915 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9915 : lratChecker f9915 p9915 = .success := by decide +kernel
theorem unsat9915 : Unsatisfiable (PosFin 65) f9915 := by
  apply lratCheckerSound f9915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9915
  · intro a ha; simp [p9915] at ha; subst a; trivial
  · exact checked9915
theorem derived9915 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9915 := by
  apply localUnsat_implies_entails f9915 [c9748, c9914, c9912, c9913, c2612, c2809, c1886] c9915 unsat9915 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9914 := derived9914 a h
  have h2 : Entails.eval a c9912 := derived9912 a h
  have h3 : Entails.eval a c9913 := derived9913 a h
  have h4 : Entails.eval a c2612 := h 2611 (by decide)
  have h5 : Entails.eval a c2809 := h 2808 (by decide)
  have h6 : Entails.eval a c1886 := h 1885 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9916 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9916 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9794, some c9895, some c9914, some c9880, some c9915, some c9855, some c2004, some c4035, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9916 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9916 : lratChecker f9916 p9916 = .success := by decide +kernel
theorem unsat9916 : Unsatisfiable (PosFin 65) f9916 := by
  apply lratCheckerSound f9916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9916
  · intro a ha; simp [p9916] at ha; subst a; trivial
  · exact checked9916
theorem derived9916 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9916 := by
  apply localUnsat_implies_entails f9916 [c9748, c9794, c9895, c9914, c9880, c9915, c9855, c2004, c4035] c9916 unsat9916 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9794 := derived9794 a h
  have h2 : Entails.eval a c9895 := derived9895 a h
  have h3 : Entails.eval a c9914 := derived9914 a h
  have h4 : Entails.eval a c9880 := derived9880 a h
  have h5 : Entails.eval a c9915 := derived9915 a h
  have h6 : Entails.eval a c9855 := derived9855 a h
  have h7 : Entails.eval a c2004 := h 2003 (by decide)
  have h8 : Entails.eval a c4035 := h 4034 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9917 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, true), (⟨5, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9917 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2018, some c4043, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p9917 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9917 : lratChecker f9917 p9917 = .success := by decide +kernel
theorem unsat9917 : Unsatisfiable (PosFin 65) f9917 := by
  apply lratCheckerSound f9917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9917
  · intro a ha; simp [p9917] at ha; subst a; trivial
  · exact checked9917
theorem derived9917 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9917 := by
  apply localUnsat_implies_entails f9917 [c9748, c2018, c4043] c9917 unsat9917 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2018 := h 2017 (by decide)
  have h2 : Entails.eval a c4043 := h 4042 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9918 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9918 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9846, some c9917, some c2612, some c5025, some c4476, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9918 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9918 : lratChecker f9918 p9918 = .success := by decide +kernel
theorem unsat9918 : Unsatisfiable (PosFin 65) f9918 := by
  apply lratCheckerSound f9918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9918
  · intro a ha; simp [p9918] at ha; subst a; trivial
  · exact checked9918
theorem derived9918 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9918 := by
  apply localUnsat_implies_entails f9918 [c9846, c9917, c2612, c5025, c4476] c9918 unsat9918 (by rfl) a
  have h0 : Entails.eval a c9846 := derived9846 a h
  have h1 : Entails.eval a c9917 := derived9917 a h
  have h2 : Entails.eval a c2612 := h 2611 (by decide)
  have h3 : Entails.eval a c5025 := h 5024 (by decide)
  have h4 : Entails.eval a c4476 := h 4475 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9919 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨61, by decide⟩, true), (⟨59, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9919 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9855, some c8001, some c4731, some c4956, some c2009, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9919 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9919 : lratChecker f9919 p9919 = .success := by decide +kernel
theorem unsat9919 : Unsatisfiable (PosFin 65) f9919 := by
  apply lratCheckerSound f9919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9919
  · intro a ha; simp [p9919] at ha; subst a; trivial
  · exact checked9919
theorem derived9919 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9919 := by
  apply localUnsat_implies_entails f9919 [c9748, c9855, c8001, c4731, c4956, c2009] c9919 unsat9919 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9855 := derived9855 a h
  have h2 : Entails.eval a c8001 := derived8001 a h
  have h3 : Entails.eval a c4731 := h 4730 (by decide)
  have h4 : Entails.eval a c4956 := h 4955 (by decide)
  have h5 : Entails.eval a c2009 := h 2008 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9920 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9920 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9914, some c9919, some c9794, some c9895, some c9916, some c9918, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9920 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9920 : lratChecker f9920 p9920 = .success := by decide +kernel
theorem unsat9920 : Unsatisfiable (PosFin 65) f9920 := by
  apply lratCheckerSound f9920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9920
  · intro a ha; simp [p9920] at ha; subst a; trivial
  · exact checked9920
theorem derived9920 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9920 := by
  apply localUnsat_implies_entails f9920 [c9914, c9919, c9794, c9895, c9916, c9918] c9920 unsat9920 (by rfl) a
  have h0 : Entails.eval a c9914 := derived9914 a h
  have h1 : Entails.eval a c9919 := derived9919 a h
  have h2 : Entails.eval a c9794 := derived9794 a h
  have h3 : Entails.eval a c9895 := derived9895 a h
  have h4 : Entails.eval a c9916 := derived9916 a h
  have h5 : Entails.eval a c9918 := derived9918 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9921 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨61, by decide⟩, true), (⟨59, by decide⟩, true), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9921 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9919, some c9866, some c4611, some c9858, some c4644, some c9906, some c9809, some c4581, some c4584, some c9861, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9921 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9921 : lratChecker f9921 p9921 = .success := by decide +kernel
theorem unsat9921 : Unsatisfiable (PosFin 65) f9921 := by
  apply lratCheckerSound f9921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9921
  · intro a ha; simp [p9921] at ha; subst a; trivial
  · exact checked9921
theorem derived9921 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9921 := by
  apply localUnsat_implies_entails f9921 [c9919, c9866, c4611, c9858, c4644, c9906, c9809, c4581, c4584, c9861] c9921 unsat9921 (by rfl) a
  have h0 : Entails.eval a c9919 := derived9919 a h
  have h1 : Entails.eval a c9866 := derived9866 a h
  have h2 : Entails.eval a c4611 := h 4610 (by decide)
  have h3 : Entails.eval a c9858 := derived9858 a h
  have h4 : Entails.eval a c4644 := h 4643 (by decide)
  have h5 : Entails.eval a c9906 := derived9906 a h
  have h6 : Entails.eval a c9809 := derived9809 a h
  have h7 : Entails.eval a c4581 := h 4580 (by decide)
  have h8 : Entails.eval a c4584 := h 4583 (by decide)
  have h9 : Entails.eval a c9861 := derived9861 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9922 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9922 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4559, some c9841, some c4530, some c4563, some c825, some c830, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9922 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9922 : lratChecker f9922 p9922 = .success := by decide +kernel
theorem unsat9922 : Unsatisfiable (PosFin 65) f9922 := by
  apply lratCheckerSound f9922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9922
  · intro a ha; simp [p9922] at ha; subst a; trivial
  · exact checked9922
theorem derived9922 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9922 := by
  apply localUnsat_implies_entails f9922 [c4559, c9841, c4530, c4563, c825, c830] c9922 unsat9922 (by rfl) a
  have h0 : Entails.eval a c4559 := h 4558 (by decide)
  have h1 : Entails.eval a c9841 := derived9841 a h
  have h2 : Entails.eval a c4530 := h 4529 (by decide)
  have h3 : Entails.eval a c4563 := h 4562 (by decide)
  have h4 : Entails.eval a c825 := h 824 (by decide)
  have h5 : Entails.eval a c830 := h 829 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9923 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9923 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9922, some c9902, some c9838, some c1918, some c4531, some c4537, some c4560, some c4561, some c4542, some c8977, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9923 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9923 : lratChecker f9923 p9923 = .success := by decide +kernel
theorem unsat9923 : Unsatisfiable (PosFin 65) f9923 := by
  apply lratCheckerSound f9923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9923
  · intro a ha; simp [p9923] at ha; subst a; trivial
  · exact checked9923
theorem derived9923 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9923 := by
  apply localUnsat_implies_entails f9923 [c9748, c9922, c9902, c9838, c1918, c4531, c4537, c4560, c4561, c4542, c8977] c9923 unsat9923 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9922 := derived9922 a h
  have h2 : Entails.eval a c9902 := derived9902 a h
  have h3 : Entails.eval a c9838 := derived9838 a h
  have h4 : Entails.eval a c1918 := h 1917 (by decide)
  have h5 : Entails.eval a c4531 := h 4530 (by decide)
  have h6 : Entails.eval a c4537 := h 4536 (by decide)
  have h7 : Entails.eval a c4560 := h 4559 (by decide)
  have h8 : Entails.eval a c4561 := h 4560 (by decide)
  have h9 : Entails.eval a c4542 := h 4541 (by decide)
  have h10 : Entails.eval a c8977 := derived8977 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9924 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9924 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9908, some c9905, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9924 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9924 : lratChecker f9924 p9924 = .success := by decide +kernel
theorem unsat9924 : Unsatisfiable (PosFin 65) f9924 := by
  apply lratCheckerSound f9924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9924
  · intro a ha; simp [p9924] at ha; subst a; trivial
  · exact checked9924
theorem derived9924 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9924 := by
  apply localUnsat_implies_entails f9924 [c9908, c9905] c9924 unsat9924 (by rfl) a
  have h0 : Entails.eval a c9908 := derived9908 a h
  have h1 : Entails.eval a c9905 := derived9905 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9925 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9925 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9924, some c3693, some c1906, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9925 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9925 : lratChecker f9925 p9925 = .success := by decide +kernel
theorem unsat9925 : Unsatisfiable (PosFin 65) f9925 := by
  apply lratCheckerSound f9925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9925
  · intro a ha; simp [p9925] at ha; subst a; trivial
  · exact checked9925
theorem derived9925 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9925 := by
  apply localUnsat_implies_entails f9925 [c9748, c9924, c3693, c1906] c9925 unsat9925 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9924 := derived9924 a h
  have h2 : Entails.eval a c3693 := h 3692 (by decide)
  have h3 : Entails.eval a c1906 := h 1905 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9926 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨6, by decide⟩, false), (⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9926 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9923, some c9908, some c9839, some c9907, some c4700, some c4696, some c4588, some c911, some c772, some c965, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9926 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9926 : lratChecker f9926 p9926 = .success := by decide +kernel
theorem unsat9926 : Unsatisfiable (PosFin 65) f9926 := by
  apply lratCheckerSound f9926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9926
  · intro a ha; simp [p9926] at ha; subst a; trivial
  · exact checked9926
theorem derived9926 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9926 := by
  apply localUnsat_implies_entails f9926 [c9923, c9908, c9839, c9907, c4700, c4696, c4588, c911, c772, c965] c9926 unsat9926 (by rfl) a
  have h0 : Entails.eval a c9923 := derived9923 a h
  have h1 : Entails.eval a c9908 := derived9908 a h
  have h2 : Entails.eval a c9839 := derived9839 a h
  have h3 : Entails.eval a c9907 := derived9907 a h
  have h4 : Entails.eval a c4700 := h 4699 (by decide)
  have h5 : Entails.eval a c4696 := h 4695 (by decide)
  have h6 : Entails.eval a c4588 := h 4587 (by decide)
  have h7 : Entails.eval a c911 := h 910 (by decide)
  have h8 : Entails.eval a c772 := h 771 (by decide)
  have h9 : Entails.eval a c965 := h 964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9927 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9927 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9923, some c9925, some c9926, some c4098, some c2375, some c2651, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9927 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9927 : lratChecker f9927 p9927 = .success := by decide +kernel
theorem unsat9927 : Unsatisfiable (PosFin 65) f9927 := by
  apply lratCheckerSound f9927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9927
  · intro a ha; simp [p9927] at ha; subst a; trivial
  · exact checked9927
theorem derived9927 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9927 := by
  apply localUnsat_implies_entails f9927 [c9748, c9923, c9925, c9926, c4098, c2375, c2651] c9927 unsat9927 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9923 := derived9923 a h
  have h2 : Entails.eval a c9925 := derived9925 a h
  have h3 : Entails.eval a c9926 := derived9926 a h
  have h4 : Entails.eval a c4098 := h 4097 (by decide)
  have h5 : Entails.eval a c2375 := h 2374 (by decide)
  have h6 : Entails.eval a c2651 := h 2650 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9928 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨59, by decide⟩, true), (⟨7, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9928 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4611, some c4644, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9928 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9928 : lratChecker f9928 p9928 = .success := by decide +kernel
theorem unsat9928 : Unsatisfiable (PosFin 65) f9928 := by
  apply lratCheckerSound f9928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9928
  · intro a ha; simp [p9928] at ha; subst a; trivial
  · exact checked9928
theorem derived9928 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9928 := by
  apply localUnsat_implies_entails f9928 [c4611, c4644] c9928 unsat9928 (by rfl) a
  have h0 : Entails.eval a c4611 := h 4610 (by decide)
  have h1 : Entails.eval a c4644 := h 4643 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9929 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9929 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9920, some c9914, some c9919, some c9794, some c9921, some c9923, some c9927, some c9928, some c2731, some c2759, some c2741, some c5089, some c2031, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9929 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9929 : lratChecker f9929 p9929 = .success := by decide +kernel
theorem unsat9929 : Unsatisfiable (PosFin 65) f9929 := by
  apply lratCheckerSound f9929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9929
  · intro a ha; simp [p9929] at ha; subst a; trivial
  · exact checked9929
theorem derived9929 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9929 := by
  apply localUnsat_implies_entails f9929 [c9748, c9920, c9914, c9919, c9794, c9921, c9923, c9927, c9928, c2731, c2759, c2741, c5089, c2031] c9929 unsat9929 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9920 := derived9920 a h
  have h2 : Entails.eval a c9914 := derived9914 a h
  have h3 : Entails.eval a c9919 := derived9919 a h
  have h4 : Entails.eval a c9794 := derived9794 a h
  have h5 : Entails.eval a c9921 := derived9921 a h
  have h6 : Entails.eval a c9923 := derived9923 a h
  have h7 : Entails.eval a c9927 := derived9927 a h
  have h8 : Entails.eval a c9928 := derived9928 a h
  have h9 : Entails.eval a c2731 := h 2730 (by decide)
  have h10 : Entails.eval a c2759 := h 2758 (by decide)
  have h11 : Entails.eval a c2741 := h 2740 (by decide)
  have h12 : Entails.eval a c5089 := h 5088 (by decide)
  have h13 : Entails.eval a c2031 := h 2030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9930 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9930 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9914, some c9794, some c9919, some c9920, some c9929, some c9844, some c9846, some c2759, some c2741, some c2746, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9930 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9930 : lratChecker f9930 p9930 = .success := by decide +kernel
theorem unsat9930 : Unsatisfiable (PosFin 65) f9930 := by
  apply lratCheckerSound f9930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9930
  · intro a ha; simp [p9930] at ha; subst a; trivial
  · exact checked9930
theorem derived9930 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9930 := by
  apply localUnsat_implies_entails f9930 [c9914, c9794, c9919, c9920, c9929, c9844, c9846, c2759, c2741, c2746] c9930 unsat9930 (by rfl) a
  have h0 : Entails.eval a c9914 := derived9914 a h
  have h1 : Entails.eval a c9794 := derived9794 a h
  have h2 : Entails.eval a c9919 := derived9919 a h
  have h3 : Entails.eval a c9920 := derived9920 a h
  have h4 : Entails.eval a c9929 := derived9929 a h
  have h5 : Entails.eval a c9844 := derived9844 a h
  have h6 : Entails.eval a c9846 := derived9846 a h
  have h7 : Entails.eval a c2759 := h 2758 (by decide)
  have h8 : Entails.eval a c2741 := h 2740 (by decide)
  have h9 : Entails.eval a c2746 := h 2745 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9931 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9931 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4737, some c1954, some c2752, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9931 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9931 : lratChecker f9931 p9931 = .success := by decide +kernel
theorem unsat9931 : Unsatisfiable (PosFin 65) f9931 := by
  apply lratCheckerSound f9931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9931
  · intro a ha; simp [p9931] at ha; subst a; trivial
  · exact checked9931
theorem derived9931 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9931 := by
  apply localUnsat_implies_entails f9931 [c9748, c4737, c1954, c2752] c9931 unsat9931 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4737 := h 4736 (by decide)
  have h2 : Entails.eval a c1954 := h 1953 (by decide)
  have h3 : Entails.eval a c2752 := h 2751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9932 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9932 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9794, some c9931, some c9930, some c4732, some c9771, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9932 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9932 : lratChecker f9932 p9932 = .success := by decide +kernel
theorem unsat9932 : Unsatisfiable (PosFin 65) f9932 := by
  apply lratCheckerSound f9932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9932
  · intro a ha; simp [p9932] at ha; subst a; trivial
  · exact checked9932
theorem derived9932 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9932 := by
  apply localUnsat_implies_entails f9932 [c9794, c9931, c9930, c4732, c9771] c9932 unsat9932 (by rfl) a
  have h0 : Entails.eval a c9794 := derived9794 a h
  have h1 : Entails.eval a c9931 := derived9931 a h
  have h2 : Entails.eval a c9930 := derived9930 a h
  have h3 : Entails.eval a c4732 := h 4731 (by decide)
  have h4 : Entails.eval a c9771 := derived9771 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9933 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9933 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4738, some c1957, some c2754, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9933 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9933 : lratChecker f9933 p9933 = .success := by decide +kernel
theorem unsat9933 : Unsatisfiable (PosFin 65) f9933 := by
  apply lratCheckerSound f9933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9933
  · intro a ha; simp [p9933] at ha; subst a; trivial
  · exact checked9933
theorem derived9933 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9933 := by
  apply localUnsat_implies_entails f9933 [c9748, c4738, c1957, c2754] c9933 unsat9933 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4738 := h 4737 (by decide)
  have h2 : Entails.eval a c1957 := h 1956 (by decide)
  have h3 : Entails.eval a c2754 := h 2753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9934 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9934 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9887, some c9894, some c9932, some c9933, some c9761, some c9880, some c9878, some c9918, some c4571, some c1999, some c9213, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9934 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9934 : lratChecker f9934 p9934 = .success := by decide +kernel
theorem unsat9934 : Unsatisfiable (PosFin 65) f9934 := by
  apply lratCheckerSound f9934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9934
  · intro a ha; simp [p9934] at ha; subst a; trivial
  · exact checked9934
theorem derived9934 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9934 := by
  apply localUnsat_implies_entails f9934 [c9748, c9887, c9894, c9932, c9933, c9761, c9880, c9878, c9918, c4571, c1999, c9213] c9934 unsat9934 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9887 := derived9887 a h
  have h2 : Entails.eval a c9894 := derived9894 a h
  have h3 : Entails.eval a c9932 := derived9932 a h
  have h4 : Entails.eval a c9933 := derived9933 a h
  have h5 : Entails.eval a c9761 := derived9761 a h
  have h6 : Entails.eval a c9880 := derived9880 a h
  have h7 : Entails.eval a c9878 := derived9878 a h
  have h8 : Entails.eval a c9918 := derived9918 a h
  have h9 : Entails.eval a c4571 := h 4570 (by decide)
  have h10 : Entails.eval a c1999 := h 1998 (by decide)
  have h11 : Entails.eval a c9213 := derived9213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9935 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨9, by decide⟩, true), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9935 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9774, some c9846, some c2759, some c2741, some c2746, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9935 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9935 : lratChecker f9935 p9935 = .success := by decide +kernel
theorem unsat9935 : Unsatisfiable (PosFin 65) f9935 := by
  apply lratCheckerSound f9935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9935
  · intro a ha; simp [p9935] at ha; subst a; trivial
  · exact checked9935
theorem derived9935 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9935 := by
  apply localUnsat_implies_entails f9935 [c9774, c9846, c2759, c2741, c2746] c9935 unsat9935 (by rfl) a
  have h0 : Entails.eval a c9774 := derived9774 a h
  have h1 : Entails.eval a c9846 := derived9846 a h
  have h2 : Entails.eval a c2759 := h 2758 (by decide)
  have h3 : Entails.eval a c2741 := h 2740 (by decide)
  have h4 : Entails.eval a c2746 := h 2745 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9936 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9936 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9887, some c9894, some c9932, some c9933, some c9761, some c9934, some c9785, some c9793, some c9935, some c4571, some c1999, some c9213, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9936 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9936 : lratChecker f9936 p9936 = .success := by decide +kernel
theorem unsat9936 : Unsatisfiable (PosFin 65) f9936 := by
  apply lratCheckerSound f9936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9936
  · intro a ha; simp [p9936] at ha; subst a; trivial
  · exact checked9936
theorem derived9936 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9936 := by
  apply localUnsat_implies_entails f9936 [c9748, c9887, c9894, c9932, c9933, c9761, c9934, c9785, c9793, c9935, c4571, c1999, c9213] c9936 unsat9936 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9887 := derived9887 a h
  have h2 : Entails.eval a c9894 := derived9894 a h
  have h3 : Entails.eval a c9932 := derived9932 a h
  have h4 : Entails.eval a c9933 := derived9933 a h
  have h5 : Entails.eval a c9761 := derived9761 a h
  have h6 : Entails.eval a c9934 := derived9934 a h
  have h7 : Entails.eval a c9785 := derived9785 a h
  have h8 : Entails.eval a c9793 := derived9793 a h
  have h9 : Entails.eval a c9935 := derived9935 a h
  have h10 : Entails.eval a c4571 := h 4570 (by decide)
  have h11 : Entails.eval a c1999 := h 1998 (by decide)
  have h12 : Entails.eval a c9213 := derived9213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9937 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨58, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9937 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4739, some c4576, some c2756, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9937 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9937 : lratChecker f9937 p9937 = .success := by decide +kernel
theorem unsat9937 : Unsatisfiable (PosFin 65) f9937 := by
  apply lratCheckerSound f9937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9937
  · intro a ha; simp [p9937] at ha; subst a; trivial
  · exact checked9937
theorem derived9937 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9937 := by
  apply localUnsat_implies_entails f9937 [c4739, c4576, c2756] c9937 unsat9937 (by rfl) a
  have h0 : Entails.eval a c4739 := h 4738 (by decide)
  have h1 : Entails.eval a c4576 := h 4575 (by decide)
  have h2 : Entails.eval a c2756 := h 2755 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9938 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9938 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9887, some c9894, some c9932, some c9933, some c9761, some c9937, some c9936, some c4732, some c9771, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9938 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9938 : lratChecker f9938 p9938 = .success := by decide +kernel
theorem unsat9938 : Unsatisfiable (PosFin 65) f9938 := by
  apply lratCheckerSound f9938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9938
  · intro a ha; simp [p9938] at ha; subst a; trivial
  · exact checked9938
theorem derived9938 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9938 := by
  apply localUnsat_implies_entails f9938 [c9887, c9894, c9932, c9933, c9761, c9937, c9936, c4732, c9771] c9938 unsat9938 (by rfl) a
  have h0 : Entails.eval a c9887 := derived9887 a h
  have h1 : Entails.eval a c9894 := derived9894 a h
  have h2 : Entails.eval a c9932 := derived9932 a h
  have h3 : Entails.eval a c9933 := derived9933 a h
  have h4 : Entails.eval a c9761 := derived9761 a h
  have h5 : Entails.eval a c9937 := derived9937 a h
  have h6 : Entails.eval a c9936 := derived9936 a h
  have h7 : Entails.eval a c4732 := h 4731 (by decide)
  have h8 : Entails.eval a c9771 := derived9771 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9939 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9939 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3554, some c1677, some c1686, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9939 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9939 : lratChecker f9939 p9939 = .success := by decide +kernel
theorem unsat9939 : Unsatisfiable (PosFin 65) f9939 := by
  apply lratCheckerSound f9939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9939
  · intro a ha; simp [p9939] at ha; subst a; trivial
  · exact checked9939
theorem derived9939 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9939 := by
  apply localUnsat_implies_entails f9939 [c9748, c3554, c1677, c1686] c9939 unsat9939 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3554 := h 3553 (by decide)
  have h2 : Entails.eval a c1677 := h 1676 (by decide)
  have h3 : Entails.eval a c1686 := h 1685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9940 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨18, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9940 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9939, some c3560, some c882, some c1682, some c3106, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9940 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9940 : lratChecker f9940 p9940 = .success := by decide +kernel
theorem unsat9940 : Unsatisfiable (PosFin 65) f9940 := by
  apply lratCheckerSound f9940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9940
  · intro a ha; simp [p9940] at ha; subst a; trivial
  · exact checked9940
theorem derived9940 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9940 := by
  apply localUnsat_implies_entails f9940 [c9748, c9939, c3560, c882, c1682, c3106] c9940 unsat9940 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9939 := derived9939 a h
  have h2 : Entails.eval a c3560 := h 3559 (by decide)
  have h3 : Entails.eval a c882 := h 881 (by decide)
  have h4 : Entails.eval a c1682 := h 1681 (by decide)
  have h5 : Entails.eval a c3106 := h 3105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9941 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9941 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3554, some c3551, some c4379, some c4382, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9941 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9941 : lratChecker f9941 p9941 = .success := by decide +kernel
theorem unsat9941 : Unsatisfiable (PosFin 65) f9941 := by
  apply lratCheckerSound f9941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9941
  · intro a ha; simp [p9941] at ha; subst a; trivial
  · exact checked9941
theorem derived9941 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9941 := by
  apply localUnsat_implies_entails f9941 [c3554, c3551, c4379, c4382] c9941 unsat9941 (by rfl) a
  have h0 : Entails.eval a c3554 := h 3553 (by decide)
  have h1 : Entails.eval a c3551 := h 3550 (by decide)
  have h2 : Entails.eval a c4379 := h 4378 (by decide)
  have h3 : Entails.eval a c4382 := h 4381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9942 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9942 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3579, some c3590, some c8003, some c3592, some c3587, some c3598, some c9828, some c9827, some c9940, some c9941, some c3560, some c882, some c4384, some c1010, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9942 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9942 : lratChecker f9942 p9942 = .success := by decide +kernel
theorem unsat9942 : Unsatisfiable (PosFin 65) f9942 := by
  apply lratCheckerSound f9942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9942
  · intro a ha; simp [p9942] at ha; subst a; trivial
  · exact checked9942
theorem derived9942 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9942 := by
  apply localUnsat_implies_entails f9942 [c9748, c3579, c3590, c8003, c3592, c3587, c3598, c9828, c9827, c9940, c9941, c3560, c882, c4384, c1010] c9942 unsat9942 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3579 := h 3578 (by decide)
  have h2 : Entails.eval a c3590 := h 3589 (by decide)
  have h3 : Entails.eval a c8003 := derived8003 a h
  have h4 : Entails.eval a c3592 := h 3591 (by decide)
  have h5 : Entails.eval a c3587 := h 3586 (by decide)
  have h6 : Entails.eval a c3598 := h 3597 (by decide)
  have h7 : Entails.eval a c9828 := derived9828 a h
  have h8 : Entails.eval a c9827 := derived9827 a h
  have h9 : Entails.eval a c9940 := derived9940 a h
  have h10 : Entails.eval a c9941 := derived9941 a h
  have h11 : Entails.eval a c3560 := h 3559 (by decide)
  have h12 : Entails.eval a c882 := h 881 (by decide)
  have h13 : Entails.eval a c4384 := h 4383 (by decide)
  have h14 : Entails.eval a c1010 := h 1009 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9943 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9943 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3579, some c3580, some c3592, some c9942, some c4398, some c1750, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9943 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9943 : lratChecker f9943 p9943 = .success := by decide +kernel
theorem unsat9943 : Unsatisfiable (PosFin 65) f9943 := by
  apply lratCheckerSound f9943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9943
  · intro a ha; simp [p9943] at ha; subst a; trivial
  · exact checked9943
theorem derived9943 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9943 := by
  apply localUnsat_implies_entails f9943 [c9748, c3579, c3580, c3592, c9942, c4398, c1750] c9943 unsat9943 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3579 := h 3578 (by decide)
  have h2 : Entails.eval a c3580 := h 3579 (by decide)
  have h3 : Entails.eval a c3592 := h 3591 (by decide)
  have h4 : Entails.eval a c9942 := derived9942 a h
  have h5 : Entails.eval a c4398 := h 4397 (by decide)
  have h6 : Entails.eval a c1750 := h 1749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9944 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9944 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3579, some c3590, some c8003, some c3592, some c3587, some c3598, some c9828, some c9943, some c9851, some c3560, some c909, some c932, some c939, some c3565, some c3561, some c940, some c930, some c3548, some c905, some c3545, some c3572, some c3573, some c3570, some c3571, some c942, some c120, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9944 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked9944 : lratChecker f9944 p9944 = .success := by decide +kernel
theorem unsat9944 : Unsatisfiable (PosFin 65) f9944 := by
  apply lratCheckerSound f9944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9944
  · intro a ha; simp [p9944] at ha; subst a; trivial
  · exact checked9944
theorem derived9944 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9944 := by
  apply localUnsat_implies_entails f9944 [c9748, c3579, c3590, c8003, c3592, c3587, c3598, c9828, c9943, c9851, c3560, c909, c932, c939, c3565, c3561, c940, c930, c3548, c905, c3545, c3572, c3573, c3570, c3571, c942, c120] c9944 unsat9944 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3579 := h 3578 (by decide)
  have h2 : Entails.eval a c3590 := h 3589 (by decide)
  have h3 : Entails.eval a c8003 := derived8003 a h
  have h4 : Entails.eval a c3592 := h 3591 (by decide)
  have h5 : Entails.eval a c3587 := h 3586 (by decide)
  have h6 : Entails.eval a c3598 := h 3597 (by decide)
  have h7 : Entails.eval a c9828 := derived9828 a h
  have h8 : Entails.eval a c9943 := derived9943 a h
  have h9 : Entails.eval a c9851 := derived9851 a h
  have h10 : Entails.eval a c3560 := h 3559 (by decide)
  have h11 : Entails.eval a c909 := h 908 (by decide)
  have h12 : Entails.eval a c932 := h 931 (by decide)
  have h13 : Entails.eval a c939 := h 938 (by decide)
  have h14 : Entails.eval a c3565 := h 3564 (by decide)
  have h15 : Entails.eval a c3561 := h 3560 (by decide)
  have h16 : Entails.eval a c940 := h 939 (by decide)
  have h17 : Entails.eval a c930 := h 929 (by decide)
  have h18 : Entails.eval a c3548 := h 3547 (by decide)
  have h19 : Entails.eval a c905 := h 904 (by decide)
  have h20 : Entails.eval a c3545 := h 3544 (by decide)
  have h21 : Entails.eval a c3572 := h 3571 (by decide)
  have h22 : Entails.eval a c3573 := h 3572 (by decide)
  have h23 : Entails.eval a c3570 := h 3569 (by decide)
  have h24 : Entails.eval a c3571 := h 3570 (by decide)
  have h25 : Entails.eval a c942 := h 941 (by decide)
  have h26 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9945 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨63, by decide⟩, true), (⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9945 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4307, some c4684, some c1803, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9945 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9945 : lratChecker f9945 p9945 = .success := by decide +kernel
theorem unsat9945 : Unsatisfiable (PosFin 65) f9945 := by
  apply lratCheckerSound f9945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9945
  · intro a ha; simp [p9945] at ha; subst a; trivial
  · exact checked9945
theorem derived9945 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9945 := by
  apply localUnsat_implies_entails f9945 [c9748, c4307, c4684, c1803] c9945 unsat9945 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4307 := h 4306 (by decide)
  have h2 : Entails.eval a c4684 := h 4683 (by decide)
  have h3 : Entails.eval a c1803 := h 1802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9946 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨15, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, false), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9946 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3580, some c3554, some c3551, some c285, some c3556, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9946 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9946 : lratChecker f9946 p9946 = .success := by decide +kernel
theorem unsat9946 : Unsatisfiable (PosFin 65) f9946 := by
  apply lratCheckerSound f9946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9946
  · intro a ha; simp [p9946] at ha; subst a; trivial
  · exact checked9946
theorem derived9946 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9946 := by
  apply localUnsat_implies_entails f9946 [c3580, c3554, c3551, c285, c3556] c9946 unsat9946 (by rfl) a
  have h0 : Entails.eval a c3580 := h 3579 (by decide)
  have h1 : Entails.eval a c3554 := h 3553 (by decide)
  have h2 : Entails.eval a c3551 := h 3550 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c3556 := h 3555 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9947 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9947 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3592, some c3580, some c3579, some c3590, some c8003, some c3587, some c9945, some c9944, some c3598, some c9828, some c3593, some c9849, some c9827, some c2068, some c9946, some c3560, some c5548, some c5530, some c5962, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9947 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9947 : lratChecker f9947 p9947 = .success := by decide +kernel
theorem unsat9947 : Unsatisfiable (PosFin 65) f9947 := by
  apply lratCheckerSound f9947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9947
  · intro a ha; simp [p9947] at ha; subst a; trivial
  · exact checked9947
theorem derived9947 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9947 := by
  apply localUnsat_implies_entails f9947 [c9748, c3592, c3580, c3579, c3590, c8003, c3587, c9945, c9944, c3598, c9828, c3593, c9849, c9827, c2068, c9946, c3560, c5548, c5530, c5962] c9947 unsat9947 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3592 := h 3591 (by decide)
  have h2 : Entails.eval a c3580 := h 3579 (by decide)
  have h3 : Entails.eval a c3579 := h 3578 (by decide)
  have h4 : Entails.eval a c3590 := h 3589 (by decide)
  have h5 : Entails.eval a c8003 := derived8003 a h
  have h6 : Entails.eval a c3587 := h 3586 (by decide)
  have h7 : Entails.eval a c9945 := derived9945 a h
  have h8 : Entails.eval a c9944 := derived9944 a h
  have h9 : Entails.eval a c3598 := h 3597 (by decide)
  have h10 : Entails.eval a c9828 := derived9828 a h
  have h11 : Entails.eval a c3593 := h 3592 (by decide)
  have h12 : Entails.eval a c9849 := derived9849 a h
  have h13 : Entails.eval a c9827 := derived9827 a h
  have h14 : Entails.eval a c2068 := h 2067 (by decide)
  have h15 : Entails.eval a c9946 := derived9946 a h
  have h16 : Entails.eval a c3560 := h 3559 (by decide)
  have h17 : Entails.eval a c5548 := h 5547 (by decide)
  have h18 : Entails.eval a c5530 := h 5529 (by decide)
  have h19 : Entails.eval a c5962 := h 5961 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9948 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9948 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3593, some c3592, some c3591, some c3580, some c3579, some c3590, some c8003, some c3587, some c3598, some c9828, some c9945, some c9947, some c9851, some c3560, some c909, some c932, some c939, some c3565, some c3561, some c940, some c930, some c3548, some c905, some c3545, some c3572, some c3573, some c3570, some c3571, some c942, some c120, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9948 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked9948 : lratChecker f9948 p9948 = .success := by decide +kernel
theorem unsat9948 : Unsatisfiable (PosFin 65) f9948 := by
  apply lratCheckerSound f9948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9948
  · intro a ha; simp [p9948] at ha; subst a; trivial
  · exact checked9948
theorem derived9948 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9948 := by
  apply localUnsat_implies_entails f9948 [c9748, c3593, c3592, c3591, c3580, c3579, c3590, c8003, c3587, c3598, c9828, c9945, c9947, c9851, c3560, c909, c932, c939, c3565, c3561, c940, c930, c3548, c905, c3545, c3572, c3573, c3570, c3571, c942, c120] c9948 unsat9948 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3593 := h 3592 (by decide)
  have h2 : Entails.eval a c3592 := h 3591 (by decide)
  have h3 : Entails.eval a c3591 := h 3590 (by decide)
  have h4 : Entails.eval a c3580 := h 3579 (by decide)
  have h5 : Entails.eval a c3579 := h 3578 (by decide)
  have h6 : Entails.eval a c3590 := h 3589 (by decide)
  have h7 : Entails.eval a c8003 := derived8003 a h
  have h8 : Entails.eval a c3587 := h 3586 (by decide)
  have h9 : Entails.eval a c3598 := h 3597 (by decide)
  have h10 : Entails.eval a c9828 := derived9828 a h
  have h11 : Entails.eval a c9945 := derived9945 a h
  have h12 : Entails.eval a c9947 := derived9947 a h
  have h13 : Entails.eval a c9851 := derived9851 a h
  have h14 : Entails.eval a c3560 := h 3559 (by decide)
  have h15 : Entails.eval a c909 := h 908 (by decide)
  have h16 : Entails.eval a c932 := h 931 (by decide)
  have h17 : Entails.eval a c939 := h 938 (by decide)
  have h18 : Entails.eval a c3565 := h 3564 (by decide)
  have h19 : Entails.eval a c3561 := h 3560 (by decide)
  have h20 : Entails.eval a c940 := h 939 (by decide)
  have h21 : Entails.eval a c930 := h 929 (by decide)
  have h22 : Entails.eval a c3548 := h 3547 (by decide)
  have h23 : Entails.eval a c905 := h 904 (by decide)
  have h24 : Entails.eval a c3545 := h 3544 (by decide)
  have h25 : Entails.eval a c3572 := h 3571 (by decide)
  have h26 : Entails.eval a c3573 := h 3572 (by decide)
  have h27 : Entails.eval a c3570 := h 3569 (by decide)
  have h28 : Entails.eval a c3571 := h 3570 (by decide)
  have h29 : Entails.eval a c942 := h 941 (by decide)
  have h30 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9949 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9949 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9948, some c3595, some c9759, some c3578, some c3591, some c3597, some c3599, some c9764, some c3584, some c8001, some c9892, some c9891, some c9893, some c1911, some c2339, some c3945, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9949 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9949 : lratChecker f9949 p9949 = .success := by decide +kernel
theorem unsat9949 : Unsatisfiable (PosFin 65) f9949 := by
  apply lratCheckerSound f9949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9949
  · intro a ha; simp [p9949] at ha; subst a; trivial
  · exact checked9949
theorem derived9949 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9949 := by
  apply localUnsat_implies_entails f9949 [c9748, c9948, c3595, c9759, c3578, c3591, c3597, c3599, c9764, c3584, c8001, c9892, c9891, c9893, c1911, c2339, c3945] c9949 unsat9949 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9948 := derived9948 a h
  have h2 : Entails.eval a c3595 := h 3594 (by decide)
  have h3 : Entails.eval a c9759 := derived9759 a h
  have h4 : Entails.eval a c3578 := h 3577 (by decide)
  have h5 : Entails.eval a c3591 := h 3590 (by decide)
  have h6 : Entails.eval a c3597 := h 3596 (by decide)
  have h7 : Entails.eval a c3599 := h 3598 (by decide)
  have h8 : Entails.eval a c9764 := derived9764 a h
  have h9 : Entails.eval a c3584 := h 3583 (by decide)
  have h10 : Entails.eval a c8001 := derived8001 a h
  have h11 : Entails.eval a c9892 := derived9892 a h
  have h12 : Entails.eval a c9891 := derived9891 a h
  have h13 : Entails.eval a c9893 := derived9893 a h
  have h14 : Entails.eval a c1911 := h 1910 (by decide)
  have h15 : Entails.eval a c2339 := h 2338 (by decide)
  have h16 : Entails.eval a c3945 := h 3944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9950 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9950 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2566, some c1471, some c2562, some c2561, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9950 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9950 : lratChecker f9950 p9950 = .success := by decide +kernel
theorem unsat9950 : Unsatisfiable (PosFin 65) f9950 := by
  apply lratCheckerSound f9950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9950
  · intro a ha; simp [p9950] at ha; subst a; trivial
  · exact checked9950
theorem derived9950 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9950 := by
  apply localUnsat_implies_entails f9950 [c9748, c2566, c1471, c2562, c2561] c9950 unsat9950 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2566 := h 2565 (by decide)
  have h2 : Entails.eval a c1471 := h 1470 (by decide)
  have h3 : Entails.eval a c2562 := h 2561 (by decide)
  have h4 : Entails.eval a c2561 := h 2560 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9950

end CochromaticTwenty.Certificates.FixedCore0
