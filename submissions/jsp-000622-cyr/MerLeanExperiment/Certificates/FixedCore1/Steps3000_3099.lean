import MerLeanExperiment.Certificates.FixedCore1.Steps2900_2999

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8881 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8881 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1902, some c1913, some c1921, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8881 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8881 : lratChecker f8881 p8881 = .success := by decide +kernel
theorem unsat8881 : Unsatisfiable (PosFin 65) f8881 := by
  apply lratCheckerSound f8881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8881
  · intro a ha; simp [p8881] at ha; subst a; trivial
  · exact checked8881
theorem derived8881 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8881 := by
  apply localUnsat_implies_entails f8881 [c1902, c1913, c1921] c8881 unsat8881 (by rfl) a
  have h0 : Entails.eval a c1902 := h 1901 (by decide)
  have h1 : Entails.eval a c1913 := h 1912 (by decide)
  have h2 : Entails.eval a c1921 := h 1920 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8882 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8882 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c122, some c2389, some c152, some c823, some c3234, some c159, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8882 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8882 : lratChecker f8882 p8882 = .success := by decide +kernel
theorem unsat8882 : Unsatisfiable (PosFin 65) f8882 := by
  apply lratCheckerSound f8882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8882
  · intro a ha; simp [p8882] at ha; subst a; trivial
  · exact checked8882
theorem derived8882 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8882 := by
  apply localUnsat_implies_entails f8882 [c8840, c122, c2389, c152, c823, c3234, c159] c8882 unsat8882 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c2389 := h 2388 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c823 := h 822 (by decide)
  have h5 : Entails.eval a c3234 := h 3233 (by decide)
  have h6 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8883 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8883 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8882, some c8620, some c1068, some c2031, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8883 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8883 : lratChecker f8883 p8883 = .success := by decide +kernel
theorem unsat8883 : Unsatisfiable (PosFin 65) f8883 := by
  apply lratCheckerSound f8883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8883
  · intro a ha; simp [p8883] at ha; subst a; trivial
  · exact checked8883
theorem derived8883 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8883 := by
  apply localUnsat_implies_entails f8883 [c8882, c8620, c1068, c2031] c8883 unsat8883 (by rfl) a
  have h0 : Entails.eval a c8882 := derived8882 a h
  have h1 : Entails.eval a c8620 := derived8620 a h
  have h2 : Entails.eval a c1068 := h 1067 (by decide)
  have h3 : Entails.eval a c2031 := h 2030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8884 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8884 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1069, some c1390, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8884 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8884 : lratChecker f8884 p8884 = .success := by decide +kernel
theorem unsat8884 : Unsatisfiable (PosFin 65) f8884 := by
  apply lratCheckerSound f8884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8884
  · intro a ha; simp [p8884] at ha; subst a; trivial
  · exact checked8884
theorem derived8884 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8884 := by
  apply localUnsat_implies_entails f8884 [c1069, c1390] c8884 unsat8884 (by rfl) a
  have h0 : Entails.eval a c1069 := h 1068 (by decide)
  have h1 : Entails.eval a c1390 := h 1389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8885 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8885 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7835, some c8840, some c8662, some c8659, some c8881, some c8883, some c8663, some c8665, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8885 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8885 : lratChecker f8885 p8885 = .success := by decide +kernel
theorem unsat8885 : Unsatisfiable (PosFin 65) f8885 := by
  apply lratCheckerSound f8885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8885
  · intro a ha; simp [p8885] at ha; subst a; trivial
  · exact checked8885
theorem derived8885 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8885 := by
  apply localUnsat_implies_entails f8885 [c7835, c8840, c8662, c8659, c8881, c8883, c8663, c8665] c8885 unsat8885 (by rfl) a
  have h0 : Entails.eval a c7835 := derived7835 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8662 := derived8662 a h
  have h3 : Entails.eval a c8659 := derived8659 a h
  have h4 : Entails.eval a c8881 := derived8881 a h
  have h5 : Entails.eval a c8883 := derived8883 a h
  have h6 : Entails.eval a c8663 := derived8663 a h
  have h7 : Entails.eval a c8665 := derived8665 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8886 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8886 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8880, some c7835, some c8884, some c8546, some c8852, some c8524, some c8098, some c8406, some c7922, some c1231, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8886 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8886 : lratChecker f8886 p8886 = .success := by decide +kernel
theorem unsat8886 : Unsatisfiable (PosFin 65) f8886 := by
  apply lratCheckerSound f8886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8886
  · intro a ha; simp [p8886] at ha; subst a; trivial
  · exact checked8886
theorem derived8886 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8886 := by
  apply localUnsat_implies_entails f8886 [c8880, c7835, c8884, c8546, c8852, c8524, c8098, c8406, c7922, c1231] c8886 unsat8886 (by rfl) a
  have h0 : Entails.eval a c8880 := derived8880 a h
  have h1 : Entails.eval a c7835 := derived7835 a h
  have h2 : Entails.eval a c8884 := derived8884 a h
  have h3 : Entails.eval a c8546 := derived8546 a h
  have h4 : Entails.eval a c8852 := derived8852 a h
  have h5 : Entails.eval a c8524 := derived8524 a h
  have h6 : Entails.eval a c8098 := derived8098 a h
  have h7 : Entails.eval a c8406 := derived8406 a h
  have h8 : Entails.eval a c7922 := derived7922 a h
  have h9 : Entails.eval a c1231 := h 1230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8887 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8887 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8853, some c8871, some c8880, some c7835, some c8884, some c8886, some c8885, some c8650, some c8575, some c8643, some c2112, some c1546, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8887 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8887 : lratChecker f8887 p8887 = .success := by decide +kernel
theorem unsat8887 : Unsatisfiable (PosFin 65) f8887 := by
  apply lratCheckerSound f8887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8887
  · intro a ha; simp [p8887] at ha; subst a; trivial
  · exact checked8887
theorem derived8887 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8887 := by
  apply localUnsat_implies_entails f8887 [c8840, c8853, c8871, c8880, c7835, c8884, c8886, c8885, c8650, c8575, c8643, c2112, c1546] c8887 unsat8887 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8853 := derived8853 a h
  have h2 : Entails.eval a c8871 := derived8871 a h
  have h3 : Entails.eval a c8880 := derived8880 a h
  have h4 : Entails.eval a c7835 := derived7835 a h
  have h5 : Entails.eval a c8884 := derived8884 a h
  have h6 : Entails.eval a c8886 := derived8886 a h
  have h7 : Entails.eval a c8885 := derived8885 a h
  have h8 : Entails.eval a c8650 := derived8650 a h
  have h9 : Entails.eval a c8575 := derived8575 a h
  have h10 : Entails.eval a c8643 := derived8643 a h
  have h11 : Entails.eval a c2112 := h 2111 (by decide)
  have h12 : Entails.eval a c1546 := h 1545 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8888 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8888 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8123, some c8133, some c8142, some c7618, some c8842, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8888 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8888 : lratChecker f8888 p8888 = .success := by decide +kernel
theorem unsat8888 : Unsatisfiable (PosFin 65) f8888 := by
  apply lratCheckerSound f8888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8888
  · intro a ha; simp [p8888] at ha; subst a; trivial
  · exact checked8888
theorem derived8888 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8888 := by
  apply localUnsat_implies_entails f8888 [c8840, c8123, c8133, c8142, c7618, c8842] c8888 unsat8888 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8123 := derived8123 a h
  have h2 : Entails.eval a c8133 := derived8133 a h
  have h3 : Entails.eval a c8142 := derived8142 a h
  have h4 : Entails.eval a c7618 := derived7618 a h
  have h5 : Entails.eval a c8842 := derived8842 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8889 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8889 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8887, some c8840, some c8888, some c8847, some c8845, some c7794, some c7527, some c8848, some c983, some c2037, some c1071, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8889 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8889 : lratChecker f8889 p8889 = .success := by decide +kernel
theorem unsat8889 : Unsatisfiable (PosFin 65) f8889 := by
  apply lratCheckerSound f8889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8889
  · intro a ha; simp [p8889] at ha; subst a; trivial
  · exact checked8889
theorem derived8889 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8889 := by
  apply localUnsat_implies_entails f8889 [c8887, c8840, c8888, c8847, c8845, c7794, c7527, c8848, c983, c2037, c1071] c8889 unsat8889 (by rfl) a
  have h0 : Entails.eval a c8887 := derived8887 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8888 := derived8888 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8845 := derived8845 a h
  have h5 : Entails.eval a c7794 := derived7794 a h
  have h6 : Entails.eval a c7527 := derived7527 a h
  have h7 : Entails.eval a c8848 := derived8848 a h
  have h8 : Entails.eval a c983 := h 982 (by decide)
  have h9 : Entails.eval a c2037 := h 2036 (by decide)
  have h10 : Entails.eval a c1071 := h 1070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8890 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8890 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8123, some c8142, some c8842, some c931, some c923, some c922, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8890 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8890 : lratChecker f8890 p8890 = .success := by decide +kernel
theorem unsat8890 : Unsatisfiable (PosFin 65) f8890 := by
  apply lratCheckerSound f8890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8890
  · intro a ha; simp [p8890] at ha; subst a; trivial
  · exact checked8890
theorem derived8890 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8890 := by
  apply localUnsat_implies_entails f8890 [c8840, c8123, c8142, c8842, c931, c923, c922] c8890 unsat8890 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8123 := derived8123 a h
  have h2 : Entails.eval a c8142 := derived8142 a h
  have h3 : Entails.eval a c8842 := derived8842 a h
  have h4 : Entails.eval a c931 := h 930 (by decide)
  have h5 : Entails.eval a c923 := h 922 (by decide)
  have h6 : Entails.eval a c922 := h 921 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8891 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8891 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8845, some c7794, some c7527, some c8848, some c983, some c2037, some c1071, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8891 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8891 : lratChecker f8891 p8891 = .success := by decide +kernel
theorem unsat8891 : Unsatisfiable (PosFin 65) f8891 := by
  apply lratCheckerSound f8891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8891
  · intro a ha; simp [p8891] at ha; subst a; trivial
  · exact checked8891
theorem derived8891 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8891 := by
  apply localUnsat_implies_entails f8891 [c8845, c7794, c7527, c8848, c983, c2037, c1071] c8891 unsat8891 (by rfl) a
  have h0 : Entails.eval a c8845 := derived8845 a h
  have h1 : Entails.eval a c7794 := derived7794 a h
  have h2 : Entails.eval a c7527 := derived7527 a h
  have h3 : Entails.eval a c8848 := derived8848 a h
  have h4 : Entails.eval a c983 := h 982 (by decide)
  have h5 : Entails.eval a c2037 := h 2036 (by decide)
  have h6 : Entails.eval a c1071 := h 1070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8892 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8892 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8887, some c8840, some c8889, some c8890, some c8891, some c8376, some c8347, some c918, some c932, some c905, some c8116, some c8342, some c924, some c919, some c8473, some c879, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8892 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8892 : lratChecker f8892 p8892 = .success := by decide +kernel
theorem unsat8892 : Unsatisfiable (PosFin 65) f8892 := by
  apply lratCheckerSound f8892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8892
  · intro a ha; simp [p8892] at ha; subst a; trivial
  · exact checked8892
theorem derived8892 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8892 := by
  apply localUnsat_implies_entails f8892 [c8887, c8840, c8889, c8890, c8891, c8376, c8347, c918, c932, c905, c8116, c8342, c924, c919, c8473, c879] c8892 unsat8892 (by rfl) a
  have h0 : Entails.eval a c8887 := derived8887 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8889 := derived8889 a h
  have h3 : Entails.eval a c8890 := derived8890 a h
  have h4 : Entails.eval a c8891 := derived8891 a h
  have h5 : Entails.eval a c8376 := derived8376 a h
  have h6 : Entails.eval a c8347 := derived8347 a h
  have h7 : Entails.eval a c918 := h 917 (by decide)
  have h8 : Entails.eval a c932 := h 931 (by decide)
  have h9 : Entails.eval a c905 := h 904 (by decide)
  have h10 : Entails.eval a c8116 := derived8116 a h
  have h11 : Entails.eval a c8342 := derived8342 a h
  have h12 : Entails.eval a c924 := h 923 (by decide)
  have h13 : Entails.eval a c919 := h 918 (by decide)
  have h14 : Entails.eval a c8473 := derived8473 a h
  have h15 : Entails.eval a c879 := h 878 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8893 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8893 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8872, some c930, some c916, some c8631, some c492, some c651, some c7846, some c2546, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8893 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8893 : lratChecker f8893 p8893 = .success := by decide +kernel
theorem unsat8893 : Unsatisfiable (PosFin 65) f8893 := by
  apply lratCheckerSound f8893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8893
  · intro a ha; simp [p8893] at ha; subst a; trivial
  · exact checked8893
theorem derived8893 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8893 := by
  apply localUnsat_implies_entails f8893 [c8872, c930, c916, c8631, c492, c651, c7846, c2546] c8893 unsat8893 (by rfl) a
  have h0 : Entails.eval a c8872 := derived8872 a h
  have h1 : Entails.eval a c930 := h 929 (by decide)
  have h2 : Entails.eval a c916 := h 915 (by decide)
  have h3 : Entails.eval a c8631 := derived8631 a h
  have h4 : Entails.eval a c492 := h 491 (by decide)
  have h5 : Entails.eval a c651 := h 650 (by decide)
  have h6 : Entails.eval a c7846 := derived7846 a h
  have h7 : Entails.eval a c2546 := h 2545 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8894 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8894 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8623, some c8624, some c523, some c8581, some c930, some c916, some c913, some c2111, some c898, some c7716, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8894 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8894 : lratChecker f8894 p8894 = .success := by decide +kernel
theorem unsat8894 : Unsatisfiable (PosFin 65) f8894 := by
  apply lratCheckerSound f8894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8894
  · intro a ha; simp [p8894] at ha; subst a; trivial
  · exact checked8894
theorem derived8894 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8894 := by
  apply localUnsat_implies_entails f8894 [c8623, c8624, c523, c8581, c930, c916, c913, c2111, c898, c7716] c8894 unsat8894 (by rfl) a
  have h0 : Entails.eval a c8623 := derived8623 a h
  have h1 : Entails.eval a c8624 := derived8624 a h
  have h2 : Entails.eval a c523 := h 522 (by decide)
  have h3 : Entails.eval a c8581 := derived8581 a h
  have h4 : Entails.eval a c930 := h 929 (by decide)
  have h5 : Entails.eval a c916 := h 915 (by decide)
  have h6 : Entails.eval a c913 := h 912 (by decide)
  have h7 : Entails.eval a c2111 := h 2110 (by decide)
  have h8 : Entails.eval a c898 := h 897 (by decide)
  have h9 : Entails.eval a c7716 := derived7716 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8895 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8895 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8894, some c8893, some c8860, some c903, some c7753, some c2287, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8895 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8895 : lratChecker f8895 p8895 = .success := by decide +kernel
theorem unsat8895 : Unsatisfiable (PosFin 65) f8895 := by
  apply lratCheckerSound f8895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8895
  · intro a ha; simp [p8895] at ha; subst a; trivial
  · exact checked8895
theorem derived8895 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8895 := by
  apply localUnsat_implies_entails f8895 [c8894, c8893, c8860, c903, c7753, c2287] c8895 unsat8895 (by rfl) a
  have h0 : Entails.eval a c8894 := derived8894 a h
  have h1 : Entails.eval a c8893 := derived8893 a h
  have h2 : Entails.eval a c8860 := derived8860 a h
  have h3 : Entails.eval a c903 := h 902 (by decide)
  have h4 : Entails.eval a c7753 := derived7753 a h
  have h5 : Entails.eval a c2287 := h 2286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8896 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8896 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8895, some c8662, some c8659, some c8863, some c7836, some c7846, some c7697, some c8881, some c1368, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8896 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8896 : lratChecker f8896 p8896 = .success := by decide +kernel
theorem unsat8896 : Unsatisfiable (PosFin 65) f8896 := by
  apply lratCheckerSound f8896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8896
  · intro a ha; simp [p8896] at ha; subst a; trivial
  · exact checked8896
theorem derived8896 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8896 := by
  apply localUnsat_implies_entails f8896 [c8895, c8662, c8659, c8863, c7836, c7846, c7697, c8881, c1368] c8896 unsat8896 (by rfl) a
  have h0 : Entails.eval a c8895 := derived8895 a h
  have h1 : Entails.eval a c8662 := derived8662 a h
  have h2 : Entails.eval a c8659 := derived8659 a h
  have h3 : Entails.eval a c8863 := derived8863 a h
  have h4 : Entails.eval a c7836 := derived7836 a h
  have h5 : Entails.eval a c7846 := derived7846 a h
  have h6 : Entails.eval a c7697 := derived7697 a h
  have h7 : Entails.eval a c8881 := derived8881 a h
  have h8 : Entails.eval a c1368 := h 1367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8897 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8897 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c913, some c910, some c7637, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8897 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8897 : lratChecker f8897 p8897 = .success := by decide +kernel
theorem unsat8897 : Unsatisfiable (PosFin 65) f8897 := by
  apply lratCheckerSound f8897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8897
  · intro a ha; simp [p8897] at ha; subst a; trivial
  · exact checked8897
theorem derived8897 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8897 := by
  apply localUnsat_implies_entails f8897 [c913, c910, c7637] c8897 unsat8897 (by rfl) a
  have h0 : Entails.eval a c913 := h 912 (by decide)
  have h1 : Entails.eval a c910 := h 909 (by decide)
  have h2 : Entails.eval a c7637 := derived7637 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8898 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8898 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8895, some c8897, some c8650, some c8896, some c8546, some c8868, some c8098, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8898 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8898 : lratChecker f8898 p8898 = .success := by decide +kernel
theorem unsat8898 : Unsatisfiable (PosFin 65) f8898 := by
  apply lratCheckerSound f8898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8898
  · intro a ha; simp [p8898] at ha; subst a; trivial
  · exact checked8898
theorem derived8898 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8898 := by
  apply localUnsat_implies_entails f8898 [c8895, c8897, c8650, c8896, c8546, c8868, c8098] c8898 unsat8898 (by rfl) a
  have h0 : Entails.eval a c8895 := derived8895 a h
  have h1 : Entails.eval a c8897 := derived8897 a h
  have h2 : Entails.eval a c8650 := derived8650 a h
  have h3 : Entails.eval a c8896 := derived8896 a h
  have h4 : Entails.eval a c8546 := derived8546 a h
  have h5 : Entails.eval a c8868 := derived8868 a h
  have h6 : Entails.eval a c8098 := derived8098 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8899 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8899 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8894, some c8893, some c8898, some c970, some c894, some c8514, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8899 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8899 : lratChecker f8899 p8899 = .success := by decide +kernel
theorem unsat8899 : Unsatisfiable (PosFin 65) f8899 := by
  apply lratCheckerSound f8899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8899
  · intro a ha; simp [p8899] at ha; subst a; trivial
  · exact checked8899
theorem derived8899 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8899 := by
  apply localUnsat_implies_entails f8899 [c8894, c8893, c8898, c970, c894, c8514] c8899 unsat8899 (by rfl) a
  have h0 : Entails.eval a c8894 := derived8894 a h
  have h1 : Entails.eval a c8893 := derived8893 a h
  have h2 : Entails.eval a c8898 := derived8898 a h
  have h3 : Entails.eval a c970 := h 969 (by decide)
  have h4 : Entails.eval a c894 := h 893 (by decide)
  have h5 : Entails.eval a c8514 := derived8514 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8900 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8900 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1058, some c1932, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p8900 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8900 : lratChecker f8900 p8900 = .success := by decide +kernel
theorem unsat8900 : Unsatisfiable (PosFin 65) f8900 := by
  apply lratCheckerSound f8900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8900
  · intro a ha; simp [p8900] at ha; subst a; trivial
  · exact checked8900
theorem derived8900 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8900 := by
  apply localUnsat_implies_entails f8900 [c1058, c1932] c8900 unsat8900 (by rfl) a
  have h0 : Entails.eval a c1058 := h 1057 (by decide)
  have h1 : Entails.eval a c1932 := h 1931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8901 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8901 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8894, some c8893, some c8898, some c8899, some c8336, some c8544, some c8900, some c7827, some c8510, some c2106, some c8522, some c8490, some c8418, some c1742, some c1070, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8901 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8901 : lratChecker f8901 p8901 = .success := by decide +kernel
theorem unsat8901 : Unsatisfiable (PosFin 65) f8901 := by
  apply lratCheckerSound f8901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8901
  · intro a ha; simp [p8901] at ha; subst a; trivial
  · exact checked8901
theorem derived8901 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8901 := by
  apply localUnsat_implies_entails f8901 [c8894, c8893, c8898, c8899, c8336, c8544, c8900, c7827, c8510, c2106, c8522, c8490, c8418, c1742, c1070] c8901 unsat8901 (by rfl) a
  have h0 : Entails.eval a c8894 := derived8894 a h
  have h1 : Entails.eval a c8893 := derived8893 a h
  have h2 : Entails.eval a c8898 := derived8898 a h
  have h3 : Entails.eval a c8899 := derived8899 a h
  have h4 : Entails.eval a c8336 := derived8336 a h
  have h5 : Entails.eval a c8544 := derived8544 a h
  have h6 : Entails.eval a c8900 := derived8900 a h
  have h7 : Entails.eval a c7827 := derived7827 a h
  have h8 : Entails.eval a c8510 := derived8510 a h
  have h9 : Entails.eval a c2106 := h 2105 (by decide)
  have h10 : Entails.eval a c8522 := derived8522 a h
  have h11 : Entails.eval a c8490 := derived8490 a h
  have h12 : Entails.eval a c8418 := derived8418 a h
  have h13 : Entails.eval a c1742 := h 1741 (by decide)
  have h14 : Entails.eval a c1070 := h 1069 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8902 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, true), (⟨19, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8902 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6703, some c6739, some c3310, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8902 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8902 : lratChecker f8902 p8902 = .success := by decide +kernel
theorem unsat8902 : Unsatisfiable (PosFin 65) f8902 := by
  apply lratCheckerSound f8902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8902
  · intro a ha; simp [p8902] at ha; subst a; trivial
  · exact checked8902
theorem derived8902 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8902 := by
  apply localUnsat_implies_entails f8902 [c6703, c6739, c3310] c8902 unsat8902 (by rfl) a
  have h0 : Entails.eval a c6703 := derived6703 a h
  have h1 : Entails.eval a c6739 := derived6739 a h
  have h2 : Entails.eval a c3310 := h 3309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8903 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, true), (⟨24, by decide⟩, false), (⟨19, by decide⟩, true), (⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8903 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2232, some c8902, some c3061, some c69, some c6756, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8903 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8903 : lratChecker f8903 p8903 = .success := by decide +kernel
theorem unsat8903 : Unsatisfiable (PosFin 65) f8903 := by
  apply lratCheckerSound f8903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8903
  · intro a ha; simp [p8903] at ha; subst a; trivial
  · exact checked8903
theorem derived8903 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8903 := by
  apply localUnsat_implies_entails f8903 [c2232, c8902, c3061, c69, c6756] c8903 unsat8903 (by rfl) a
  have h0 : Entails.eval a c2232 := h 2231 (by decide)
  have h1 : Entails.eval a c8902 := derived8902 a h
  have h2 : Entails.eval a c3061 := h 3060 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c6756 := derived6756 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8904 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨12, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8904 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6703, some c6685, some c80, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8904 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8904 : lratChecker f8904 p8904 = .success := by decide +kernel
theorem unsat8904 : Unsatisfiable (PosFin 65) f8904 := by
  apply lratCheckerSound f8904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8904
  · intro a ha; simp [p8904] at ha; subst a; trivial
  · exact checked8904
theorem derived8904 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8904 := by
  apply localUnsat_implies_entails f8904 [c6703, c6685, c80] c8904 unsat8904 (by rfl) a
  have h0 : Entails.eval a c6703 := derived6703 a h
  have h1 : Entails.eval a c6685 := derived6685 a h
  have h2 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8905 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8905 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8887, some c8840, some c8892, some c8898, some c8894, some c8893, some c8901, some c8098, some c8876, some c8859, some c8670, some c875, some c985, some c894, some c993, some c969, some c867, some c8501, some c878, some c8482, some c876, some c8503, some c8481, some c8903, some c2236, some c1458, some c8904, some c3298, some c3287, some c6686, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8905 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked8905 : lratChecker f8905 p8905 = .success := by decide +kernel
theorem unsat8905 : Unsatisfiable (PosFin 65) f8905 := by
  apply lratCheckerSound f8905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8905
  · intro a ha; simp [p8905] at ha; subst a; trivial
  · exact checked8905
theorem derived8905 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8905 := by
  apply localUnsat_implies_entails f8905 [c8887, c8840, c8892, c8898, c8894, c8893, c8901, c8098, c8876, c8859, c8670, c875, c985, c894, c993, c969, c867, c8501, c878, c8482, c876, c8503, c8481, c8903, c2236, c1458, c8904, c3298, c3287, c6686] c8905 unsat8905 (by rfl) a
  have h0 : Entails.eval a c8887 := derived8887 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8892 := derived8892 a h
  have h3 : Entails.eval a c8898 := derived8898 a h
  have h4 : Entails.eval a c8894 := derived8894 a h
  have h5 : Entails.eval a c8893 := derived8893 a h
  have h6 : Entails.eval a c8901 := derived8901 a h
  have h7 : Entails.eval a c8098 := derived8098 a h
  have h8 : Entails.eval a c8876 := derived8876 a h
  have h9 : Entails.eval a c8859 := derived8859 a h
  have h10 : Entails.eval a c8670 := derived8670 a h
  have h11 : Entails.eval a c875 := h 874 (by decide)
  have h12 : Entails.eval a c985 := h 984 (by decide)
  have h13 : Entails.eval a c894 := h 893 (by decide)
  have h14 : Entails.eval a c993 := h 992 (by decide)
  have h15 : Entails.eval a c969 := h 968 (by decide)
  have h16 : Entails.eval a c867 := h 866 (by decide)
  have h17 : Entails.eval a c8501 := derived8501 a h
  have h18 : Entails.eval a c878 := h 877 (by decide)
  have h19 : Entails.eval a c8482 := derived8482 a h
  have h20 : Entails.eval a c876 := h 875 (by decide)
  have h21 : Entails.eval a c8503 := derived8503 a h
  have h22 : Entails.eval a c8481 := derived8481 a h
  have h23 : Entails.eval a c8903 := derived8903 a h
  have h24 : Entails.eval a c2236 := h 2235 (by decide)
  have h25 : Entails.eval a c1458 := h 1457 (by decide)
  have h26 : Entails.eval a c8904 := derived8904 a h
  have h27 : Entails.eval a c3298 := h 3297 (by decide)
  have h28 : Entails.eval a c3287 := h 3286 (by decide)
  have h29 : Entails.eval a c6686 := derived6686 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8906 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false), (⟨28, by decide⟩, true), (⟨16, by decide⟩, false), (⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨30, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8906 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6757, some c6739, some c6724, some c79, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8906 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8906 : lratChecker f8906 p8906 = .success := by decide +kernel
theorem unsat8906 : Unsatisfiable (PosFin 65) f8906 := by
  apply lratCheckerSound f8906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8906
  · intro a ha; simp [p8906] at ha; subst a; trivial
  · exact checked8906
theorem derived8906 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8906 := by
  apply localUnsat_implies_entails f8906 [c6757, c6739, c6724, c79] c8906 unsat8906 (by rfl) a
  have h0 : Entails.eval a c6757 := derived6757 a h
  have h1 : Entails.eval a c6739 := derived6739 a h
  have h2 : Entails.eval a c6724 := derived6724 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8907 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨28, by decide⟩, true), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8907 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8906, some c3060, some c3061, some c69, some c2126, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8907 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8907 : lratChecker f8907 p8907 = .success := by decide +kernel
theorem unsat8907 : Unsatisfiable (PosFin 65) f8907 := by
  apply lratCheckerSound f8907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8907
  · intro a ha; simp [p8907] at ha; subst a; trivial
  · exact checked8907
theorem derived8907 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8907 := by
  apply localUnsat_implies_entails f8907 [c8906, c3060, c3061, c69, c2126] c8907 unsat8907 (by rfl) a
  have h0 : Entails.eval a c8906 := derived8906 a h
  have h1 : Entails.eval a c3060 := h 3059 (by decide)
  have h2 : Entails.eval a c3061 := h 3060 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c2126 := h 2125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8908 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨21, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8908 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6677, some c6685, some c50, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8908 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8908 : lratChecker f8908 p8908 = .success := by decide +kernel
theorem unsat8908 : Unsatisfiable (PosFin 65) f8908 := by
  apply lratCheckerSound f8908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8908
  · intro a ha; simp [p8908] at ha; subst a; trivial
  · exact checked8908
theorem derived8908 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8908 := by
  apply localUnsat_implies_entails f8908 [c6677, c6685, c50] c8908 unsat8908 (by rfl) a
  have h0 : Entails.eval a c6677 := derived6677 a h
  have h1 : Entails.eval a c6685 := derived6685 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8909 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8909 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8887, some c8892, some c8894, some c8893, some c8898, some c8670, some c8901, some c8098, some c8859, some c8876, some c8905, some c1923, some c1917, some c1926, some c1912, some c1892, some c8501, some c8620, some c8482, some c2105, some c8503, some c2121, some c8481, some c8907, some c8908, some c3298, some c3287, some c3295, some c51, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8909 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked8909 : lratChecker f8909 p8909 = .success := by decide +kernel
theorem unsat8909 : Unsatisfiable (PosFin 65) f8909 := by
  apply lratCheckerSound f8909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8909
  · intro a ha; simp [p8909] at ha; subst a; trivial
  · exact checked8909
theorem derived8909 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8909 := by
  apply localUnsat_implies_entails f8909 [c8840, c8887, c8892, c8894, c8893, c8898, c8670, c8901, c8098, c8859, c8876, c8905, c1923, c1917, c1926, c1912, c1892, c8501, c8620, c8482, c2105, c8503, c2121, c8481, c8907, c8908, c3298, c3287, c3295, c51] c8909 unsat8909 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8887 := derived8887 a h
  have h2 : Entails.eval a c8892 := derived8892 a h
  have h3 : Entails.eval a c8894 := derived8894 a h
  have h4 : Entails.eval a c8893 := derived8893 a h
  have h5 : Entails.eval a c8898 := derived8898 a h
  have h6 : Entails.eval a c8670 := derived8670 a h
  have h7 : Entails.eval a c8901 := derived8901 a h
  have h8 : Entails.eval a c8098 := derived8098 a h
  have h9 : Entails.eval a c8859 := derived8859 a h
  have h10 : Entails.eval a c8876 := derived8876 a h
  have h11 : Entails.eval a c8905 := derived8905 a h
  have h12 : Entails.eval a c1923 := h 1922 (by decide)
  have h13 : Entails.eval a c1917 := h 1916 (by decide)
  have h14 : Entails.eval a c1926 := h 1925 (by decide)
  have h15 : Entails.eval a c1912 := h 1911 (by decide)
  have h16 : Entails.eval a c1892 := h 1891 (by decide)
  have h17 : Entails.eval a c8501 := derived8501 a h
  have h18 : Entails.eval a c8620 := derived8620 a h
  have h19 : Entails.eval a c8482 := derived8482 a h
  have h20 : Entails.eval a c2105 := h 2104 (by decide)
  have h21 : Entails.eval a c8503 := derived8503 a h
  have h22 : Entails.eval a c2121 := h 2120 (by decide)
  have h23 : Entails.eval a c8481 := derived8481 a h
  have h24 : Entails.eval a c8907 := derived8907 a h
  have h25 : Entails.eval a c8908 := derived8908 a h
  have h26 : Entails.eval a c3298 := h 3297 (by decide)
  have h27 : Entails.eval a c3287 := h 3286 (by decide)
  have h28 : Entails.eval a c3295 := h 3294 (by decide)
  have h29 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8910 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8910 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8892, some c8887, some c8840, some c8894, some c8893, some c8909, some c903, some c8500, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8910 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8910 : lratChecker f8910 p8910 = .success := by decide +kernel
theorem unsat8910 : Unsatisfiable (PosFin 65) f8910 := by
  apply lratCheckerSound f8910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8910
  · intro a ha; simp [p8910] at ha; subst a; trivial
  · exact checked8910
theorem derived8910 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8910 := by
  apply localUnsat_implies_entails f8910 [c8892, c8887, c8840, c8894, c8893, c8909, c903, c8500] c8910 unsat8910 (by rfl) a
  have h0 : Entails.eval a c8892 := derived8892 a h
  have h1 : Entails.eval a c8887 := derived8887 a h
  have h2 : Entails.eval a c8840 := derived8840 a h
  have h3 : Entails.eval a c8894 := derived8894 a h
  have h4 : Entails.eval a c8893 := derived8893 a h
  have h5 : Entails.eval a c8909 := derived8909 a h
  have h6 : Entails.eval a c903 := h 902 (by decide)
  have h7 : Entails.eval a c8500 := derived8500 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8911 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8911 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7835, some c8840, some c8662, some c8885, some c1069, some c2032, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8911 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8911 : lratChecker f8911 p8911 = .success := by decide +kernel
theorem unsat8911 : Unsatisfiable (PosFin 65) f8911 := by
  apply lratCheckerSound f8911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8911
  · intro a ha; simp [p8911] at ha; subst a; trivial
  · exact checked8911
theorem derived8911 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8911 := by
  apply localUnsat_implies_entails f8911 [c7835, c8840, c8662, c8885, c1069, c2032] c8911 unsat8911 (by rfl) a
  have h0 : Entails.eval a c7835 := derived7835 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8662 := derived8662 a h
  have h3 : Entails.eval a c8885 := derived8885 a h
  have h4 : Entails.eval a c1069 := h 1068 (by decide)
  have h5 : Entails.eval a c2032 := h 2031 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8912 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8912 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8887, some c8892, some c8898, some c8910, some c8897, some c8650, some c8911, some c8546, some c8524, some c8098, some c1926, some c1912, some c1910, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8912 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8912 : lratChecker f8912 p8912 = .success := by decide +kernel
theorem unsat8912 : Unsatisfiable (PosFin 65) f8912 := by
  apply lratCheckerSound f8912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8912
  · intro a ha; simp [p8912] at ha; subst a; trivial
  · exact checked8912
theorem derived8912 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8912 := by
  apply localUnsat_implies_entails f8912 [c8840, c8887, c8892, c8898, c8910, c8897, c8650, c8911, c8546, c8524, c8098, c1926, c1912, c1910] c8912 unsat8912 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8887 := derived8887 a h
  have h2 : Entails.eval a c8892 := derived8892 a h
  have h3 : Entails.eval a c8898 := derived8898 a h
  have h4 : Entails.eval a c8910 := derived8910 a h
  have h5 : Entails.eval a c8897 := derived8897 a h
  have h6 : Entails.eval a c8650 := derived8650 a h
  have h7 : Entails.eval a c8911 := derived8911 a h
  have h8 : Entails.eval a c8546 := derived8546 a h
  have h9 : Entails.eval a c8524 := derived8524 a h
  have h10 : Entails.eval a c8098 := derived8098 a h
  have h11 : Entails.eval a c1926 := h 1925 (by decide)
  have h12 : Entails.eval a c1912 := h 1911 (by decide)
  have h13 : Entails.eval a c1910 := h 1909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8913 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8913 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8376, some c8842, some c8359, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8913 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8913 : lratChecker f8913 p8913 = .success := by decide +kernel
theorem unsat8913 : Unsatisfiable (PosFin 65) f8913 := by
  apply lratCheckerSound f8913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8913
  · intro a ha; simp [p8913] at ha; subst a; trivial
  · exact checked8913
theorem derived8913 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8913 := by
  apply localUnsat_implies_entails f8913 [c8376, c8842, c8359] c8913 unsat8913 (by rfl) a
  have h0 : Entails.eval a c8376 := derived8376 a h
  have h1 : Entails.eval a c8842 := derived8842 a h
  have h2 : Entails.eval a c8359 := derived8359 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8914 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8914 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8376, some c8913, some c8036, some c8161, some c8353, some c8352, some c8354, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8914 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8914 : lratChecker f8914 p8914 = .success := by decide +kernel
theorem unsat8914 : Unsatisfiable (PosFin 65) f8914 := by
  apply lratCheckerSound f8914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8914
  · intro a ha; simp [p8914] at ha; subst a; trivial
  · exact checked8914
theorem derived8914 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8914 := by
  apply localUnsat_implies_entails f8914 [c8376, c8913, c8036, c8161, c8353, c8352, c8354] c8914 unsat8914 (by rfl) a
  have h0 : Entails.eval a c8376 := derived8376 a h
  have h1 : Entails.eval a c8913 := derived8913 a h
  have h2 : Entails.eval a c8036 := derived8036 a h
  have h3 : Entails.eval a c8161 := derived8161 a h
  have h4 : Entails.eval a c8353 := derived8353 a h
  have h5 : Entails.eval a c8352 := derived8352 a h
  have h6 : Entails.eval a c8354 := derived8354 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8915 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8915 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8914, some c8347, some c8321, some c8331, some c8212, some c8336, some c1252, some c1608, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8915 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8915 : lratChecker f8915 p8915 = .success := by decide +kernel
theorem unsat8915 : Unsatisfiable (PosFin 65) f8915 := by
  apply lratCheckerSound f8915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8915
  · intro a ha; simp [p8915] at ha; subst a; trivial
  · exact checked8915
theorem derived8915 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8915 := by
  apply localUnsat_implies_entails f8915 [c8914, c8347, c8321, c8331, c8212, c8336, c1252, c1608] c8915 unsat8915 (by rfl) a
  have h0 : Entails.eval a c8914 := derived8914 a h
  have h1 : Entails.eval a c8347 := derived8347 a h
  have h2 : Entails.eval a c8321 := derived8321 a h
  have h3 : Entails.eval a c8331 := derived8331 a h
  have h4 : Entails.eval a c8212 := derived8212 a h
  have h5 : Entails.eval a c8336 := derived8336 a h
  have h6 : Entails.eval a c1252 := h 1251 (by decide)
  have h7 : Entails.eval a c1608 := h 1607 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8916 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨13, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8916 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8319, some c8529, some c8533, some c533, some c1594, some c8161, some c1259, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8916 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8916 : lratChecker f8916 p8916 = .success := by decide +kernel
theorem unsat8916 : Unsatisfiable (PosFin 65) f8916 := by
  apply lratCheckerSound f8916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8916
  · intro a ha; simp [p8916] at ha; subst a; trivial
  · exact checked8916
theorem derived8916 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8916 := by
  apply localUnsat_implies_entails f8916 [c8319, c8529, c8533, c533, c1594, c8161, c1259] c8916 unsat8916 (by rfl) a
  have h0 : Entails.eval a c8319 := derived8319 a h
  have h1 : Entails.eval a c8529 := derived8529 a h
  have h2 : Entails.eval a c8533 := derived8533 a h
  have h3 : Entails.eval a c533 := h 532 (by decide)
  have h4 : Entails.eval a c1594 := h 1593 (by decide)
  have h5 : Entails.eval a c8161 := derived8161 a h
  have h6 : Entails.eval a c1259 := h 1258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8917 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8917 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c941, some c2043, some c1735, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8917 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8917 : lratChecker f8917 p8917 = .success := by decide +kernel
theorem unsat8917 : Unsatisfiable (PosFin 65) f8917 := by
  apply lratCheckerSound f8917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8917
  · intro a ha; simp [p8917] at ha; subst a; trivial
  · exact checked8917
theorem derived8917 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8917 := by
  apply localUnsat_implies_entails f8917 [c941, c2043, c1735] c8917 unsat8917 (by rfl) a
  have h0 : Entails.eval a c941 := h 940 (by decide)
  have h1 : Entails.eval a c2043 := h 2042 (by decide)
  have h2 : Entails.eval a c1735 := h 1734 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8918 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8918 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8916, some c8917, some c8321, some c8327, some c8533, some c8161, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8918 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8918 : lratChecker f8918 p8918 = .success := by decide +kernel
theorem unsat8918 : Unsatisfiable (PosFin 65) f8918 := by
  apply lratCheckerSound f8918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8918
  · intro a ha; simp [p8918] at ha; subst a; trivial
  · exact checked8918
theorem derived8918 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8918 := by
  apply localUnsat_implies_entails f8918 [c8916, c8917, c8321, c8327, c8533, c8161] c8918 unsat8918 (by rfl) a
  have h0 : Entails.eval a c8916 := derived8916 a h
  have h1 : Entails.eval a c8917 := derived8917 a h
  have h2 : Entails.eval a c8321 := derived8321 a h
  have h3 : Entails.eval a c8327 := derived8327 a h
  have h4 : Entails.eval a c8533 := derived8533 a h
  have h5 : Entails.eval a c8161 := derived8161 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8919 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8919 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c499, some c506, some c515, some c494, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p8919 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8919 : lratChecker f8919 p8919 = .success := by decide +kernel
theorem unsat8919 : Unsatisfiable (PosFin 65) f8919 := by
  apply lratCheckerSound f8919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8919
  · intro a ha; simp [p8919] at ha; subst a; trivial
  · exact checked8919
theorem derived8919 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8919 := by
  apply localUnsat_implies_entails f8919 [c499, c506, c515, c494] c8919 unsat8919 (by rfl) a
  have h0 : Entails.eval a c499 := h 498 (by decide)
  have h1 : Entails.eval a c506 := h 505 (by decide)
  have h2 : Entails.eval a c515 := h 514 (by decide)
  have h3 : Entails.eval a c494 := h 493 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8920 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8920 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8919, some c8319, some c8533, some c8530, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8920 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8920 : lratChecker f8920 p8920 = .success := by decide +kernel
theorem unsat8920 : Unsatisfiable (PosFin 65) f8920 := by
  apply lratCheckerSound f8920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8920
  · intro a ha; simp [p8920] at ha; subst a; trivial
  · exact checked8920
theorem derived8920 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8920 := by
  apply localUnsat_implies_entails f8920 [c8919, c8319, c8533, c8530] c8920 unsat8920 (by rfl) a
  have h0 : Entails.eval a c8919 := derived8919 a h
  have h1 : Entails.eval a c8319 := derived8319 a h
  have h2 : Entails.eval a c8533 := derived8533 a h
  have h3 : Entails.eval a c8530 := derived8530 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8921 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8921 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8918, some c8920, some c8545, some c8321, some c8111, some c8473, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8921 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8921 : lratChecker f8921 p8921 = .success := by decide +kernel
theorem unsat8921 : Unsatisfiable (PosFin 65) f8921 := by
  apply lratCheckerSound f8921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8921
  · intro a ha; simp [p8921] at ha; subst a; trivial
  · exact checked8921
theorem derived8921 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8921 := by
  apply localUnsat_implies_entails f8921 [c8918, c8920, c8545, c8321, c8111, c8473] c8921 unsat8921 (by rfl) a
  have h0 : Entails.eval a c8918 := derived8918 a h
  have h1 : Entails.eval a c8920 := derived8920 a h
  have h2 : Entails.eval a c8545 := derived8545 a h
  have h3 : Entails.eval a c8321 := derived8321 a h
  have h4 : Entails.eval a c8111 := derived8111 a h
  have h5 : Entails.eval a c8473 := derived8473 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8922 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8922 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8912, some c8840, some c8843, some c8914, some c8915, some c8919, some c8921, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8922 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8922 : lratChecker f8922 p8922 = .success := by decide +kernel
theorem unsat8922 : Unsatisfiable (PosFin 65) f8922 := by
  apply lratCheckerSound f8922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8922
  · intro a ha; simp [p8922] at ha; subst a; trivial
  · exact checked8922
theorem derived8922 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8922 := by
  apply localUnsat_implies_entails f8922 [c8912, c8840, c8843, c8914, c8915, c8919, c8921] c8922 unsat8922 (by rfl) a
  have h0 : Entails.eval a c8912 := derived8912 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8843 := derived8843 a h
  have h3 : Entails.eval a c8914 := derived8914 a h
  have h4 : Entails.eval a c8915 := derived8915 a h
  have h5 : Entails.eval a c8919 := derived8919 a h
  have h6 : Entails.eval a c8921 := derived8921 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8923 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8923 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8861, some c8872, some c8855, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8923 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8923 : lratChecker f8923 p8923 = .success := by decide +kernel
theorem unsat8923 : Unsatisfiable (PosFin 65) f8923 := by
  apply lratCheckerSound f8923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8923
  · intro a ha; simp [p8923] at ha; subst a; trivial
  · exact checked8923
theorem derived8923 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8923 := by
  apply localUnsat_implies_entails f8923 [c8861, c8872, c8855] c8923 unsat8923 (by rfl) a
  have h0 : Entails.eval a c8861 := derived8861 a h
  have h1 : Entails.eval a c8872 := derived8872 a h
  have h2 : Entails.eval a c8855 := derived8855 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8924 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8924 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8923, some c8650, some c8866, some c8863, some c2336, some c2205, some c2476, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8924 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8924 : lratChecker f8924 p8924 = .success := by decide +kernel
theorem unsat8924 : Unsatisfiable (PosFin 65) f8924 := by
  apply lratCheckerSound f8924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8924
  · intro a ha; simp [p8924] at ha; subst a; trivial
  · exact checked8924
theorem derived8924 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8924 := by
  apply localUnsat_implies_entails f8924 [c8923, c8650, c8866, c8863, c2336, c2205, c2476] c8924 unsat8924 (by rfl) a
  have h0 : Entails.eval a c8923 := derived8923 a h
  have h1 : Entails.eval a c8650 := derived8650 a h
  have h2 : Entails.eval a c8866 := derived8866 a h
  have h3 : Entails.eval a c8863 := derived8863 a h
  have h4 : Entails.eval a c2336 := h 2335 (by decide)
  have h5 : Entails.eval a c2205 := h 2204 (by decide)
  have h6 : Entails.eval a c2476 := h 2475 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8925 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8925 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8861, some c8580, some c8855, some c8856, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8925 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8925 : lratChecker f8925 p8925 = .success := by decide +kernel
theorem unsat8925 : Unsatisfiable (PosFin 65) f8925 := by
  apply lratCheckerSound f8925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8925
  · intro a ha; simp [p8925] at ha; subst a; trivial
  · exact checked8925
theorem derived8925 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8925 := by
  apply localUnsat_implies_entails f8925 [c8861, c8580, c8855, c8856] c8925 unsat8925 (by rfl) a
  have h0 : Entails.eval a c8861 := derived8861 a h
  have h1 : Entails.eval a c8580 := derived8580 a h
  have h2 : Entails.eval a c8855 := derived8855 a h
  have h3 : Entails.eval a c8856 := derived8856 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8926 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8926 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8925, some c8659, some c8595, some c1512, some c1518, some c1521, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8926 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8926 : lratChecker f8926 p8926 = .success := by decide +kernel
theorem unsat8926 : Unsatisfiable (PosFin 65) f8926 := by
  apply lratCheckerSound f8926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8926
  · intro a ha; simp [p8926] at ha; subst a; trivial
  · exact checked8926
theorem derived8926 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8926 := by
  apply localUnsat_implies_entails f8926 [c8925, c8659, c8595, c1512, c1518, c1521] c8926 unsat8926 (by rfl) a
  have h0 : Entails.eval a c8925 := derived8925 a h
  have h1 : Entails.eval a c8659 := derived8659 a h
  have h2 : Entails.eval a c8595 := derived8595 a h
  have h3 : Entails.eval a c1512 := h 1511 (by decide)
  have h4 : Entails.eval a c1518 := h 1517 (by decide)
  have h5 : Entails.eval a c1521 := h 1520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8927 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8927 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8924, some c8926, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8927 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8927 : lratChecker f8927 p8927 = .success := by decide +kernel
theorem unsat8927 : Unsatisfiable (PosFin 65) f8927 := by
  apply lratCheckerSound f8927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8927
  · intro a ha; simp [p8927] at ha; subst a; trivial
  · exact checked8927
theorem derived8927 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8927 := by
  apply localUnsat_implies_entails f8927 [c8924, c8926] c8927 unsat8927 (by rfl) a
  have h0 : Entails.eval a c8924 := derived8924 a h
  have h1 : Entails.eval a c8926 := derived8926 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8928 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8928 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8872, some c8623, some c8624, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8928 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8928 : lratChecker f8928 p8928 = .success := by decide +kernel
theorem unsat8928 : Unsatisfiable (PosFin 65) f8928 := by
  apply lratCheckerSound f8928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8928
  · intro a ha; simp [p8928] at ha; subst a; trivial
  · exact checked8928
theorem derived8928 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8928 := by
  apply localUnsat_implies_entails f8928 [c8872, c8623, c8624] c8928 unsat8928 (by rfl) a
  have h0 : Entails.eval a c8872 := derived8872 a h
  have h1 : Entails.eval a c8623 := derived8623 a h
  have h2 : Entails.eval a c8624 := derived8624 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8929 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8929 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8881, some c1917, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8929 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8929 : lratChecker f8929 p8929 = .success := by decide +kernel
theorem unsat8929 : Unsatisfiable (PosFin 65) f8929 := by
  apply lratCheckerSound f8929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8929
  · intro a ha; simp [p8929] at ha; subst a; trivial
  · exact checked8929
theorem derived8929 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8929 := by
  apply localUnsat_implies_entails f8929 [c8881, c1917] c8929 unsat8929 (by rfl) a
  have h0 : Entails.eval a c8881 := derived8881 a h
  have h1 : Entails.eval a c1917 := h 1916 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8930 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8930 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c588, some c587, some c604, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8930 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8930 : lratChecker f8930 p8930 = .success := by decide +kernel
theorem unsat8930 : Unsatisfiable (PosFin 65) f8930 := by
  apply lratCheckerSound f8930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8930
  · intro a ha; simp [p8930] at ha; subst a; trivial
  · exact checked8930
theorem derived8930 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8930 := by
  apply localUnsat_implies_entails f8930 [c588, c587, c604] c8930 unsat8930 (by rfl) a
  have h0 : Entails.eval a c588 := h 587 (by decide)
  have h1 : Entails.eval a c587 := h 586 (by decide)
  have h2 : Entails.eval a c604 := h 603 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8931 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8931 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1104, some c1189, some c2606, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8931 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8931 : lratChecker f8931 p8931 = .success := by decide +kernel
theorem unsat8931 : Unsatisfiable (PosFin 65) f8931 := by
  apply lratCheckerSound f8931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8931
  · intro a ha; simp [p8931] at ha; subst a; trivial
  · exact checked8931
theorem derived8931 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8931 := by
  apply localUnsat_implies_entails f8931 [c1104, c1189, c2606] c8931 unsat8931 (by rfl) a
  have h0 : Entails.eval a c1104 := h 1103 (by decide)
  have h1 : Entails.eval a c1189 := h 1188 (by decide)
  have h2 : Entails.eval a c2606 := h 2605 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8932 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8932 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c672, some c1938, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8932 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8932 : lratChecker f8932 p8932 = .success := by decide +kernel
theorem unsat8932 : Unsatisfiable (PosFin 65) f8932 := by
  apply lratCheckerSound f8932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8932
  · intro a ha; simp [p8932] at ha; subst a; trivial
  · exact checked8932
theorem derived8932 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8932 := by
  apply localUnsat_implies_entails f8932 [c672, c1938] c8932 unsat8932 (by rfl) a
  have h0 : Entails.eval a c672 := h 671 (by decide)
  have h1 : Entails.eval a c1938 := h 1937 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8933 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8933 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8932, some c8931, some c1939, some c673, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8933 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8933 : lratChecker f8933 p8933 = .success := by decide +kernel
theorem unsat8933 : Unsatisfiable (PosFin 65) f8933 := by
  apply lratCheckerSound f8933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8933
  · intro a ha; simp [p8933] at ha; subst a; trivial
  · exact checked8933
theorem derived8933 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8933 := by
  apply localUnsat_implies_entails f8933 [c8932, c8931, c1939, c673] c8933 unsat8933 (by rfl) a
  have h0 : Entails.eval a c8932 := derived8932 a h
  have h1 : Entails.eval a c8931 := derived8931 a h
  have h2 : Entails.eval a c1939 := h 1938 (by decide)
  have h3 : Entails.eval a c673 := h 672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8934 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8934 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8933, some c2156, some c2157, some c2173, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8934 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8934 : lratChecker f8934 p8934 = .success := by decide +kernel
theorem unsat8934 : Unsatisfiable (PosFin 65) f8934 := by
  apply lratCheckerSound f8934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8934
  · intro a ha; simp [p8934] at ha; subst a; trivial
  · exact checked8934
theorem derived8934 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8934 := by
  apply localUnsat_implies_entails f8934 [c8933, c2156, c2157, c2173] c8934 unsat8934 (by rfl) a
  have h0 : Entails.eval a c8933 := derived8933 a h
  have h1 : Entails.eval a c2156 := h 2155 (by decide)
  have h2 : Entails.eval a c2157 := h 2156 (by decide)
  have h3 : Entails.eval a c2173 := h 2172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8935 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8935 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8928, some c8650, some c8662, some c8929, some c8930, some c8934, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8935 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8935 : lratChecker f8935 p8935 = .success := by decide +kernel
theorem unsat8935 : Unsatisfiable (PosFin 65) f8935 := by
  apply lratCheckerSound f8935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8935
  · intro a ha; simp [p8935] at ha; subst a; trivial
  · exact checked8935
theorem derived8935 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8935 := by
  apply localUnsat_implies_entails f8935 [c8928, c8650, c8662, c8929, c8930, c8934] c8935 unsat8935 (by rfl) a
  have h0 : Entails.eval a c8928 := derived8928 a h
  have h1 : Entails.eval a c8650 := derived8650 a h
  have h2 : Entails.eval a c8662 := derived8662 a h
  have h3 : Entails.eval a c8929 := derived8929 a h
  have h4 : Entails.eval a c8930 := derived8930 a h
  have h5 : Entails.eval a c8934 := derived8934 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8936 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8936 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8580, some c8631, some c8629, some c8593, some c8578, some c580, some c8930, some c2047, some c2053, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8936 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8936 : lratChecker f8936 p8936 = .success := by decide +kernel
theorem unsat8936 : Unsatisfiable (PosFin 65) f8936 := by
  apply lratCheckerSound f8936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8936
  · intro a ha; simp [p8936] at ha; subst a; trivial
  · exact checked8936
theorem derived8936 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8936 := by
  apply localUnsat_implies_entails f8936 [c8580, c8631, c8629, c8593, c8578, c580, c8930, c2047, c2053] c8936 unsat8936 (by rfl) a
  have h0 : Entails.eval a c8580 := derived8580 a h
  have h1 : Entails.eval a c8631 := derived8631 a h
  have h2 : Entails.eval a c8629 := derived8629 a h
  have h3 : Entails.eval a c8593 := derived8593 a h
  have h4 : Entails.eval a c8578 := derived8578 a h
  have h5 : Entails.eval a c580 := h 579 (by decide)
  have h6 : Entails.eval a c8930 := derived8930 a h
  have h7 : Entails.eval a c2047 := h 2046 (by decide)
  have h8 : Entails.eval a c2053 := h 2052 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8937 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8937 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8580, some c8936, some c7439, some c1263, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8937 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8937 : lratChecker f8937 p8937 = .success := by decide +kernel
theorem unsat8937 : Unsatisfiable (PosFin 65) f8937 := by
  apply lratCheckerSound f8937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8937
  · intro a ha; simp [p8937] at ha; subst a; trivial
  · exact checked8937
theorem derived8937 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8937 := by
  apply localUnsat_implies_entails f8937 [c8580, c8936, c7439, c1263] c8937 unsat8937 (by rfl) a
  have h0 : Entails.eval a c8580 := derived8580 a h
  have h1 : Entails.eval a c8936 := derived8936 a h
  have h2 : Entails.eval a c7439 := derived7439 a h
  have h3 : Entails.eval a c1263 := h 1262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8938 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8938 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8353, some c8367, some c497, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8938 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8938 : lratChecker f8938 p8938 = .success := by decide +kernel
theorem unsat8938 : Unsatisfiable (PosFin 65) f8938 := by
  apply lratCheckerSound f8938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8938
  · intro a ha; simp [p8938] at ha; subst a; trivial
  · exact checked8938
theorem derived8938 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8938 := by
  apply localUnsat_implies_entails f8938 [c8353, c8367, c497] c8938 unsat8938 (by rfl) a
  have h0 : Entails.eval a c8353 := derived8353 a h
  have h1 : Entails.eval a c8367 := derived8367 a h
  have h2 : Entails.eval a c497 := h 496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8939 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8939 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8927, some c8935, some c8937, some c8659, some c8595, some c8643, some c8577, some c8644, some c8938, some c8354, some c2178, some c2170, some c8642, some c8640, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8939 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8939 : lratChecker f8939 p8939 = .success := by decide +kernel
theorem unsat8939 : Unsatisfiable (PosFin 65) f8939 := by
  apply lratCheckerSound f8939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8939
  · intro a ha; simp [p8939] at ha; subst a; trivial
  · exact checked8939
theorem derived8939 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8939 := by
  apply localUnsat_implies_entails f8939 [c8927, c8935, c8937, c8659, c8595, c8643, c8577, c8644, c8938, c8354, c2178, c2170, c8642, c8640] c8939 unsat8939 (by rfl) a
  have h0 : Entails.eval a c8927 := derived8927 a h
  have h1 : Entails.eval a c8935 := derived8935 a h
  have h2 : Entails.eval a c8937 := derived8937 a h
  have h3 : Entails.eval a c8659 := derived8659 a h
  have h4 : Entails.eval a c8595 := derived8595 a h
  have h5 : Entails.eval a c8643 := derived8643 a h
  have h6 : Entails.eval a c8577 := derived8577 a h
  have h7 : Entails.eval a c8644 := derived8644 a h
  have h8 : Entails.eval a c8938 := derived8938 a h
  have h9 : Entails.eval a c8354 := derived8354 a h
  have h10 : Entails.eval a c2178 := h 2177 (by decide)
  have h11 : Entails.eval a c2170 := h 2169 (by decide)
  have h12 : Entails.eval a c8642 := derived8642 a h
  have h13 : Entails.eval a c8640 := derived8640 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8940 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8940 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8860, some c8002, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8940 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8940 : lratChecker f8940 p8940 = .success := by decide +kernel
theorem unsat8940 : Unsatisfiable (PosFin 65) f8940 := by
  apply lratCheckerSound f8940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8940
  · intro a ha; simp [p8940] at ha; subst a; trivial
  · exact checked8940
theorem derived8940 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8940 := by
  apply localUnsat_implies_entails f8940 [c8860, c8002] c8940 unsat8940 (by rfl) a
  have h0 : Entails.eval a c8860 := derived8860 a h
  have h1 : Entails.eval a c8002 := derived8002 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8941 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8941 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1574, some c1259, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8941 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8941 : lratChecker f8941 p8941 = .success := by decide +kernel
theorem unsat8941 : Unsatisfiable (PosFin 65) f8941 := by
  apply lratCheckerSound f8941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8941
  · intro a ha; simp [p8941] at ha; subst a; trivial
  · exact checked8941
theorem derived8941 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8941 := by
  apply localUnsat_implies_entails f8941 [c1574, c1259] c8941 unsat8941 (by rfl) a
  have h0 : Entails.eval a c1574 := h 1573 (by decide)
  have h1 : Entails.eval a c1259 := h 1258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8942 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8942 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8514, some c1252, some c1608, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8942 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8942 : lratChecker f8942 p8942 = .success := by decide +kernel
theorem unsat8942 : Unsatisfiable (PosFin 65) f8942 := by
  apply lratCheckerSound f8942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8942
  · intro a ha; simp [p8942] at ha; subst a; trivial
  · exact checked8942
theorem derived8942 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8942 := by
  apply localUnsat_implies_entails f8942 [c8514, c1252, c1608] c8942 unsat8942 (by rfl) a
  have h0 : Entails.eval a c8514 := derived8514 a h
  have h1 : Entails.eval a c1252 := h 1251 (by decide)
  have h2 : Entails.eval a c1608 := h 1607 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8943 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8943 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c454, some c434, some c8501, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8943 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8943 : lratChecker f8943 p8943 = .success := by decide +kernel
theorem unsat8943 : Unsatisfiable (PosFin 65) f8943 := by
  apply lratCheckerSound f8943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8943
  · intro a ha; simp [p8943] at ha; subst a; trivial
  · exact checked8943
theorem derived8943 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8943 := by
  apply localUnsat_implies_entails f8943 [c454, c434, c8501] c8943 unsat8943 (by rfl) a
  have h0 : Entails.eval a c454 := h 453 (by decide)
  have h1 : Entails.eval a c434 := h 433 (by decide)
  have h2 : Entails.eval a c8501 := derived8501 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8944 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8944 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8940, some c8265, some c8942, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8944 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8944 : lratChecker f8944 p8944 = .success := by decide +kernel
theorem unsat8944 : Unsatisfiable (PosFin 65) f8944 := by
  apply lratCheckerSound f8944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8944
  · intro a ha; simp [p8944] at ha; subst a; trivial
  · exact checked8944
theorem derived8944 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8944 := by
  apply localUnsat_implies_entails f8944 [c8940, c8265, c8942] c8944 unsat8944 (by rfl) a
  have h0 : Entails.eval a c8940 := derived8940 a h
  have h1 : Entails.eval a c8265 := derived8265 a h
  have h2 : Entails.eval a c8942 := derived8942 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8945 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8945 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8940, some c8944, some c8098, some c439, some c434, some c8502, some c8943, some c8482, some c473, some c8941, some c8877, some c7316, some c1264, some c1262, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8945 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8945 : lratChecker f8945 p8945 = .success := by decide +kernel
theorem unsat8945 : Unsatisfiable (PosFin 65) f8945 := by
  apply lratCheckerSound f8945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8945
  · intro a ha; simp [p8945] at ha; subst a; trivial
  · exact checked8945
theorem derived8945 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8945 := by
  apply localUnsat_implies_entails f8945 [c8940, c8944, c8098, c439, c434, c8502, c8943, c8482, c473, c8941, c8877, c7316, c1264, c1262] c8945 unsat8945 (by rfl) a
  have h0 : Entails.eval a c8940 := derived8940 a h
  have h1 : Entails.eval a c8944 := derived8944 a h
  have h2 : Entails.eval a c8098 := derived8098 a h
  have h3 : Entails.eval a c439 := h 438 (by decide)
  have h4 : Entails.eval a c434 := h 433 (by decide)
  have h5 : Entails.eval a c8502 := derived8502 a h
  have h6 : Entails.eval a c8943 := derived8943 a h
  have h7 : Entails.eval a c8482 := derived8482 a h
  have h8 : Entails.eval a c473 := h 472 (by decide)
  have h9 : Entails.eval a c8941 := derived8941 a h
  have h10 : Entails.eval a c8877 := derived8877 a h
  have h11 : Entails.eval a c7316 := derived7316 a h
  have h12 : Entails.eval a c1264 := h 1263 (by decide)
  have h13 : Entails.eval a c1262 := h 1261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8946 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8946 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1932, some c1895, some c574, some c569, some c557, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8946 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8946 : lratChecker f8946 p8946 = .success := by decide +kernel
theorem unsat8946 : Unsatisfiable (PosFin 65) f8946 := by
  apply lratCheckerSound f8946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8946
  · intro a ha; simp [p8946] at ha; subst a; trivial
  · exact checked8946
theorem derived8946 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8946 := by
  apply localUnsat_implies_entails f8946 [c1932, c1895, c574, c569, c557] c8946 unsat8946 (by rfl) a
  have h0 : Entails.eval a c1932 := h 1931 (by decide)
  have h1 : Entails.eval a c1895 := h 1894 (by decide)
  have h2 : Entails.eval a c574 := h 573 (by decide)
  have h3 : Entails.eval a c569 := h 568 (by decide)
  have h4 : Entails.eval a c557 := h 556 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8947 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8947 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1923, some c1912, some c2622, some c8503, some c2221, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8947 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8947 : lratChecker f8947 p8947 = .success := by decide +kernel
theorem unsat8947 : Unsatisfiable (PosFin 65) f8947 := by
  apply lratCheckerSound f8947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8947
  · intro a ha; simp [p8947] at ha; subst a; trivial
  · exact checked8947
theorem derived8947 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8947 := by
  apply localUnsat_implies_entails f8947 [c1923, c1912, c2622, c8503, c2221] c8947 unsat8947 (by rfl) a
  have h0 : Entails.eval a c1923 := h 1922 (by decide)
  have h1 : Entails.eval a c1912 := h 1911 (by decide)
  have h2 : Entails.eval a c2622 := h 2621 (by decide)
  have h3 : Entails.eval a c8503 := derived8503 a h
  have h4 : Entails.eval a c2221 := h 2220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8948 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8948 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c610, some c595, some c599, some c590, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8948 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8948 : lratChecker f8948 p8948 = .success := by decide +kernel
theorem unsat8948 : Unsatisfiable (PosFin 65) f8948 := by
  apply lratCheckerSound f8948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8948
  · intro a ha; simp [p8948] at ha; subst a; trivial
  · exact checked8948
theorem derived8948 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8948 := by
  apply localUnsat_implies_entails f8948 [c610, c595, c599, c590] c8948 unsat8948 (by rfl) a
  have h0 : Entails.eval a c610 := h 609 (by decide)
  have h1 : Entails.eval a c595 := h 594 (by decide)
  have h2 : Entails.eval a c599 := h 598 (by decide)
  have h3 : Entails.eval a c590 := h 589 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8949 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8949 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8947, some c8948, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8949 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8949 : lratChecker f8949 p8949 = .success := by decide +kernel
theorem unsat8949 : Unsatisfiable (PosFin 65) f8949 := by
  apply lratCheckerSound f8949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8949
  · intro a ha; simp [p8949] at ha; subst a; trivial
  · exact checked8949
theorem derived8949 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8949 := by
  apply localUnsat_implies_entails f8949 [c8947, c8948] c8949 unsat8949 (by rfl) a
  have h0 : Entails.eval a c8947 := derived8947 a h
  have h1 : Entails.eval a c8948 := derived8948 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8950 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8950 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8877, some c1923, some c1926, some c2145, some c7316, some c1264, some c1262, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8950 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8950 : lratChecker f8950 p8950 = .success := by decide +kernel
theorem unsat8950 : Unsatisfiable (PosFin 65) f8950 := by
  apply lratCheckerSound f8950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8950
  · intro a ha; simp [p8950] at ha; subst a; trivial
  · exact checked8950
theorem derived8950 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8950 := by
  apply localUnsat_implies_entails f8950 [c8877, c1923, c1926, c2145, c7316, c1264, c1262] c8950 unsat8950 (by rfl) a
  have h0 : Entails.eval a c8877 := derived8877 a h
  have h1 : Entails.eval a c1923 := h 1922 (by decide)
  have h2 : Entails.eval a c1926 := h 1925 (by decide)
  have h3 : Entails.eval a c2145 := h 2144 (by decide)
  have h4 : Entails.eval a c7316 := derived7316 a h
  have h5 : Entails.eval a c1264 := h 1263 (by decide)
  have h6 : Entails.eval a c1262 := h 1261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8951 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8951 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8945, some c8946, some c8940, some c8877, some c8949, some c8950, some c8098, some c8492, some c8336, some c8418, some c1812, some c2145, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8951 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8951 : lratChecker f8951 p8951 = .success := by decide +kernel
theorem unsat8951 : Unsatisfiable (PosFin 65) f8951 := by
  apply lratCheckerSound f8951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8951
  · intro a ha; simp [p8951] at ha; subst a; trivial
  · exact checked8951
theorem derived8951 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8951 := by
  apply localUnsat_implies_entails f8951 [c8945, c8946, c8940, c8877, c8949, c8950, c8098, c8492, c8336, c8418, c1812, c2145] c8951 unsat8951 (by rfl) a
  have h0 : Entails.eval a c8945 := derived8945 a h
  have h1 : Entails.eval a c8946 := derived8946 a h
  have h2 : Entails.eval a c8940 := derived8940 a h
  have h3 : Entails.eval a c8877 := derived8877 a h
  have h4 : Entails.eval a c8949 := derived8949 a h
  have h5 : Entails.eval a c8950 := derived8950 a h
  have h6 : Entails.eval a c8098 := derived8098 a h
  have h7 : Entails.eval a c8492 := derived8492 a h
  have h8 : Entails.eval a c8336 := derived8336 a h
  have h9 : Entails.eval a c8418 := derived8418 a h
  have h10 : Entails.eval a c1812 := h 1811 (by decide)
  have h11 : Entails.eval a c2145 := h 2144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8952 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8952 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8939, some c8945, some c8946, some c8951, some c8510, some c8455, some c852, some c8098, some c670, some c2229, some c1033, some c2595, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8952 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8952 : lratChecker f8952 p8952 = .success := by decide +kernel
theorem unsat8952 : Unsatisfiable (PosFin 65) f8952 := by
  apply lratCheckerSound f8952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8952
  · intro a ha; simp [p8952] at ha; subst a; trivial
  · exact checked8952
theorem derived8952 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8952 := by
  apply localUnsat_implies_entails f8952 [c8939, c8945, c8946, c8951, c8510, c8455, c852, c8098, c670, c2229, c1033, c2595] c8952 unsat8952 (by rfl) a
  have h0 : Entails.eval a c8939 := derived8939 a h
  have h1 : Entails.eval a c8945 := derived8945 a h
  have h2 : Entails.eval a c8946 := derived8946 a h
  have h3 : Entails.eval a c8951 := derived8951 a h
  have h4 : Entails.eval a c8510 := derived8510 a h
  have h5 : Entails.eval a c8455 := derived8455 a h
  have h6 : Entails.eval a c852 := h 851 (by decide)
  have h7 : Entails.eval a c8098 := derived8098 a h
  have h8 : Entails.eval a c670 := h 669 (by decide)
  have h9 : Entails.eval a c2229 := h 2228 (by decide)
  have h10 : Entails.eval a c1033 := h 1032 (by decide)
  have h11 : Entails.eval a c2595 := h 2594 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8953 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8953 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8952, some c8623, some c8624, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8953 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8953 : lratChecker f8953 p8953 = .success := by decide +kernel
theorem unsat8953 : Unsatisfiable (PosFin 65) f8953 := by
  apply lratCheckerSound f8953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8953
  · intro a ha; simp [p8953] at ha; subst a; trivial
  · exact checked8953
theorem derived8953 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8953 := by
  apply localUnsat_implies_entails f8953 [c8952, c8623, c8624] c8953 unsat8953 (by rfl) a
  have h0 : Entails.eval a c8952 := derived8952 a h
  have h1 : Entails.eval a c8623 := derived8623 a h
  have h2 : Entails.eval a c8624 := derived8624 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8954 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8954 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8939, some c8953, some c8546, some c8524, some c8098, some c1926, some c1912, some c1910, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8954 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8954 : lratChecker f8954 p8954 = .success := by decide +kernel
theorem unsat8954 : Unsatisfiable (PosFin 65) f8954 := by
  apply lratCheckerSound f8954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8954
  · intro a ha; simp [p8954] at ha; subst a; trivial
  · exact checked8954
theorem derived8954 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8954 := by
  apply localUnsat_implies_entails f8954 [c8939, c8953, c8546, c8524, c8098, c1926, c1912, c1910] c8954 unsat8954 (by rfl) a
  have h0 : Entails.eval a c8939 := derived8939 a h
  have h1 : Entails.eval a c8953 := derived8953 a h
  have h2 : Entails.eval a c8546 := derived8546 a h
  have h3 : Entails.eval a c8524 := derived8524 a h
  have h4 : Entails.eval a c8098 := derived8098 a h
  have h5 : Entails.eval a c1926 := h 1925 (by decide)
  have h6 : Entails.eval a c1912 := h 1911 (by decide)
  have h7 : Entails.eval a c1910 := h 1909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8955 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8955 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8919, some c8378, some c8500, some c1509, some c8917, some c1574, some c1259, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8955 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8955 : lratChecker f8955 p8955 = .success := by decide +kernel
theorem unsat8955 : Unsatisfiable (PosFin 65) f8955 := by
  apply lratCheckerSound f8955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8955
  · intro a ha; simp [p8955] at ha; subst a; trivial
  · exact checked8955
theorem derived8955 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8955 := by
  apply localUnsat_implies_entails f8955 [c8919, c8378, c8500, c1509, c8917, c1574, c1259] c8955 unsat8955 (by rfl) a
  have h0 : Entails.eval a c8919 := derived8919 a h
  have h1 : Entails.eval a c8378 := derived8378 a h
  have h2 : Entails.eval a c8500 := derived8500 a h
  have h3 : Entails.eval a c1509 := h 1508 (by decide)
  have h4 : Entails.eval a c8917 := derived8917 a h
  have h5 : Entails.eval a c1574 := h 1573 (by decide)
  have h6 : Entails.eval a c1259 := h 1258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8956 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8956 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8524, some c8919, some c8473, some c8116, some c8095, some c2055, some c8540, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8956 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8956 : lratChecker f8956 p8956 = .success := by decide +kernel
theorem unsat8956 : Unsatisfiable (PosFin 65) f8956 := by
  apply lratCheckerSound f8956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8956
  · intro a ha; simp [p8956] at ha; subst a; trivial
  · exact checked8956
theorem derived8956 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8956 := by
  apply localUnsat_implies_entails f8956 [c8524, c8919, c8473, c8116, c8095, c2055, c8540] c8956 unsat8956 (by rfl) a
  have h0 : Entails.eval a c8524 := derived8524 a h
  have h1 : Entails.eval a c8919 := derived8919 a h
  have h2 : Entails.eval a c8473 := derived8473 a h
  have h3 : Entails.eval a c8116 := derived8116 a h
  have h4 : Entails.eval a c8095 := derived8095 a h
  have h5 : Entails.eval a c2055 := h 2054 (by decide)
  have h6 : Entails.eval a c8540 := derived8540 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8957 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8957 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8406, some c2175, some c2169, some c2144, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8957 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8957 : lratChecker f8957 p8957 = .success := by decide +kernel
theorem unsat8957 : Unsatisfiable (PosFin 65) f8957 := by
  apply lratCheckerSound f8957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8957
  · intro a ha; simp [p8957] at ha; subst a; trivial
  · exact checked8957
theorem derived8957 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8957 := by
  apply localUnsat_implies_entails f8957 [c8406, c2175, c2169, c2144] c8957 unsat8957 (by rfl) a
  have h0 : Entails.eval a c8406 := derived8406 a h
  have h1 : Entails.eval a c2175 := h 2174 (by decide)
  have h2 : Entails.eval a c2169 := h 2168 (by decide)
  have h3 : Entails.eval a c2144 := h 2143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8958 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8958 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8939, some c8954, some c8919, some c8955, some c8546, some c8524, some c8098, some c8956, some c8957, some c8116, some c7961, some c2055, some c1047, some c659, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8958 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8958 : lratChecker f8958 p8958 = .success := by decide +kernel
theorem unsat8958 : Unsatisfiable (PosFin 65) f8958 := by
  apply lratCheckerSound f8958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8958
  · intro a ha; simp [p8958] at ha; subst a; trivial
  · exact checked8958
theorem derived8958 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8958 := by
  apply localUnsat_implies_entails f8958 [c8939, c8954, c8919, c8955, c8546, c8524, c8098, c8956, c8957, c8116, c7961, c2055, c1047, c659] c8958 unsat8958 (by rfl) a
  have h0 : Entails.eval a c8939 := derived8939 a h
  have h1 : Entails.eval a c8954 := derived8954 a h
  have h2 : Entails.eval a c8919 := derived8919 a h
  have h3 : Entails.eval a c8955 := derived8955 a h
  have h4 : Entails.eval a c8546 := derived8546 a h
  have h5 : Entails.eval a c8524 := derived8524 a h
  have h6 : Entails.eval a c8098 := derived8098 a h
  have h7 : Entails.eval a c8956 := derived8956 a h
  have h8 : Entails.eval a c8957 := derived8957 a h
  have h9 : Entails.eval a c8116 := derived8116 a h
  have h10 : Entails.eval a c7961 := derived7961 a h
  have h11 : Entails.eval a c2055 := h 2054 (by decide)
  have h12 : Entails.eval a c1047 := h 1046 (by decide)
  have h13 : Entails.eval a c659 := h 658 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8959 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8959 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8912, some c8840, some c8922, some c8958, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8959 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8959 : lratChecker f8959 p8959 = .success := by decide +kernel
theorem unsat8959 : Unsatisfiable (PosFin 65) f8959 := by
  apply lratCheckerSound f8959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8959
  · intro a ha; simp [p8959] at ha; subst a; trivial
  · exact checked8959
theorem derived8959 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8959 := by
  apply localUnsat_implies_entails f8959 [c8912, c8840, c8922, c8958] c8959 unsat8959 (by rfl) a
  have h0 : Entails.eval a c8912 := derived8912 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8922 := derived8922 a h
  have h3 : Entails.eval a c8958 := derived8958 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8960 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8960 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8842, some c8913, some c8142, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8960 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8960 : lratChecker f8960 p8960 = .success := by decide +kernel
theorem unsat8960 : Unsatisfiable (PosFin 65) f8960 := by
  apply lratCheckerSound f8960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8960
  · intro a ha; simp [p8960] at ha; subst a; trivial
  · exact checked8960
theorem derived8960 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8960 := by
  apply localUnsat_implies_entails f8960 [c8840, c8842, c8913, c8142] c8960 unsat8960 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8842 := derived8842 a h
  have h2 : Entails.eval a c8913 := derived8913 a h
  have h3 : Entails.eval a c8142 := derived8142 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8961 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8961 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8948, some c8503, some c2395, some c2217, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8961 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8961 : lratChecker f8961 p8961 = .success := by decide +kernel
theorem unsat8961 : Unsatisfiable (PosFin 65) f8961 := by
  apply lratCheckerSound f8961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8961
  · intro a ha; simp [p8961] at ha; subst a; trivial
  · exact checked8961
theorem derived8961 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8961 := by
  apply localUnsat_implies_entails f8961 [c8948, c8503, c2395, c2217] c8961 unsat8961 (by rfl) a
  have h0 : Entails.eval a c8948 := derived8948 a h
  have h1 : Entails.eval a c8503 := derived8503 a h
  have h2 : Entails.eval a c2395 := h 2394 (by decide)
  have h3 : Entails.eval a c2217 := h 2216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8962 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8962 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8948, some c8123, some c8347, some c8321, some c2247, some c1576, some c1036, some c1281, some c8333, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8962 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8962 : lratChecker f8962 p8962 = .success := by decide +kernel
theorem unsat8962 : Unsatisfiable (PosFin 65) f8962 := by
  apply lratCheckerSound f8962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8962
  · intro a ha; simp [p8962] at ha; subst a; trivial
  · exact checked8962
theorem derived8962 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8962 := by
  apply localUnsat_implies_entails f8962 [c8948, c8123, c8347, c8321, c2247, c1576, c1036, c1281, c8333] c8962 unsat8962 (by rfl) a
  have h0 : Entails.eval a c8948 := derived8948 a h
  have h1 : Entails.eval a c8123 := derived8123 a h
  have h2 : Entails.eval a c8347 := derived8347 a h
  have h3 : Entails.eval a c8321 := derived8321 a h
  have h4 : Entails.eval a c2247 := h 2246 (by decide)
  have h5 : Entails.eval a c1576 := h 1575 (by decide)
  have h6 : Entails.eval a c1036 := h 1035 (by decide)
  have h7 : Entails.eval a c1281 := h 1280 (by decide)
  have h8 : Entails.eval a c8333 := derived8333 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8963 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8963 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8347, some c8321, some c8948, some c8962, some c1297, some c2265, some c1608, some c1040, some c8333, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8963 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8963 : lratChecker f8963 p8963 = .success := by decide +kernel
theorem unsat8963 : Unsatisfiable (PosFin 65) f8963 := by
  apply lratCheckerSound f8963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8963
  · intro a ha; simp [p8963] at ha; subst a; trivial
  · exact checked8963
theorem derived8963 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8963 := by
  apply localUnsat_implies_entails f8963 [c8123, c8347, c8321, c8948, c8962, c1297, c2265, c1608, c1040, c8333] c8963 unsat8963 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8347 := derived8347 a h
  have h2 : Entails.eval a c8321 := derived8321 a h
  have h3 : Entails.eval a c8948 := derived8948 a h
  have h4 : Entails.eval a c8962 := derived8962 a h
  have h5 : Entails.eval a c1297 := h 1296 (by decide)
  have h6 : Entails.eval a c2265 := h 2264 (by decide)
  have h7 : Entails.eval a c1608 := h 1607 (by decide)
  have h8 : Entails.eval a c1040 := h 1039 (by decide)
  have h9 : Entails.eval a c8333 := derived8333 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8964 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8964 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1576, some c8418, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8964 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8964 : lratChecker f8964 p8964 = .success := by decide +kernel
theorem unsat8964 : Unsatisfiable (PosFin 65) f8964 := by
  apply lratCheckerSound f8964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8964
  · intro a ha; simp [p8964] at ha; subst a; trivial
  · exact checked8964
theorem derived8964 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8964 := by
  apply localUnsat_implies_entails f8964 [c1576, c8418] c8964 unsat8964 (by rfl) a
  have h0 : Entails.eval a c1576 := h 1575 (by decide)
  have h1 : Entails.eval a c8418 := derived8418 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8965 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8965 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8347, some c8321, some c8963, some c8964, some c1297, some c1193, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8965 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8965 : lratChecker f8965 p8965 = .success := by decide +kernel
theorem unsat8965 : Unsatisfiable (PosFin 65) f8965 := by
  apply lratCheckerSound f8965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8965
  · intro a ha; simp [p8965] at ha; subst a; trivial
  · exact checked8965
theorem derived8965 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8965 := by
  apply localUnsat_implies_entails f8965 [c8123, c8347, c8321, c8963, c8964, c1297, c1193] c8965 unsat8965 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8347 := derived8347 a h
  have h2 : Entails.eval a c8321 := derived8321 a h
  have h3 : Entails.eval a c8963 := derived8963 a h
  have h4 : Entails.eval a c8964 := derived8964 a h
  have h5 : Entails.eval a c1297 := h 1296 (by decide)
  have h6 : Entails.eval a c1193 := h 1192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8966 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8966 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8347, some c8321, some c8544, some c8336, some c1947, some c8268, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8966 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8966 : lratChecker f8966 p8966 = .success := by decide +kernel
theorem unsat8966 : Unsatisfiable (PosFin 65) f8966 := by
  apply lratCheckerSound f8966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8966
  · intro a ha; simp [p8966] at ha; subst a; trivial
  · exact checked8966
theorem derived8966 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8966 := by
  apply localUnsat_implies_entails f8966 [c8123, c8347, c8321, c8544, c8336, c1947, c8268] c8966 unsat8966 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8347 := derived8347 a h
  have h2 : Entails.eval a c8321 := derived8321 a h
  have h3 : Entails.eval a c8544 := derived8544 a h
  have h4 : Entails.eval a c8336 := derived8336 a h
  have h5 : Entails.eval a c1947 := h 1946 (by decide)
  have h6 : Entails.eval a c8268 := derived8268 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8967 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8967 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8960, some c8840, some c8948, some c8912, some c8959, some c8123, some c8347, some c8331, some c8966, some c8965, some c8321, some c8536, some c8670, some c1036, some c8239, some c1281, some c2627, some c3015, some c3014, some c75, some c8743, some c2662, some c1464, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8967 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8967 : lratChecker f8967 p8967 = .success := by decide +kernel
theorem unsat8967 : Unsatisfiable (PosFin 65) f8967 := by
  apply lratCheckerSound f8967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8967
  · intro a ha; simp [p8967] at ha; subst a; trivial
  · exact checked8967
theorem derived8967 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8967 := by
  apply localUnsat_implies_entails f8967 [c8960, c8840, c8948, c8912, c8959, c8123, c8347, c8331, c8966, c8965, c8321, c8536, c8670, c1036, c8239, c1281, c2627, c3015, c3014, c75, c8743, c2662, c1464] c8967 unsat8967 (by rfl) a
  have h0 : Entails.eval a c8960 := derived8960 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8948 := derived8948 a h
  have h3 : Entails.eval a c8912 := derived8912 a h
  have h4 : Entails.eval a c8959 := derived8959 a h
  have h5 : Entails.eval a c8123 := derived8123 a h
  have h6 : Entails.eval a c8347 := derived8347 a h
  have h7 : Entails.eval a c8331 := derived8331 a h
  have h8 : Entails.eval a c8966 := derived8966 a h
  have h9 : Entails.eval a c8965 := derived8965 a h
  have h10 : Entails.eval a c8321 := derived8321 a h
  have h11 : Entails.eval a c8536 := derived8536 a h
  have h12 : Entails.eval a c8670 := derived8670 a h
  have h13 : Entails.eval a c1036 := h 1035 (by decide)
  have h14 : Entails.eval a c8239 := derived8239 a h
  have h15 : Entails.eval a c1281 := h 1280 (by decide)
  have h16 : Entails.eval a c2627 := h 2626 (by decide)
  have h17 : Entails.eval a c3015 := h 3014 (by decide)
  have h18 : Entails.eval a c3014 := h 3013 (by decide)
  have h19 : Entails.eval a c75 := h 74 (by decide)
  have h20 : Entails.eval a c8743 := derived8743 a h
  have h21 : Entails.eval a c2662 := h 2661 (by decide)
  have h22 : Entails.eval a c1464 := h 1463 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8968 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8968 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8960, some c8840, some c8948, some c8912, some c8967, some c1040, some c8123, some c8347, some c8331, some c8966, some c1608, some c8321, some c2265, some c8959, some c1297, some c8965, some c8536, some c8670, some c2508, some c2091, some c1302, some c824, some c2502, some c8743, some c658, some c6680, some c6676, some c46, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8968 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked8968 : lratChecker f8968 p8968 = .success := by decide +kernel
theorem unsat8968 : Unsatisfiable (PosFin 65) f8968 := by
  apply lratCheckerSound f8968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8968
  · intro a ha; simp [p8968] at ha; subst a; trivial
  · exact checked8968
theorem derived8968 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8968 := by
  apply localUnsat_implies_entails f8968 [c8960, c8840, c8948, c8912, c8967, c1040, c8123, c8347, c8331, c8966, c1608, c8321, c2265, c8959, c1297, c8965, c8536, c8670, c2508, c2091, c1302, c824, c2502, c8743, c658, c6680, c6676, c46] c8968 unsat8968 (by rfl) a
  have h0 : Entails.eval a c8960 := derived8960 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8948 := derived8948 a h
  have h3 : Entails.eval a c8912 := derived8912 a h
  have h4 : Entails.eval a c8967 := derived8967 a h
  have h5 : Entails.eval a c1040 := h 1039 (by decide)
  have h6 : Entails.eval a c8123 := derived8123 a h
  have h7 : Entails.eval a c8347 := derived8347 a h
  have h8 : Entails.eval a c8331 := derived8331 a h
  have h9 : Entails.eval a c8966 := derived8966 a h
  have h10 : Entails.eval a c1608 := h 1607 (by decide)
  have h11 : Entails.eval a c8321 := derived8321 a h
  have h12 : Entails.eval a c2265 := h 2264 (by decide)
  have h13 : Entails.eval a c8959 := derived8959 a h
  have h14 : Entails.eval a c1297 := h 1296 (by decide)
  have h15 : Entails.eval a c8965 := derived8965 a h
  have h16 : Entails.eval a c8536 := derived8536 a h
  have h17 : Entails.eval a c8670 := derived8670 a h
  have h18 : Entails.eval a c2508 := h 2507 (by decide)
  have h19 : Entails.eval a c2091 := h 2090 (by decide)
  have h20 : Entails.eval a c1302 := h 1301 (by decide)
  have h21 : Entails.eval a c824 := h 823 (by decide)
  have h22 : Entails.eval a c2502 := h 2501 (by decide)
  have h23 : Entails.eval a c8743 := derived8743 a h
  have h24 : Entails.eval a c658 := h 657 (by decide)
  have h25 : Entails.eval a c6680 := derived6680 a h
  have h26 : Entails.eval a c6676 := derived6676 a h
  have h27 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8969 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8969 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8912, some c8959, some c8960, some c8123, some c8347, some c8331, some c8966, some c8965, some c8321, some c8536, some c8670, some c8948, some c8967, some c1297, some c1608, some c8968, some c2395, some c2384, some c2369, some c1867, some c1881, some c8743, some c2490, some c6684, some c6680, some c6676, some c965, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8969 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked8969 : lratChecker f8969 p8969 = .success := by decide +kernel
theorem unsat8969 : Unsatisfiable (PosFin 65) f8969 := by
  apply lratCheckerSound f8969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8969
  · intro a ha; simp [p8969] at ha; subst a; trivial
  · exact checked8969
theorem derived8969 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8969 := by
  apply localUnsat_implies_entails f8969 [c8840, c8912, c8959, c8960, c8123, c8347, c8331, c8966, c8965, c8321, c8536, c8670, c8948, c8967, c1297, c1608, c8968, c2395, c2384, c2369, c1867, c1881, c8743, c2490, c6684, c6680, c6676, c965] c8969 unsat8969 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8912 := derived8912 a h
  have h2 : Entails.eval a c8959 := derived8959 a h
  have h3 : Entails.eval a c8960 := derived8960 a h
  have h4 : Entails.eval a c8123 := derived8123 a h
  have h5 : Entails.eval a c8347 := derived8347 a h
  have h6 : Entails.eval a c8331 := derived8331 a h
  have h7 : Entails.eval a c8966 := derived8966 a h
  have h8 : Entails.eval a c8965 := derived8965 a h
  have h9 : Entails.eval a c8321 := derived8321 a h
  have h10 : Entails.eval a c8536 := derived8536 a h
  have h11 : Entails.eval a c8670 := derived8670 a h
  have h12 : Entails.eval a c8948 := derived8948 a h
  have h13 : Entails.eval a c8967 := derived8967 a h
  have h14 : Entails.eval a c1297 := h 1296 (by decide)
  have h15 : Entails.eval a c1608 := h 1607 (by decide)
  have h16 : Entails.eval a c8968 := derived8968 a h
  have h17 : Entails.eval a c2395 := h 2394 (by decide)
  have h18 : Entails.eval a c2384 := h 2383 (by decide)
  have h19 : Entails.eval a c2369 := h 2368 (by decide)
  have h20 : Entails.eval a c1867 := h 1866 (by decide)
  have h21 : Entails.eval a c1881 := h 1880 (by decide)
  have h22 : Entails.eval a c8743 := derived8743 a h
  have h23 : Entails.eval a c2490 := h 2489 (by decide)
  have h24 : Entails.eval a c6684 := derived6684 a h
  have h25 : Entails.eval a c6680 := derived6680 a h
  have h26 : Entails.eval a c6676 := derived6676 a h
  have h27 : Entails.eval a c965 := h 964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8970 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8970 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8959, some c8912, some c8840, some c8960, some c8123, some c8347, some c8321, some c8331, some c8966, some c8965, some c8969, some c8530, some c1297, some c1193, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8970 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8970 : lratChecker f8970 p8970 = .success := by decide +kernel
theorem unsat8970 : Unsatisfiable (PosFin 65) f8970 := by
  apply lratCheckerSound f8970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8970
  · intro a ha; simp [p8970] at ha; subst a; trivial
  · exact checked8970
theorem derived8970 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8970 := by
  apply localUnsat_implies_entails f8970 [c8959, c8912, c8840, c8960, c8123, c8347, c8321, c8331, c8966, c8965, c8969, c8530, c1297, c1193] c8970 unsat8970 (by rfl) a
  have h0 : Entails.eval a c8959 := derived8959 a h
  have h1 : Entails.eval a c8912 := derived8912 a h
  have h2 : Entails.eval a c8840 := derived8840 a h
  have h3 : Entails.eval a c8960 := derived8960 a h
  have h4 : Entails.eval a c8123 := derived8123 a h
  have h5 : Entails.eval a c8347 := derived8347 a h
  have h6 : Entails.eval a c8321 := derived8321 a h
  have h7 : Entails.eval a c8331 := derived8331 a h
  have h8 : Entails.eval a c8966 := derived8966 a h
  have h9 : Entails.eval a c8965 := derived8965 a h
  have h10 : Entails.eval a c8969 := derived8969 a h
  have h11 : Entails.eval a c8530 := derived8530 a h
  have h12 : Entails.eval a c1297 := h 1296 (by decide)
  have h13 : Entails.eval a c1193 := h 1192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8971 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8971 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8351, some c8376, some c8058, some c8066, some c8079, some c1279, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8971 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8971 : lratChecker f8971 p8971 = .success := by decide +kernel
theorem unsat8971 : Unsatisfiable (PosFin 65) f8971 := by
  apply lratCheckerSound f8971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8971
  · intro a ha; simp [p8971] at ha; subst a; trivial
  · exact checked8971
theorem derived8971 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8971 := by
  apply localUnsat_implies_entails f8971 [c8351, c8376, c8058, c8066, c8079, c1279] c8971 unsat8971 (by rfl) a
  have h0 : Entails.eval a c8351 := derived8351 a h
  have h1 : Entails.eval a c8376 := derived8376 a h
  have h2 : Entails.eval a c8058 := derived8058 a h
  have h3 : Entails.eval a c8066 := derived8066 a h
  have h4 : Entails.eval a c8079 := derived8079 a h
  have h5 : Entails.eval a c1279 := h 1278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8972 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8972 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8970, some c8959, some c8912, some c8840, some c8670, some c8214, some c8351, some c8971, some c8133, some c8286, some c8352, some c8287, some c1576, some c8239, some c951, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8972 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8972 : lratChecker f8972 p8972 = .success := by decide +kernel
theorem unsat8972 : Unsatisfiable (PosFin 65) f8972 := by
  apply lratCheckerSound f8972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8972
  · intro a ha; simp [p8972] at ha; subst a; trivial
  · exact checked8972
theorem derived8972 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8972 := by
  apply localUnsat_implies_entails f8972 [c8970, c8959, c8912, c8840, c8670, c8214, c8351, c8971, c8133, c8286, c8352, c8287, c1576, c8239, c951] c8972 unsat8972 (by rfl) a
  have h0 : Entails.eval a c8970 := derived8970 a h
  have h1 : Entails.eval a c8959 := derived8959 a h
  have h2 : Entails.eval a c8912 := derived8912 a h
  have h3 : Entails.eval a c8840 := derived8840 a h
  have h4 : Entails.eval a c8670 := derived8670 a h
  have h5 : Entails.eval a c8214 := derived8214 a h
  have h6 : Entails.eval a c8351 := derived8351 a h
  have h7 : Entails.eval a c8971 := derived8971 a h
  have h8 : Entails.eval a c8133 := derived8133 a h
  have h9 : Entails.eval a c8286 := derived8286 a h
  have h10 : Entails.eval a c8352 := derived8352 a h
  have h11 : Entails.eval a c8287 := derived8287 a h
  have h12 : Entails.eval a c1576 := h 1575 (by decide)
  have h13 : Entails.eval a c8239 := derived8239 a h
  have h14 : Entails.eval a c951 := h 950 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8973 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8973 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8376, some c8362, some c8351, some c8058, some c8067, some c8079, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8973 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8973 : lratChecker f8973 p8973 = .success := by decide +kernel
theorem unsat8973 : Unsatisfiable (PosFin 65) f8973 := by
  apply lratCheckerSound f8973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8973
  · intro a ha; simp [p8973] at ha; subst a; trivial
  · exact checked8973
theorem derived8973 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8973 := by
  apply localUnsat_implies_entails f8973 [c8376, c8362, c8351, c8058, c8067, c8079] c8973 unsat8973 (by rfl) a
  have h0 : Entails.eval a c8376 := derived8376 a h
  have h1 : Entails.eval a c8362 := derived8362 a h
  have h2 : Entails.eval a c8351 := derived8351 a h
  have h3 : Entails.eval a c8058 := derived8058 a h
  have h4 : Entails.eval a c8067 := derived8067 a h
  have h5 : Entails.eval a c8079 := derived8079 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8974 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8974 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8353, some c1326, some c8104, some c8239, some c583, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8974 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8974 : lratChecker f8974 p8974 = .success := by decide +kernel
theorem unsat8974 : Unsatisfiable (PosFin 65) f8974 := by
  apply lratCheckerSound f8974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8974
  · intro a ha; simp [p8974] at ha; subst a; trivial
  · exact checked8974
theorem derived8974 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8974 := by
  apply localUnsat_implies_entails f8974 [c8840, c8353, c1326, c8104, c8239, c583] c8974 unsat8974 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8353 := derived8353 a h
  have h2 : Entails.eval a c1326 := h 1325 (by decide)
  have h3 : Entails.eval a c8104 := derived8104 a h
  have h4 : Entails.eval a c8239 := derived8239 a h
  have h5 : Entails.eval a c583 := h 582 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8975 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8975 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8970, some c8959, some c8912, some c8840, some c8670, some c8972, some c8973, some c8133, some c8350, some c8351, some c8974, some c8354, some c2145, some c8239, some c2108, some c1308, some c7316, some c936, some c147, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8975 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8975 : lratChecker f8975 p8975 = .success := by decide +kernel
theorem unsat8975 : Unsatisfiable (PosFin 65) f8975 := by
  apply lratCheckerSound f8975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8975
  · intro a ha; simp [p8975] at ha; subst a; trivial
  · exact checked8975
theorem derived8975 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8975 := by
  apply localUnsat_implies_entails f8975 [c8970, c8959, c8912, c8840, c8670, c8972, c8973, c8133, c8350, c8351, c8974, c8354, c2145, c8239, c2108, c1308, c7316, c936, c147] c8975 unsat8975 (by rfl) a
  have h0 : Entails.eval a c8970 := derived8970 a h
  have h1 : Entails.eval a c8959 := derived8959 a h
  have h2 : Entails.eval a c8912 := derived8912 a h
  have h3 : Entails.eval a c8840 := derived8840 a h
  have h4 : Entails.eval a c8670 := derived8670 a h
  have h5 : Entails.eval a c8972 := derived8972 a h
  have h6 : Entails.eval a c8973 := derived8973 a h
  have h7 : Entails.eval a c8133 := derived8133 a h
  have h8 : Entails.eval a c8350 := derived8350 a h
  have h9 : Entails.eval a c8351 := derived8351 a h
  have h10 : Entails.eval a c8974 := derived8974 a h
  have h11 : Entails.eval a c8354 := derived8354 a h
  have h12 : Entails.eval a c2145 := h 2144 (by decide)
  have h13 : Entails.eval a c8239 := derived8239 a h
  have h14 : Entails.eval a c2108 := h 2107 (by decide)
  have h15 : Entails.eval a c1308 := h 1307 (by decide)
  have h16 : Entails.eval a c7316 := derived7316 a h
  have h17 : Entails.eval a c936 := h 935 (by decide)
  have h18 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8976 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8976 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8376, some c8351, some c8153, some c2449, some c8055, some c8609, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8976 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8976 : lratChecker f8976 p8976 = .success := by decide +kernel
theorem unsat8976 : Unsatisfiable (PosFin 65) f8976 := by
  apply lratCheckerSound f8976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8976
  · intro a ha; simp [p8976] at ha; subst a; trivial
  · exact checked8976
theorem derived8976 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8976 := by
  apply localUnsat_implies_entails f8976 [c8376, c8351, c8153, c2449, c8055, c8609] c8976 unsat8976 (by rfl) a
  have h0 : Entails.eval a c8376 := derived8376 a h
  have h1 : Entails.eval a c8351 := derived8351 a h
  have h2 : Entails.eval a c8153 := derived8153 a h
  have h3 : Entails.eval a c2449 := h 2448 (by decide)
  have h4 : Entails.eval a c8055 := derived8055 a h
  have h5 : Entails.eval a c8609 := derived8609 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8977 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8977 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8376, some c8976, some c8155, some c2590, some c1315, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8977 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8977 : lratChecker f8977 p8977 = .success := by decide +kernel
theorem unsat8977 : Unsatisfiable (PosFin 65) f8977 := by
  apply lratCheckerSound f8977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8977
  · intro a ha; simp [p8977] at ha; subst a; trivial
  · exact checked8977
theorem derived8977 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8977 := by
  apply localUnsat_implies_entails f8977 [c8376, c8976, c8155, c2590, c1315] c8977 unsat8977 (by rfl) a
  have h0 : Entails.eval a c8376 := derived8376 a h
  have h1 : Entails.eval a c8976 := derived8976 a h
  have h2 : Entails.eval a c8155 := derived8155 a h
  have h3 : Entails.eval a c2590 := h 2589 (by decide)
  have h4 : Entails.eval a c1315 := h 1314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8978 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8978 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8970, some c8975, some c8938, some c8959, some c8912, some c8214, some c8351, some c8977, some c8133, some c8286, some c8352, some c8287, some c1281, some c8077, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8978 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8978 : lratChecker f8978 p8978 = .success := by decide +kernel
theorem unsat8978 : Unsatisfiable (PosFin 65) f8978 := by
  apply lratCheckerSound f8978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8978
  · intro a ha; simp [p8978] at ha; subst a; trivial
  · exact checked8978
theorem derived8978 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8978 := by
  apply localUnsat_implies_entails f8978 [c8840, c8970, c8975, c8938, c8959, c8912, c8214, c8351, c8977, c8133, c8286, c8352, c8287, c1281, c8077] c8978 unsat8978 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8970 := derived8970 a h
  have h2 : Entails.eval a c8975 := derived8975 a h
  have h3 : Entails.eval a c8938 := derived8938 a h
  have h4 : Entails.eval a c8959 := derived8959 a h
  have h5 : Entails.eval a c8912 := derived8912 a h
  have h6 : Entails.eval a c8214 := derived8214 a h
  have h7 : Entails.eval a c8351 := derived8351 a h
  have h8 : Entails.eval a c8977 := derived8977 a h
  have h9 : Entails.eval a c8133 := derived8133 a h
  have h10 : Entails.eval a c8286 := derived8286 a h
  have h11 : Entails.eval a c8352 := derived8352 a h
  have h12 : Entails.eval a c8287 := derived8287 a h
  have h13 : Entails.eval a c1281 := h 1280 (by decide)
  have h14 : Entails.eval a c8077 := derived8077 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8979 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8979 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8362, some c8977, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8979 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8979 : lratChecker f8979 p8979 = .success := by decide +kernel
theorem unsat8979 : Unsatisfiable (PosFin 65) f8979 := by
  apply lratCheckerSound f8979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8979
  · intro a ha; simp [p8979] at ha; subst a; trivial
  · exact checked8979
theorem derived8979 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8979 := by
  apply localUnsat_implies_entails f8979 [c8362, c8977] c8979 unsat8979 (by rfl) a
  have h0 : Entails.eval a c8362 := derived8362 a h
  have h1 : Entails.eval a c8977 := derived8977 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8980 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8980 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8970, some c8959, some c8840, some c8975, some c8938, some c8978, some c8979, some c8350, some c8351, some c8354, some c8239, some c1308, some c145, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8980 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8980 : lratChecker f8980 p8980 = .success := by decide +kernel
theorem unsat8980 : Unsatisfiable (PosFin 65) f8980 := by
  apply lratCheckerSound f8980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8980
  · intro a ha; simp [p8980] at ha; subst a; trivial
  · exact checked8980
theorem derived8980 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8980 := by
  apply localUnsat_implies_entails f8980 [c8970, c8959, c8840, c8975, c8938, c8978, c8979, c8350, c8351, c8354, c8239, c1308, c145] c8980 unsat8980 (by rfl) a
  have h0 : Entails.eval a c8970 := derived8970 a h
  have h1 : Entails.eval a c8959 := derived8959 a h
  have h2 : Entails.eval a c8840 := derived8840 a h
  have h3 : Entails.eval a c8975 := derived8975 a h
  have h4 : Entails.eval a c8938 := derived8938 a h
  have h5 : Entails.eval a c8978 := derived8978 a h
  have h6 : Entails.eval a c8979 := derived8979 a h
  have h7 : Entails.eval a c8350 := derived8350 a h
  have h8 : Entails.eval a c8351 := derived8351 a h
  have h9 : Entails.eval a c8354 := derived8354 a h
  have h10 : Entails.eval a c8239 := derived8239 a h
  have h11 : Entails.eval a c1308 := h 1307 (by decide)
  have h12 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8980

end CochromaticTwenty.Certificates.FixedCore1
