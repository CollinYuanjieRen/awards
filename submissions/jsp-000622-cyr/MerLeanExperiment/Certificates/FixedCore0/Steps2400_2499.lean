import MerLeanExperiment.Certificates.FixedCore0.Steps2300_2399

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9951 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9951 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1939, some c2592, some c9865, some c1457, some c1458, some c9950, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9951 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9951 : lratChecker f9951 p9951 = .success := by decide +kernel
theorem unsat9951 : Unsatisfiable (PosFin 65) f9951 := by
  apply lratCheckerSound f9951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9951
  · intro a ha; simp [p9951] at ha; subst a; trivial
  · exact checked9951
theorem derived9951 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9951 := by
  apply localUnsat_implies_entails f9951 [c9748, c1939, c2592, c9865, c1457, c1458, c9950] c9951 unsat9951 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1939 := h 1938 (by decide)
  have h2 : Entails.eval a c2592 := h 2591 (by decide)
  have h3 : Entails.eval a c9865 := derived9865 a h
  have h4 : Entails.eval a c1457 := h 1456 (by decide)
  have h5 : Entails.eval a c1458 := h 1457 (by decide)
  have h6 : Entails.eval a c9950 := derived9950 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9952 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9952 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9855, some c1939, some c9794, some c4119, some c4139, some c9874, some c9859, some c1918, some c4104, some c1923, some c1922, some c309, some c4109, some c4108, some c4111, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9952 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9952 : lratChecker f9952 p9952 = .success := by decide +kernel
theorem unsat9952 : Unsatisfiable (PosFin 65) f9952 := by
  apply lratCheckerSound f9952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9952
  · intro a ha; simp [p9952] at ha; subst a; trivial
  · exact checked9952
theorem derived9952 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9952 := by
  apply localUnsat_implies_entails f9952 [c9748, c9855, c1939, c9794, c4119, c4139, c9874, c9859, c1918, c4104, c1923, c1922, c309, c4109, c4108, c4111] c9952 unsat9952 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9855 := derived9855 a h
  have h2 : Entails.eval a c1939 := h 1938 (by decide)
  have h3 : Entails.eval a c9794 := derived9794 a h
  have h4 : Entails.eval a c4119 := h 4118 (by decide)
  have h5 : Entails.eval a c4139 := h 4138 (by decide)
  have h6 : Entails.eval a c9874 := derived9874 a h
  have h7 : Entails.eval a c9859 := derived9859 a h
  have h8 : Entails.eval a c1918 := h 1917 (by decide)
  have h9 : Entails.eval a c4104 := h 4103 (by decide)
  have h10 : Entails.eval a c1923 := h 1922 (by decide)
  have h11 : Entails.eval a c1922 := h 1921 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  have h13 : Entails.eval a c4109 := h 4108 (by decide)
  have h14 : Entails.eval a c4108 := h 4107 (by decide)
  have h15 : Entails.eval a c4111 := h 4110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9953 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨9, by decide⟩, true), (⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9953 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9817, some c9838, some c3213, some c3212, some c3216, some c3221, some c1925, some c4539, some c1929, some c4534, some c1914, some c1915, some c1934, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9953 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9953 : lratChecker f9953 p9953 = .success := by decide +kernel
theorem unsat9953 : Unsatisfiable (PosFin 65) f9953 := by
  apply lratCheckerSound f9953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9953
  · intro a ha; simp [p9953] at ha; subst a; trivial
  · exact checked9953
theorem derived9953 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9953 := by
  apply localUnsat_implies_entails f9953 [c9748, c9817, c9838, c3213, c3212, c3216, c3221, c1925, c4539, c1929, c4534, c1914, c1915, c1934] c9953 unsat9953 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9817 := derived9817 a h
  have h2 : Entails.eval a c9838 := derived9838 a h
  have h3 : Entails.eval a c3213 := h 3212 (by decide)
  have h4 : Entails.eval a c3212 := h 3211 (by decide)
  have h5 : Entails.eval a c3216 := h 3215 (by decide)
  have h6 : Entails.eval a c3221 := h 3220 (by decide)
  have h7 : Entails.eval a c1925 := h 1924 (by decide)
  have h8 : Entails.eval a c4539 := h 4538 (by decide)
  have h9 : Entails.eval a c1929 := h 1928 (by decide)
  have h10 : Entails.eval a c4534 := h 4533 (by decide)
  have h11 : Entails.eval a c1914 := h 1913 (by decide)
  have h12 : Entails.eval a c1915 := h 1914 (by decide)
  have h13 : Entails.eval a c1934 := h 1933 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9954 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9954 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9855, some c9952, some c4546, some c9953, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9954 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9954 : lratChecker f9954 p9954 = .success := by decide +kernel
theorem unsat9954 : Unsatisfiable (PosFin 65) f9954 := by
  apply lratCheckerSound f9954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9954
  · intro a ha; simp [p9954] at ha; subst a; trivial
  · exact checked9954
theorem derived9954 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9954 := by
  apply localUnsat_implies_entails f9954 [c9855, c9952, c4546, c9953] c9954 unsat9954 (by rfl) a
  have h0 : Entails.eval a c9855 := derived9855 a h
  have h1 : Entails.eval a c9952 := derived9952 a h
  have h2 : Entails.eval a c4546 := h 4545 (by decide)
  have h3 : Entails.eval a c9953 := derived9953 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9955 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨9, by decide⟩, false), (⟨56, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9955 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9902, some c2660, some c2658, some c4565, some c1922, some c309, some c2661, some c9897, some c4379, some c4383, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9955 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9955 : lratChecker f9955 p9955 = .success := by decide +kernel
theorem unsat9955 : Unsatisfiable (PosFin 65) f9955 := by
  apply lratCheckerSound f9955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9955
  · intro a ha; simp [p9955] at ha; subst a; trivial
  · exact checked9955
theorem derived9955 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9955 := by
  apply localUnsat_implies_entails f9955 [c9748, c9902, c2660, c2658, c4565, c1922, c309, c2661, c9897, c4379, c4383] c9955 unsat9955 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9902 := derived9902 a h
  have h2 : Entails.eval a c2660 := h 2659 (by decide)
  have h3 : Entails.eval a c2658 := h 2657 (by decide)
  have h4 : Entails.eval a c4565 := h 4564 (by decide)
  have h5 : Entails.eval a c1922 := h 1921 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c2661 := h 2660 (by decide)
  have h8 : Entails.eval a c9897 := derived9897 a h
  have h9 : Entails.eval a c4379 := h 4378 (by decide)
  have h10 : Entails.eval a c4383 := h 4382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9956 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9956 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2663, some c2665, some c2664, some c2670, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9956 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9956 : lratChecker f9956 p9956 = .success := by decide +kernel
theorem unsat9956 : Unsatisfiable (PosFin 65) f9956 := by
  apply lratCheckerSound f9956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9956
  · intro a ha; simp [p9956] at ha; subst a; trivial
  · exact checked9956
theorem derived9956 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9956 := by
  apply localUnsat_implies_entails f9956 [c2663, c2665, c2664, c2670] c9956 unsat9956 (by rfl) a
  have h0 : Entails.eval a c2663 := h 2662 (by decide)
  have h1 : Entails.eval a c2665 := h 2664 (by decide)
  have h2 : Entails.eval a c2664 := h 2663 (by decide)
  have h3 : Entails.eval a c2670 := h 2669 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9957 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9957 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4559, some c4558, some c9956, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9957 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9957 : lratChecker f9957 p9957 = .success := by decide +kernel
theorem unsat9957 : Unsatisfiable (PosFin 65) f9957 := by
  apply lratCheckerSound f9957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9957
  · intro a ha; simp [p9957] at ha; subst a; trivial
  · exact checked9957
theorem derived9957 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9957 := by
  apply localUnsat_implies_entails f9957 [c4559, c4558, c9956] c9957 unsat9957 (by rfl) a
  have h0 : Entails.eval a c4559 := h 4558 (by decide)
  have h1 : Entails.eval a c4558 := h 4557 (by decide)
  have h2 : Entails.eval a c9956 := derived9956 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9958 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9958 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9794, some c9855, some c1939, some c9951, some c9954, some c2695, some c9957, some c9902, some c9955, some c2660, some c4531, some c9838, some c4537, some c2662, some c4535, some c8977, some c4542, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9958 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9958 : lratChecker f9958 p9958 = .success := by decide +kernel
theorem unsat9958 : Unsatisfiable (PosFin 65) f9958 := by
  apply lratCheckerSound f9958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9958
  · intro a ha; simp [p9958] at ha; subst a; trivial
  · exact checked9958
theorem derived9958 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9958 := by
  apply localUnsat_implies_entails f9958 [c9748, c9794, c9855, c1939, c9951, c9954, c2695, c9957, c9902, c9955, c2660, c4531, c9838, c4537, c2662, c4535, c8977, c4542] c9958 unsat9958 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9794 := derived9794 a h
  have h2 : Entails.eval a c9855 := derived9855 a h
  have h3 : Entails.eval a c1939 := h 1938 (by decide)
  have h4 : Entails.eval a c9951 := derived9951 a h
  have h5 : Entails.eval a c9954 := derived9954 a h
  have h6 : Entails.eval a c2695 := h 2694 (by decide)
  have h7 : Entails.eval a c9957 := derived9957 a h
  have h8 : Entails.eval a c9902 := derived9902 a h
  have h9 : Entails.eval a c9955 := derived9955 a h
  have h10 : Entails.eval a c2660 := h 2659 (by decide)
  have h11 : Entails.eval a c4531 := h 4530 (by decide)
  have h12 : Entails.eval a c9838 := derived9838 a h
  have h13 : Entails.eval a c4537 := h 4536 (by decide)
  have h14 : Entails.eval a c2662 := h 2661 (by decide)
  have h15 : Entails.eval a c4535 := h 4534 (by decide)
  have h16 : Entails.eval a c8977 := derived8977 a h
  have h17 : Entails.eval a c4542 := h 4541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9959 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9959 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2569, some c1490, some c2570, some c2572, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9959 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9959 : lratChecker f9959 p9959 = .success := by decide +kernel
theorem unsat9959 : Unsatisfiable (PosFin 65) f9959 := by
  apply lratCheckerSound f9959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9959
  · intro a ha; simp [p9959] at ha; subst a; trivial
  · exact checked9959
theorem derived9959 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9959 := by
  apply localUnsat_implies_entails f9959 [c9748, c2569, c1490, c2570, c2572] c9959 unsat9959 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2569 := h 2568 (by decide)
  have h2 : Entails.eval a c1490 := h 1489 (by decide)
  have h3 : Entails.eval a c2570 := h 2569 (by decide)
  have h4 : Entails.eval a c2572 := h 2571 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9960 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9960 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9864, some c2567, some c9959, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9960 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9960 : lratChecker f9960 p9960 = .success := by decide +kernel
theorem unsat9960 : Unsatisfiable (PosFin 65) f9960 := by
  apply lratCheckerSound f9960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9960
  · intro a ha; simp [p9960] at ha; subst a; trivial
  · exact checked9960
theorem derived9960 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9960 := by
  apply localUnsat_implies_entails f9960 [c9864, c2567, c9959] c9960 unsat9960 (by rfl) a
  have h0 : Entails.eval a c9864 := derived9864 a h
  have h1 : Entails.eval a c2567 := h 2566 (by decide)
  have h2 : Entails.eval a c9959 := derived9959 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9961 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9961 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1500, some c1528, some c9960, some c2559, some c8676, some c9818, some c919, some c1469, some c1458, some c1480, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9961 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9961 : lratChecker f9961 p9961 = .success := by decide +kernel
theorem unsat9961 : Unsatisfiable (PosFin 65) f9961 := by
  apply lratCheckerSound f9961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9961
  · intro a ha; simp [p9961] at ha; subst a; trivial
  · exact checked9961
theorem derived9961 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9961 := by
  apply localUnsat_implies_entails f9961 [c9748, c1500, c1528, c9960, c2559, c8676, c9818, c919, c1469, c1458, c1480] c9961 unsat9961 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1500 := h 1499 (by decide)
  have h2 : Entails.eval a c1528 := h 1527 (by decide)
  have h3 : Entails.eval a c9960 := derived9960 a h
  have h4 : Entails.eval a c2559 := h 2558 (by decide)
  have h5 : Entails.eval a c8676 := derived8676 a h
  have h6 : Entails.eval a c9818 := derived9818 a h
  have h7 : Entails.eval a c919 := h 918 (by decide)
  have h8 : Entails.eval a c1469 := h 1468 (by decide)
  have h9 : Entails.eval a c1458 := h 1457 (by decide)
  have h10 : Entails.eval a c1480 := h 1479 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9962 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9962 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4111, some c911, some c3804, some c2698, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9962 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9962 : lratChecker f9962 p9962 = .success := by decide +kernel
theorem unsat9962 : Unsatisfiable (PosFin 65) f9962 := by
  apply lratCheckerSound f9962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9962
  · intro a ha; simp [p9962] at ha; subst a; trivial
  · exact checked9962
theorem derived9962 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9962 := by
  apply localUnsat_implies_entails f9962 [c4111, c911, c3804, c2698] c9962 unsat9962 (by rfl) a
  have h0 : Entails.eval a c4111 := h 4110 (by decide)
  have h1 : Entails.eval a c911 := h 910 (by decide)
  have h2 : Entails.eval a c3804 := h 3803 (by decide)
  have h3 : Entails.eval a c2698 := h 2697 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9963 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9963 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4104, some c9962, some c922, some c923, some c908, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9963 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9963 : lratChecker f9963 p9963 = .success := by decide +kernel
theorem unsat9963 : Unsatisfiable (PosFin 65) f9963 := by
  apply lratCheckerSound f9963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9963
  · intro a ha; simp [p9963] at ha; subst a; trivial
  · exact checked9963
theorem derived9963 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9963 := by
  apply localUnsat_implies_entails f9963 [c4104, c9962, c922, c923, c908] c9963 unsat9963 (by rfl) a
  have h0 : Entails.eval a c4104 := h 4103 (by decide)
  have h1 : Entails.eval a c9962 := derived9962 a h
  have h2 : Entails.eval a c922 := h 921 (by decide)
  have h3 : Entails.eval a c923 := h 922 (by decide)
  have h4 : Entails.eval a c908 := h 907 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9964 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9964 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9963, some c976, some c4114, some c4112, some c982, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9964 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9964 : lratChecker f9964 p9964 = .success := by decide +kernel
theorem unsat9964 : Unsatisfiable (PosFin 65) f9964 := by
  apply lratCheckerSound f9964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9964
  · intro a ha; simp [p9964] at ha; subst a; trivial
  · exact checked9964
theorem derived9964 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9964 := by
  apply localUnsat_implies_entails f9964 [c9963, c976, c4114, c4112, c982] c9964 unsat9964 (by rfl) a
  have h0 : Entails.eval a c9963 := derived9963 a h
  have h1 : Entails.eval a c976 := h 975 (by decide)
  have h2 : Entails.eval a c4114 := h 4113 (by decide)
  have h3 : Entails.eval a c4112 := h 4111 (by decide)
  have h4 : Entails.eval a c982 := h 981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9965 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9965 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4125, some c4119, some c4139, some c9874, some c9964, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9965 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9965 : lratChecker f9965 p9965 = .success := by decide +kernel
theorem unsat9965 : Unsatisfiable (PosFin 65) f9965 := by
  apply lratCheckerSound f9965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9965
  · intro a ha; simp [p9965] at ha; subst a; trivial
  · exact checked9965
theorem derived9965 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9965 := by
  apply localUnsat_implies_entails f9965 [c4125, c4119, c4139, c9874, c9964] c9965 unsat9965 (by rfl) a
  have h0 : Entails.eval a c4125 := h 4124 (by decide)
  have h1 : Entails.eval a c4119 := h 4118 (by decide)
  have h2 : Entails.eval a c4139 := h 4138 (by decide)
  have h3 : Entails.eval a c9874 := derived9874 a h
  have h4 : Entails.eval a c9964 := derived9964 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9966 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨18, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9966 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c911, some c905, some c923, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9966 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9966 : lratChecker f9966 p9966 = .success := by decide +kernel
theorem unsat9966 : Unsatisfiable (PosFin 65) f9966 := by
  apply lratCheckerSound f9966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9966
  · intro a ha; simp [p9966] at ha; subst a; trivial
  · exact checked9966
theorem derived9966 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9966 := by
  apply localUnsat_implies_entails f9966 [c911, c905, c923] c9966 unsat9966 (by rfl) a
  have h0 : Entails.eval a c911 := h 910 (by decide)
  have h1 : Entails.eval a c905 := h 904 (by decide)
  have h2 : Entails.eval a c923 := h 922 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9967 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9967 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4584, some c5075, some c2697, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9967 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9967 : lratChecker f9967 p9967 = .success := by decide +kernel
theorem unsat9967 : Unsatisfiable (PosFin 65) f9967 := by
  apply lratCheckerSound f9967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9967
  · intro a ha; simp [p9967] at ha; subst a; trivial
  · exact checked9967
theorem derived9967 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9967 := by
  apply localUnsat_implies_entails f9967 [c4584, c5075, c2697] c9967 unsat9967 (by rfl) a
  have h0 : Entails.eval a c4584 := h 4583 (by decide)
  have h1 : Entails.eval a c5075 := h 5074 (by decide)
  have h2 : Entails.eval a c2697 := h 2696 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9968 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨56, by decide⟩, false), (⟨18, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9968 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9967, some c9966, some c4647, some c3803, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9968 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9968 : lratChecker f9968 p9968 = .success := by decide +kernel
theorem unsat9968 : Unsatisfiable (PosFin 65) f9968 := by
  apply lratCheckerSound f9968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9968
  · intro a ha; simp [p9968] at ha; subst a; trivial
  · exact checked9968
theorem derived9968 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9968 := by
  apply localUnsat_implies_entails f9968 [c9967, c9966, c4647, c3803] c9968 unsat9968 (by rfl) a
  have h0 : Entails.eval a c9967 := derived9967 a h
  have h1 : Entails.eval a c9966 := derived9966 a h
  have h2 : Entails.eval a c4647 := h 4646 (by decide)
  have h3 : Entails.eval a c3803 := h 3802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9969 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨18, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9969 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9968, some c976, some c975, some c910, some c982, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9969 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9969 : lratChecker f9969 p9969 = .success := by decide +kernel
theorem unsat9969 : Unsatisfiable (PosFin 65) f9969 := by
  apply lratCheckerSound f9969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9969
  · intro a ha; simp [p9969] at ha; subst a; trivial
  · exact checked9969
theorem derived9969 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9969 := by
  apply localUnsat_implies_entails f9969 [c9968, c976, c975, c910, c982] c9969 unsat9969 (by rfl) a
  have h0 : Entails.eval a c9968 := derived9968 a h
  have h1 : Entails.eval a c976 := h 975 (by decide)
  have h2 : Entails.eval a c975 := h 974 (by decide)
  have h3 : Entails.eval a c910 := h 909 (by decide)
  have h4 : Entails.eval a c982 := h 981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9970 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9970 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2714, some c3801, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9970 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9970 : lratChecker f9970 p9970 = .success := by decide +kernel
theorem unsat9970 : Unsatisfiable (PosFin 65) f9970 := by
  apply lratCheckerSound f9970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9970
  · intro a ha; simp [p9970] at ha; subst a; trivial
  · exact checked9970
theorem derived9970 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9970 := by
  apply localUnsat_implies_entails f9970 [c2714, c3801] c9970 unsat9970 (by rfl) a
  have h0 : Entails.eval a c2714 := h 2713 (by decide)
  have h1 : Entails.eval a c3801 := h 3800 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9971 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9971 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3644, some c2001, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9971 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9971 : lratChecker f9971 p9971 = .success := by decide +kernel
theorem unsat9971 : Unsatisfiable (PosFin 65) f9971 := by
  apply lratCheckerSound f9971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9971
  · intro a ha; simp [p9971] at ha; subst a; trivial
  · exact checked9971
theorem derived9971 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9971 := by
  apply localUnsat_implies_entails f9971 [c9748, c3644, c2001] c9971 unsat9971 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3644 := h 3643 (by decide)
  have h2 : Entails.eval a c2001 := h 2000 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9972 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9972 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9967, some c8609, some c919, some c905, some c4646, some c3803, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9972 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9972 : lratChecker f9972 p9972 = .success := by decide +kernel
theorem unsat9972 : Unsatisfiable (PosFin 65) f9972 := by
  apply lratCheckerSound f9972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9972
  · intro a ha; simp [p9972] at ha; subst a; trivial
  · exact checked9972
theorem derived9972 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9972 := by
  apply localUnsat_implies_entails f9972 [c9967, c8609, c919, c905, c4646, c3803] c9972 unsat9972 (by rfl) a
  have h0 : Entails.eval a c9967 := derived9967 a h
  have h1 : Entails.eval a c8609 := derived8609 a h
  have h2 : Entails.eval a c919 := h 918 (by decide)
  have h3 : Entails.eval a c905 := h 904 (by decide)
  have h4 : Entails.eval a c4646 := h 4645 (by decide)
  have h5 : Entails.eval a c3803 := h 3802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9973 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9973 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3776, some c4232, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9973 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9973 : lratChecker f9973 p9973 = .success := by decide +kernel
theorem unsat9973 : Unsatisfiable (PosFin 65) f9973 := by
  apply lratCheckerSound f9973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9973
  · intro a ha; simp [p9973] at ha; subst a; trivial
  · exact checked9973
theorem derived9973 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9973 := by
  apply localUnsat_implies_entails f9973 [c3776, c4232] c9973 unsat9973 (by rfl) a
  have h0 : Entails.eval a c3776 := h 3775 (by decide)
  have h1 : Entails.eval a c4232 := h 4231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9974 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9974 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9794, some c9961, some c9965, some c9971, some c9970, some c9969, some c9972, some c8676, some c919, some c978, some c981, some c924, some c983, some c980, some c982, some c936, some c929, some c903, some c928, some c9973, some c2699, some c1970, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9974 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9974 : lratChecker f9974 p9974 = .success := by decide +kernel
theorem unsat9974 : Unsatisfiable (PosFin 65) f9974 := by
  apply lratCheckerSound f9974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9974
  · intro a ha; simp [p9974] at ha; subst a; trivial
  · exact checked9974
theorem derived9974 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9974 := by
  apply localUnsat_implies_entails f9974 [c9748, c9794, c9961, c9965, c9971, c9970, c9969, c9972, c8676, c919, c978, c981, c924, c983, c980, c982, c936, c929, c903, c928, c9973, c2699, c1970] c9974 unsat9974 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9794 := derived9794 a h
  have h2 : Entails.eval a c9961 := derived9961 a h
  have h3 : Entails.eval a c9965 := derived9965 a h
  have h4 : Entails.eval a c9971 := derived9971 a h
  have h5 : Entails.eval a c9970 := derived9970 a h
  have h6 : Entails.eval a c9969 := derived9969 a h
  have h7 : Entails.eval a c9972 := derived9972 a h
  have h8 : Entails.eval a c8676 := derived8676 a h
  have h9 : Entails.eval a c919 := h 918 (by decide)
  have h10 : Entails.eval a c978 := h 977 (by decide)
  have h11 : Entails.eval a c981 := h 980 (by decide)
  have h12 : Entails.eval a c924 := h 923 (by decide)
  have h13 : Entails.eval a c983 := h 982 (by decide)
  have h14 : Entails.eval a c980 := h 979 (by decide)
  have h15 : Entails.eval a c982 := h 981 (by decide)
  have h16 : Entails.eval a c936 := h 935 (by decide)
  have h17 : Entails.eval a c929 := h 928 (by decide)
  have h18 : Entails.eval a c903 := h 902 (by decide)
  have h19 : Entails.eval a c928 := h 927 (by decide)
  have h20 : Entails.eval a c9973 := derived9973 a h
  have h21 : Entails.eval a c2699 := h 2698 (by decide)
  have h22 : Entails.eval a c1970 := h 1969 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9975 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9975 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3649, some c2709, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9975 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9975 : lratChecker f9975 p9975 = .success := by decide +kernel
theorem unsat9975 : Unsatisfiable (PosFin 65) f9975 := by
  apply lratCheckerSound f9975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9975
  · intro a ha; simp [p9975] at ha; subst a; trivial
  · exact checked9975
theorem derived9975 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9975 := by
  apply localUnsat_implies_entails f9975 [c3649, c2709] c9975 unsat9975 (by rfl) a
  have h0 : Entails.eval a c3649 := h 3648 (by decide)
  have h1 : Entails.eval a c2709 := h 2708 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9976 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9976 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2660, some c2658, some c9966, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9976 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9976 : lratChecker f9976 p9976 = .success := by decide +kernel
theorem unsat9976 : Unsatisfiable (PosFin 65) f9976 := by
  apply lratCheckerSound f9976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9976
  · intro a ha; simp [p9976] at ha; subst a; trivial
  · exact checked9976
theorem derived9976 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9976 := by
  apply localUnsat_implies_entails f9976 [c2660, c2658, c9966] c9976 unsat9976 (by rfl) a
  have h0 : Entails.eval a c2660 := h 2659 (by decide)
  have h1 : Entails.eval a c2658 := h 2657 (by decide)
  have h2 : Entails.eval a c9966 := derived9966 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9977 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9977 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9976, some c976, some c975, some c910, some c982, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9977 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9977 : lratChecker f9977 p9977 = .success := by decide +kernel
theorem unsat9977 : Unsatisfiable (PosFin 65) f9977 := by
  apply lratCheckerSound f9977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9977
  · intro a ha; simp [p9977] at ha; subst a; trivial
  · exact checked9977
theorem derived9977 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9977 := by
  apply localUnsat_implies_entails f9977 [c9976, c976, c975, c910, c982] c9977 unsat9977 (by rfl) a
  have h0 : Entails.eval a c9976 := derived9976 a h
  have h1 : Entails.eval a c976 := h 975 (by decide)
  have h2 : Entails.eval a c975 := h 974 (by decide)
  have h3 : Entails.eval a c910 := h 909 (by decide)
  have h4 : Entails.eval a c982 := h 981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9978 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9978 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2660, some c2658, some c8609, some c2662, some c919, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9978 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9978 : lratChecker f9978 p9978 = .success := by decide +kernel
theorem unsat9978 : Unsatisfiable (PosFin 65) f9978 := by
  apply lratCheckerSound f9978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9978
  · intro a ha; simp [p9978] at ha; subst a; trivial
  · exact checked9978
theorem derived9978 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9978 := by
  apply localUnsat_implies_entails f9978 [c2660, c2658, c8609, c2662, c919] c9978 unsat9978 (by rfl) a
  have h0 : Entails.eval a c2660 := h 2659 (by decide)
  have h1 : Entails.eval a c2658 := h 2657 (by decide)
  have h2 : Entails.eval a c8609 := derived8609 a h
  have h3 : Entails.eval a c2662 := h 2661 (by decide)
  have h4 : Entails.eval a c919 := h 918 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9979 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9979 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9914, some c9794, some c9958, some c9975, some c8003, some c9961, some c9971, some c9974, some c9970, some c9977, some c9906, some c9978, some c8676, some c919, some c978, some c2669, some c1970, some c5074, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9979 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9979 : lratChecker f9979 p9979 = .success := by decide +kernel
theorem unsat9979 : Unsatisfiable (PosFin 65) f9979 := by
  apply lratCheckerSound f9979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9979
  · intro a ha; simp [p9979] at ha; subst a; trivial
  · exact checked9979
theorem derived9979 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9979 := by
  apply localUnsat_implies_entails f9979 [c9748, c9914, c9794, c9958, c9975, c8003, c9961, c9971, c9974, c9970, c9977, c9906, c9978, c8676, c919, c978, c2669, c1970, c5074] c9979 unsat9979 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9914 := derived9914 a h
  have h2 : Entails.eval a c9794 := derived9794 a h
  have h3 : Entails.eval a c9958 := derived9958 a h
  have h4 : Entails.eval a c9975 := derived9975 a h
  have h5 : Entails.eval a c8003 := derived8003 a h
  have h6 : Entails.eval a c9961 := derived9961 a h
  have h7 : Entails.eval a c9971 := derived9971 a h
  have h8 : Entails.eval a c9974 := derived9974 a h
  have h9 : Entails.eval a c9970 := derived9970 a h
  have h10 : Entails.eval a c9977 := derived9977 a h
  have h11 : Entails.eval a c9906 := derived9906 a h
  have h12 : Entails.eval a c9978 := derived9978 a h
  have h13 : Entails.eval a c8676 := derived8676 a h
  have h14 : Entails.eval a c919 := h 918 (by decide)
  have h15 : Entails.eval a c978 := h 977 (by decide)
  have h16 : Entails.eval a c2669 := h 2668 (by decide)
  have h17 : Entails.eval a c1970 := h 1969 (by decide)
  have h18 : Entails.eval a c5074 := h 5073 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9980 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9980 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1945, some c1937, some c9846, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9980 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9980 : lratChecker f9980 p9980 = .success := by decide +kernel
theorem unsat9980 : Unsatisfiable (PosFin 65) f9980 := by
  apply lratCheckerSound f9980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9980
  · intro a ha; simp [p9980] at ha; subst a; trivial
  · exact checked9980
theorem derived9980 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9980 := by
  apply localUnsat_implies_entails f9980 [c9748, c1945, c1937, c9846] c9980 unsat9980 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1945 := h 1944 (by decide)
  have h2 : Entails.eval a c1937 := h 1936 (by decide)
  have h3 : Entails.eval a c9846 := derived9846 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9981 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9981 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2702, some c3787, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9981 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9981 : lratChecker f9981 p9981 = .success := by decide +kernel
theorem unsat9981 : Unsatisfiable (PosFin 65) f9981 := by
  apply lratCheckerSound f9981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9981
  · intro a ha; simp [p9981] at ha; subst a; trivial
  · exact checked9981
theorem derived9981 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9981 := by
  apply localUnsat_implies_entails f9981 [c2702, c3787] c9981 unsat9981 (by rfl) a
  have h0 : Entails.eval a c2702 := h 2701 (by decide)
  have h1 : Entails.eval a c3787 := h 3786 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9982 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9982 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9914, some c9979, some c2689, some c1954, some c9974, some c9975, some c8001, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9982 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9982 : lratChecker f9982 p9982 = .success := by decide +kernel
theorem unsat9982 : Unsatisfiable (PosFin 65) f9982 := by
  apply lratCheckerSound f9982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9982
  · intro a ha; simp [p9982] at ha; subst a; trivial
  · exact checked9982
theorem derived9982 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9982 := by
  apply localUnsat_implies_entails f9982 [c9748, c9914, c9979, c2689, c1954, c9974, c9975, c8001] c9982 unsat9982 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9914 := derived9914 a h
  have h2 : Entails.eval a c9979 := derived9979 a h
  have h3 : Entails.eval a c2689 := h 2688 (by decide)
  have h4 : Entails.eval a c1954 := h 1953 (by decide)
  have h5 : Entails.eval a c9974 := derived9974 a h
  have h6 : Entails.eval a c9975 := derived9975 a h
  have h7 : Entails.eval a c8001 := derived8001 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9983 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9983 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9794, some c9981, some c9982, some c9878, some c9980, some c9917, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9983 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9983 : lratChecker f9983 p9983 = .success := by decide +kernel
theorem unsat9983 : Unsatisfiable (PosFin 65) f9983 := by
  apply lratCheckerSound f9983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9983
  · intro a ha; simp [p9983] at ha; subst a; trivial
  · exact checked9983
theorem derived9983 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9983 := by
  apply localUnsat_implies_entails f9983 [c9794, c9981, c9982, c9878, c9980, c9917] c9983 unsat9983 (by rfl) a
  have h0 : Entails.eval a c9794 := derived9794 a h
  have h1 : Entails.eval a c9981 := derived9981 a h
  have h2 : Entails.eval a c9982 := derived9982 a h
  have h3 : Entails.eval a c9878 := derived9878 a h
  have h4 : Entails.eval a c9980 := derived9980 a h
  have h5 : Entails.eval a c9917 := derived9917 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9984 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9984 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1949, some c1954, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9984 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9984 : lratChecker f9984 p9984 = .success := by decide +kernel
theorem unsat9984 : Unsatisfiable (PosFin 65) f9984 := by
  apply lratCheckerSound f9984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9984
  · intro a ha; simp [p9984] at ha; subst a; trivial
  · exact checked9984
theorem derived9984 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9984 := by
  apply localUnsat_implies_entails f9984 [c9748, c1949, c1954] c9984 unsat9984 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1949 := h 1948 (by decide)
  have h2 : Entails.eval a c1954 := h 1953 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9985 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨61, by decide⟩, true), (⟨51, by decide⟩, true), (⟨57, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9985 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5604, some c5579, some c307, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9985 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9985 : lratChecker f9985 p9985 = .success := by decide +kernel
theorem unsat9985 : Unsatisfiable (PosFin 65) f9985 := by
  apply lratCheckerSound f9985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9985
  · intro a ha; simp [p9985] at ha; subst a; trivial
  · exact checked9985
theorem derived9985 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9985 := by
  apply localUnsat_implies_entails f9985 [c5604, c5579, c307] c9985 unsat9985 (by rfl) a
  have h0 : Entails.eval a c5604 := h 5603 (by decide)
  have h1 : Entails.eval a c5579 := h 5578 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9986 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨61, by decide⟩, true), (⟨8, by decide⟩, false), (⟨51, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9986 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c340, some c337, some c327, some c6097, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p9986 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9986 : lratChecker f9986 p9986 = .success := by decide +kernel
theorem unsat9986 : Unsatisfiable (PosFin 65) f9986 := by
  apply lratCheckerSound f9986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9986
  · intro a ha; simp [p9986] at ha; subst a; trivial
  · exact checked9986
theorem derived9986 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9986 := by
  apply localUnsat_implies_entails f9986 [c340, c337, c327, c6097] c9986 unsat9986 (by rfl) a
  have h0 : Entails.eval a c340 := h 339 (by decide)
  have h1 : Entails.eval a c337 := h 336 (by decide)
  have h2 : Entails.eval a c327 := h 326 (by decide)
  have h3 : Entails.eval a c6097 := h 6096 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9987 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨18, by decide⟩, false), (⟨21, by decide⟩, true), (⟨5, by decide⟩, false), (⟨61, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, true), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9987 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8609, some c5691, some c5647, some c978, some c6186, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9987 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9987 : lratChecker f9987 p9987 = .success := by decide +kernel
theorem unsat9987 : Unsatisfiable (PosFin 65) f9987 := by
  apply lratCheckerSound f9987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9987
  · intro a ha; simp [p9987] at ha; subst a; trivial
  · exact checked9987
theorem derived9987 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9987 := by
  apply localUnsat_implies_entails f9987 [c8609, c5691, c5647, c978, c6186] c9987 unsat9987 (by rfl) a
  have h0 : Entails.eval a c8609 := derived8609 a h
  have h1 : Entails.eval a c5691 := h 5690 (by decide)
  have h2 : Entails.eval a c5647 := h 5646 (by decide)
  have h3 : Entails.eval a c978 := h 977 (by decide)
  have h4 : Entails.eval a c6186 := h 6185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9988 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9988 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3794, some c2011, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9988 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9988 : lratChecker f9988 p9988 = .success := by decide +kernel
theorem unsat9988 : Unsatisfiable (PosFin 65) f9988 := by
  apply lratCheckerSound f9988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9988
  · intro a ha; simp [p9988] at ha; subst a; trivial
  · exact checked9988
theorem derived9988 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9988 := by
  apply localUnsat_implies_entails f9988 [c9748, c3794, c2011] c9988 unsat9988 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3794 := h 3793 (by decide)
  have h2 : Entails.eval a c2011 := h 2010 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9989 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, true), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9989 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9988, some c2683, some c3689, some c1508, some c1893, some c9986, some c9985, some c9987, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9989 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9989 : lratChecker f9989 p9989 = .success := by decide +kernel
theorem unsat9989 : Unsatisfiable (PosFin 65) f9989 := by
  apply lratCheckerSound f9989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9989
  · intro a ha; simp [p9989] at ha; subst a; trivial
  · exact checked9989
theorem derived9989 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9989 := by
  apply localUnsat_implies_entails f9989 [c9748, c9988, c2683, c3689, c1508, c1893, c9986, c9985, c9987] c9989 unsat9989 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9988 := derived9988 a h
  have h2 : Entails.eval a c2683 := h 2682 (by decide)
  have h3 : Entails.eval a c3689 := h 3688 (by decide)
  have h4 : Entails.eval a c1508 := h 1507 (by decide)
  have h5 : Entails.eval a c1893 := h 1892 (by decide)
  have h6 : Entails.eval a c9986 := derived9986 a h
  have h7 : Entails.eval a c9985 := derived9985 a h
  have h8 : Entails.eval a c9987 := derived9987 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9990 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9990 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9949, some c9794, some c9938, some c9983, some c9988, some c9984, some c9989, some c2689, some c1516, some c4135, some c3045, some c4636, some c9578, some c3815, some c4665, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9990 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9990 : lratChecker f9990 p9990 = .success := by decide +kernel
theorem unsat9990 : Unsatisfiable (PosFin 65) f9990 := by
  apply lratCheckerSound f9990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9990
  · intro a ha; simp [p9990] at ha; subst a; trivial
  · exact checked9990
theorem derived9990 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9990 := by
  apply localUnsat_implies_entails f9990 [c9748, c9949, c9794, c9938, c9983, c9988, c9984, c9989, c2689, c1516, c4135, c3045, c4636, c9578, c3815, c4665] c9990 unsat9990 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9949 := derived9949 a h
  have h2 : Entails.eval a c9794 := derived9794 a h
  have h3 : Entails.eval a c9938 := derived9938 a h
  have h4 : Entails.eval a c9983 := derived9983 a h
  have h5 : Entails.eval a c9988 := derived9988 a h
  have h6 : Entails.eval a c9984 := derived9984 a h
  have h7 : Entails.eval a c9989 := derived9989 a h
  have h8 : Entails.eval a c2689 := h 2688 (by decide)
  have h9 : Entails.eval a c1516 := h 1515 (by decide)
  have h10 : Entails.eval a c4135 := h 4134 (by decide)
  have h11 : Entails.eval a c3045 := h 3044 (by decide)
  have h12 : Entails.eval a c4636 := h 4635 (by decide)
  have h13 : Entails.eval a c9578 := derived9578 a h
  have h14 : Entails.eval a c3815 := h 3814 (by decide)
  have h15 : Entails.eval a c4665 := h 4664 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9991 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨51, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9991 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2680, some c2708, some c1507, some c4243, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9991 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9991 : lratChecker f9991 p9991 = .success := by decide +kernel
theorem unsat9991 : Unsatisfiable (PosFin 65) f9991 := by
  apply lratCheckerSound f9991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9991
  · intro a ha; simp [p9991] at ha; subst a; trivial
  · exact checked9991
theorem derived9991 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9991 := by
  apply localUnsat_implies_entails f9991 [c9748, c2680, c2708, c1507, c4243] c9991 unsat9991 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2680 := h 2679 (by decide)
  have h2 : Entails.eval a c2708 := h 2707 (by decide)
  have h3 : Entails.eval a c1507 := h 1506 (by decide)
  have h4 : Entails.eval a c4243 := h 4242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9992 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9992 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9949, some c9938, some c9794, some c9983, some c9990, some c9991, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9992 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9992 : lratChecker f9992 p9992 = .success := by decide +kernel
theorem unsat9992 : Unsatisfiable (PosFin 65) f9992 := by
  apply lratCheckerSound f9992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9992
  · intro a ha; simp [p9992] at ha; subst a; trivial
  · exact checked9992
theorem derived9992 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9992 := by
  apply localUnsat_implies_entails f9992 [c9949, c9938, c9794, c9983, c9990, c9991] c9992 unsat9992 (by rfl) a
  have h0 : Entails.eval a c9949 := derived9949 a h
  have h1 : Entails.eval a c9938 := derived9938 a h
  have h2 : Entails.eval a c9794 := derived9794 a h
  have h3 : Entails.eval a c9983 := derived9983 a h
  have h4 : Entails.eval a c9990 := derived9990 a h
  have h5 : Entails.eval a c9991 := derived9991 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9993 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9993 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3797, some c2712, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9993 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9993 : lratChecker f9993 p9993 = .success := by decide +kernel
theorem unsat9993 : Unsatisfiable (PosFin 65) f9993 := by
  apply lratCheckerSound f9993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9993
  · intro a ha; simp [p9993] at ha; subst a; trivial
  · exact checked9993
theorem derived9993 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9993 := by
  apply localUnsat_implies_entails f9993 [c3797, c2712] c9993 unsat9993 (by rfl) a
  have h0 : Entails.eval a c3797 := h 3796 (by decide)
  have h1 : Entails.eval a c2712 := h 2711 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9994 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9994 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1949, some c1948, some c1961, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9994 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9994 : lratChecker f9994 p9994 = .success := by decide +kernel
theorem unsat9994 : Unsatisfiable (PosFin 65) f9994 := by
  apply lratCheckerSound f9994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9994
  · intro a ha; simp [p9994] at ha; subst a; trivial
  · exact checked9994
theorem derived9994 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9994 := by
  apply localUnsat_implies_entails f9994 [c9748, c1949, c1948, c1961] c9994 unsat9994 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1949 := h 1948 (by decide)
  have h2 : Entails.eval a c1948 := h 1947 (by decide)
  have h3 : Entails.eval a c1961 := h 1960 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9995 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9995 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2691, some c9782, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9995 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9995 : lratChecker f9995 p9995 = .success := by decide +kernel
theorem unsat9995 : Unsatisfiable (PosFin 65) f9995 := by
  apply lratCheckerSound f9995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9995
  · intro a ha; simp [p9995] at ha; subst a; trivial
  · exact checked9995
theorem derived9995 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9995 := by
  apply localUnsat_implies_entails f9995 [c2691, c9782] c9995 unsat9995 (by rfl) a
  have h0 : Entails.eval a c2691 := h 2690 (by decide)
  have h1 : Entails.eval a c9782 := derived9782 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9996 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨60, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9996 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2678, some c2581, some c2706, some c4241, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9996 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9996 : lratChecker f9996 p9996 = .success := by decide +kernel
theorem unsat9996 : Unsatisfiable (PosFin 65) f9996 := by
  apply lratCheckerSound f9996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9996
  · intro a ha; simp [p9996] at ha; subst a; trivial
  · exact checked9996
theorem derived9996 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9996 := by
  apply localUnsat_implies_entails f9996 [c2678, c2581, c2706, c4241] c9996 unsat9996 (by rfl) a
  have h0 : Entails.eval a c2678 := h 2677 (by decide)
  have h1 : Entails.eval a c2581 := h 2580 (by decide)
  have h2 : Entails.eval a c2706 := h 2705 (by decide)
  have h3 : Entails.eval a c4241 := h 4240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9997 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9997 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9938, some c9949, some c9992, some c9993, some c9995, some c9996, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9997 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9997 : lratChecker f9997 p9997 = .success := by decide +kernel
theorem unsat9997 : Unsatisfiable (PosFin 65) f9997 := by
  apply lratCheckerSound f9997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9997
  · intro a ha; simp [p9997] at ha; subst a; trivial
  · exact checked9997
theorem derived9997 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9997 := by
  apply localUnsat_implies_entails f9997 [c9938, c9949, c9992, c9993, c9995, c9996] c9997 unsat9997 (by rfl) a
  have h0 : Entails.eval a c9938 := derived9938 a h
  have h1 : Entails.eval a c9949 := derived9949 a h
  have h2 : Entails.eval a c9992 := derived9992 a h
  have h3 : Entails.eval a c9993 := derived9993 a h
  have h4 : Entails.eval a c9995 := derived9995 a h
  have h5 : Entails.eval a c9996 := derived9996 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9998 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9998 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3581, some c9476, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9998 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9998 : lratChecker f9998 p9998 = .success := by decide +kernel
theorem unsat9998 : Unsatisfiable (PosFin 65) f9998 := by
  apply lratCheckerSound f9998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9998
  · intro a ha; simp [p9998] at ha; subst a; trivial
  · exact checked9998
theorem derived9998 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9998 := by
  apply localUnsat_implies_entails f9998 [c3581, c9476] c9998 unsat9998 (by rfl) a
  have h0 : Entails.eval a c3581 := h 3580 (by decide)
  have h1 : Entails.eval a c9476 := derived9476 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9999 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9999 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9997, some c9998, some c9794, some c3979, some c9885, some c5096, some c2901, some c2738, some c1572, some c2062, some c2061, some c4549, some c9865, some c4391, some c1939, some c1457, some c243, some c248, some c1773, some c6122, some c8955, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9999 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9999 : lratChecker f9999 p9999 = .success := by decide +kernel
theorem unsat9999 : Unsatisfiable (PosFin 65) f9999 := by
  apply lratCheckerSound f9999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9999
  · intro a ha; simp [p9999] at ha; subst a; trivial
  · exact checked9999
theorem derived9999 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9999 := by
  apply localUnsat_implies_entails f9999 [c9748, c9997, c9998, c9794, c3979, c9885, c5096, c2901, c2738, c1572, c2062, c2061, c4549, c9865, c4391, c1939, c1457, c243, c248, c1773, c6122, c8955] c9999 unsat9999 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9997 := derived9997 a h
  have h2 : Entails.eval a c9998 := derived9998 a h
  have h3 : Entails.eval a c9794 := derived9794 a h
  have h4 : Entails.eval a c3979 := h 3978 (by decide)
  have h5 : Entails.eval a c9885 := derived9885 a h
  have h6 : Entails.eval a c5096 := h 5095 (by decide)
  have h7 : Entails.eval a c2901 := h 2900 (by decide)
  have h8 : Entails.eval a c2738 := h 2737 (by decide)
  have h9 : Entails.eval a c1572 := h 1571 (by decide)
  have h10 : Entails.eval a c2062 := h 2061 (by decide)
  have h11 : Entails.eval a c2061 := h 2060 (by decide)
  have h12 : Entails.eval a c4549 := h 4548 (by decide)
  have h13 : Entails.eval a c9865 := derived9865 a h
  have h14 : Entails.eval a c4391 := h 4390 (by decide)
  have h15 : Entails.eval a c1939 := h 1938 (by decide)
  have h16 : Entails.eval a c1457 := h 1456 (by decide)
  have h17 : Entails.eval a c243 := h 242 (by decide)
  have h18 : Entails.eval a c248 := h 247 (by decide)
  have h19 : Entails.eval a c1773 := h 1772 (by decide)
  have h20 : Entails.eval a c6122 := h 6121 (by decide)
  have h21 : Entails.eval a c8955 := derived8955 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10000 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10000 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9997, some c9998, some c9999, some c3042, some c4123, some c9294, some c9474, some c2738, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10000 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10000 : lratChecker f10000 p10000 = .success := by decide +kernel
theorem unsat10000 : Unsatisfiable (PosFin 65) f10000 := by
  apply lratCheckerSound f10000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10000
  · intro a ha; simp [p10000] at ha; subst a; trivial
  · exact checked10000
theorem derived10000 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10000 := by
  apply localUnsat_implies_entails f10000 [c9997, c9998, c9999, c3042, c4123, c9294, c9474, c2738] c10000 unsat10000 (by rfl) a
  have h0 : Entails.eval a c9997 := derived9997 a h
  have h1 : Entails.eval a c9998 := derived9998 a h
  have h2 : Entails.eval a c9999 := derived9999 a h
  have h3 : Entails.eval a c3042 := h 3041 (by decide)
  have h4 : Entails.eval a c4123 := h 4122 (by decide)
  have h5 : Entails.eval a c9294 := derived9294 a h
  have h6 : Entails.eval a c9474 := derived9474 a h
  have h7 : Entails.eval a c2738 := h 2737 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10001 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨9, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10001 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9869, some c9789, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p10001 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10001 : lratChecker f10001 p10001 = .success := by decide +kernel
theorem unsat10001 : Unsatisfiable (PosFin 65) f10001 := by
  apply lratCheckerSound f10001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10001
  · intro a ha; simp [p10001] at ha; subst a; trivial
  · exact checked10001
theorem derived10001 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10001 := by
  apply localUnsat_implies_entails f10001 [c9869, c9789] c10001 unsat10001 (by rfl) a
  have h0 : Entails.eval a c9869 := derived9869 a h
  have h1 : Entails.eval a c9789 := derived9789 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10002 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10002 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9997, some c9998, some c9794, some c10000, some c9795, some c10001, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10002 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10002 : lratChecker f10002 p10002 = .success := by decide +kernel
theorem unsat10002 : Unsatisfiable (PosFin 65) f10002 := by
  apply lratCheckerSound f10002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10002
  · intro a ha; simp [p10002] at ha; subst a; trivial
  · exact checked10002
theorem derived10002 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10002 := by
  apply localUnsat_implies_entails f10002 [c9997, c9998, c9794, c10000, c9795, c10001] c10002 unsat10002 (by rfl) a
  have h0 : Entails.eval a c9997 := derived9997 a h
  have h1 : Entails.eval a c9998 := derived9998 a h
  have h2 : Entails.eval a c9794 := derived9794 a h
  have h3 : Entails.eval a c10000 := derived10000 a h
  have h4 : Entails.eval a c9795 := derived9795 a h
  have h5 : Entails.eval a c10001 := derived10001 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10003 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10003 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9931, some c4723, some c4570, some c2738, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10003 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10003 : lratChecker f10003 p10003 = .success := by decide +kernel
theorem unsat10003 : Unsatisfiable (PosFin 65) f10003 := by
  apply lratCheckerSound f10003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10003
  · intro a ha; simp [p10003] at ha; subst a; trivial
  · exact checked10003
theorem derived10003 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10003 := by
  apply localUnsat_implies_entails f10003 [c9931, c4723, c4570, c2738] c10003 unsat10003 (by rfl) a
  have h0 : Entails.eval a c9931 := derived9931 a h
  have h1 : Entails.eval a c4723 := h 4722 (by decide)
  have h2 : Entails.eval a c4570 := h 4569 (by decide)
  have h3 : Entails.eval a c2738 := h 2737 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10004 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10004 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10003, some c4123, some c2738, some c9844, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10004 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10004 : lratChecker f10004 p10004 = .success := by decide +kernel
theorem unsat10004 : Unsatisfiable (PosFin 65) f10004 := by
  apply lratCheckerSound f10004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10004
  · intro a ha; simp [p10004] at ha; subst a; trivial
  · exact checked10004
theorem derived10004 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10004 := by
  apply localUnsat_implies_entails f10004 [c10003, c4123, c2738, c9844] c10004 unsat10004 (by rfl) a
  have h0 : Entails.eval a c10003 := derived10003 a h
  have h1 : Entails.eval a c4123 := h 4122 (by decide)
  have h2 : Entails.eval a c2738 := h 2737 (by decide)
  have h3 : Entails.eval a c9844 := derived9844 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10005 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10005 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9997, some c9998, some c10003, some c9794, some c10002, some c9878, some c9980, some c9917, some c10004, some c9795, some c4137, some c4132, some c4124, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10005 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10005 : lratChecker f10005 p10005 = .success := by decide +kernel
theorem unsat10005 : Unsatisfiable (PosFin 65) f10005 := by
  apply lratCheckerSound f10005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10005
  · intro a ha; simp [p10005] at ha; subst a; trivial
  · exact checked10005
theorem derived10005 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10005 := by
  apply localUnsat_implies_entails f10005 [c9997, c9998, c10003, c9794, c10002, c9878, c9980, c9917, c10004, c9795, c4137, c4132, c4124] c10005 unsat10005 (by rfl) a
  have h0 : Entails.eval a c9997 := derived9997 a h
  have h1 : Entails.eval a c9998 := derived9998 a h
  have h2 : Entails.eval a c10003 := derived10003 a h
  have h3 : Entails.eval a c9794 := derived9794 a h
  have h4 : Entails.eval a c10002 := derived10002 a h
  have h5 : Entails.eval a c9878 := derived9878 a h
  have h6 : Entails.eval a c9980 := derived9980 a h
  have h7 : Entails.eval a c9917 := derived9917 a h
  have h8 : Entails.eval a c10004 := derived10004 a h
  have h9 : Entails.eval a c9795 := derived9795 a h
  have h10 : Entails.eval a c4137 := h 4136 (by decide)
  have h11 : Entails.eval a c4132 := h 4131 (by decide)
  have h12 : Entails.eval a c4124 := h 4123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10006 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10006 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9831, some c1508, some c4123, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10006 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10006 : lratChecker f10006 p10006 = .success := by decide +kernel
theorem unsat10006 : Unsatisfiable (PosFin 65) f10006 := by
  apply lratCheckerSound f10006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10006
  · intro a ha; simp [p10006] at ha; subst a; trivial
  · exact checked10006
theorem derived10006 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10006 := by
  apply localUnsat_implies_entails f10006 [c9748, c9831, c1508, c4123] c10006 unsat10006 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9831 := derived9831 a h
  have h2 : Entails.eval a c1508 := h 1507 (by decide)
  have h3 : Entails.eval a c4123 := h 4122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10007 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10007 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9997, some c9998, some c9794, some c10003, some c10005, some c10006, some c9795, some c9789, some c9853, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10007 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10007 : lratChecker f10007 p10007 = .success := by decide +kernel
theorem unsat10007 : Unsatisfiable (PosFin 65) f10007 := by
  apply lratCheckerSound f10007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10007
  · intro a ha; simp [p10007] at ha; subst a; trivial
  · exact checked10007
theorem derived10007 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10007 := by
  apply localUnsat_implies_entails f10007 [c9997, c9998, c9794, c10003, c10005, c10006, c9795, c9789, c9853] c10007 unsat10007 (by rfl) a
  have h0 : Entails.eval a c9997 := derived9997 a h
  have h1 : Entails.eval a c9998 := derived9998 a h
  have h2 : Entails.eval a c9794 := derived9794 a h
  have h3 : Entails.eval a c10003 := derived10003 a h
  have h4 : Entails.eval a c10005 := derived10005 a h
  have h5 : Entails.eval a c10006 := derived10006 a h
  have h6 : Entails.eval a c9795 := derived9795 a h
  have h7 : Entails.eval a c9789 := derived9789 a h
  have h8 : Entails.eval a c9853 := derived9853 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10008 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10008 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10007, some c9997, some c9998, some c2583, some c3042, some c4123, some c9294, some c9975, some c8388, some c3823, some c9971, some c3128, some c8001, some c4415, some c4664, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10008 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked10008 : lratChecker f10008 p10008 = .success := by decide +kernel
theorem unsat10008 : Unsatisfiable (PosFin 65) f10008 := by
  apply lratCheckerSound f10008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10008
  · intro a ha; simp [p10008] at ha; subst a; trivial
  · exact checked10008
theorem derived10008 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10008 := by
  apply localUnsat_implies_entails f10008 [c10007, c9997, c9998, c2583, c3042, c4123, c9294, c9975, c8388, c3823, c9971, c3128, c8001, c4415, c4664] c10008 unsat10008 (by rfl) a
  have h0 : Entails.eval a c10007 := derived10007 a h
  have h1 : Entails.eval a c9997 := derived9997 a h
  have h2 : Entails.eval a c9998 := derived9998 a h
  have h3 : Entails.eval a c2583 := h 2582 (by decide)
  have h4 : Entails.eval a c3042 := h 3041 (by decide)
  have h5 : Entails.eval a c4123 := h 4122 (by decide)
  have h6 : Entails.eval a c9294 := derived9294 a h
  have h7 : Entails.eval a c9975 := derived9975 a h
  have h8 : Entails.eval a c8388 := derived8388 a h
  have h9 : Entails.eval a c3823 := h 3822 (by decide)
  have h10 : Entails.eval a c9971 := derived9971 a h
  have h11 : Entails.eval a c3128 := h 3127 (by decide)
  have h12 : Entails.eval a c8001 := derived8001 a h
  have h13 : Entails.eval a c4415 := h 4414 (by decide)
  have h14 : Entails.eval a c4664 := h 4663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10009 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨62, by decide⟩, true), (⟨61, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10009 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4137, some c4124, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10009 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10009 : lratChecker f10009 p10009 = .success := by decide +kernel
theorem unsat10009 : Unsatisfiable (PosFin 65) f10009 := by
  apply lratCheckerSound f10009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10009
  · intro a ha; simp [p10009] at ha; subst a; trivial
  · exact checked10009
theorem derived10009 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10009 := by
  apply localUnsat_implies_entails f10009 [c4137, c4124] c10009 unsat10009 (by rfl) a
  have h0 : Entails.eval a c4137 := h 4136 (by decide)
  have h1 : Entails.eval a c4124 := h 4123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10010 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨62, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10010 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9304, some c3791, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10010 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10010 : lratChecker f10010 p10010 = .success := by decide +kernel
theorem unsat10010 : Unsatisfiable (PosFin 65) f10010 := by
  apply lratCheckerSound f10010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10010
  · intro a ha; simp [p10010] at ha; subst a; trivial
  · exact checked10010
theorem derived10010 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10010 := by
  apply localUnsat_implies_entails f10010 [c9304, c3791] c10010 unsat10010 (by rfl) a
  have h0 : Entails.eval a c9304 := derived9304 a h
  have h1 : Entails.eval a c3791 := h 3790 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10011 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨62, by decide⟩, true), (⟨61, by decide⟩, false), (⟨11, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10011 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1954, some c4636, some c5098, some c2365, some c3410, some c10010, some c9971, some c8001, some c3648, some c4664, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10011 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10011 : lratChecker f10011 p10011 = .success := by decide +kernel
theorem unsat10011 : Unsatisfiable (PosFin 65) f10011 := by
  apply lratCheckerSound f10011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10011
  · intro a ha; simp [p10011] at ha; subst a; trivial
  · exact checked10011
theorem derived10011 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10011 := by
  apply localUnsat_implies_entails f10011 [c9748, c1954, c4636, c5098, c2365, c3410, c10010, c9971, c8001, c3648, c4664] c10011 unsat10011 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1954 := h 1953 (by decide)
  have h2 : Entails.eval a c4636 := h 4635 (by decide)
  have h3 : Entails.eval a c5098 := h 5097 (by decide)
  have h4 : Entails.eval a c2365 := h 2364 (by decide)
  have h5 : Entails.eval a c3410 := h 3409 (by decide)
  have h6 : Entails.eval a c10010 := derived10010 a h
  have h7 : Entails.eval a c9971 := derived9971 a h
  have h8 : Entails.eval a c8001 := derived8001 a h
  have h9 : Entails.eval a c3648 := h 3647 (by decide)
  have h10 : Entails.eval a c4664 := h 4663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10012 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10012 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10007, some c9997, some c9998, some c9794, some c10008, some c1954, some c3690, some c9975, some c10011, some c10009, some c2591, some c9878, some c1516, some c1667, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10012 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked10012 : lratChecker f10012 p10012 = .success := by decide +kernel
theorem unsat10012 : Unsatisfiable (PosFin 65) f10012 := by
  apply lratCheckerSound f10012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10012
  · intro a ha; simp [p10012] at ha; subst a; trivial
  · exact checked10012
theorem derived10012 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10012 := by
  apply localUnsat_implies_entails f10012 [c9748, c10007, c9997, c9998, c9794, c10008, c1954, c3690, c9975, c10011, c10009, c2591, c9878, c1516, c1667] c10012 unsat10012 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10007 := derived10007 a h
  have h2 : Entails.eval a c9997 := derived9997 a h
  have h3 : Entails.eval a c9998 := derived9998 a h
  have h4 : Entails.eval a c9794 := derived9794 a h
  have h5 : Entails.eval a c10008 := derived10008 a h
  have h6 : Entails.eval a c1954 := h 1953 (by decide)
  have h7 : Entails.eval a c3690 := h 3689 (by decide)
  have h8 : Entails.eval a c9975 := derived9975 a h
  have h9 : Entails.eval a c10011 := derived10011 a h
  have h10 : Entails.eval a c10009 := derived10009 a h
  have h11 : Entails.eval a c2591 := h 2590 (by decide)
  have h12 : Entails.eval a c9878 := derived9878 a h
  have h13 : Entails.eval a c1516 := h 1515 (by decide)
  have h14 : Entails.eval a c1667 := h 1666 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10013 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10013 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2689, some c2679, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10013 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10013 : lratChecker f10013 p10013 = .success := by decide +kernel
theorem unsat10013 : Unsatisfiable (PosFin 65) f10013 := by
  apply lratCheckerSound f10013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10013
  · intro a ha; simp [p10013] at ha; subst a; trivial
  · exact checked10013
theorem derived10013 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10013 := by
  apply localUnsat_implies_entails f10013 [c2689, c2679] c10013 unsat10013 (by rfl) a
  have h0 : Entails.eval a c2689 := h 2688 (by decide)
  have h1 : Entails.eval a c2679 := h 2678 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10014 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10014 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9304, some c10010, some c4420, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10014 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10014 : lratChecker f10014 p10014 = .success := by decide +kernel
theorem unsat10014 : Unsatisfiable (PosFin 65) f10014 := by
  apply lratCheckerSound f10014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10014
  · intro a ha; simp [p10014] at ha; subst a; trivial
  · exact checked10014
theorem derived10014 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10014 := by
  apply localUnsat_implies_entails f10014 [c9304, c10010, c4420] c10014 unsat10014 (by rfl) a
  have h0 : Entails.eval a c9304 := derived9304 a h
  have h1 : Entails.eval a c10010 := derived10010 a h
  have h2 : Entails.eval a c4420 := h 4419 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10015 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false), (⟨61, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10015 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5605, some c5588, some c308, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10015 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10015 : lratChecker f10015 p10015 = .success := by decide +kernel
theorem unsat10015 : Unsatisfiable (PosFin 65) f10015 := by
  apply lratCheckerSound f10015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10015
  · intro a ha; simp [p10015] at ha; subst a; trivial
  · exact checked10015
theorem derived10015 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10015 := by
  apply localUnsat_implies_entails f10015 [c5605, c5588, c308] c10015 unsat10015 (by rfl) a
  have h0 : Entails.eval a c5605 := h 5604 (by decide)
  have h1 : Entails.eval a c5588 := h 5587 (by decide)
  have h2 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10016 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨60, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, false), (⟨61, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10016 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c341, some c338, some c333, some c1056, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p10016 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10016 : lratChecker f10016 p10016 = .success := by decide +kernel
theorem unsat10016 : Unsatisfiable (PosFin 65) f10016 := by
  apply lratCheckerSound f10016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10016
  · intro a ha; simp [p10016] at ha; subst a; trivial
  · exact checked10016
theorem derived10016 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10016 := by
  apply localUnsat_implies_entails f10016 [c341, c338, c333, c1056] c10016 unsat10016 (by rfl) a
  have h0 : Entails.eval a c341 := h 340 (by decide)
  have h1 : Entails.eval a c338 := h 337 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c1056 := h 1055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10017 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, false), (⟨61, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, false), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10017 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10016, some c10015, some c8609, some c1054, some c5649, some c5693, some c6187, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10017 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10017 : lratChecker f10017 p10017 = .success := by decide +kernel
theorem unsat10017 : Unsatisfiable (PosFin 65) f10017 := by
  apply lratCheckerSound f10017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10017
  · intro a ha; simp [p10017] at ha; subst a; trivial
  · exact checked10017
theorem derived10017 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10017 := by
  apply localUnsat_implies_entails f10017 [c10016, c10015, c8609, c1054, c5649, c5693, c6187] c10017 unsat10017 (by rfl) a
  have h0 : Entails.eval a c10016 := derived10016 a h
  have h1 : Entails.eval a c10015 := derived10015 a h
  have h2 : Entails.eval a c8609 := derived8609 a h
  have h3 : Entails.eval a c1054 := h 1053 (by decide)
  have h4 : Entails.eval a c5649 := h 5648 (by decide)
  have h5 : Entails.eval a c5693 := h 5692 (by decide)
  have h6 : Entails.eval a c6187 := h 6186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10018 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨60, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, false), (⟨57, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10018 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3956, some c4246, some c3664, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10018 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10018 : lratChecker f10018 p10018 = .success := by decide +kernel
theorem unsat10018 : Unsatisfiable (PosFin 65) f10018 := by
  apply lratCheckerSound f10018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10018
  · intro a ha; simp [p10018] at ha; subst a; trivial
  · exact checked10018
theorem derived10018 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10018 := by
  apply localUnsat_implies_entails f10018 [c3956, c4246, c3664] c10018 unsat10018 (by rfl) a
  have h0 : Entails.eval a c3956 := h 3955 (by decide)
  have h1 : Entails.eval a c4246 := h 4245 (by decide)
  have h2 : Entails.eval a c3664 := h 3663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10019 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨63, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, false), (⟨57, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10019 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10018, some c2335, some c3458, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10019 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10019 : lratChecker f10019 p10019 = .success := by decide +kernel
theorem unsat10019 : Unsatisfiable (PosFin 65) f10019 := by
  apply lratCheckerSound f10019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10019
  · intro a ha; simp [p10019] at ha; subst a; trivial
  · exact checked10019
theorem derived10019 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10019 := by
  apply localUnsat_implies_entails f10019 [c9748, c10018, c2335, c3458] c10019 unsat10019 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10018 := derived10018 a h
  have h2 : Entails.eval a c2335 := h 2334 (by decide)
  have h3 : Entails.eval a c3458 := h 3457 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10020 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10020 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9997, some c9998, some c9794, some c10007, some c10013, some c10012, some c9994, some c9991, some c9988, some c9989, some c1516, some c3045, some c3690, some c4135, some c9490, some c3135, some c5098, some c2365, some c10014, some c9971, some c10019, some c10017, some c8003, some c4420, some c2021, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10020 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked10020 : lratChecker f10020 p10020 = .success := by decide +kernel
theorem unsat10020 : Unsatisfiable (PosFin 65) f10020 := by
  apply lratCheckerSound f10020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10020
  · intro a ha; simp [p10020] at ha; subst a; trivial
  · exact checked10020
theorem derived10020 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10020 := by
  apply localUnsat_implies_entails f10020 [c9748, c9997, c9998, c9794, c10007, c10013, c10012, c9994, c9991, c9988, c9989, c1516, c3045, c3690, c4135, c9490, c3135, c5098, c2365, c10014, c9971, c10019, c10017, c8003, c4420, c2021] c10020 unsat10020 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9997 := derived9997 a h
  have h2 : Entails.eval a c9998 := derived9998 a h
  have h3 : Entails.eval a c9794 := derived9794 a h
  have h4 : Entails.eval a c10007 := derived10007 a h
  have h5 : Entails.eval a c10013 := derived10013 a h
  have h6 : Entails.eval a c10012 := derived10012 a h
  have h7 : Entails.eval a c9994 := derived9994 a h
  have h8 : Entails.eval a c9991 := derived9991 a h
  have h9 : Entails.eval a c9988 := derived9988 a h
  have h10 : Entails.eval a c9989 := derived9989 a h
  have h11 : Entails.eval a c1516 := h 1515 (by decide)
  have h12 : Entails.eval a c3045 := h 3044 (by decide)
  have h13 : Entails.eval a c3690 := h 3689 (by decide)
  have h14 : Entails.eval a c4135 := h 4134 (by decide)
  have h15 : Entails.eval a c9490 := derived9490 a h
  have h16 : Entails.eval a c3135 := h 3134 (by decide)
  have h17 : Entails.eval a c5098 := h 5097 (by decide)
  have h18 : Entails.eval a c2365 := h 2364 (by decide)
  have h19 : Entails.eval a c10014 := derived10014 a h
  have h20 : Entails.eval a c9971 := derived9971 a h
  have h21 : Entails.eval a c10019 := derived10019 a h
  have h22 : Entails.eval a c10017 := derived10017 a h
  have h23 : Entails.eval a c8003 := derived8003 a h
  have h24 : Entails.eval a c4420 := h 4419 (by decide)
  have h25 : Entails.eval a c2021 := h 2020 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10021 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10021 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9997, some c9998, some c10020, some c3788, some c2024, some c2025, some c4658, some c2703, some c2027, some c2615, some c5028, some c4477, some c2261, some c1820, some c4122, some c9885, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10021 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked10021 : lratChecker f10021 p10021 = .success := by decide +kernel
theorem unsat10021 : Unsatisfiable (PosFin 65) f10021 := by
  apply lratCheckerSound f10021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10021
  · intro a ha; simp [p10021] at ha; subst a; trivial
  · exact checked10021
theorem derived10021 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10021 := by
  apply localUnsat_implies_entails f10021 [c9748, c9997, c9998, c10020, c3788, c2024, c2025, c4658, c2703, c2027, c2615, c5028, c4477, c2261, c1820, c4122, c9885] c10021 unsat10021 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9997 := derived9997 a h
  have h2 : Entails.eval a c9998 := derived9998 a h
  have h3 : Entails.eval a c10020 := derived10020 a h
  have h4 : Entails.eval a c3788 := h 3787 (by decide)
  have h5 : Entails.eval a c2024 := h 2023 (by decide)
  have h6 : Entails.eval a c2025 := h 2024 (by decide)
  have h7 : Entails.eval a c4658 := h 4657 (by decide)
  have h8 : Entails.eval a c2703 := h 2702 (by decide)
  have h9 : Entails.eval a c2027 := h 2026 (by decide)
  have h10 : Entails.eval a c2615 := h 2614 (by decide)
  have h11 : Entails.eval a c5028 := h 5027 (by decide)
  have h12 : Entails.eval a c4477 := h 4476 (by decide)
  have h13 : Entails.eval a c2261 := h 2260 (by decide)
  have h14 : Entails.eval a c1820 := h 1819 (by decide)
  have h15 : Entails.eval a c4122 := h 4121 (by decide)
  have h16 : Entails.eval a c9885 := derived9885 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10022 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10022 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3536, some c1838, some c3099, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p10022 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10022 : lratChecker f10022 p10022 = .success := by decide +kernel
theorem unsat10022 : Unsatisfiable (PosFin 65) f10022 := by
  apply lratCheckerSound f10022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10022
  · intro a ha; simp [p10022] at ha; subst a; trivial
  · exact checked10022
theorem derived10022 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10022 := by
  apply localUnsat_implies_entails f10022 [c9748, c3536, c1838, c3099] c10022 unsat10022 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3536 := h 3535 (by decide)
  have h2 : Entails.eval a c1838 := h 1837 (by decide)
  have h3 : Entails.eval a c3099 := h 3098 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10023 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10023 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3514, some c2036, some c1836, some c1616, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10023 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10023 : lratChecker f10023 p10023 = .success := by decide +kernel
theorem unsat10023 : Unsatisfiable (PosFin 65) f10023 := by
  apply lratCheckerSound f10023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10023
  · intro a ha; simp [p10023] at ha; subst a; trivial
  · exact checked10023
theorem derived10023 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10023 := by
  apply localUnsat_implies_entails f10023 [c9748, c3514, c2036, c1836, c1616] c10023 unsat10023 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3514 := h 3513 (by decide)
  have h2 : Entails.eval a c2036 := h 2035 (by decide)
  have h3 : Entails.eval a c1836 := h 1835 (by decide)
  have h4 : Entails.eval a c1616 := h 1615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10024 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10024 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10023, some c10022, some c3463, some c3492, some c3461, some c3493, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10024 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10024 : lratChecker f10024 p10024 = .success := by decide +kernel
theorem unsat10024 : Unsatisfiable (PosFin 65) f10024 := by
  apply lratCheckerSound f10024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10024
  · intro a ha; simp [p10024] at ha; subst a; trivial
  · exact checked10024
theorem derived10024 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10024 := by
  apply localUnsat_implies_entails f10024 [c10023, c10022, c3463, c3492, c3461, c3493] c10024 unsat10024 (by rfl) a
  have h0 : Entails.eval a c10023 := derived10023 a h
  have h1 : Entails.eval a c10022 := derived10022 a h
  have h2 : Entails.eval a c3463 := h 3462 (by decide)
  have h3 : Entails.eval a c3492 := h 3491 (by decide)
  have h4 : Entails.eval a c3461 := h 3460 (by decide)
  have h5 : Entails.eval a c3493 := h 3492 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10025 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨15, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10025 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3514, some c1836, some c5101, some c1616, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10025 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10025 : lratChecker f10025 p10025 = .success := by decide +kernel
theorem unsat10025 : Unsatisfiable (PosFin 65) f10025 := by
  apply lratCheckerSound f10025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10025
  · intro a ha; simp [p10025] at ha; subst a; trivial
  · exact checked10025
theorem derived10025 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10025 := by
  apply localUnsat_implies_entails f10025 [c9748, c3514, c1836, c5101, c1616] c10025 unsat10025 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3514 := h 3513 (by decide)
  have h2 : Entails.eval a c1836 := h 1835 (by decide)
  have h3 : Entails.eval a c5101 := h 5100 (by decide)
  have h4 : Entails.eval a c1616 := h 1615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10026 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10026 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10024, some c10025, some c10022, some c3463, some c3464, some c3461, some c3466, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10026 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10026 : lratChecker f10026 p10026 = .success := by decide +kernel
theorem unsat10026 : Unsatisfiable (PosFin 65) f10026 := by
  apply lratCheckerSound f10026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10026
  · intro a ha; simp [p10026] at ha; subst a; trivial
  · exact checked10026
theorem derived10026 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10026 := by
  apply localUnsat_implies_entails f10026 [c10024, c10025, c10022, c3463, c3464, c3461, c3466] c10026 unsat10026 (by rfl) a
  have h0 : Entails.eval a c10024 := derived10024 a h
  have h1 : Entails.eval a c10025 := derived10025 a h
  have h2 : Entails.eval a c10022 := derived10022 a h
  have h3 : Entails.eval a c3463 := h 3462 (by decide)
  have h4 : Entails.eval a c3464 := h 3463 (by decide)
  have h5 : Entails.eval a c3461 := h 3460 (by decide)
  have h6 : Entails.eval a c3466 := h 3465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10027 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10027 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c5075, some c5076, some c1836, some c1616, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10027 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10027 : lratChecker f10027 p10027 = .success := by decide +kernel
theorem unsat10027 : Unsatisfiable (PosFin 65) f10027 := by
  apply lratCheckerSound f10027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10027
  · intro a ha; simp [p10027] at ha; subst a; trivial
  · exact checked10027
theorem derived10027 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10027 := by
  apply localUnsat_implies_entails f10027 [c9748, c5075, c5076, c1836, c1616] c10027 unsat10027 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c5075 := h 5074 (by decide)
  have h2 : Entails.eval a c5076 := h 5075 (by decide)
  have h3 : Entails.eval a c1836 := h 1835 (by decide)
  have h4 : Entails.eval a c1616 := h 1615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10028 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10028 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10026, some c10027, some c10022, some c1595, some c1594, some c3098, some c5077, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10028 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10028 : lratChecker f10028 p10028 = .success := by decide +kernel
theorem unsat10028 : Unsatisfiable (PosFin 65) f10028 := by
  apply lratCheckerSound f10028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10028
  · intro a ha; simp [p10028] at ha; subst a; trivial
  · exact checked10028
theorem derived10028 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10028 := by
  apply localUnsat_implies_entails f10028 [c9748, c10026, c10027, c10022, c1595, c1594, c3098, c5077] c10028 unsat10028 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10026 := derived10026 a h
  have h2 : Entails.eval a c10027 := derived10027 a h
  have h3 : Entails.eval a c10022 := derived10022 a h
  have h4 : Entails.eval a c1595 := h 1594 (by decide)
  have h5 : Entails.eval a c1594 := h 1593 (by decide)
  have h6 : Entails.eval a c3098 := h 3097 (by decide)
  have h7 : Entails.eval a c5077 := h 5076 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10029 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10029 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c5022, some c5023, some c2935, some c1624, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10029 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10029 : lratChecker f10029 p10029 = .success := by decide +kernel
theorem unsat10029 : Unsatisfiable (PosFin 65) f10029 := by
  apply lratCheckerSound f10029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10029
  · intro a ha; simp [p10029] at ha; subst a; trivial
  · exact checked10029
theorem derived10029 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10029 := by
  apply localUnsat_implies_entails f10029 [c9748, c5022, c5023, c2935, c1624] c10029 unsat10029 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c5022 := h 5021 (by decide)
  have h2 : Entails.eval a c5023 := h 5022 (by decide)
  have h3 : Entails.eval a c2935 := h 2934 (by decide)
  have h4 : Entails.eval a c1624 := h 1623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10030 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10030 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10023, some c10025, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10030 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10030 : lratChecker f10030 p10030 = .success := by decide +kernel
theorem unsat10030 : Unsatisfiable (PosFin 65) f10030 := by
  apply lratCheckerSound f10030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10030
  · intro a ha; simp [p10030] at ha; subst a; trivial
  · exact checked10030
theorem derived10030 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10030 := by
  apply localUnsat_implies_entails f10030 [c10023, c10025] c10030 unsat10030 (by rfl) a
  have h0 : Entails.eval a c10023 := derived10023 a h
  have h1 : Entails.eval a c10025 := derived10025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10031 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10031 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10030, some c10029, some c3463, some c3464, some c3461, some c3466, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10031 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10031 : lratChecker f10031 p10031 = .success := by decide +kernel
theorem unsat10031 : Unsatisfiable (PosFin 65) f10031 := by
  apply lratCheckerSound f10031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10031
  · intro a ha; simp [p10031] at ha; subst a; trivial
  · exact checked10031
theorem derived10031 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10031 := by
  apply localUnsat_implies_entails f10031 [c10030, c10029, c3463, c3464, c3461, c3466] c10031 unsat10031 (by rfl) a
  have h0 : Entails.eval a c10030 := derived10030 a h
  have h1 : Entails.eval a c10029 := derived10029 a h
  have h2 : Entails.eval a c3463 := h 3462 (by decide)
  have h3 : Entails.eval a c3464 := h 3463 (by decide)
  have h4 : Entails.eval a c3461 := h 3460 (by decide)
  have h5 : Entails.eval a c3466 := h 3465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10032 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10032 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10031, some c10027, some c10029, some c1595, some c1594, some c3098, some c5077, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10032 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10032 : lratChecker f10032 p10032 = .success := by decide +kernel
theorem unsat10032 : Unsatisfiable (PosFin 65) f10032 := by
  apply lratCheckerSound f10032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10032
  · intro a ha; simp [p10032] at ha; subst a; trivial
  · exact checked10032
theorem derived10032 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10032 := by
  apply localUnsat_implies_entails f10032 [c9748, c10031, c10027, c10029, c1595, c1594, c3098, c5077] c10032 unsat10032 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10031 := derived10031 a h
  have h2 : Entails.eval a c10027 := derived10027 a h
  have h3 : Entails.eval a c10029 := derived10029 a h
  have h4 : Entails.eval a c1595 := h 1594 (by decide)
  have h5 : Entails.eval a c1594 := h 1593 (by decide)
  have h6 : Entails.eval a c3098 := h 3097 (by decide)
  have h7 : Entails.eval a c5077 := h 5076 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10033 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10033 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10028, some c10032, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10033 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10033 : lratChecker f10033 p10033 = .success := by decide +kernel
theorem unsat10033 : Unsatisfiable (PosFin 65) f10033 := by
  apply lratCheckerSound f10033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10033
  · intro a ha; simp [p10033] at ha; subst a; trivial
  · exact checked10033
theorem derived10033 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10033 := by
  apply localUnsat_implies_entails f10033 [c10028, c10032] c10033 unsat10033 (by rfl) a
  have h0 : Entails.eval a c10028 := derived10028 a h
  have h1 : Entails.eval a c10032 := derived10032 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10034 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10034 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c855, some c854, some c3536, some c1624, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p10034 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10034 : lratChecker f10034 p10034 = .success := by decide +kernel
theorem unsat10034 : Unsatisfiable (PosFin 65) f10034 := by
  apply lratCheckerSound f10034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10034
  · intro a ha; simp [p10034] at ha; subst a; trivial
  · exact checked10034
theorem derived10034 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10034 := by
  apply localUnsat_implies_entails f10034 [c9748, c855, c854, c3536, c1624] c10034 unsat10034 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c855 := h 854 (by decide)
  have h2 : Entails.eval a c854 := h 853 (by decide)
  have h3 : Entails.eval a c3536 := h 3535 (by decide)
  have h4 : Entails.eval a c1624 := h 1623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10035 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10035 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10027, some c10030, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10035 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10035 : lratChecker f10035 p10035 = .success := by decide +kernel
theorem unsat10035 : Unsatisfiable (PosFin 65) f10035 := by
  apply lratCheckerSound f10035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10035
  · intro a ha; simp [p10035] at ha; subst a; trivial
  · exact checked10035
theorem derived10035 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10035 := by
  apply localUnsat_implies_entails f10035 [c10027, c10030] c10035 unsat10035 (by rfl) a
  have h0 : Entails.eval a c10027 := derived10027 a h
  have h1 : Entails.eval a c10030 := derived10030 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10036 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10036 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10034, some c1595, some c1594, some c3534, some c850, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10036 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10036 : lratChecker f10036 p10036 = .success := by decide +kernel
theorem unsat10036 : Unsatisfiable (PosFin 65) f10036 := by
  apply lratCheckerSound f10036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10036
  · intro a ha; simp [p10036] at ha; subst a; trivial
  · exact checked10036
theorem derived10036 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10036 := by
  apply localUnsat_implies_entails f10036 [c9748, c10034, c1595, c1594, c3534, c850] c10036 unsat10036 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10034 := derived10034 a h
  have h2 : Entails.eval a c1595 := h 1594 (by decide)
  have h3 : Entails.eval a c1594 := h 1593 (by decide)
  have h4 : Entails.eval a c3534 := h 3533 (by decide)
  have h5 : Entails.eval a c850 := h 849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10037 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10037 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c855, some c854, some c1686, some c1624, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p10037 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10037 : lratChecker f10037 p10037 = .success := by decide +kernel
theorem unsat10037 : Unsatisfiable (PosFin 65) f10037 := by
  apply lratCheckerSound f10037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10037
  · intro a ha; simp [p10037] at ha; subst a; trivial
  · exact checked10037
theorem derived10037 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10037 := by
  apply localUnsat_implies_entails f10037 [c9748, c855, c854, c1686, c1624] c10037 unsat10037 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c855 := h 854 (by decide)
  have h2 : Entails.eval a c854 := h 853 (by decide)
  have h3 : Entails.eval a c1686 := h 1685 (by decide)
  have h4 : Entails.eval a c1624 := h 1623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10038 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10038 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10033, some c10035, some c10036, some c10037, some c1595, some c1594, some c5020, some c850, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10038 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10038 : lratChecker f10038 p10038 = .success := by decide +kernel
theorem unsat10038 : Unsatisfiable (PosFin 65) f10038 := by
  apply lratCheckerSound f10038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10038
  · intro a ha; simp [p10038] at ha; subst a; trivial
  · exact checked10038
theorem derived10038 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10038 := by
  apply localUnsat_implies_entails f10038 [c9748, c10033, c10035, c10036, c10037, c1595, c1594, c5020, c850] c10038 unsat10038 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10033 := derived10033 a h
  have h2 : Entails.eval a c10035 := derived10035 a h
  have h3 : Entails.eval a c10036 := derived10036 a h
  have h4 : Entails.eval a c10037 := derived10037 a h
  have h5 : Entails.eval a c1595 := h 1594 (by decide)
  have h6 : Entails.eval a c1594 := h 1593 (by decide)
  have h7 : Entails.eval a c5020 := h 5019 (by decide)
  have h8 : Entails.eval a c850 := h 849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10039 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10039 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4385, some c4386, some c1001, some c1624, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10039 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10039 : lratChecker f10039 p10039 = .success := by decide +kernel
theorem unsat10039 : Unsatisfiable (PosFin 65) f10039 := by
  apply lratCheckerSound f10039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10039
  · intro a ha; simp [p10039] at ha; subst a; trivial
  · exact checked10039
theorem derived10039 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10039 := by
  apply localUnsat_implies_entails f10039 [c9748, c4385, c4386, c1001, c1624] c10039 unsat10039 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4385 := h 4384 (by decide)
  have h2 : Entails.eval a c4386 := h 4385 (by decide)
  have h3 : Entails.eval a c1001 := h 1000 (by decide)
  have h4 : Entails.eval a c1624 := h 1623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10040 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10040 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10039, some c2607, some c4274, some c1607, some c999, some c2610, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10040 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10040 : lratChecker f10040 p10040 = .success := by decide +kernel
theorem unsat10040 : Unsatisfiable (PosFin 65) f10040 := by
  apply lratCheckerSound f10040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10040
  · intro a ha; simp [p10040] at ha; subst a; trivial
  · exact checked10040
theorem derived10040 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10040 := by
  apply localUnsat_implies_entails f10040 [c9748, c10039, c2607, c4274, c1607, c999, c2610] c10040 unsat10040 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10039 := derived10039 a h
  have h2 : Entails.eval a c2607 := h 2606 (by decide)
  have h3 : Entails.eval a c4274 := h 4273 (by decide)
  have h4 : Entails.eval a c1607 := h 1606 (by decide)
  have h5 : Entails.eval a c999 := h 998 (by decide)
  have h6 : Entails.eval a c2610 := h 2609 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10041 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨63, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10041 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1664, some c1667, some c1649, some c1647, some c10038, some c10040, some c1595, some c1594, some c4266, some c3466, some c5077, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10041 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10041 : lratChecker f10041 p10041 = .success := by decide +kernel
theorem unsat10041 : Unsatisfiable (PosFin 65) f10041 := by
  apply lratCheckerSound f10041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10041
  · intro a ha; simp [p10041] at ha; subst a; trivial
  · exact checked10041
theorem derived10041 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10041 := by
  apply localUnsat_implies_entails f10041 [c9748, c1664, c1667, c1649, c1647, c10038, c10040, c1595, c1594, c4266, c3466, c5077] c10041 unsat10041 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1664 := h 1663 (by decide)
  have h2 : Entails.eval a c1667 := h 1666 (by decide)
  have h3 : Entails.eval a c1649 := h 1648 (by decide)
  have h4 : Entails.eval a c1647 := h 1646 (by decide)
  have h5 : Entails.eval a c10038 := derived10038 a h
  have h6 : Entails.eval a c10040 := derived10040 a h
  have h7 : Entails.eval a c1595 := h 1594 (by decide)
  have h8 : Entails.eval a c1594 := h 1593 (by decide)
  have h9 : Entails.eval a c4266 := h 4265 (by decide)
  have h10 : Entails.eval a c3466 := h 3465 (by decide)
  have h11 : Entails.eval a c5077 := h 5076 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10042 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10042 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1685, some c1686, some c1679, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10042 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10042 : lratChecker f10042 p10042 = .success := by decide +kernel
theorem unsat10042 : Unsatisfiable (PosFin 65) f10042 := by
  apply lratCheckerSound f10042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10042
  · intro a ha; simp [p10042] at ha; subst a; trivial
  · exact checked10042
theorem derived10042 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10042 := by
  apply localUnsat_implies_entails f10042 [c9748, c1685, c1686, c1679] c10042 unsat10042 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1685 := h 1684 (by decide)
  have h2 : Entails.eval a c1686 := h 1685 (by decide)
  have h3 : Entails.eval a c1679 := h 1678 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10043 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10043 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2799, some c2800, some c2804, some c2801, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10043 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10043 : lratChecker f10043 p10043 = .success := by decide +kernel
theorem unsat10043 : Unsatisfiable (PosFin 65) f10043 := by
  apply lratCheckerSound f10043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10043
  · intro a ha; simp [p10043] at ha; subst a; trivial
  · exact checked10043
theorem derived10043 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10043 := by
  apply localUnsat_implies_entails f10043 [c2799, c2800, c2804, c2801] c10043 unsat10043 (by rfl) a
  have h0 : Entails.eval a c2799 := h 2798 (by decide)
  have h1 : Entails.eval a c2800 := h 2799 (by decide)
  have h2 : Entails.eval a c2804 := h 2803 (by decide)
  have h3 : Entails.eval a c2801 := h 2800 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10044 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10044 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5034, some c5036, some c5037, some c2803, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10044 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10044 : lratChecker f10044 p10044 = .success := by decide +kernel
theorem unsat10044 : Unsatisfiable (PosFin 65) f10044 := by
  apply lratCheckerSound f10044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10044
  · intro a ha; simp [p10044] at ha; subst a; trivial
  · exact checked10044
theorem derived10044 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10044 := by
  apply localUnsat_implies_entails f10044 [c5034, c5036, c5037, c2803] c10044 unsat10044 (by rfl) a
  have h0 : Entails.eval a c5034 := h 5033 (by decide)
  have h1 : Entails.eval a c5036 := h 5035 (by decide)
  have h2 : Entails.eval a c5037 := h 5036 (by decide)
  have h3 : Entails.eval a c2803 := h 2802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10045 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨63, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10045 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9880, some c10041, some c2822, some c2808, some c2809, some c2820, some c2818, some c5045, some c10043, some c10044, some c10042, some c4405, some c4406, some c4380, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10045 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10045 : lratChecker f10045 p10045 = .success := by decide +kernel
theorem unsat10045 : Unsatisfiable (PosFin 65) f10045 := by
  apply lratCheckerSound f10045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10045
  · intro a ha; simp [p10045] at ha; subst a; trivial
  · exact checked10045
theorem derived10045 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10045 := by
  apply localUnsat_implies_entails f10045 [c9880, c10041, c2822, c2808, c2809, c2820, c2818, c5045, c10043, c10044, c10042, c4405, c4406, c4380] c10045 unsat10045 (by rfl) a
  have h0 : Entails.eval a c9880 := derived9880 a h
  have h1 : Entails.eval a c10041 := derived10041 a h
  have h2 : Entails.eval a c2822 := h 2821 (by decide)
  have h3 : Entails.eval a c2808 := h 2807 (by decide)
  have h4 : Entails.eval a c2809 := h 2808 (by decide)
  have h5 : Entails.eval a c2820 := h 2819 (by decide)
  have h6 : Entails.eval a c2818 := h 2817 (by decide)
  have h7 : Entails.eval a c5045 := h 5044 (by decide)
  have h8 : Entails.eval a c10043 := derived10043 a h
  have h9 : Entails.eval a c10044 := derived10044 a h
  have h10 : Entails.eval a c10042 := derived10042 a h
  have h11 : Entails.eval a c4405 := h 4404 (by decide)
  have h12 : Entails.eval a c4406 := h 4405 (by decide)
  have h13 : Entails.eval a c4380 := h 4379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10046 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10046 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1676, some c1836, some c2276, some c2291, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10046 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10046 : lratChecker f10046 p10046 = .success := by decide +kernel
theorem unsat10046 : Unsatisfiable (PosFin 65) f10046 := by
  apply lratCheckerSound f10046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10046
  · intro a ha; simp [p10046] at ha; subst a; trivial
  · exact checked10046
theorem derived10046 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10046 := by
  apply localUnsat_implies_entails f10046 [c9748, c1676, c1836, c2276, c2291] c10046 unsat10046 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1676 := h 1675 (by decide)
  have h2 : Entails.eval a c1836 := h 1835 (by decide)
  have h3 : Entails.eval a c2276 := h 2275 (by decide)
  have h4 : Entails.eval a c2291 := h 2290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10047 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10047 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10046, some c10042, some c1591, some c1595, some c1594, some c2291, some c1670, some c1597, some c1638, some c1874, some c2314, some c1633, some c240, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10047 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10047 : lratChecker f10047 p10047 = .success := by decide +kernel
theorem unsat10047 : Unsatisfiable (PosFin 65) f10047 := by
  apply lratCheckerSound f10047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10047
  · intro a ha; simp [p10047] at ha; subst a; trivial
  · exact checked10047
theorem derived10047 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10047 := by
  apply localUnsat_implies_entails f10047 [c9748, c10046, c10042, c1591, c1595, c1594, c2291, c1670, c1597, c1638, c1874, c2314, c1633, c240] c10047 unsat10047 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10046 := derived10046 a h
  have h2 : Entails.eval a c10042 := derived10042 a h
  have h3 : Entails.eval a c1591 := h 1590 (by decide)
  have h4 : Entails.eval a c1595 := h 1594 (by decide)
  have h5 : Entails.eval a c1594 := h 1593 (by decide)
  have h6 : Entails.eval a c2291 := h 2290 (by decide)
  have h7 : Entails.eval a c1670 := h 1669 (by decide)
  have h8 : Entails.eval a c1597 := h 1596 (by decide)
  have h9 : Entails.eval a c1638 := h 1637 (by decide)
  have h10 : Entails.eval a c1874 := h 1873 (by decide)
  have h11 : Entails.eval a c2314 := h 2313 (by decide)
  have h12 : Entails.eval a c1633 := h 1632 (by decide)
  have h13 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10048 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨63, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10048 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2338, some c2324, some c1664, some c1647, some c10047, some c10040, some c1595, some c1594, some c4266, some c3443, some c850, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10048 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10048 : lratChecker f10048 p10048 = .success := by decide +kernel
theorem unsat10048 : Unsatisfiable (PosFin 65) f10048 := by
  apply lratCheckerSound f10048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10048
  · intro a ha; simp [p10048] at ha; subst a; trivial
  · exact checked10048
theorem derived10048 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10048 := by
  apply localUnsat_implies_entails f10048 [c9748, c2338, c2324, c1664, c1647, c10047, c10040, c1595, c1594, c4266, c3443, c850] c10048 unsat10048 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2338 := h 2337 (by decide)
  have h2 : Entails.eval a c2324 := h 2323 (by decide)
  have h3 : Entails.eval a c1664 := h 1663 (by decide)
  have h4 : Entails.eval a c1647 := h 1646 (by decide)
  have h5 : Entails.eval a c10047 := derived10047 a h
  have h6 : Entails.eval a c10040 := derived10040 a h
  have h7 : Entails.eval a c1595 := h 1594 (by decide)
  have h8 : Entails.eval a c1594 := h 1593 (by decide)
  have h9 : Entails.eval a c4266 := h 4265 (by decide)
  have h10 : Entails.eval a c3443 := h 3442 (by decide)
  have h11 : Entails.eval a c850 := h 849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10049 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10049 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9880, some c10045, some c10048, some c2822, some c2808, some c2809, some c2820, some c2818, some c5045, some c10043, some c10044, some c10042, some c4275, some c5039, some c4380, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10049 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked10049 : lratChecker f10049 p10049 = .success := by decide +kernel
theorem unsat10049 : Unsatisfiable (PosFin 65) f10049 := by
  apply lratCheckerSound f10049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10049
  · intro a ha; simp [p10049] at ha; subst a; trivial
  · exact checked10049
theorem derived10049 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10049 := by
  apply localUnsat_implies_entails f10049 [c9880, c10045, c10048, c2822, c2808, c2809, c2820, c2818, c5045, c10043, c10044, c10042, c4275, c5039, c4380] c10049 unsat10049 (by rfl) a
  have h0 : Entails.eval a c9880 := derived9880 a h
  have h1 : Entails.eval a c10045 := derived10045 a h
  have h2 : Entails.eval a c10048 := derived10048 a h
  have h3 : Entails.eval a c2822 := h 2821 (by decide)
  have h4 : Entails.eval a c2808 := h 2807 (by decide)
  have h5 : Entails.eval a c2809 := h 2808 (by decide)
  have h6 : Entails.eval a c2820 := h 2819 (by decide)
  have h7 : Entails.eval a c2818 := h 2817 (by decide)
  have h8 : Entails.eval a c5045 := h 5044 (by decide)
  have h9 : Entails.eval a c10043 := derived10043 a h
  have h10 : Entails.eval a c10044 := derived10044 a h
  have h11 : Entails.eval a c10042 := derived10042 a h
  have h12 : Entails.eval a c4275 := h 4274 (by decide)
  have h13 : Entails.eval a c5039 := h 5038 (by decide)
  have h14 : Entails.eval a c4380 := h 4379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10050 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨63, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10050 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1664, some c1657, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10050 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10050 : lratChecker f10050 p10050 = .success := by decide +kernel
theorem unsat10050 : Unsatisfiable (PosFin 65) f10050 := by
  apply lratCheckerSound f10050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10050
  · intro a ha; simp [p10050] at ha; subst a; trivial
  · exact checked10050
theorem derived10050 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10050 := by
  apply localUnsat_implies_entails f10050 [c9748, c1664, c1657] c10050 unsat10050 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1664 := h 1663 (by decide)
  have h2 : Entails.eval a c1657 := h 1656 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived10050

end CochromaticTwenty.Certificates.FixedCore0
