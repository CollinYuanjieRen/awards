import MerLeanExperiment.Certificates.B16_2_2.Steps1600_1699

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2084 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2084 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c2033, some c1319, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2084 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2084 : lratChecker f2084 p2084 = .success := by decide +kernel
theorem unsat2084 : Unsatisfiable (PosFin 57) f2084 := by
  apply lratCheckerSound f2084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2084
  · intro a ha; simp [p2084] at ha; subst a; trivial
  · exact checked2084
theorem derived2084 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2084 := by
  apply localUnsat_implies_entails f2084 [c1817, c2033, c1319] c2084 unsat2084 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c2033 := derived2033 a h
  have h2 : Entails.eval a c1319 := derived1319 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2085 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2085 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1332, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p2085 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2085 : lratChecker f2085 p2085 = .success := by decide +kernel
theorem unsat2085 : Unsatisfiable (PosFin 57) f2085 := by
  apply lratCheckerSound f2085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2085
  · intro a ha; simp [p2085] at ha; subst a; trivial
  · exact checked2085
theorem derived2085 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2085 := by
  apply localUnsat_implies_entails f2085 [c2033, c1332] c2085 unsat2085 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2086 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2086 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1817, some c1339, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2086 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2086 : lratChecker f2086 p2086 = .success := by decide +kernel
theorem unsat2086 : Unsatisfiable (PosFin 57) f2086 := by
  apply lratCheckerSound f2086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2086
  · intro a ha; simp [p2086] at ha; subst a; trivial
  · exact checked2086
theorem derived2086 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2086 := by
  apply localUnsat_implies_entails f2086 [c2033, c1817, c1339] c2086 unsat2086 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1339 := derived1339 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2087 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2087 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c2033, some c1345, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p2087 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2087 : lratChecker f2087 p2087 = .success := by decide +kernel
theorem unsat2087 : Unsatisfiable (PosFin 57) f2087 := by
  apply lratCheckerSound f2087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2087
  · intro a ha; simp [p2087] at ha; subst a; trivial
  · exact checked2087
theorem derived2087 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2087 := by
  apply localUnsat_implies_entails f2087 [c1817, c2033, c1345] c2087 unsat2087 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c2033 := derived2033 a h
  have h2 : Entails.eval a c1345 := derived1345 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2088 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2088 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1360, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2088 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2088 : lratChecker f2088 p2088 = .success := by decide +kernel
theorem unsat2088 : Unsatisfiable (PosFin 57) f2088 := by
  apply lratCheckerSound f2088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2088
  · intro a ha; simp [p2088] at ha; subst a; trivial
  · exact checked2088
theorem derived2088 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2088 := by
  apply localUnsat_implies_entails f2088 [c2033, c1360] c2088 unsat2088 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1360 := derived1360 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2089 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2089 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1376, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p2089 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2089 : lratChecker f2089 p2089 = .success := by decide +kernel
theorem unsat2089 : Unsatisfiable (PosFin 57) f2089 := by
  apply lratCheckerSound f2089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2089
  · intro a ha; simp [p2089] at ha; subst a; trivial
  · exact checked2089
theorem derived2089 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2089 := by
  apply localUnsat_implies_entails f2089 [c2033, c1376] c2089 unsat2089 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1376 := derived1376 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2090 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2090 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1377, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p2090 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2090 : lratChecker f2090 p2090 = .success := by decide +kernel
theorem unsat2090 : Unsatisfiable (PosFin 57) f2090 := by
  apply lratCheckerSound f2090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2090
  · intro a ha; simp [p2090] at ha; subst a; trivial
  · exact checked2090
theorem derived2090 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2090 := by
  apply localUnsat_implies_entails f2090 [c2033, c1377] c2090 unsat2090 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1377 := derived1377 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2091 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2091 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1379, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p2091 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2091 : lratChecker f2091 p2091 = .success := by decide +kernel
theorem unsat2091 : Unsatisfiable (PosFin 57) f2091 := by
  apply lratCheckerSound f2091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2091
  · intro a ha; simp [p2091] at ha; subst a; trivial
  · exact checked2091
theorem derived2091 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2091 := by
  apply localUnsat_implies_entails f2091 [c2033, c1379] c2091 unsat2091 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1379 := derived1379 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2092 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2092 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1392, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p2092 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2092 : lratChecker f2092 p2092 = .success := by decide +kernel
theorem unsat2092 : Unsatisfiable (PosFin 57) f2092 := by
  apply lratCheckerSound f2092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2092
  · intro a ha; simp [p2092] at ha; subst a; trivial
  · exact checked2092
theorem derived2092 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2092 := by
  apply localUnsat_implies_entails f2092 [c2033, c1392] c2092 unsat2092 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1392 := derived1392 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2093 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨39, by decide⟩, true), (⟨4, by decide⟩, false), (⟨23, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2093 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1401, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2093 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2093 : lratChecker f2093 p2093 = .success := by decide +kernel
theorem unsat2093 : Unsatisfiable (PosFin 57) f2093 := by
  apply lratCheckerSound f2093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2093
  · intro a ha; simp [p2093] at ha; subst a; trivial
  · exact checked2093
theorem derived2093 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2093 := by
  apply localUnsat_implies_entails f2093 [c2033, c1401] c2093 unsat2093 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1401 := derived1401 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2094 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2094 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1473, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p2094 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2094 : lratChecker f2094 p2094 = .success := by decide +kernel
theorem unsat2094 : Unsatisfiable (PosFin 57) f2094 := by
  apply lratCheckerSound f2094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2094
  · intro a ha; simp [p2094] at ha; subst a; trivial
  · exact checked2094
theorem derived2094 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2094 := by
  apply localUnsat_implies_entails f2094 [c2033, c1473] c2094 unsat2094 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1473 := derived1473 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2095 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2095 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2051, some c2061, some c2038, some c2045, some c14, some c190, some c2035, some c1887, some c2036, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2095 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2095 : lratChecker f2095 p2095 = .success := by decide +kernel
theorem unsat2095 : Unsatisfiable (PosFin 57) f2095 := by
  apply lratCheckerSound f2095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2095
  · intro a ha; simp [p2095] at ha; subst a; trivial
  · exact checked2095
theorem derived2095 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2095 := by
  apply localUnsat_implies_entails f2095 [c2051, c2061, c2038, c2045, c14, c190, c2035, c1887, c2036] c2095 unsat2095 (by rfl) a
  have h0 : Entails.eval a c2051 := derived2051 a h
  have h1 : Entails.eval a c2061 := derived2061 a h
  have h2 : Entails.eval a c2038 := derived2038 a h
  have h3 : Entails.eval a c2045 := derived2045 a h
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c2035 := derived2035 a h
  have h7 : Entails.eval a c1887 := derived1887 a h
  have h8 : Entails.eval a c2036 := derived2036 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2096 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨13, by decide⟩, false), (⟨43, by decide⟩, false), (⟨56, by decide⟩, true), (⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2096 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1827, some c250, some c113, some c264, some c366, some c2070, some c684, some c370, some c371, some c363, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p2096 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2096 : lratChecker f2096 p2096 = .success := by decide +kernel
theorem unsat2096 : Unsatisfiable (PosFin 57) f2096 := by
  apply lratCheckerSound f2096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2096
  · intro a ha; simp [p2096] at ha; subst a; trivial
  · exact checked2096
theorem derived2096 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2096 := by
  apply localUnsat_implies_entails f2096 [c1827, c250, c113, c264, c366, c2070, c684, c370, c371, c363] c2096 unsat2096 (by rfl) a
  have h0 : Entails.eval a c1827 := derived1827 a h
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c2070 := derived2070 a h
  have h6 : Entails.eval a c684 := derived684 a h
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2097 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2097 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2051, some c3, some c2061, some c2034, some c2038, some c2045, some c14, some c2063, some c1827, some c2095, some c189, some c181, some c245, some c2096, some c754, some c232, some c363, some c364, some c373, some c370, some c78, some c26, some c2058, some c2070, some c242, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2097 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2097 : lratChecker f2097 p2097 = .success := by decide +kernel
theorem unsat2097 : Unsatisfiable (PosFin 57) f2097 := by
  apply lratCheckerSound f2097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2097
  · intro a ha; simp [p2097] at ha; subst a; trivial
  · exact checked2097
theorem derived2097 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2097 := by
  apply localUnsat_implies_entails f2097 [c2051, c3, c2061, c2034, c2038, c2045, c14, c2063, c1827, c2095, c189, c181, c245, c2096, c754, c232, c363, c364, c373, c370, c78, c26, c2058, c2070, c242] c2097 unsat2097 (by rfl) a
  have h0 : Entails.eval a c2051 := derived2051 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c2061 := derived2061 a h
  have h3 : Entails.eval a c2034 := derived2034 a h
  have h4 : Entails.eval a c2038 := derived2038 a h
  have h5 : Entails.eval a c2045 := derived2045 a h
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c2063 := derived2063 a h
  have h8 : Entails.eval a c1827 := derived1827 a h
  have h9 : Entails.eval a c2095 := derived2095 a h
  have h10 : Entails.eval a c189 := h 188 (by decide)
  have h11 : Entails.eval a c181 := h 180 (by decide)
  have h12 : Entails.eval a c245 := h 244 (by decide)
  have h13 : Entails.eval a c2096 := derived2096 a h
  have h14 : Entails.eval a c754 := derived754 a h
  have h15 : Entails.eval a c232 := h 231 (by decide)
  have h16 : Entails.eval a c363 := h 362 (by decide)
  have h17 : Entails.eval a c364 := h 363 (by decide)
  have h18 : Entails.eval a c373 := h 372 (by decide)
  have h19 : Entails.eval a c370 := h 369 (by decide)
  have h20 : Entails.eval a c78 := h 77 (by decide)
  have h21 : Entails.eval a c26 := h 25 (by decide)
  have h22 : Entails.eval a c2058 := derived2058 a h
  have h23 : Entails.eval a c2070 := derived2070 a h
  have h24 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2098 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨4, by decide⟩, true), (⟨51, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2098 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c182, some c852, some c78, some c367, some c361, some c2046, some c1827, some c19, some c91, some c176, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2098 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2098 : lratChecker f2098 p2098 = .success := by decide +kernel
theorem unsat2098 : Unsatisfiable (PosFin 57) f2098 := by
  apply lratCheckerSound f2098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2098
  · intro a ha; simp [p2098] at ha; subst a; trivial
  · exact checked2098
theorem derived2098 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2098 := by
  apply localUnsat_implies_entails f2098 [c182, c852, c78, c367, c361, c2046, c1827, c19, c91, c176] c2098 unsat2098 (by rfl) a
  have h0 : Entails.eval a c182 := h 181 (by decide)
  have h1 : Entails.eval a c852 := derived852 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c361 := h 360 (by decide)
  have h5 : Entails.eval a c2046 := derived2046 a h
  have h6 : Entails.eval a c1827 := derived1827 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2099 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2099 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c191, some c1314, some c2089, some c2090, some c2046, some c18, some c2060, some c114, some c2070, some c162, some c90, some c277, some c316, some c197, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2099 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2099 : lratChecker f2099 p2099 = .success := by decide +kernel
theorem unsat2099 : Unsatisfiable (PosFin 57) f2099 := by
  apply lratCheckerSound f2099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2099
  · intro a ha; simp [p2099] at ha; subst a; trivial
  · exact checked2099
theorem derived2099 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2099 := by
  apply localUnsat_implies_entails f2099 [c5, c191, c1314, c2089, c2090, c2046, c18, c2060, c114, c2070, c162, c90, c277, c316, c197] c2099 unsat2099 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c1314 := derived1314 a h
  have h3 : Entails.eval a c2089 := derived2089 a h
  have h4 : Entails.eval a c2090 := derived2090 a h
  have h5 : Entails.eval a c2046 := derived2046 a h
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c2060 := derived2060 a h
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c2070 := derived2070 a h
  have h10 : Entails.eval a c162 := h 161 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c277 := h 276 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2100 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2100 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2097, some c5, some c2099, some c2056, some c2061, some c1928, some c2048, some c2053, some c2098, some c2088, some c377, some c852, some c2045, some c26, some c242, some c125, some c2067, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2100 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2100 : lratChecker f2100 p2100 = .success := by decide +kernel
theorem unsat2100 : Unsatisfiable (PosFin 57) f2100 := by
  apply lratCheckerSound f2100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2100
  · intro a ha; simp [p2100] at ha; subst a; trivial
  · exact checked2100
theorem derived2100 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2100 := by
  apply localUnsat_implies_entails f2100 [c2097, c5, c2099, c2056, c2061, c1928, c2048, c2053, c2098, c2088, c377, c852, c2045, c26, c242, c125, c2067] c2100 unsat2100 (by rfl) a
  have h0 : Entails.eval a c2097 := derived2097 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c2099 := derived2099 a h
  have h3 : Entails.eval a c2056 := derived2056 a h
  have h4 : Entails.eval a c2061 := derived2061 a h
  have h5 : Entails.eval a c1928 := derived1928 a h
  have h6 : Entails.eval a c2048 := derived2048 a h
  have h7 : Entails.eval a c2053 := derived2053 a h
  have h8 : Entails.eval a c2098 := derived2098 a h
  have h9 : Entails.eval a c2088 := derived2088 a h
  have h10 : Entails.eval a c377 := h 376 (by decide)
  have h11 : Entails.eval a c852 := derived852 a h
  have h12 : Entails.eval a c2045 := derived2045 a h
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c242 := h 241 (by decide)
  have h15 : Entails.eval a c125 := h 124 (by decide)
  have h16 : Entails.eval a c2067 := derived2067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2101 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2101 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c19, some c2089, some c2090, some c302, some c341, some c131, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2101 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2101 : lratChecker f2101 p2101 = .success := by decide +kernel
theorem unsat2101 : Unsatisfiable (PosFin 57) f2101 := by
  apply lratCheckerSound f2101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2101
  · intro a ha; simp [p2101] at ha; subst a; trivial
  · exact checked2101
theorem derived2101 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2101 := by
  apply localUnsat_implies_entails f2101 [c5, c19, c2089, c2090, c302, c341, c131] c2101 unsat2101 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c2089 := derived2089 a h
  have h3 : Entails.eval a c2090 := derived2090 a h
  have h4 : Entails.eval a c302 := h 301 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2102 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2102 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2097, some c2100, some c181, some c2086, some c3, some c2061, some c2101, some c190, some c18, some c188, some c2045, some c381, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2102 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2102 : lratChecker f2102 p2102 = .success := by decide +kernel
theorem unsat2102 : Unsatisfiable (PosFin 57) f2102 := by
  apply lratCheckerSound f2102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2102
  · intro a ha; simp [p2102] at ha; subst a; trivial
  · exact checked2102
theorem derived2102 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2102 := by
  apply localUnsat_implies_entails f2102 [c2097, c2100, c181, c2086, c3, c2061, c2101, c190, c18, c188, c2045, c381] c2102 unsat2102 (by rfl) a
  have h0 : Entails.eval a c2097 := derived2097 a h
  have h1 : Entails.eval a c2100 := derived2100 a h
  have h2 : Entails.eval a c181 := h 180 (by decide)
  have h3 : Entails.eval a c2086 := derived2086 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c2061 := derived2061 a h
  have h6 : Entails.eval a c2101 := derived2101 a h
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c2045 := derived2045 a h
  have h11 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2103 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2103 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2056, some c2061, some c2048, some c2053, some c76, some c172, some c77, some c25, some c241, some c124, some c2067, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2103 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2103 : lratChecker f2103 p2103 = .success := by decide +kernel
theorem unsat2103 : Unsatisfiable (PosFin 57) f2103 := by
  apply lratCheckerSound f2103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2103
  · intro a ha; simp [p2103] at ha; subst a; trivial
  · exact checked2103
theorem derived2103 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2103 := by
  apply localUnsat_implies_entails f2103 [c2056, c2061, c2048, c2053, c76, c172, c77, c25, c241, c124, c2067] c2103 unsat2103 (by rfl) a
  have h0 : Entails.eval a c2056 := derived2056 a h
  have h1 : Entails.eval a c2061 := derived2061 a h
  have h2 : Entails.eval a c2048 := derived2048 a h
  have h3 : Entails.eval a c2053 := derived2053 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c2067 := derived2067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2104 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2104 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2097, some c2102, some c2103, some c189, some c2086, some c3, some c1972, some c1852, some c77, some c25, some c250, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p2104 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2104 : lratChecker f2104 p2104 = .success := by decide +kernel
theorem unsat2104 : Unsatisfiable (PosFin 57) f2104 := by
  apply lratCheckerSound f2104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2104
  · intro a ha; simp [p2104] at ha; subst a; trivial
  · exact checked2104
theorem derived2104 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2104 := by
  apply localUnsat_implies_entails f2104 [c2097, c2102, c2103, c189, c2086, c3, c1972, c1852, c77, c25, c250] c2104 unsat2104 (by rfl) a
  have h0 : Entails.eval a c2097 := derived2097 a h
  have h1 : Entails.eval a c2102 := derived2102 a h
  have h2 : Entails.eval a c2103 := derived2103 a h
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c2086 := derived2086 a h
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1972 := derived1972 a h
  have h7 : Entails.eval a c1852 := derived1852 a h
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2105 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2105 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2061, some c15, some c191, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2105 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2105 : lratChecker f2105 p2105 = .success := by decide +kernel
theorem unsat2105 : Unsatisfiable (PosFin 57) f2105 := by
  apply lratCheckerSound f2105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2105
  · intro a ha; simp [p2105] at ha; subst a; trivial
  · exact checked2105
theorem derived2105 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2105 := by
  apply localUnsat_implies_entails f2105 [c2061, c15, c191] c2105 unsat2105 (by rfl) a
  have h0 : Entails.eval a c2061 := derived2061 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2106 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2106 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2104, some c1254, some c2046, some c2039, some c2045, some c4, some c2057, some c1278, some c377, some c188, some c2105, some c2051, some c2082, some c1314, some c2081, some c2103, some c19, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2106 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2106 : lratChecker f2106 p2106 = .success := by decide +kernel
theorem unsat2106 : Unsatisfiable (PosFin 57) f2106 := by
  apply lratCheckerSound f2106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2106
  · intro a ha; simp [p2106] at ha; subst a; trivial
  · exact checked2106
theorem derived2106 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2106 := by
  apply localUnsat_implies_entails f2106 [c2104, c1254, c2046, c2039, c2045, c4, c2057, c1278, c377, c188, c2105, c2051, c2082, c1314, c2081, c2103, c19] c2106 unsat2106 (by rfl) a
  have h0 : Entails.eval a c2104 := derived2104 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2039 := derived2039 a h
  have h4 : Entails.eval a c2045 := derived2045 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c2057 := derived2057 a h
  have h7 : Entails.eval a c1278 := derived1278 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c2105 := derived2105 a h
  have h11 : Entails.eval a c2051 := derived2051 a h
  have h12 : Entails.eval a c2082 := derived2082 a h
  have h13 : Entails.eval a c1314 := derived1314 a h
  have h14 : Entails.eval a c2081 := derived2081 a h
  have h15 : Entails.eval a c2103 := derived2103 a h
  have h16 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2107 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, false), (⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2107 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2051, some c3, some c1003, some c2061, some c189, some c1872, some c383, some c469, some c2034, some c251, some c1158, some c236, some c2093, some c359, some c386, some c342, some c155, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2107 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2107 : lratChecker f2107 p2107 = .success := by decide +kernel
theorem unsat2107 : Unsatisfiable (PosFin 57) f2107 := by
  apply lratCheckerSound f2107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2107
  · intro a ha; simp [p2107] at ha; subst a; trivial
  · exact checked2107
theorem derived2107 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2107 := by
  apply localUnsat_implies_entails f2107 [c2051, c3, c1003, c2061, c189, c1872, c383, c469, c2034, c251, c1158, c236, c2093, c359, c386, c342, c155] c2107 unsat2107 (by rfl) a
  have h0 : Entails.eval a c2051 := derived2051 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c2061 := derived2061 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c1872 := derived1872 a h
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c469 := derived469 a h
  have h8 : Entails.eval a c2034 := derived2034 a h
  have h9 : Entails.eval a c251 := h 250 (by decide)
  have h10 : Entails.eval a c1158 := derived1158 a h
  have h11 : Entails.eval a c236 := h 235 (by decide)
  have h12 : Entails.eval a c2093 := derived2093 a h
  have h13 : Entails.eval a c359 := h 358 (by decide)
  have h14 : Entails.eval a c386 := derived386 a h
  have h15 : Entails.eval a c342 := h 341 (by decide)
  have h16 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2108 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2108 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2051, some c3, some c2106, some c1003, some c2061, some c189, some c1872, some c383, some c2034, some c251, some c190, some c15, some c2046, some c1746, some c2063, some c185, some c469, some c364, some c76, some c2107, some c260, some c125, some c26, some c373, some c233, some c359, some c375, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2108 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2108 : lratChecker f2108 p2108 = .success := by decide +kernel
theorem unsat2108 : Unsatisfiable (PosFin 57) f2108 := by
  apply lratCheckerSound f2108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2108
  · intro a ha; simp [p2108] at ha; subst a; trivial
  · exact checked2108
theorem derived2108 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2108 := by
  apply localUnsat_implies_entails f2108 [c2051, c3, c2106, c1003, c2061, c189, c1872, c383, c2034, c251, c190, c15, c2046, c1746, c2063, c185, c469, c364, c76, c2107, c260, c125, c26, c373, c233, c359, c375] c2108 unsat2108 (by rfl) a
  have h0 : Entails.eval a c2051 := derived2051 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c2106 := derived2106 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c2061 := derived2061 a h
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c1872 := derived1872 a h
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c2034 := derived2034 a h
  have h9 : Entails.eval a c251 := h 250 (by decide)
  have h10 : Entails.eval a c190 := h 189 (by decide)
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c2046 := derived2046 a h
  have h13 : Entails.eval a c1746 := derived1746 a h
  have h14 : Entails.eval a c2063 := derived2063 a h
  have h15 : Entails.eval a c185 := h 184 (by decide)
  have h16 : Entails.eval a c469 := derived469 a h
  have h17 : Entails.eval a c364 := h 363 (by decide)
  have h18 : Entails.eval a c76 := h 75 (by decide)
  have h19 : Entails.eval a c2107 := derived2107 a h
  have h20 : Entails.eval a c260 := h 259 (by decide)
  have h21 : Entails.eval a c125 := h 124 (by decide)
  have h22 : Entails.eval a c26 := h 25 (by decide)
  have h23 : Entails.eval a c373 := h 372 (by decide)
  have h24 : Entails.eval a c233 := h 232 (by decide)
  have h25 : Entails.eval a c359 := h 358 (by decide)
  have h26 : Entails.eval a c375 := h 374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2109 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2109 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2039, some c2045, some c2057, some c378, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p2109 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2109 : lratChecker f2109 p2109 = .success := by decide +kernel
theorem unsat2109 : Unsatisfiable (PosFin 57) f2109 := by
  apply lratCheckerSound f2109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2109
  · intro a ha; simp [p2109] at ha; subst a; trivial
  · exact checked2109
theorem derived2109 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2109 := by
  apply localUnsat_implies_entails f2109 [c2039, c2045, c2057, c378] c2109 unsat2109 (by rfl) a
  have h0 : Entails.eval a c2039 := derived2039 a h
  have h1 : Entails.eval a c2045 := derived2045 a h
  have h2 : Entails.eval a c2057 := derived2057 a h
  have h3 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2110 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2110 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2106, some c2109, some c1254, some c2051, some c14, some c2108, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2110 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2110 : lratChecker f2110 p2110 = .success := by decide +kernel
theorem unsat2110 : Unsatisfiable (PosFin 57) f2110 := by
  apply lratCheckerSound f2110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2110
  · intro a ha; simp [p2110] at ha; subst a; trivial
  · exact checked2110
theorem derived2110 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2110 := by
  apply localUnsat_implies_entails f2110 [c2106, c2109, c1254, c2051, c14, c2108] c2110 unsat2110 (by rfl) a
  have h0 : Entails.eval a c2106 := derived2106 a h
  have h1 : Entails.eval a c2109 := derived2109 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c2051 := derived2051 a h
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c2108 := derived2108 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2111 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2111 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2106, some c1003, some c2109, some c1254, some c2110, some c2103, some c189, some c1806, some c2086, some c383, some c3, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2111 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2111 : lratChecker f2111 p2111 = .success := by decide +kernel
theorem unsat2111 : Unsatisfiable (PosFin 57) f2111 := by
  apply lratCheckerSound f2111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2111
  · intro a ha; simp [p2111] at ha; subst a; trivial
  · exact checked2111
theorem derived2111 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2111 := by
  apply localUnsat_implies_entails f2111 [c2106, c1003, c2109, c1254, c2110, c2103, c189, c1806, c2086, c383, c3] c2111 unsat2111 (by rfl) a
  have h0 : Entails.eval a c2106 := derived2106 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c2109 := derived2109 a h
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c2110 := derived2110 a h
  have h5 : Entails.eval a c2103 := derived2103 a h
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c1806 := derived1806 a h
  have h8 : Entails.eval a c2086 := derived2086 a h
  have h9 : Entails.eval a c383 := h 382 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2112 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2112 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2034, some c2051, some c3, some c2111, some c379, some c2061, some c382, some c180, some c189, some c181, some c251, some c249, some c190, some c15, some c2046, some c2063, some c1746, some c469, some c1158, some c2077, some c366, some c2107, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2112 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2112 : lratChecker f2112 p2112 = .success := by decide +kernel
theorem unsat2112 : Unsatisfiable (PosFin 57) f2112 := by
  apply lratCheckerSound f2112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2112
  · intro a ha; simp [p2112] at ha; subst a; trivial
  · exact checked2112
theorem derived2112 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2112 := by
  apply localUnsat_implies_entails f2112 [c2034, c2051, c3, c2111, c379, c2061, c382, c180, c189, c181, c251, c249, c190, c15, c2046, c2063, c1746, c469, c1158, c2077, c366, c2107] c2112 unsat2112 (by rfl) a
  have h0 : Entails.eval a c2034 := derived2034 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c2111 := derived2111 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c2061 := derived2061 a h
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c181 := h 180 (by decide)
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c249 := h 248 (by decide)
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c2046 := derived2046 a h
  have h15 : Entails.eval a c2063 := derived2063 a h
  have h16 : Entails.eval a c1746 := derived1746 a h
  have h17 : Entails.eval a c469 := derived469 a h
  have h18 : Entails.eval a c1158 := derived1158 a h
  have h19 : Entails.eval a c2077 := derived2077 a h
  have h20 : Entails.eval a c366 := h 365 (by decide)
  have h21 : Entails.eval a c2107 := derived2107 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2113 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2113 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2034, some c2111, some c2051, some c3, some c249, some c2061, some c2046, some c2039, some c2047, some c15, some c2067, some c116, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2113 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2113 : lratChecker f2113 p2113 = .success := by decide +kernel
theorem unsat2113 : Unsatisfiable (PosFin 57) f2113 := by
  apply lratCheckerSound f2113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2113
  · intro a ha; simp [p2113] at ha; subst a; trivial
  · exact checked2113
theorem derived2113 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2113 := by
  apply localUnsat_implies_entails f2113 [c2034, c2111, c2051, c3, c249, c2061, c2046, c2039, c2047, c15, c2067, c116] c2113 unsat2113 (by rfl) a
  have h0 : Entails.eval a c2034 := derived2034 a h
  have h1 : Entails.eval a c2111 := derived2111 a h
  have h2 : Entails.eval a c2051 := derived2051 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c249 := h 248 (by decide)
  have h5 : Entails.eval a c2061 := derived2061 a h
  have h6 : Entails.eval a c2046 := derived2046 a h
  have h7 : Entails.eval a c2039 := derived2039 a h
  have h8 : Entails.eval a c2047 := derived2047 a h
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c2067 := derived2067 a h
  have h11 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2114 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2114 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2051, some c2113, some c1254, some c14, some c2112, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2114 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2114 : lratChecker f2114 p2114 = .success := by decide +kernel
theorem unsat2114 : Unsatisfiable (PosFin 57) f2114 := by
  apply lratCheckerSound f2114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2114
  · intro a ha; simp [p2114] at ha; subst a; trivial
  · exact checked2114
theorem derived2114 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2114 := by
  apply localUnsat_implies_entails f2114 [c2051, c2113, c1254, c14, c2112] c2114 unsat2114 (by rfl) a
  have h0 : Entails.eval a c2051 := derived2051 a h
  have h1 : Entails.eval a c2113 := derived2113 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c2112 := derived2112 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2115 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2115 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2114, some c2111, some c3, some c2061, some c379, some c382, some c180, some c77, some c1806, some c512, some c2066, some c374, some c2039, some c2069, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2115 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2115 : lratChecker f2115 p2115 = .success := by decide +kernel
theorem unsat2115 : Unsatisfiable (PosFin 57) f2115 := by
  apply lratCheckerSound f2115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2115
  · intro a ha; simp [p2115] at ha; subst a; trivial
  · exact checked2115
theorem derived2115 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2115 := by
  apply localUnsat_implies_entails f2115 [c2114, c2111, c3, c2061, c379, c382, c180, c77, c1806, c512, c2066, c374, c2039, c2069] c2115 unsat2115 (by rfl) a
  have h0 : Entails.eval a c2114 := derived2114 a h
  have h1 : Entails.eval a c2111 := derived2111 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c2061 := derived2061 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c1806 := derived1806 a h
  have h9 : Entails.eval a c512 := derived512 a h
  have h10 : Entails.eval a c2066 := derived2066 a h
  have h11 : Entails.eval a c374 := h 373 (by decide)
  have h12 : Entails.eval a c2039 := derived2039 a h
  have h13 : Entails.eval a c2069 := derived2069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2116 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2116 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c2099, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p2116 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2116 : lratChecker f2116 p2116 = .success := by decide +kernel
theorem unsat2116 : Unsatisfiable (PosFin 57) f2116 := by
  apply lratCheckerSound f2116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2116
  · intro a ha; simp [p2116] at ha; subst a; trivial
  · exact checked2116
theorem derived2116 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2116 := by
  apply localUnsat_implies_entails f2116 [c189, c2099] c2116 unsat2116 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c2099 := derived2099 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2117 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨23, by decide⟩, true), (⟨45, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2117 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c244, some c2070, some c368, some c367, some c1458, some c2043, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p2117 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2117 : lratChecker f2117 p2117 = .success := by decide +kernel
theorem unsat2117 : Unsatisfiable (PosFin 57) f2117 := by
  apply lratCheckerSound f2117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2117
  · intro a ha; simp [p2117] at ha; subst a; trivial
  · exact checked2117
theorem derived2117 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2117 := by
  apply localUnsat_implies_entails f2117 [c377, c244, c2070, c368, c367, c1458, c2043] c2117 unsat2117 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c244 := h 243 (by decide)
  have h2 : Entails.eval a c2070 := derived2070 a h
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c1458 := derived1458 a h
  have h6 : Entails.eval a c2043 := derived2043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2118 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2118 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2115, some c2083, some c2046, some c2114, some c2086, some c2116, some c2056, some c2048, some c2111, some c5, some c19, some c1790, some c2085, some c25, some c128, some c127, some c2117, some c80, some c175, some c176, some c240, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2118 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2118 : lratChecker f2118 p2118 = .success := by decide +kernel
theorem unsat2118 : Unsatisfiable (PosFin 57) f2118 := by
  apply lratCheckerSound f2118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2118
  · intro a ha; simp [p2118] at ha; subst a; trivial
  · exact checked2118
theorem derived2118 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2118 := by
  apply localUnsat_implies_entails f2118 [c2115, c2083, c2046, c2114, c2086, c2116, c2056, c2048, c2111, c5, c19, c1790, c2085, c25, c128, c127, c2117, c80, c175, c176, c240] c2118 unsat2118 (by rfl) a
  have h0 : Entails.eval a c2115 := derived2115 a h
  have h1 : Entails.eval a c2083 := derived2083 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2114 := derived2114 a h
  have h4 : Entails.eval a c2086 := derived2086 a h
  have h5 : Entails.eval a c2116 := derived2116 a h
  have h6 : Entails.eval a c2056 := derived2056 a h
  have h7 : Entails.eval a c2048 := derived2048 a h
  have h8 : Entails.eval a c2111 := derived2111 a h
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c1790 := derived1790 a h
  have h12 : Entails.eval a c2085 := derived2085 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c128 := h 127 (by decide)
  have h15 : Entails.eval a c127 := h 126 (by decide)
  have h16 : Entails.eval a c2117 := derived2117 a h
  have h17 : Entails.eval a c80 := h 79 (by decide)
  have h18 : Entails.eval a c175 := h 174 (by decide)
  have h19 : Entails.eval a c176 := h 175 (by decide)
  have h20 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2119 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨54, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, true), (⟨12, by decide⟩, false), (⟨15, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2119 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c174, some c172, some c367, some c89, some c2069, some c369, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2119 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2119 : lratChecker f2119 p2119 = .success := by decide +kernel
theorem unsat2119 : Unsatisfiable (PosFin 57) f2119 := by
  apply lratCheckerSound f2119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2119
  · intro a ha; simp [p2119] at ha; subst a; trivial
  · exact checked2119
theorem derived2119 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2119 := by
  apply localUnsat_implies_entails f2119 [c174, c172, c367, c89, c2069, c369] c2119 unsat2119 (by rfl) a
  have h0 : Entails.eval a c174 := h 173 (by decide)
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c2069 := derived2069 a h
  have h5 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2120 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2120 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2114, some c2115, some c2086, some c2116, some c2056, some c2048, some c2111, some c77, some c25, some c1790, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2120 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2120 : lratChecker f2120 p2120 = .success := by decide +kernel
theorem unsat2120 : Unsatisfiable (PosFin 57) f2120 := by
  apply lratCheckerSound f2120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2120
  · intro a ha; simp [p2120] at ha; subst a; trivial
  · exact checked2120
theorem derived2120 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2120 := by
  apply localUnsat_implies_entails f2120 [c2114, c2115, c2086, c2116, c2056, c2048, c2111, c77, c25, c1790] c2120 unsat2120 (by rfl) a
  have h0 : Entails.eval a c2114 := derived2114 a h
  have h1 : Entails.eval a c2115 := derived2115 a h
  have h2 : Entails.eval a c2086 := derived2086 a h
  have h3 : Entails.eval a c2116 := derived2116 a h
  have h4 : Entails.eval a c2056 := derived2056 a h
  have h5 : Entails.eval a c2048 := derived2048 a h
  have h6 : Entails.eval a c2111 := derived2111 a h
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c1790 := derived1790 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2121 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2121 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2120, some c2115, some c2048, some c2114, some c2086, some c2116, some c2053, some c2056, some c2046, some c2083, some c2118, some c174, some c172, some c2064, some c2119, some c567, some c89, some c124, some c377, some c1704, some c39, some c8, some c240, some c128, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2121 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2121 : lratChecker f2121 p2121 = .success := by decide +kernel
theorem unsat2121 : Unsatisfiable (PosFin 57) f2121 := by
  apply lratCheckerSound f2121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2121
  · intro a ha; simp [p2121] at ha; subst a; trivial
  · exact checked2121
theorem derived2121 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2121 := by
  apply localUnsat_implies_entails f2121 [c2120, c2115, c2048, c2114, c2086, c2116, c2053, c2056, c2046, c2083, c2118, c174, c172, c2064, c2119, c567, c89, c124, c377, c1704, c39, c8, c240, c128] c2121 unsat2121 (by rfl) a
  have h0 : Entails.eval a c2120 := derived2120 a h
  have h1 : Entails.eval a c2115 := derived2115 a h
  have h2 : Entails.eval a c2048 := derived2048 a h
  have h3 : Entails.eval a c2114 := derived2114 a h
  have h4 : Entails.eval a c2086 := derived2086 a h
  have h5 : Entails.eval a c2116 := derived2116 a h
  have h6 : Entails.eval a c2053 := derived2053 a h
  have h7 : Entails.eval a c2056 := derived2056 a h
  have h8 : Entails.eval a c2046 := derived2046 a h
  have h9 : Entails.eval a c2083 := derived2083 a h
  have h10 : Entails.eval a c2118 := derived2118 a h
  have h11 : Entails.eval a c174 := h 173 (by decide)
  have h12 : Entails.eval a c172 := h 171 (by decide)
  have h13 : Entails.eval a c2064 := derived2064 a h
  have h14 : Entails.eval a c2119 := derived2119 a h
  have h15 : Entails.eval a c567 := derived567 a h
  have h16 : Entails.eval a c89 := h 88 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c377 := h 376 (by decide)
  have h19 : Entails.eval a c1704 := derived1704 a h
  have h20 : Entails.eval a c39 := h 38 (by decide)
  have h21 : Entails.eval a c8 := h 7 (by decide)
  have h22 : Entails.eval a c240 := h 239 (by decide)
  have h23 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2122 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2122 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2115, some c2048, some c2114, some c2086, some c2116, some c2053, some c2056, some c2111, some c5, some c18, some c1790, some c38, some c125, some c24, some c2067, some c173, some c242, some c78, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2122 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2122 : lratChecker f2122 p2122 = .success := by decide +kernel
theorem unsat2122 : Unsatisfiable (PosFin 57) f2122 := by
  apply lratCheckerSound f2122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2122
  · intro a ha; simp [p2122] at ha; subst a; trivial
  · exact checked2122
theorem derived2122 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2122 := by
  apply localUnsat_implies_entails f2122 [c2115, c2048, c2114, c2086, c2116, c2053, c2056, c2111, c5, c18, c1790, c38, c125, c24, c2067, c173, c242, c78] c2122 unsat2122 (by rfl) a
  have h0 : Entails.eval a c2115 := derived2115 a h
  have h1 : Entails.eval a c2048 := derived2048 a h
  have h2 : Entails.eval a c2114 := derived2114 a h
  have h3 : Entails.eval a c2086 := derived2086 a h
  have h4 : Entails.eval a c2116 := derived2116 a h
  have h5 : Entails.eval a c2053 := derived2053 a h
  have h6 : Entails.eval a c2056 := derived2056 a h
  have h7 : Entails.eval a c2111 := derived2111 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c1790 := derived1790 a h
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c2067 := derived2067 a h
  have h15 : Entails.eval a c173 := h 172 (by decide)
  have h16 : Entails.eval a c242 := h 241 (by decide)
  have h17 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2123 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2123 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2120, some c2115, some c2048, some c2114, some c2086, some c2116, some c2053, some c2122, some c2064, some c2054, some c124, some c6, some c38, some c125, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2123 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2123 : lratChecker f2123 p2123 = .success := by decide +kernel
theorem unsat2123 : Unsatisfiable (PosFin 57) f2123 := by
  apply lratCheckerSound f2123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2123
  · intro a ha; simp [p2123] at ha; subst a; trivial
  · exact checked2123
theorem derived2123 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2123 := by
  apply localUnsat_implies_entails f2123 [c2120, c2115, c2048, c2114, c2086, c2116, c2053, c2122, c2064, c2054, c124, c6, c38, c125] c2123 unsat2123 (by rfl) a
  have h0 : Entails.eval a c2120 := derived2120 a h
  have h1 : Entails.eval a c2115 := derived2115 a h
  have h2 : Entails.eval a c2048 := derived2048 a h
  have h3 : Entails.eval a c2114 := derived2114 a h
  have h4 : Entails.eval a c2086 := derived2086 a h
  have h5 : Entails.eval a c2116 := derived2116 a h
  have h6 : Entails.eval a c2053 := derived2053 a h
  have h7 : Entails.eval a c2122 := derived2122 a h
  have h8 : Entails.eval a c2064 := derived2064 a h
  have h9 : Entails.eval a c2054 := derived2054 a h
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2124 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2124 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2114, some c2115, some c2086, some c2116, some c2056, some c2123, some c2046, some c2121, some c378, some c376, some c103, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2124 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2124 : lratChecker f2124 p2124 = .success := by decide +kernel
theorem unsat2124 : Unsatisfiable (PosFin 57) f2124 := by
  apply lratCheckerSound f2124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2124
  · intro a ha; simp [p2124] at ha; subst a; trivial
  · exact checked2124
theorem derived2124 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2124 := by
  apply localUnsat_implies_entails f2124 [c2114, c2115, c2086, c2116, c2056, c2123, c2046, c2121, c378, c376, c103] c2124 unsat2124 (by rfl) a
  have h0 : Entails.eval a c2114 := derived2114 a h
  have h1 : Entails.eval a c2115 := derived2115 a h
  have h2 : Entails.eval a c2086 := derived2086 a h
  have h3 : Entails.eval a c2116 := derived2116 a h
  have h4 : Entails.eval a c2056 := derived2056 a h
  have h5 : Entails.eval a c2123 := derived2123 a h
  have h6 : Entails.eval a c2046 := derived2046 a h
  have h7 : Entails.eval a c2121 := derived2121 a h
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2125 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2125 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2124, some c1254, some c2046, some c2114, some c2111, some c382, some c2094, some c2059, some c377, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2125 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2125 : lratChecker f2125 p2125 = .success := by decide +kernel
theorem unsat2125 : Unsatisfiable (PosFin 57) f2125 := by
  apply lratCheckerSound f2125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2125
  · intro a ha; simp [p2125] at ha; subst a; trivial
  · exact checked2125
theorem derived2125 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2125 := by
  apply localUnsat_implies_entails f2125 [c2124, c1254, c2046, c2114, c2111, c382, c2094, c2059, c377] c2125 unsat2125 (by rfl) a
  have h0 : Entails.eval a c2124 := derived2124 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2114 := derived2114 a h
  have h4 : Entails.eval a c2111 := derived2111 a h
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c2094 := derived2094 a h
  have h7 : Entails.eval a c2059 := derived2059 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2126 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2126 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2124, some c1254, some c2046, some c2114, some c2111, some c5, some c19, some c2085, some c120, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2126 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2126 : lratChecker f2126 p2126 = .success := by decide +kernel
theorem unsat2126 : Unsatisfiable (PosFin 57) f2126 := by
  apply lratCheckerSound f2126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2126
  · intro a ha; simp [p2126] at ha; subst a; trivial
  · exact checked2126
theorem derived2126 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2126 := by
  apply localUnsat_implies_entails f2126 [c2124, c1254, c2046, c2114, c2111, c5, c19, c2085, c120] c2126 unsat2126 (by rfl) a
  have h0 : Entails.eval a c2124 := derived2124 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2114 := derived2114 a h
  have h4 : Entails.eval a c2111 := derived2111 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c2085 := derived2085 a h
  have h8 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2127 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2127 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2124, some c1254, some c2046, some c2114, some c2059, some c103, some c377, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2127 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2127 : lratChecker f2127 p2127 = .success := by decide +kernel
theorem unsat2127 : Unsatisfiable (PosFin 57) f2127 := by
  apply lratCheckerSound f2127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2127
  · intro a ha; simp [p2127] at ha; subst a; trivial
  · exact checked2127
theorem derived2127 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2127 := by
  apply localUnsat_implies_entails f2127 [c2124, c1254, c2046, c2114, c2059, c103, c377] c2127 unsat2127 (by rfl) a
  have h0 : Entails.eval a c2124 := derived2124 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2114 := derived2114 a h
  have h4 : Entails.eval a c2059 := derived2059 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2128 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2128 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2124, some c1254, some c2046, some c2039, some c1278, some c2114, some c2111, some c1314, some c188, some c2125, some c3, some c2082, some c2126, some c2127, some c2062, some c2085, some c25, some c120, some c161, some c183, some c2058, some c377, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2128 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2128 : lratChecker f2128 p2128 = .success := by decide +kernel
theorem unsat2128 : Unsatisfiable (PosFin 57) f2128 := by
  apply lratCheckerSound f2128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2128
  · intro a ha; simp [p2128] at ha; subst a; trivial
  · exact checked2128
theorem derived2128 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2128 := by
  apply localUnsat_implies_entails f2128 [c2124, c1254, c2046, c2039, c1278, c2114, c2111, c1314, c188, c2125, c3, c2082, c2126, c2127, c2062, c2085, c25, c120, c161, c183, c2058, c377] c2128 unsat2128 (by rfl) a
  have h0 : Entails.eval a c2124 := derived2124 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2039 := derived2039 a h
  have h4 : Entails.eval a c1278 := derived1278 a h
  have h5 : Entails.eval a c2114 := derived2114 a h
  have h6 : Entails.eval a c2111 := derived2111 a h
  have h7 : Entails.eval a c1314 := derived1314 a h
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c2125 := derived2125 a h
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c2082 := derived2082 a h
  have h12 : Entails.eval a c2126 := derived2126 a h
  have h13 : Entails.eval a c2127 := derived2127 a h
  have h14 : Entails.eval a c2062 := derived2062 a h
  have h15 : Entails.eval a c2085 := derived2085 a h
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c120 := h 119 (by decide)
  have h18 : Entails.eval a c161 := h 160 (by decide)
  have h19 : Entails.eval a c183 := h 182 (by decide)
  have h20 : Entails.eval a c2058 := derived2058 a h
  have h21 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2129 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2129 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2124, some c1254, some c2046, some c2039, some c1278, some c2056, some c2061, some c2053, some c2082, some c2081, some c118, some c8, some c2047, some c2067, some c244, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2129 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2129 : lratChecker f2129 p2129 = .success := by decide +kernel
theorem unsat2129 : Unsatisfiable (PosFin 57) f2129 := by
  apply lratCheckerSound f2129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2129
  · intro a ha; simp [p2129] at ha; subst a; trivial
  · exact checked2129
theorem derived2129 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2129 := by
  apply localUnsat_implies_entails f2129 [c2124, c1254, c2046, c2039, c1278, c2056, c2061, c2053, c2082, c2081, c118, c8, c2047, c2067, c244] c2129 unsat2129 (by rfl) a
  have h0 : Entails.eval a c2124 := derived2124 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2039 := derived2039 a h
  have h4 : Entails.eval a c1278 := derived1278 a h
  have h5 : Entails.eval a c2056 := derived2056 a h
  have h6 : Entails.eval a c2061 := derived2061 a h
  have h7 : Entails.eval a c2053 := derived2053 a h
  have h8 : Entails.eval a c2082 := derived2082 a h
  have h9 : Entails.eval a c2081 := derived2081 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c2047 := derived2047 a h
  have h13 : Entails.eval a c2067 := derived2067 a h
  have h14 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2130 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2130 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2129, some c2128, some c2124, some c1254, some c2046, some c2114, some c2111, some c382, some c2094, some c2059, some c378, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2130 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2130 : lratChecker f2130 p2130 = .success := by decide +kernel
theorem unsat2130 : Unsatisfiable (PosFin 57) f2130 := by
  apply lratCheckerSound f2130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2130
  · intro a ha; simp [p2130] at ha; subst a; trivial
  · exact checked2130
theorem derived2130 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2130 := by
  apply localUnsat_implies_entails f2130 [c2129, c2128, c2124, c1254, c2046, c2114, c2111, c382, c2094, c2059, c378] c2130 unsat2130 (by rfl) a
  have h0 : Entails.eval a c2129 := derived2129 a h
  have h1 : Entails.eval a c2128 := derived2128 a h
  have h2 : Entails.eval a c2124 := derived2124 a h
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c2046 := derived2046 a h
  have h5 : Entails.eval a c2114 := derived2114 a h
  have h6 : Entails.eval a c2111 := derived2111 a h
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c2094 := derived2094 a h
  have h9 : Entails.eval a c2059 := derived2059 a h
  have h10 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2131 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2131 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2111, some c2114, some c2124, some c1254, some c2046, some c2039, some c1278, some c2129, some c1314, some c2128, some c1263, some c2130, some c3, some c182, some c2082, some c2127, some c120, some c2085, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2131 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2131 : lratChecker f2131 p2131 = .success := by decide +kernel
theorem unsat2131 : Unsatisfiable (PosFin 57) f2131 := by
  apply lratCheckerSound f2131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2131
  · intro a ha; simp [p2131] at ha; subst a; trivial
  · exact checked2131
theorem derived2131 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2131 := by
  apply localUnsat_implies_entails f2131 [c2111, c2114, c2124, c1254, c2046, c2039, c1278, c2129, c1314, c2128, c1263, c2130, c3, c182, c2082, c2127, c120, c2085] c2131 unsat2131 (by rfl) a
  have h0 : Entails.eval a c2111 := derived2111 a h
  have h1 : Entails.eval a c2114 := derived2114 a h
  have h2 : Entails.eval a c2124 := derived2124 a h
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c2046 := derived2046 a h
  have h5 : Entails.eval a c2039 := derived2039 a h
  have h6 : Entails.eval a c1278 := derived1278 a h
  have h7 : Entails.eval a c2129 := derived2129 a h
  have h8 : Entails.eval a c1314 := derived1314 a h
  have h9 : Entails.eval a c2128 := derived2128 a h
  have h10 : Entails.eval a c1263 := derived1263 a h
  have h11 : Entails.eval a c2130 := derived2130 a h
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c182 := h 181 (by decide)
  have h14 : Entails.eval a c2082 := derived2082 a h
  have h15 : Entails.eval a c2127 := derived2127 a h
  have h16 : Entails.eval a c120 := h 119 (by decide)
  have h17 : Entails.eval a c2085 := derived2085 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2132 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2132 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2039, some c2046, some c2045, some c2057, some c761, some c377, some c2065, some c87, some c370, some c369, some c367, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2132 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2132 : lratChecker f2132 p2132 = .success := by decide +kernel
theorem unsat2132 : Unsatisfiable (PosFin 57) f2132 := by
  apply lratCheckerSound f2132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2132
  · intro a ha; simp [p2132] at ha; subst a; trivial
  · exact checked2132
theorem derived2132 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2132 := by
  apply localUnsat_implies_entails f2132 [c2131, c2039, c2046, c2045, c2057, c761, c377, c2065, c87, c370, c369, c367] c2132 unsat2132 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2039 := derived2039 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2045 := derived2045 a h
  have h4 : Entails.eval a c2057 := derived2057 a h
  have h5 : Entails.eval a c761 := derived761 a h
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c2065 := derived2065 a h
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2133 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨54, by decide⟩, true), (⟨14, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2133 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2039, some c2046, some c2069, some c89, some c370, some c162, some c367, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2133 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2133 : lratChecker f2133 p2133 = .success := by decide +kernel
theorem unsat2133 : Unsatisfiable (PosFin 57) f2133 := by
  apply lratCheckerSound f2133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2133
  · intro a ha; simp [p2133] at ha; subst a; trivial
  · exact checked2133
theorem derived2133 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2133 := by
  apply localUnsat_implies_entails f2133 [c2039, c2046, c2069, c89, c370, c162, c367] c2133 unsat2133 (by rfl) a
  have h0 : Entails.eval a c2039 := derived2039 a h
  have h1 : Entails.eval a c2046 := derived2046 a h
  have h2 : Entails.eval a c2069 := derived2069 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2134 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨14, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2134 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2046, some c2039, some c190, some c17, some c2133, some c169, some c173, some c2065, some c87, some c367, some c370, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2134 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2134 : lratChecker f2134 p2134 = .success := by decide +kernel
theorem unsat2134 : Unsatisfiable (PosFin 57) f2134 := by
  apply lratCheckerSound f2134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2134
  · intro a ha; simp [p2134] at ha; subst a; trivial
  · exact checked2134
theorem derived2134 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2134 := by
  apply localUnsat_implies_entails f2134 [c2131, c2046, c2039, c190, c17, c2133, c169, c173, c2065, c87, c367, c370] c2134 unsat2134 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2046 := derived2046 a h
  have h2 : Entails.eval a c2039 := derived2039 a h
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c2133 := derived2133 a h
  have h6 : Entails.eval a c169 := h 168 (by decide)
  have h7 : Entails.eval a c173 := h 172 (by decide)
  have h8 : Entails.eval a c2065 := derived2065 a h
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2135 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2135 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2132, some c2039, some c2046, some c190, some c17, some c195, some c2134, some c377, some c1428, some c2076, some c382, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2135 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2135 : lratChecker f2135 p2135 = .success := by decide +kernel
theorem unsat2135 : Unsatisfiable (PosFin 57) f2135 := by
  apply lratCheckerSound f2135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2135
  · intro a ha; simp [p2135] at ha; subst a; trivial
  · exact checked2135
theorem derived2135 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2135 := by
  apply localUnsat_implies_entails f2135 [c2131, c2132, c2039, c2046, c190, c17, c195, c2134, c377, c1428, c2076, c382] c2135 unsat2135 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2132 := derived2132 a h
  have h2 : Entails.eval a c2039 := derived2039 a h
  have h3 : Entails.eval a c2046 := derived2046 a h
  have h4 : Entails.eval a c190 := h 189 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c2134 := derived2134 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c1428 := derived1428 a h
  have h10 : Entails.eval a c2076 := derived2076 a h
  have h11 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2136 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2136 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2132, some c2039, some c2046, some c188, some c196, some c191, some c186, some c17, some c382, some c75, some c1014, some c169, some c367, some c2069, some c89, some c369, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2136 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2136 : lratChecker f2136 p2136 = .success := by decide +kernel
theorem unsat2136 : Unsatisfiable (PosFin 57) f2136 := by
  apply lratCheckerSound f2136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2136
  · intro a ha; simp [p2136] at ha; subst a; trivial
  · exact checked2136
theorem derived2136 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2136 := by
  apply localUnsat_implies_entails f2136 [c2131, c2132, c2039, c2046, c188, c196, c191, c186, c17, c382, c75, c1014, c169, c367, c2069, c89, c369] c2136 unsat2136 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2132 := derived2132 a h
  have h2 : Entails.eval a c2039 := derived2039 a h
  have h3 : Entails.eval a c2046 := derived2046 a h
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c1014 := derived1014 a h
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c367 := h 366 (by decide)
  have h14 : Entails.eval a c2069 := derived2069 a h
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2137 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2137 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2132, some c2135, some c2136, some c380, some c377, some c181, some c2076, some c196, some c191, some c382, some c1428, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2137 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2137 : lratChecker f2137 p2137 = .success := by decide +kernel
theorem unsat2137 : Unsatisfiable (PosFin 57) f2137 := by
  apply lratCheckerSound f2137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2137
  · intro a ha; simp [p2137] at ha; subst a; trivial
  · exact checked2137
theorem derived2137 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2137 := by
  apply localUnsat_implies_entails f2137 [c2131, c2132, c2135, c2136, c380, c377, c181, c2076, c196, c191, c382, c1428] c2137 unsat2137 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2132 := derived2132 a h
  have h2 : Entails.eval a c2135 := derived2135 a h
  have h3 : Entails.eval a c2136 := derived2136 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c181 := h 180 (by decide)
  have h7 : Entails.eval a c2076 := derived2076 a h
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c191 := h 190 (by decide)
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c1428 := derived1428 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2138 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2138 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2132, some c2046, some c2137, some c8, some c99, some c191, some c379, some c181, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2138 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2138 : lratChecker f2138 p2138 = .success := by decide +kernel
theorem unsat2138 : Unsatisfiable (PosFin 57) f2138 := by
  apply lratCheckerSound f2138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2138
  · intro a ha; simp [p2138] at ha; subst a; trivial
  · exact checked2138
theorem derived2138 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2138 := by
  apply localUnsat_implies_entails f2138 [c2132, c2046, c2137, c8, c99, c191, c379, c181] c2138 unsat2138 (by rfl) a
  have h0 : Entails.eval a c2132 := derived2132 a h
  have h1 : Entails.eval a c2046 := derived2046 a h
  have h2 : Entails.eval a c2137 := derived2137 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2139 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨54, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2139 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2039, some c2046, some c2069, some c89, some c370, some c369, some c367, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2139 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2139 : lratChecker f2139 p2139 = .success := by decide +kernel
theorem unsat2139 : Unsatisfiable (PosFin 57) f2139 := by
  apply lratCheckerSound f2139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2139
  · intro a ha; simp [p2139] at ha; subst a; trivial
  · exact checked2139
theorem derived2139 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2139 := by
  apply localUnsat_implies_entails f2139 [c2039, c2046, c2069, c89, c370, c369, c367] c2139 unsat2139 (by rfl) a
  have h0 : Entails.eval a c2039 := derived2039 a h
  have h1 : Entails.eval a c2046 := derived2046 a h
  have h2 : Entails.eval a c2069 := derived2069 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2140 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2140 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c382, some c180, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2140 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2140 : lratChecker f2140 p2140 = .success := by decide +kernel
theorem unsat2140 : Unsatisfiable (PosFin 57) f2140 := by
  apply lratCheckerSound f2140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2140
  · intro a ha; simp [p2140] at ha; subst a; trivial
  · exact checked2140
theorem derived2140 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2140 := by
  apply localUnsat_implies_entails f2140 [c379, c382, c180] c2140 unsat2140 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2141 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2141 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2046, some c2039, some c2132, some c2138, some c2056, some c2053, some c195, some c2140, some c99, some c75, some c377, some c169, some c2139, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2141 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2141 : lratChecker f2141 p2141 = .success := by decide +kernel
theorem unsat2141 : Unsatisfiable (PosFin 57) f2141 := by
  apply lratCheckerSound f2141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2141
  · intro a ha; simp [p2141] at ha; subst a; trivial
  · exact checked2141
theorem derived2141 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2141 := by
  apply localUnsat_implies_entails f2141 [c2131, c2046, c2039, c2132, c2138, c2056, c2053, c195, c2140, c99, c75, c377, c169, c2139] c2141 unsat2141 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2046 := derived2046 a h
  have h2 : Entails.eval a c2039 := derived2039 a h
  have h3 : Entails.eval a c2132 := derived2132 a h
  have h4 : Entails.eval a c2138 := derived2138 a h
  have h5 : Entails.eval a c2056 := derived2056 a h
  have h6 : Entails.eval a c2053 := derived2053 a h
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c2140 := derived2140 a h
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c2139 := derived2139 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2142 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2142 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c78, some c6, some c162, some c190, some c852, some c2070, some c2092, some c1896, some c195, some c1897, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2142 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2142 : lratChecker f2142 p2142 = .success := by decide +kernel
theorem unsat2142 : Unsatisfiable (PosFin 57) f2142 := by
  apply lratCheckerSound f2142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2142
  · intro a ha; simp [p2142] at ha; subst a; trivial
  · exact checked2142
theorem derived2142 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2142 := by
  apply localUnsat_implies_entails f2142 [c2131, c78, c6, c162, c190, c852, c2070, c2092, c1896, c195, c1897] c2142 unsat2142 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c190 := h 189 (by decide)
  have h5 : Entails.eval a c852 := derived852 a h
  have h6 : Entails.eval a c2070 := derived2070 a h
  have h7 : Entails.eval a c2092 := derived2092 a h
  have h8 : Entails.eval a c1896 := derived1896 a h
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c1897 := derived1897 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2143 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨52, by decide⟩, true), (⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2143 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2141, some c2142, some c381, some c377, some c181, some c2057, some c196, some c1896, some c2091, some c2074, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2143 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2143 : lratChecker f2143 p2143 = .success := by decide +kernel
theorem unsat2143 : Unsatisfiable (PosFin 57) f2143 := by
  apply lratCheckerSound f2143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2143
  · intro a ha; simp [p2143] at ha; subst a; trivial
  · exact checked2143
theorem derived2143 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2143 := by
  apply localUnsat_implies_entails f2143 [c2131, c2051, c2141, c2142, c381, c377, c181, c2057, c196, c1896, c2091, c2074] c2143 unsat2143 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2141 := derived2141 a h
  have h3 : Entails.eval a c2142 := derived2142 a h
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c181 := h 180 (by decide)
  have h7 : Entails.eval a c2057 := derived2057 a h
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c1896 := derived1896 a h
  have h10 : Entails.eval a c2091 := derived2091 a h
  have h11 : Entails.eval a c2074 := derived2074 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2144 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨52, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2144 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c189, some c195, some c184, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2144 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2144 : lratChecker f2144 p2144 = .success := by decide +kernel
theorem unsat2144 : Unsatisfiable (PosFin 57) f2144 := by
  apply lratCheckerSound f2144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2144
  · intro a ha; simp [p2144] at ha; subst a; trivial
  · exact checked2144
theorem derived2144 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2144 := by
  apply localUnsat_implies_entails f2144 [c2131, c189, c195, c184] c2144 unsat2144 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c195 := h 194 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2145 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2145 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2141, some c2143, some c2080, some c761, some c2144, some c2091, some c2074, some c34, some c35, some c258, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2145 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2145 : lratChecker f2145 p2145 = .success := by decide +kernel
theorem unsat2145 : Unsatisfiable (PosFin 57) f2145 := by
  apply lratCheckerSound f2145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2145
  · intro a ha; simp [p2145] at ha; subst a; trivial
  · exact checked2145
theorem derived2145 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2145 := by
  apply localUnsat_implies_entails f2145 [c2131, c2051, c2141, c2143, c2080, c761, c2144, c2091, c2074, c34, c35, c258] c2145 unsat2145 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2141 := derived2141 a h
  have h3 : Entails.eval a c2143 := derived2143 a h
  have h4 : Entails.eval a c2080 := derived2080 a h
  have h5 : Entails.eval a c761 := derived761 a h
  have h6 : Entails.eval a c2144 := derived2144 a h
  have h7 : Entails.eval a c2091 := derived2091 a h
  have h8 : Entails.eval a c2074 := derived2074 a h
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2146 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2146 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2141, some c2145, some c1008, some c181, some c196, some c2140, some c98, some c2076, some c377, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2146 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2146 : lratChecker f2146 p2146 = .success := by decide +kernel
theorem unsat2146 : Unsatisfiable (PosFin 57) f2146 := by
  apply lratCheckerSound f2146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2146
  · intro a ha; simp [p2146] at ha; subst a; trivial
  · exact checked2146
theorem derived2146 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2146 := by
  apply localUnsat_implies_entails f2146 [c2131, c2051, c2141, c2145, c1008, c181, c196, c2140, c98, c2076, c377] c2146 unsat2146 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2141 := derived2141 a h
  have h3 : Entails.eval a c2145 := derived2145 a h
  have h4 : Entails.eval a c1008 := derived1008 a h
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c2140 := derived2140 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c2076 := derived2076 a h
  have h10 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2147 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨52, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2147 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2144, some c2146, some c2051, some c2141, some c2074, some c23, some c34, some c258, some c1880, some c35, some c181, some c1899, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2147 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2147 : lratChecker f2147 p2147 = .success := by decide +kernel
theorem unsat2147 : Unsatisfiable (PosFin 57) f2147 := by
  apply lratCheckerSound f2147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2147
  · intro a ha; simp [p2147] at ha; subst a; trivial
  · exact checked2147
theorem derived2147 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2147 := by
  apply localUnsat_implies_entails f2147 [c2131, c2144, c2146, c2051, c2141, c2074, c23, c34, c258, c1880, c35, c181, c1899] c2147 unsat2147 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2144 := derived2144 a h
  have h2 : Entails.eval a c2146 := derived2146 a h
  have h3 : Entails.eval a c2051 := derived2051 a h
  have h4 : Entails.eval a c2141 := derived2141 a h
  have h5 : Entails.eval a c2074 := derived2074 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c258 := h 257 (by decide)
  have h9 : Entails.eval a c1880 := derived1880 a h
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c181 := h 180 (by decide)
  have h12 : Entails.eval a c1899 := derived1899 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2148 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2148 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2146, some c2144, some c2147, some c1886, some c2091, some c181, some c101, some c1899, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2148 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2148 : lratChecker f2148 p2148 = .success := by decide +kernel
theorem unsat2148 : Unsatisfiable (PosFin 57) f2148 := by
  apply lratCheckerSound f2148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2148
  · intro a ha; simp [p2148] at ha; subst a; trivial
  · exact checked2148
theorem derived2148 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2148 := by
  apply localUnsat_implies_entails f2148 [c2131, c2146, c2144, c2147, c1886, c2091, c181, c101, c1899] c2148 unsat2148 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2146 := derived2146 a h
  have h2 : Entails.eval a c2144 := derived2144 a h
  have h3 : Entails.eval a c2147 := derived2147 a h
  have h4 : Entails.eval a c1886 := derived1886 a h
  have h5 : Entails.eval a c2091 := derived2091 a h
  have h6 : Entails.eval a c181 := h 180 (by decide)
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c1899 := derived1899 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2149 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2149 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c1886, some c191, some c2074, some c8, some c1896, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p2149 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2149 : lratChecker f2149 p2149 = .success := by decide +kernel
theorem unsat2149 : Unsatisfiable (PosFin 57) f2149 := by
  apply lratCheckerSound f2149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2149
  · intro a ha; simp [p2149] at ha; subst a; trivial
  · exact checked2149
theorem derived2149 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2149 := by
  apply localUnsat_implies_entails f2149 [c2131, c1886, c191, c2074, c8, c1896] c2149 unsat2149 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c1886 := derived1886 a h
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c2074 := derived2074 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c1896 := derived1896 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2150 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2150 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2051, some c2141, some c2146, some c2148, some c1008, some c181, some c2149, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2150 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2150 : lratChecker f2150 p2150 = .success := by decide +kernel
theorem unsat2150 : Unsatisfiable (PosFin 57) f2150 := by
  apply lratCheckerSound f2150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2150
  · intro a ha; simp [p2150] at ha; subst a; trivial
  · exact checked2150
theorem derived2150 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2150 := by
  apply localUnsat_implies_entails f2150 [c2051, c2141, c2146, c2148, c1008, c181, c2149] c2150 unsat2150 (by rfl) a
  have h0 : Entails.eval a c2051 := derived2051 a h
  have h1 : Entails.eval a c2141 := derived2141 a h
  have h2 : Entails.eval a c2146 := derived2146 a h
  have h3 : Entails.eval a c2148 := derived2148 a h
  have h4 : Entails.eval a c1008 := derived1008 a h
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c2149 := derived2149 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2151 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨4, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2151 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2091, some c2042, some c2040, some c2041, some c34, some c132, some c125, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2151 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2151 : lratChecker f2151 p2151 = .success := by decide +kernel
theorem unsat2151 : Unsatisfiable (PosFin 57) f2151 := by
  apply lratCheckerSound f2151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2151
  · intro a ha; simp [p2151] at ha; subst a; trivial
  · exact checked2151
theorem derived2151 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2151 := by
  apply localUnsat_implies_entails f2151 [c2131, c2051, c2091, c2042, c2040, c2041, c34, c132, c125] c2151 unsat2151 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2091 := derived2091 a h
  have h3 : Entails.eval a c2042 := derived2042 a h
  have h4 : Entails.eval a c2040 := derived2040 a h
  have h5 : Entails.eval a c2041 := derived2041 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2152 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2152 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2141, some c6, some c78, some c852, some c2151, some c196, some c195, some c184, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2152 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2152 : lratChecker f2152 p2152 = .success := by decide +kernel
theorem unsat2152 : Unsatisfiable (PosFin 57) f2152 := by
  apply lratCheckerSound f2152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2152
  · intro a ha; simp [p2152] at ha; subst a; trivial
  · exact checked2152
theorem derived2152 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2152 := by
  apply localUnsat_implies_entails f2152 [c2131, c2051, c2141, c6, c78, c852, c2151, c196, c195, c184] c2152 unsat2152 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2141 := derived2141 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c852 := derived852 a h
  have h6 : Entails.eval a c2151 := derived2151 a h
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2153 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2153 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2141, some c98, some c2152, some c1008, some c2140, some c181, some c196, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2153 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2153 : lratChecker f2153 p2153 = .success := by decide +kernel
theorem unsat2153 : Unsatisfiable (PosFin 57) f2153 := by
  apply lratCheckerSound f2153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2153
  · intro a ha; simp [p2153] at ha; subst a; trivial
  · exact checked2153
theorem derived2153 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2153 := by
  apply localUnsat_implies_entails f2153 [c2131, c2051, c2141, c98, c2152, c1008, c2140, c181, c196] c2153 unsat2153 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2141 := derived2141 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c2152 := derived2152 a h
  have h5 : Entails.eval a c1008 := derived1008 a h
  have h6 : Entails.eval a c2140 := derived2140 a h
  have h7 : Entails.eval a c181 := h 180 (by decide)
  have h8 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2154 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2154 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2150, some c2056, some c2051, some c2141, some c2153, some c2073, some c196, some c123, some c2091, some c4, some c761, some c76, some c768, some c121, some c86, some c173, some c372, some c2067, some c882, some c360, some c242, some c2079, some c2049, some c966, some c158, some c228, some c2078, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2154 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2154 : lratChecker f2154 p2154 = .success := by decide +kernel
theorem unsat2154 : Unsatisfiable (PosFin 57) f2154 := by
  apply lratCheckerSound f2154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2154
  · intro a ha; simp [p2154] at ha; subst a; trivial
  · exact checked2154
theorem derived2154 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2154 := by
  apply localUnsat_implies_entails f2154 [c2131, c2150, c2056, c2051, c2141, c2153, c2073, c196, c123, c2091, c4, c761, c76, c768, c121, c86, c173, c372, c2067, c882, c360, c242, c2079, c2049, c966, c158, c228, c2078] c2154 unsat2154 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2150 := derived2150 a h
  have h2 : Entails.eval a c2056 := derived2056 a h
  have h3 : Entails.eval a c2051 := derived2051 a h
  have h4 : Entails.eval a c2141 := derived2141 a h
  have h5 : Entails.eval a c2153 := derived2153 a h
  have h6 : Entails.eval a c2073 := derived2073 a h
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c2091 := derived2091 a h
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c761 := derived761 a h
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c768 := derived768 a h
  have h14 : Entails.eval a c121 := h 120 (by decide)
  have h15 : Entails.eval a c86 := h 85 (by decide)
  have h16 : Entails.eval a c173 := h 172 (by decide)
  have h17 : Entails.eval a c372 := h 371 (by decide)
  have h18 : Entails.eval a c2067 := derived2067 a h
  have h19 : Entails.eval a c882 := derived882 a h
  have h20 : Entails.eval a c360 := h 359 (by decide)
  have h21 : Entails.eval a c242 := h 241 (by decide)
  have h22 : Entails.eval a c2079 := derived2079 a h
  have h23 : Entails.eval a c2049 := derived2049 a h
  have h24 : Entails.eval a c966 := derived966 a h
  have h25 : Entails.eval a c158 := h 157 (by decide)
  have h26 : Entails.eval a c228 := h 227 (by decide)
  have h27 : Entails.eval a c2078 := derived2078 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2155 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2155 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2150, some c2056, some c2051, some c2141, some c2153, some c2073, some c2154, some c181, some c184, some c195, some c2091, some c882, some c761, some c852, some c86, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2155 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2155 : lratChecker f2155 p2155 = .success := by decide +kernel
theorem unsat2155 : Unsatisfiable (PosFin 57) f2155 := by
  apply lratCheckerSound f2155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2155
  · intro a ha; simp [p2155] at ha; subst a; trivial
  · exact checked2155
theorem derived2155 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2155 := by
  apply localUnsat_implies_entails f2155 [c2131, c2150, c2056, c2051, c2141, c2153, c2073, c2154, c181, c184, c195, c2091, c882, c761, c852, c86] c2155 unsat2155 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2150 := derived2150 a h
  have h2 : Entails.eval a c2056 := derived2056 a h
  have h3 : Entails.eval a c2051 := derived2051 a h
  have h4 : Entails.eval a c2141 := derived2141 a h
  have h5 : Entails.eval a c2153 := derived2153 a h
  have h6 : Entails.eval a c2073 := derived2073 a h
  have h7 : Entails.eval a c2154 := derived2154 a h
  have h8 : Entails.eval a c181 := h 180 (by decide)
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c2091 := derived2091 a h
  have h12 : Entails.eval a c882 := derived882 a h
  have h13 : Entails.eval a c761 := derived761 a h
  have h14 : Entails.eval a c852 := derived852 a h
  have h15 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2156 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2156 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2141, some c2150, some c2056, some c2153, some c2073, some c2155, some c1008, some c181, some c196, some c2140, some c2091, some c75, some c2053, some c169, some c121, some c24, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2156 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2156 : lratChecker f2156 p2156 = .success := by decide +kernel
theorem unsat2156 : Unsatisfiable (PosFin 57) f2156 := by
  apply lratCheckerSound f2156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2156
  · intro a ha; simp [p2156] at ha; subst a; trivial
  · exact checked2156
theorem derived2156 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2156 := by
  apply localUnsat_implies_entails f2156 [c2131, c2051, c2141, c2150, c2056, c2153, c2073, c2155, c1008, c181, c196, c2140, c2091, c75, c2053, c169, c121, c24] c2156 unsat2156 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2141 := derived2141 a h
  have h3 : Entails.eval a c2150 := derived2150 a h
  have h4 : Entails.eval a c2056 := derived2056 a h
  have h5 : Entails.eval a c2153 := derived2153 a h
  have h6 : Entails.eval a c2073 := derived2073 a h
  have h7 : Entails.eval a c2155 := derived2155 a h
  have h8 : Entails.eval a c1008 := derived1008 a h
  have h9 : Entails.eval a c181 := h 180 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c2140 := derived2140 a h
  have h12 : Entails.eval a c2091 := derived2091 a h
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c2053 := derived2053 a h
  have h15 : Entails.eval a c169 := h 168 (by decide)
  have h16 : Entails.eval a c121 := h 120 (by decide)
  have h17 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2157 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2157 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c1003, some c195, some c2039, some c2053, some c1920, some c2109, some c378, some c2076, some c383, some c1630, some c379, some c359, some c2043, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2157 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2157 : lratChecker f2157 p2157 = .success := by decide +kernel
theorem unsat2157 : Unsatisfiable (PosFin 57) f2157 := by
  apply lratCheckerSound f2157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2157
  · intro a ha; simp [p2157] at ha; subst a; trivial
  · exact checked2157
theorem derived2157 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2157 := by
  apply localUnsat_implies_entails f2157 [c2131, c1003, c195, c2039, c2053, c1920, c2109, c378, c2076, c383, c1630, c379, c359, c2043] c2157 unsat2157 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c195 := h 194 (by decide)
  have h3 : Entails.eval a c2039 := derived2039 a h
  have h4 : Entails.eval a c2053 := derived2053 a h
  have h5 : Entails.eval a c1920 := derived1920 a h
  have h6 : Entails.eval a c2109 := derived2109 a h
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c2076 := derived2076 a h
  have h9 : Entails.eval a c383 := h 382 (by decide)
  have h10 : Entails.eval a c1630 := derived1630 a h
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c2043 := derived2043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2158 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2158 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c1003, some c195, some c2046, some c2039, some c2109, some c2053, some c17, some c2157, some c80, some c99, some c164, some c383, some c379, some c2065, some c2069, some c469, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2158 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2158 : lratChecker f2158 p2158 = .success := by decide +kernel
theorem unsat2158 : Unsatisfiable (PosFin 57) f2158 := by
  apply lratCheckerSound f2158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2158
  · intro a ha; simp [p2158] at ha; subst a; trivial
  · exact checked2158
theorem derived2158 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2158 := by
  apply localUnsat_implies_entails f2158 [c2131, c1003, c195, c2046, c2039, c2109, c2053, c17, c2157, c80, c99, c164, c383, c379, c2065, c2069, c469] c2158 unsat2158 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c195 := h 194 (by decide)
  have h3 : Entails.eval a c2046 := derived2046 a h
  have h4 : Entails.eval a c2039 := derived2039 a h
  have h5 : Entails.eval a c2109 := derived2109 a h
  have h6 : Entails.eval a c2053 := derived2053 a h
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c2157 := derived2157 a h
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c383 := h 382 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c2065 := derived2065 a h
  have h15 : Entails.eval a c2069 := derived2069 a h
  have h16 : Entails.eval a c469 := derived469 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2159 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2159 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2156, some c2158, some c1003, some c195, some c196, some c2050, some c122, some c2074, some c34, some c113, some c258, some c2056, some c35, some c378, some c376, some c2092, some c1687, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2159 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2159 : lratChecker f2159 p2159 = .success := by decide +kernel
theorem unsat2159 : Unsatisfiable (PosFin 57) f2159 := by
  apply lratCheckerSound f2159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2159
  · intro a ha; simp [p2159] at ha; subst a; trivial
  · exact checked2159
theorem derived2159 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2159 := by
  apply localUnsat_implies_entails f2159 [c2131, c2051, c2156, c2158, c1003, c195, c196, c2050, c122, c2074, c34, c113, c258, c2056, c35, c378, c376, c2092, c1687] c2159 unsat2159 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2156 := derived2156 a h
  have h3 : Entails.eval a c2158 := derived2158 a h
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c195 := h 194 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c2050 := derived2050 a h
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c2074 := derived2074 a h
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c2056 := derived2056 a h
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c378 := h 377 (by decide)
  have h16 : Entails.eval a c376 := h 375 (by decide)
  have h17 : Entails.eval a c2092 := derived2092 a h
  have h18 : Entails.eval a c1687 := derived1687 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2160 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2160 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c1746, some c6, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p2160 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2160 : lratChecker f2160 p2160 = .success := by decide +kernel
theorem unsat2160 : Unsatisfiable (PosFin 57) f2160 := by
  apply lratCheckerSound f2160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2160
  · intro a ha; simp [p2160] at ha; subst a; trivial
  · exact checked2160
theorem derived2160 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2160 := by
  apply localUnsat_implies_entails f2160 [c589, c1746, c6] c2160 unsat2160 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c1746 := derived1746 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2161 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨4, by decide⟩, true), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2161 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2158, some c1003, some c195, some c4, some c1008, some c2053, some c98, some c6, some c383, some c2063, some c2077, some c469, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2161 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2161 : lratChecker f2161 p2161 = .success := by decide +kernel
theorem unsat2161 : Unsatisfiable (PosFin 57) f2161 := by
  apply lratCheckerSound f2161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2161
  · intro a ha; simp [p2161] at ha; subst a; trivial
  · exact checked2161
theorem derived2161 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2161 := by
  apply localUnsat_implies_entails f2161 [c2131, c2158, c1003, c195, c4, c1008, c2053, c98, c6, c383, c2063, c2077, c469] c2161 unsat2161 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2158 := derived2158 a h
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c195 := h 194 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c1008 := derived1008 a h
  have h6 : Entails.eval a c2053 := derived2053 a h
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c383 := h 382 (by decide)
  have h10 : Entails.eval a c2063 := derived2063 a h
  have h11 : Entails.eval a c2077 := derived2077 a h
  have h12 : Entails.eval a c469 := derived469 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2162 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2162 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2161, some c1003, some c195, some c2053, some c1920, some c2158, some c4, some c1008, some c376, some c1714, some c2073, some c359, some c122, some c373, some c26, some c86, some c567, some c1417, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2162 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2162 : lratChecker f2162 p2162 = .success := by decide +kernel
theorem unsat2162 : Unsatisfiable (PosFin 57) f2162 := by
  apply lratCheckerSound f2162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2162
  · intro a ha; simp [p2162] at ha; subst a; trivial
  · exact checked2162
theorem derived2162 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2162 := by
  apply localUnsat_implies_entails f2162 [c2131, c2161, c1003, c195, c2053, c1920, c2158, c4, c1008, c376, c1714, c2073, c359, c122, c373, c26, c86, c567, c1417] c2162 unsat2162 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2161 := derived2161 a h
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c195 := h 194 (by decide)
  have h4 : Entails.eval a c2053 := derived2053 a h
  have h5 : Entails.eval a c1920 := derived1920 a h
  have h6 : Entails.eval a c2158 := derived2158 a h
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c1008 := derived1008 a h
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c1714 := derived1714 a h
  have h11 : Entails.eval a c2073 := derived2073 a h
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c373 := h 372 (by decide)
  have h15 : Entails.eval a c26 := h 25 (by decide)
  have h16 : Entails.eval a c86 := h 85 (by decide)
  have h17 : Entails.eval a c567 := derived567 a h
  have h18 : Entails.eval a c1417 := derived1417 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2163 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2163 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2156, some c1003, some c195, some c2158, some c2159, some c4, some c2053, some c1008, some c1920, some c2160, some c2161, some c2162, some c2076, some c383, some c359, some c366, some c373, some c26, some c86, some c567, some c469, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2163 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2163 : lratChecker f2163 p2163 = .success := by decide +kernel
theorem unsat2163 : Unsatisfiable (PosFin 57) f2163 := by
  apply lratCheckerSound f2163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2163
  · intro a ha; simp [p2163] at ha; subst a; trivial
  · exact checked2163
theorem derived2163 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2163 := by
  apply localUnsat_implies_entails f2163 [c2131, c2051, c2156, c1003, c195, c2158, c2159, c4, c2053, c1008, c1920, c2160, c2161, c2162, c2076, c383, c359, c366, c373, c26, c86, c567, c469] c2163 unsat2163 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2156 := derived2156 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c195 := h 194 (by decide)
  have h5 : Entails.eval a c2158 := derived2158 a h
  have h6 : Entails.eval a c2159 := derived2159 a h
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c2053 := derived2053 a h
  have h9 : Entails.eval a c1008 := derived1008 a h
  have h10 : Entails.eval a c1920 := derived1920 a h
  have h11 : Entails.eval a c2160 := derived2160 a h
  have h12 : Entails.eval a c2161 := derived2161 a h
  have h13 : Entails.eval a c2162 := derived2162 a h
  have h14 : Entails.eval a c2076 := derived2076 a h
  have h15 : Entails.eval a c383 := h 382 (by decide)
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c366 := h 365 (by decide)
  have h18 : Entails.eval a c373 := h 372 (by decide)
  have h19 : Entails.eval a c26 := h 25 (by decide)
  have h20 : Entails.eval a c86 := h 85 (by decide)
  have h21 : Entails.eval a c567 := derived567 a h
  have h22 : Entails.eval a c469 := derived469 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2164 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2164 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2163, some c1254, some c2039, some c2046, some c2051, some c2158, some c192, some c2053, some c1278, some c2136, some c1034, some c4, some c17, some c2058, some c2076, some c164, some c382, some c87, some c2068, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2164 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2164 : lratChecker f2164 p2164 = .success := by decide +kernel
theorem unsat2164 : Unsatisfiable (PosFin 57) f2164 := by
  apply lratCheckerSound f2164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2164
  · intro a ha; simp [p2164] at ha; subst a; trivial
  · exact checked2164
theorem derived2164 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2164 := by
  apply localUnsat_implies_entails f2164 [c2131, c2163, c1254, c2039, c2046, c2051, c2158, c192, c2053, c1278, c2136, c1034, c4, c17, c2058, c2076, c164, c382, c87, c2068] c2164 unsat2164 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2163 := derived2163 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c2039 := derived2039 a h
  have h4 : Entails.eval a c2046 := derived2046 a h
  have h5 : Entails.eval a c2051 := derived2051 a h
  have h6 : Entails.eval a c2158 := derived2158 a h
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c2053 := derived2053 a h
  have h9 : Entails.eval a c1278 := derived1278 a h
  have h10 : Entails.eval a c2136 := derived2136 a h
  have h11 : Entails.eval a c1034 := derived1034 a h
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c2058 := derived2058 a h
  have h15 : Entails.eval a c2076 := derived2076 a h
  have h16 : Entails.eval a c164 := h 163 (by decide)
  have h17 : Entails.eval a c382 := h 381 (by decide)
  have h18 : Entails.eval a c87 := h 86 (by decide)
  have h19 : Entails.eval a c2068 := derived2068 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2165 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2165 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2051, some c2163, some c1254, some c192, some c2046, some c2039, some c2158, some c17, some c1278, some c4, some c2053, some c2136, some c1034, some c2164, some c377, some c80, some c99, some c164, some c382, some c2065, some c2068, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2165 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2165 : lratChecker f2165 p2165 = .success := by decide +kernel
theorem unsat2165 : Unsatisfiable (PosFin 57) f2165 := by
  apply lratCheckerSound f2165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2165
  · intro a ha; simp [p2165] at ha; subst a; trivial
  · exact checked2165
theorem derived2165 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2165 := by
  apply localUnsat_implies_entails f2165 [c2131, c2051, c2163, c1254, c192, c2046, c2039, c2158, c17, c1278, c4, c2053, c2136, c1034, c2164, c377, c80, c99, c164, c382, c2065, c2068] c2165 unsat2165 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2051 := derived2051 a h
  have h2 : Entails.eval a c2163 := derived2163 a h
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c2046 := derived2046 a h
  have h6 : Entails.eval a c2039 := derived2039 a h
  have h7 : Entails.eval a c2158 := derived2158 a h
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c1278 := derived1278 a h
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c2053 := derived2053 a h
  have h12 : Entails.eval a c2136 := derived2136 a h
  have h13 : Entails.eval a c1034 := derived1034 a h
  have h14 : Entails.eval a c2164 := derived2164 a h
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c99 := h 98 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  have h19 : Entails.eval a c382 := h 381 (by decide)
  have h20 : Entails.eval a c2065 := derived2065 a h
  have h21 : Entails.eval a c2068 := derived2068 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2166 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨54, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2166 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c2046, some c2039, some c1318, some c1314, some c190, some c188, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2166 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2166 : lratChecker f2166 p2166 = .success := by decide +kernel
theorem unsat2166 : Unsatisfiable (PosFin 57) f2166 := by
  apply lratCheckerSound f2166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2166
  · intro a ha; simp [p2166] at ha; subst a; trivial
  · exact checked2166
theorem derived2166 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2166 := by
  apply localUnsat_implies_entails f2166 [c2131, c2165, c2046, c2039, c1318, c1314, c190, c188] c2166 unsat2166 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2039 := derived2039 a h
  have h4 : Entails.eval a c1318 := derived1318 a h
  have h5 : Entails.eval a c1314 := derived1314 a h
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2167 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨15, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2167 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c2039, some c2057, some c2045, some c2046, some c1318, some c91, some c28, some c2117, some c128, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2167 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2167 : lratChecker f2167 p2167 = .success := by decide +kernel
theorem unsat2167 : Unsatisfiable (PosFin 57) f2167 := by
  apply lratCheckerSound f2167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2167
  · intro a ha; simp [p2167] at ha; subst a; trivial
  · exact checked2167
theorem derived2167 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2167 := by
  apply localUnsat_implies_entails f2167 [c2131, c2165, c2039, c2057, c2045, c2046, c1318, c91, c28, c2117, c128] c2167 unsat2167 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c2039 := derived2039 a h
  have h3 : Entails.eval a c2057 := derived2057 a h
  have h4 : Entails.eval a c2045 := derived2045 a h
  have h5 : Entails.eval a c2046 := derived2046 a h
  have h6 : Entails.eval a c1318 := derived1318 a h
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c2117 := derived2117 a h
  have h10 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2168 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2168 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c244, some c241, some c39, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p2168 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2168 : lratChecker f2168 p2168 = .success := by decide +kernel
theorem unsat2168 : Unsatisfiable (PosFin 57) f2168 := by
  apply lratCheckerSound f2168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2168
  · intro a ha; simp [p2168] at ha; subst a; trivial
  · exact checked2168
theorem derived2168 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2168 := by
  apply localUnsat_implies_entails f2168 [c2165, c244, c241, c39] c2168 unsat2168 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c244 := h 243 (by decide)
  have h2 : Entails.eval a c241 := h 240 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2169 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2169 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c2046, some c2045, some c2039, some c2057, some c4, some c195, some c5, some c2168, some c2070, some c377, some c1318, some c2167, some c176, some c369, some c367, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2169 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2169 : lratChecker f2169 p2169 = .success := by decide +kernel
theorem unsat2169 : Unsatisfiable (PosFin 57) f2169 := by
  apply lratCheckerSound f2169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2169
  · intro a ha; simp [p2169] at ha; subst a; trivial
  · exact checked2169
theorem derived2169 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2169 := by
  apply localUnsat_implies_entails f2169 [c2131, c2165, c2046, c2045, c2039, c2057, c4, c195, c5, c2168, c2070, c377, c1318, c2167, c176, c369, c367] c2169 unsat2169 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2045 := derived2045 a h
  have h4 : Entails.eval a c2039 := derived2039 a h
  have h5 : Entails.eval a c2057 := derived2057 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c2168 := derived2168 a h
  have h10 : Entails.eval a c2070 := derived2070 a h
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c1318 := derived1318 a h
  have h13 : Entails.eval a c2167 := derived2167 a h
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2170 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2170 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2131, some c2141, some c2039, some c2046, some c2045, some c4, some c2057, some c195, some c5, some c2168, some c2067, some c121, some c2169, some c2084, some c2087, some c199, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2170 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2170 : lratChecker f2170 p2170 = .success := by decide +kernel
theorem unsat2170 : Unsatisfiable (PosFin 57) f2170 := by
  apply lratCheckerSound f2170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2170
  · intro a ha; simp [p2170] at ha; subst a; trivial
  · exact checked2170
theorem derived2170 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2170 := by
  apply localUnsat_implies_entails f2170 [c2165, c2131, c2141, c2039, c2046, c2045, c4, c2057, c195, c5, c2168, c2067, c121, c2169, c2084, c2087, c199] c2170 unsat2170 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2131 := derived2131 a h
  have h2 : Entails.eval a c2141 := derived2141 a h
  have h3 : Entails.eval a c2039 := derived2039 a h
  have h4 : Entails.eval a c2046 := derived2046 a h
  have h5 : Entails.eval a c2045 := derived2045 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c2057 := derived2057 a h
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c2168 := derived2168 a h
  have h11 : Entails.eval a c2067 := derived2067 a h
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c2169 := derived2169 a h
  have h14 : Entails.eval a c2084 := derived2084 a h
  have h15 : Entails.eval a c2087 := derived2087 a h
  have h16 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2171 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2171 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2039, some c2046, some c1314, some c2166, some c181, some c1034, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2171 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2171 : lratChecker f2171 p2171 = .success := by decide +kernel
theorem unsat2171 : Unsatisfiable (PosFin 57) f2171 := by
  apply lratCheckerSound f2171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2171
  · intro a ha; simp [p2171] at ha; subst a; trivial
  · exact checked2171
theorem derived2171 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2171 := by
  apply localUnsat_implies_entails f2171 [c2165, c2039, c2046, c1314, c2166, c181, c1034] c2171 unsat2171 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2039 := derived2039 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c1314 := derived1314 a h
  have h4 : Entails.eval a c2166 := derived2166 a h
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c1034 := derived1034 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2172 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨45, by decide⟩, false), (⟨24, by decide⟩, false), (⟨51, by decide⟩, true), (⟨12, by decide⟩, false), (⟨49, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2172 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2131, some c2046, some c2039, some c1318, some c377, some c2139, some c169, some c361, some c173, some c2117, some c188, some c128, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2172 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2172 : lratChecker f2172 p2172 = .success := by decide +kernel
theorem unsat2172 : Unsatisfiable (PosFin 57) f2172 := by
  apply lratCheckerSound f2172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2172
  · intro a ha; simp [p2172] at ha; subst a; trivial
  · exact checked2172
theorem derived2172 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2172 := by
  apply localUnsat_implies_entails f2172 [c2165, c2131, c2046, c2039, c1318, c377, c2139, c169, c361, c173, c2117, c188, c128] c2172 unsat2172 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2131 := derived2131 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2039 := derived2039 a h
  have h4 : Entails.eval a c1318 := derived1318 a h
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c2139 := derived2139 a h
  have h7 : Entails.eval a c169 := h 168 (by decide)
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c173 := h 172 (by decide)
  have h10 : Entails.eval a c2117 := derived2117 a h
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2173 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2173 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2131, some c2046, some c2171, some c2056, some c2039, some c2053, some c2170, some c195, some c2140, some c5, some c2085, some c1790, some c25, some c2172, some c80, some c1318, some c2139, some c169, some c361, some c2043, some c369, some c175, some c2070, some c188, some c2044, some c259, some c176, some c343, some c332, some c233, some c360, some c129, some c246, some c293, some c200, some c140, some c298, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2173 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked2173 : lratChecker f2173 p2173 = .success := by decide +kernel
theorem unsat2173 : Unsatisfiable (PosFin 57) f2173 := by
  apply lratCheckerSound f2173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2173
  · intro a ha; simp [p2173] at ha; subst a; trivial
  · exact checked2173
theorem derived2173 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2173 := by
  apply localUnsat_implies_entails f2173 [c2165, c2131, c2046, c2171, c2056, c2039, c2053, c2170, c195, c2140, c5, c2085, c1790, c25, c2172, c80, c1318, c2139, c169, c361, c2043, c369, c175, c2070, c188, c2044, c259, c176, c343, c332, c233, c360, c129, c246, c293, c200, c140, c298] c2173 unsat2173 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2131 := derived2131 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2171 := derived2171 a h
  have h4 : Entails.eval a c2056 := derived2056 a h
  have h5 : Entails.eval a c2039 := derived2039 a h
  have h6 : Entails.eval a c2053 := derived2053 a h
  have h7 : Entails.eval a c2170 := derived2170 a h
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c2140 := derived2140 a h
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c2085 := derived2085 a h
  have h12 : Entails.eval a c1790 := derived1790 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c2172 := derived2172 a h
  have h15 : Entails.eval a c80 := h 79 (by decide)
  have h16 : Entails.eval a c1318 := derived1318 a h
  have h17 : Entails.eval a c2139 := derived2139 a h
  have h18 : Entails.eval a c169 := h 168 (by decide)
  have h19 : Entails.eval a c361 := h 360 (by decide)
  have h20 : Entails.eval a c2043 := derived2043 a h
  have h21 : Entails.eval a c369 := h 368 (by decide)
  have h22 : Entails.eval a c175 := h 174 (by decide)
  have h23 : Entails.eval a c2070 := derived2070 a h
  have h24 : Entails.eval a c188 := h 187 (by decide)
  have h25 : Entails.eval a c2044 := derived2044 a h
  have h26 : Entails.eval a c259 := h 258 (by decide)
  have h27 : Entails.eval a c176 := h 175 (by decide)
  have h28 : Entails.eval a c343 := h 342 (by decide)
  have h29 : Entails.eval a c332 := h 331 (by decide)
  have h30 : Entails.eval a c233 := h 232 (by decide)
  have h31 : Entails.eval a c360 := h 359 (by decide)
  have h32 : Entails.eval a c129 := h 128 (by decide)
  have h33 : Entails.eval a c246 := h 245 (by decide)
  have h34 : Entails.eval a c293 := h 292 (by decide)
  have h35 : Entails.eval a c200 := h 199 (by decide)
  have h36 : Entails.eval a c140 := h 139 (by decide)
  have h37 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2174 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2174 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c2046, some c2039, some c1318, some c2170, some c2171, some c2056, some c2053, some c195, some c5, some c2140, some c2085, some c1790, some c25, some c2172, some c80, some c2173, some c1034, some c181, some c128, some c176, some c360, some c2043, some c240, some c253, some c242, some c2067, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2174 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2174 : lratChecker f2174 p2174 = .success := by decide +kernel
theorem unsat2174 : Unsatisfiable (PosFin 57) f2174 := by
  apply lratCheckerSound f2174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2174
  · intro a ha; simp [p2174] at ha; subst a; trivial
  · exact checked2174
theorem derived2174 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2174 := by
  apply localUnsat_implies_entails f2174 [c2131, c2165, c2046, c2039, c1318, c2170, c2171, c2056, c2053, c195, c5, c2140, c2085, c1790, c25, c2172, c80, c2173, c1034, c181, c128, c176, c360, c2043, c240, c253, c242, c2067] c2174 unsat2174 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c2046 := derived2046 a h
  have h3 : Entails.eval a c2039 := derived2039 a h
  have h4 : Entails.eval a c1318 := derived1318 a h
  have h5 : Entails.eval a c2170 := derived2170 a h
  have h6 : Entails.eval a c2171 := derived2171 a h
  have h7 : Entails.eval a c2056 := derived2056 a h
  have h8 : Entails.eval a c2053 := derived2053 a h
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c2140 := derived2140 a h
  have h12 : Entails.eval a c2085 := derived2085 a h
  have h13 : Entails.eval a c1790 := derived1790 a h
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c2172 := derived2172 a h
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c2173 := derived2173 a h
  have h18 : Entails.eval a c1034 := derived1034 a h
  have h19 : Entails.eval a c181 := h 180 (by decide)
  have h20 : Entails.eval a c128 := h 127 (by decide)
  have h21 : Entails.eval a c176 := h 175 (by decide)
  have h22 : Entails.eval a c360 := h 359 (by decide)
  have h23 : Entails.eval a c2043 := derived2043 a h
  have h24 : Entails.eval a c240 := h 239 (by decide)
  have h25 : Entails.eval a c253 := h 252 (by decide)
  have h26 : Entails.eval a c242 := h 241 (by decide)
  have h27 : Entails.eval a c2067 := derived2067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2175 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2175 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2174, some c2116, some c2144, some c184, some c5, some c18, some c2060, some c125, some c114, some c2070, some c2067, some c162, some c2048, some c90, some c86, some c1827, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2175 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2175 : lratChecker f2175 p2175 = .success := by decide +kernel
theorem unsat2175 : Unsatisfiable (PosFin 57) f2175 := by
  apply lratCheckerSound f2175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2175
  · intro a ha; simp [p2175] at ha; subst a; trivial
  · exact checked2175
theorem derived2175 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2175 := by
  apply localUnsat_implies_entails f2175 [c2165, c2174, c2116, c2144, c184, c5, c18, c2060, c125, c114, c2070, c2067, c162, c2048, c90, c86, c1827] c2175 unsat2175 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2174 := derived2174 a h
  have h2 : Entails.eval a c2116 := derived2116 a h
  have h3 : Entails.eval a c2144 := derived2144 a h
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c2060 := derived2060 a h
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c2070 := derived2070 a h
  have h11 : Entails.eval a c2067 := derived2067 a h
  have h12 : Entails.eval a c162 := h 161 (by decide)
  have h13 : Entails.eval a c2048 := derived2048 a h
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c86 := h 85 (by decide)
  have h16 : Entails.eval a c1827 := derived1827 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2176 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨51, by decide⟩, false), (⟨15, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2176 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c196, some c5, some c171, some c23, some c2065, some c250, some c368, some c25, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2176 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2176 : lratChecker f2176 p2176 = .success := by decide +kernel
theorem unsat2176 : Unsatisfiable (PosFin 57) f2176 := by
  apply lratCheckerSound f2176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2176
  · intro a ha; simp [p2176] at ha; subst a; trivial
  · exact checked2176
theorem derived2176 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2176 := by
  apply localUnsat_implies_entails f2176 [c2131, c2165, c196, c5, c171, c23, c2065, c250, c368, c25] c2176 unsat2176 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c2065 := derived2065 a h
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2177 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2177 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c250, some c241, some c2075, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p2177 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2177 : lratChecker f2177 p2177 = .success := by decide +kernel
theorem unsat2177 : Unsatisfiable (PosFin 57) f2177 := by
  apply lratCheckerSound f2177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2177
  · intro a ha; simp [p2177] at ha; subst a; trivial
  · exact checked2177
theorem derived2177 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2177 := by
  apply localUnsat_implies_entails f2177 [c250, c241, c2075] c2177 unsat2177 (by rfl) a
  have h0 : Entails.eval a c250 := h 249 (by decide)
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c2075 := derived2075 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2178 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨15, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2178 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2131, some c196, some c5, some c98, some c78, some c2176, some c363, some c372, some c360, some c2177, some c25, some c1827, some c23, some c123, some c245, some c233, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2178 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2178 : lratChecker f2178 p2178 = .success := by decide +kernel
theorem unsat2178 : Unsatisfiable (PosFin 57) f2178 := by
  apply lratCheckerSound f2178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2178
  · intro a ha; simp [p2178] at ha; subst a; trivial
  · exact checked2178
theorem derived2178 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2178 := by
  apply localUnsat_implies_entails f2178 [c2165, c2131, c196, c5, c98, c78, c2176, c363, c372, c360, c2177, c25, c1827, c23, c123, c245, c233] c2178 unsat2178 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2131 := derived2131 a h
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c2176 := derived2176 a h
  have h7 : Entails.eval a c363 := h 362 (by decide)
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c360 := h 359 (by decide)
  have h10 : Entails.eval a c2177 := derived2177 a h
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c1827 := derived1827 a h
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c245 := h 244 (by decide)
  have h16 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2179 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨46, by decide⟩, false), (⟨15, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2179 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c2178, some c2073, some c123, some c196, some c5, some c2176, some c2177, some c363, some c25, some c38, some c372, some c2071, some c247, some c233, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2179 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2179 : lratChecker f2179 p2179 = .success := by decide +kernel
theorem unsat2179 : Unsatisfiable (PosFin 57) f2179 := by
  apply lratCheckerSound f2179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2179
  · intro a ha; simp [p2179] at ha; subst a; trivial
  · exact checked2179
theorem derived2179 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2179 := by
  apply localUnsat_implies_entails f2179 [c2131, c2165, c2178, c2073, c123, c196, c5, c2176, c2177, c363, c25, c38, c372, c2071, c247, c233] c2179 unsat2179 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c2178 := derived2178 a h
  have h3 : Entails.eval a c2073 := derived2073 a h
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c2176 := derived2176 a h
  have h8 : Entails.eval a c2177 := derived2177 a h
  have h9 : Entails.eval a c363 := h 362 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c2071 := derived2071 a h
  have h14 : Entails.eval a c247 := h 246 (by decide)
  have h15 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2180 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2180 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c149, some c2072, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2180 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2180 : lratChecker f2180 p2180 = .success := by decide +kernel
theorem unsat2180 : Unsatisfiable (PosFin 57) f2180 := by
  apply lratCheckerSound f2180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2180
  · intro a ha; simp [p2180] at ha; subst a; trivial
  · exact checked2180
theorem derived2180 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2180 := by
  apply localUnsat_implies_entails f2180 [c151, c149, c2072] c2180 unsat2180 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c2072 := derived2072 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2181 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨15, by decide⟩, false), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2181 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2131, some c2175, some c2056, some c2174, some c2048, some c2178, some c2073, some c123, some c196, some c18, some c5, some c2179, some c75, some c1014, some c1827, some c363, some c1133, some c173, some c360, some c233, some c247, some c2180, some c332, some c333, some c133, some c202, some c293, some c299, some c137, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2181 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2181 : lratChecker f2181 p2181 = .success := by decide +kernel
theorem unsat2181 : Unsatisfiable (PosFin 57) f2181 := by
  apply lratCheckerSound f2181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2181
  · intro a ha; simp [p2181] at ha; subst a; trivial
  · exact checked2181
theorem derived2181 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2181 := by
  apply localUnsat_implies_entails f2181 [c2165, c2131, c2175, c2056, c2174, c2048, c2178, c2073, c123, c196, c18, c5, c2179, c75, c1014, c1827, c363, c1133, c173, c360, c233, c247, c2180, c332, c333, c133, c202, c293, c299, c137] c2181 unsat2181 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2131 := derived2131 a h
  have h2 : Entails.eval a c2175 := derived2175 a h
  have h3 : Entails.eval a c2056 := derived2056 a h
  have h4 : Entails.eval a c2174 := derived2174 a h
  have h5 : Entails.eval a c2048 := derived2048 a h
  have h6 : Entails.eval a c2178 := derived2178 a h
  have h7 : Entails.eval a c2073 := derived2073 a h
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c2179 := derived2179 a h
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c1014 := derived1014 a h
  have h15 : Entails.eval a c1827 := derived1827 a h
  have h16 : Entails.eval a c363 := h 362 (by decide)
  have h17 : Entails.eval a c1133 := derived1133 a h
  have h18 : Entails.eval a c173 := h 172 (by decide)
  have h19 : Entails.eval a c360 := h 359 (by decide)
  have h20 : Entails.eval a c233 := h 232 (by decide)
  have h21 : Entails.eval a c247 := h 246 (by decide)
  have h22 : Entails.eval a c2180 := derived2180 a h
  have h23 : Entails.eval a c332 := h 331 (by decide)
  have h24 : Entails.eval a c333 := h 332 (by decide)
  have h25 : Entails.eval a c133 := h 132 (by decide)
  have h26 : Entails.eval a c202 := h 201 (by decide)
  have h27 : Entails.eval a c293 := h 292 (by decide)
  have h28 : Entails.eval a c299 := h 298 (by decide)
  have h29 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2182 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2182 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c90, some c86, some c1827, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2182 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2182 : lratChecker f2182 p2182 = .success := by decide +kernel
theorem unsat2182 : Unsatisfiable (PosFin 57) f2182 := by
  apply lratCheckerSound f2182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2182
  · intro a ha; simp [p2182] at ha; subst a; trivial
  · exact checked2182
theorem derived2182 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2182 := by
  apply localUnsat_implies_entails f2182 [c2165, c90, c86, c1827] c2182 unsat2182 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c1827 := derived1827 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2183 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2183 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1827, some c368, some c2065, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2183 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2183 : lratChecker f2183 p2183 = .success := by decide +kernel
theorem unsat2183 : Unsatisfiable (PosFin 57) f2183 := by
  apply lratCheckerSound f2183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2183
  · intro a ha; simp [p2183] at ha; subst a; trivial
  · exact checked2183
theorem derived2183 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2183 := by
  apply localUnsat_implies_entails f2183 [c1827, c368, c2065] c2183 unsat2183 (by rfl) a
  have h0 : Entails.eval a c1827 := derived1827 a h
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c2065 := derived2065 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived2183

end CochromaticTwenty.Certificates.B16_2_2
