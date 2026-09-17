import MerLeanExperiment.Certificates.B16_8_2.Steps1500_1599

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1981 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1981 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c841, some c1970, some c1976, some c1980, some c72, some c156, some c102, some c8, some c148, some c183, some c946, some c100, some c1667, some c1668, some c1670, some c361, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1981 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1981 : lratChecker f1981 p1981 = .success := by decide +kernel
theorem unsat1981 : Unsatisfiable (PosFin 57) f1981 := by
  apply lratCheckerSound f1981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1981
  · intro a ha; simp [p1981] at ha; subst a; trivial
  · exact checked1981
theorem derived1981 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1981 := by
  apply localUnsat_implies_entails f1981 [c71, c841, c1970, c1976, c1980, c72, c156, c102, c8, c148, c183, c946, c100, c1667, c1668, c1670, c361] c1981 unsat1981 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c1970 := derived1970 a h
  have h3 : Entails.eval a c1976 := derived1976 a h
  have h4 : Entails.eval a c1980 := derived1980 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c946 := derived946 a h
  have h12 : Entails.eval a c100 := h 99 (by decide)
  have h13 : Entails.eval a c1667 := derived1667 a h
  have h14 : Entails.eval a c1668 := derived1668 a h
  have h15 : Entails.eval a c1670 := derived1670 a h
  have h16 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1982 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1982 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c280, some c276, some c41, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1982 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1982 : lratChecker f1982 p1982 = .success := by decide +kernel
theorem unsat1982 : Unsatisfiable (PosFin 57) f1982 := by
  apply lratCheckerSound f1982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1982
  · intro a ha; simp [p1982] at ha; subst a; trivial
  · exact checked1982
theorem derived1982 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1982 := by
  apply localUnsat_implies_entails f1982 [c1946, c280, c276, c41] c1982 unsat1982 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c280 := h 279 (by decide)
  have h2 : Entails.eval a c276 := h 275 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1983 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨43, by decide⟩, true), (⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1983 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c67, some c841, some c1972, some c956, some c39, some c85, some c331, some c339, some c54, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1983 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1983 : lratChecker f1983 p1983 = .success := by decide +kernel
theorem unsat1983 : Unsatisfiable (PosFin 57) f1983 := by
  apply lratCheckerSound f1983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1983
  · intro a ha; simp [p1983] at ha; subst a; trivial
  · exact checked1983
theorem derived1983 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1983 := by
  apply localUnsat_implies_entails f1983 [c1946, c67, c841, c1972, c956, c39, c85, c331, c339, c54] c1983 unsat1983 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c1972 := derived1972 a h
  have h4 : Entails.eval a c956 := derived956 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c339 := h 338 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1984 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1984 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1981, some c40, some c84, some c196, some c31, some c71, some c380, some c77, some c841, some c168, some c1960, some c179, some c177, some c12, some c185, some c951, some c87, some c105, some c109, some c117, some c1024, some c247, some c271, some c1974, some c1036, some c352, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1984 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1984 : lratChecker f1984 p1984 = .success := by decide +kernel
theorem unsat1984 : Unsatisfiable (PosFin 57) f1984 := by
  apply lratCheckerSound f1984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1984
  · intro a ha; simp [p1984] at ha; subst a; trivial
  · exact checked1984
theorem derived1984 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1984 := by
  apply localUnsat_implies_entails f1984 [c1946, c1981, c40, c84, c196, c31, c71, c380, c77, c841, c168, c1960, c179, c177, c12, c185, c951, c87, c105, c109, c117, c1024, c247, c271, c1974, c1036, c352] c1984 unsat1984 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1981 := derived1981 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c1960 := derived1960 a h
  have h12 : Entails.eval a c179 := h 178 (by decide)
  have h13 : Entails.eval a c177 := h 176 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c185 := h 184 (by decide)
  have h16 : Entails.eval a c951 := derived951 a h
  have h17 : Entails.eval a c87 := h 86 (by decide)
  have h18 : Entails.eval a c105 := h 104 (by decide)
  have h19 : Entails.eval a c109 := h 108 (by decide)
  have h20 : Entails.eval a c117 := h 116 (by decide)
  have h21 : Entails.eval a c1024 := derived1024 a h
  have h22 : Entails.eval a c247 := h 246 (by decide)
  have h23 : Entails.eval a c271 := h 270 (by decide)
  have h24 : Entails.eval a c1974 := derived1974 a h
  have h25 : Entails.eval a c1036 := derived1036 a h
  have h26 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1985 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1985 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c181, some c183, some c179, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1985 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1985 : lratChecker f1985 p1985 = .success := by decide +kernel
theorem unsat1985 : Unsatisfiable (PosFin 57) f1985 := by
  apply lratCheckerSound f1985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1985
  · intro a ha; simp [p1985] at ha; subst a; trivial
  · exact checked1985
theorem derived1985 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1985 := by
  apply localUnsat_implies_entails f1985 [c181, c183, c179] c1985 unsat1985 (by rfl) a
  have h0 : Entails.eval a c181 := h 180 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1986 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1986 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c179, some c177, some c12, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1986 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1986 : lratChecker f1986 p1986 = .success := by decide +kernel
theorem unsat1986 : Unsatisfiable (PosFin 57) f1986 := by
  apply lratCheckerSound f1986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1986
  · intro a ha; simp [p1986] at ha; subst a; trivial
  · exact checked1986
theorem derived1986 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1986 := by
  apply localUnsat_implies_entails f1986 [c179, c177, c12] c1986 unsat1986 (by rfl) a
  have h0 : Entails.eval a c179 := h 178 (by decide)
  have h1 : Entails.eval a c177 := h 176 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1987 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨43, by decide⟩, true), (⟨6, by decide⟩, false), (⟨46, by decide⟩, true), (⟨56, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1987 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1986, some c15, some c162, some c1866, some c184, some c28, some c107, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1987 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1987 : lratChecker f1987 p1987 = .success := by decide +kernel
theorem unsat1987 : Unsatisfiable (PosFin 57) f1987 := by
  apply lratCheckerSound f1987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1987
  · intro a ha; simp [p1987] at ha; subst a; trivial
  · exact checked1987
theorem derived1987 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1987 := by
  apply localUnsat_implies_entails f1987 [c1986, c15, c162, c1866, c184, c28, c107] c1987 unsat1987 (by rfl) a
  have h0 : Entails.eval a c1986 := derived1986 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  have h3 : Entails.eval a c1866 := derived1866 a h
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1988 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1988 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c77, some c71, some c87, some c1024, some c1974, some c318, some c331, some c55, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1988 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1988 : lratChecker f1988 p1988 = .success := by decide +kernel
theorem unsat1988 : Unsatisfiable (PosFin 57) f1988 := by
  apply lratCheckerSound f1988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1988
  · intro a ha; simp [p1988] at ha; subst a; trivial
  · exact checked1988
theorem derived1988 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1988 := by
  apply localUnsat_implies_entails f1988 [c1946, c77, c71, c87, c1024, c1974, c318, c331, c55] c1988 unsat1988 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c1024 := derived1024 a h
  have h5 : Entails.eval a c1974 := derived1974 a h
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1989 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1989 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1988, some c1981, some c40, some c84, some c196, some c31, some c71, some c380, some c77, some c368, some c841, some c1984, some c1985, some c105, some c1987, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1989 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1989 : lratChecker f1989 p1989 = .success := by decide +kernel
theorem unsat1989 : Unsatisfiable (PosFin 57) f1989 := by
  apply lratCheckerSound f1989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1989
  · intro a ha; simp [p1989] at ha; subst a; trivial
  · exact checked1989
theorem derived1989 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1989 := by
  apply localUnsat_implies_entails f1989 [c1988, c1981, c40, c84, c196, c31, c71, c380, c77, c368, c841, c1984, c1985, c105, c1987] c1989 unsat1989 (by rfl) a
  have h0 : Entails.eval a c1988 := derived1988 a h
  have h1 : Entails.eval a c1981 := derived1981 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c368 := h 367 (by decide)
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c1984 := derived1984 a h
  have h12 : Entails.eval a c1985 := derived1985 a h
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c1987 := derived1987 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1990 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1990 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c77, some c370, some c1981, some c71, some c368, some c67, some c74, some c380, some c1982, some c196, some c224, some c228, some c1983, some c1989, some c88, some c69, some c1061, some c293, some c1713, some c35, some c57, some c333, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1990 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1990 : lratChecker f1990 p1990 = .success := by decide +kernel
theorem unsat1990 : Unsatisfiable (PosFin 57) f1990 := by
  apply lratCheckerSound f1990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1990
  · intro a ha; simp [p1990] at ha; subst a; trivial
  · exact checked1990
theorem derived1990 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1990 := by
  apply localUnsat_implies_entails f1990 [c1946, c77, c370, c1981, c71, c368, c67, c74, c380, c1982, c196, c224, c228, c1983, c1989, c88, c69, c1061, c293, c1713, c35, c57, c333] c1990 unsat1990 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c1981 := derived1981 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c1982 := derived1982 a h
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c224 := h 223 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  have h13 : Entails.eval a c1983 := derived1983 a h
  have h14 : Entails.eval a c1989 := derived1989 a h
  have h15 : Entails.eval a c88 := h 87 (by decide)
  have h16 : Entails.eval a c69 := h 68 (by decide)
  have h17 : Entails.eval a c1061 := derived1061 a h
  have h18 : Entails.eval a c293 := h 292 (by decide)
  have h19 : Entails.eval a c1713 := derived1713 a h
  have h20 : Entails.eval a c35 := h 34 (by decide)
  have h21 : Entails.eval a c57 := h 56 (by decide)
  have h22 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1991 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1991 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c132, some c45, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1991 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1991 : lratChecker f1991 p1991 = .success := by decide +kernel
theorem unsat1991 : Unsatisfiable (PosFin 57) f1991 := by
  apply lratCheckerSound f1991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1991
  · intro a ha; simp [p1991] at ha; subst a; trivial
  · exact checked1991
theorem derived1991 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1991 := by
  apply localUnsat_implies_entails f1991 [c280, c132, c45] c1991 unsat1991 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1992 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨18, by decide⟩, true), (⟨24, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1992 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c74, some c162, some c224, some c184, some c105, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1992 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1992 : lratChecker f1992 p1992 = .success := by decide +kernel
theorem unsat1992 : Unsatisfiable (PosFin 57) f1992 := by
  apply lratCheckerSound f1992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1992
  · intro a ha; simp [p1992] at ha; subst a; trivial
  · exact checked1992
theorem derived1992 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1992 := by
  apply localUnsat_implies_entails f1992 [c1946, c74, c162, c224, c184, c105] c1992 unsat1992 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  have h3 : Entails.eval a c224 := h 223 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1993 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1993 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c71, some c841, some c380, some c77, some c370, some c84, some c1990, some c1226, some c168, some c1985, some c154, some c152, some c80, some c1981, some c1986, some c12, some c153, some c1991, some c40, some c196, some c31, some c228, some c114, some c1992, some c1032, some c230, some c184, some c105, some c172, some c224, some c65, some c1024, some c333, some c335, some c214, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1993 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked1993 : lratChecker f1993 p1993 = .success := by decide +kernel
theorem unsat1993 : Unsatisfiable (PosFin 57) f1993 := by
  apply lratCheckerSound f1993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1993
  · intro a ha; simp [p1993] at ha; subst a; trivial
  · exact checked1993
theorem derived1993 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1993 := by
  apply localUnsat_implies_entails f1993 [c1946, c71, c841, c380, c77, c370, c84, c1990, c1226, c168, c1985, c154, c152, c80, c1981, c1986, c12, c153, c1991, c40, c196, c31, c228, c114, c1992, c1032, c230, c184, c105, c172, c224, c65, c1024, c333, c335, c214] c1993 unsat1993 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c1990 := derived1990 a h
  have h8 : Entails.eval a c1226 := derived1226 a h
  have h9 : Entails.eval a c168 := h 167 (by decide)
  have h10 : Entails.eval a c1985 := derived1985 a h
  have h11 : Entails.eval a c154 := h 153 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c1981 := derived1981 a h
  have h15 : Entails.eval a c1986 := derived1986 a h
  have h16 : Entails.eval a c12 := h 11 (by decide)
  have h17 : Entails.eval a c153 := h 152 (by decide)
  have h18 : Entails.eval a c1991 := derived1991 a h
  have h19 : Entails.eval a c40 := h 39 (by decide)
  have h20 : Entails.eval a c196 := h 195 (by decide)
  have h21 : Entails.eval a c31 := h 30 (by decide)
  have h22 : Entails.eval a c228 := h 227 (by decide)
  have h23 : Entails.eval a c114 := h 113 (by decide)
  have h24 : Entails.eval a c1992 := derived1992 a h
  have h25 : Entails.eval a c1032 := derived1032 a h
  have h26 : Entails.eval a c230 := h 229 (by decide)
  have h27 : Entails.eval a c184 := h 183 (by decide)
  have h28 : Entails.eval a c105 := h 104 (by decide)
  have h29 : Entails.eval a c172 := h 171 (by decide)
  have h30 : Entails.eval a c224 := h 223 (by decide)
  have h31 : Entails.eval a c65 := h 64 (by decide)
  have h32 : Entails.eval a c1024 := derived1024 a h
  have h33 : Entails.eval a c333 := h 332 (by decide)
  have h34 : Entails.eval a c335 := h 334 (by decide)
  have h35 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1994 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1994 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c370, some c74, some c1982, some c196, some c228, some c1992, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1994 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1994 : lratChecker f1994 p1994 = .success := by decide +kernel
theorem unsat1994 : Unsatisfiable (PosFin 57) f1994 := by
  apply lratCheckerSound f1994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1994
  · intro a ha; simp [p1994] at ha; subst a; trivial
  · exact checked1994
theorem derived1994 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1994 := by
  apply localUnsat_implies_entails f1994 [c1946, c370, c74, c1982, c196, c228, c1992] c1994 unsat1994 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c370 := h 369 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c1982 := derived1982 a h
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c1992 := derived1992 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1995 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1995 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c380, some c1990, some c77, some c370, some c84, some c1981, some c841, some c1226, some c152, some c168, some c1985, some c1993, some c88, some c69, some c1994, some c1017, some c35, some c282, some c293, some c44, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1995 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1995 : lratChecker f1995 p1995 = .success := by decide +kernel
theorem unsat1995 : Unsatisfiable (PosFin 57) f1995 := by
  apply lratCheckerSound f1995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1995
  · intro a ha; simp [p1995] at ha; subst a; trivial
  · exact checked1995
theorem derived1995 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1995 := by
  apply localUnsat_implies_entails f1995 [c71, c380, c1990, c77, c370, c84, c1981, c841, c1226, c152, c168, c1985, c1993, c88, c69, c1994, c1017, c35, c282, c293, c44] c1995 unsat1995 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c1990 := derived1990 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c1981 := derived1981 a h
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c1226 := derived1226 a h
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c1985 := derived1985 a h
  have h12 : Entails.eval a c1993 := derived1993 a h
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c1994 := derived1994 a h
  have h16 : Entails.eval a c1017 := derived1017 a h
  have h17 : Entails.eval a c35 := h 34 (by decide)
  have h18 : Entails.eval a c282 := h 281 (by decide)
  have h19 : Entails.eval a c293 := h 292 (by decide)
  have h20 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1996 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1996 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c71, some c1995, some c1972, some c376, some c39, some c85, some c339, some c331, some c54, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1996 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1996 : lratChecker f1996 p1996 = .success := by decide +kernel
theorem unsat1996 : Unsatisfiable (PosFin 57) f1996 := by
  apply lratCheckerSound f1996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1996
  · intro a ha; simp [p1996] at ha; subst a; trivial
  · exact checked1996
theorem derived1996 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1996 := by
  apply localUnsat_implies_entails f1996 [c1946, c71, c1995, c1972, c376, c39, c85, c339, c331, c54] c1996 unsat1996 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c1995 := derived1995 a h
  have h3 : Entails.eval a c1972 := derived1972 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c331 := h 330 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1997 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1997 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c77, some c370, some c84, some c71, some c1996, some c67, some c86, some c1025, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1997 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1997 : lratChecker f1997 p1997 = .success := by decide +kernel
theorem unsat1997 : Unsatisfiable (PosFin 57) f1997 := by
  apply lratCheckerSound f1997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1997
  · intro a ha; simp [p1997] at ha; subst a; trivial
  · exact checked1997
theorem derived1997 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1997 := by
  apply localUnsat_implies_entails f1997 [c1946, c77, c370, c84, c71, c1996, c67, c86, c1025] c1997 unsat1997 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c1996 := derived1996 a h
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c1025 := derived1025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1998 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1998 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c71, some c841, some c168, some c1960, some c13, some c177, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1998 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1998 : lratChecker f1998 p1998 = .success := by decide +kernel
theorem unsat1998 : Unsatisfiable (PosFin 57) f1998 := by
  apply lratCheckerSound f1998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1998
  · intro a ha; simp [p1998] at ha; subst a; trivial
  · exact checked1998
theorem derived1998 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1998 := by
  apply localUnsat_implies_entails f1998 [c84, c71, c841, c168, c1960, c13, c177] c1998 unsat1998 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c168 := h 167 (by decide)
  have h4 : Entails.eval a c1960 := derived1960 a h
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1999 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨15, by decide⟩, false), (⟨4, by decide⟩, false), (⟨43, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨6, by decide⟩, false), (⟨46, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1999 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c179, some c177, some c188, some c13, some c162, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1999 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1999 : lratChecker f1999 p1999 = .success := by decide +kernel
theorem unsat1999 : Unsatisfiable (PosFin 57) f1999 := by
  apply lratCheckerSound f1999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1999
  · intro a ha; simp [p1999] at ha; subst a; trivial
  · exact checked1999
theorem derived1999 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1999 := by
  apply localUnsat_implies_entails f1999 [c179, c177, c188, c13, c162] c1999 unsat1999 (by rfl) a
  have h0 : Entails.eval a c179 := h 178 (by decide)
  have h1 : Entails.eval a c177 := h 176 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2000 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2000 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c380, some c1997, some c77, some c370, some c84, some c1981, some c841, some c368, some c1988, some c103, some c1085, some c95, some c1998, some c1999, some c15, some c1991, some c154, some c196, some c1735, some c1709, some c295, some c31, some c57, some c194, some c335, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2000 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2000 : lratChecker f2000 p2000 = .success := by decide +kernel
theorem unsat2000 : Unsatisfiable (PosFin 57) f2000 := by
  apply lratCheckerSound f2000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2000
  · intro a ha; simp [p2000] at ha; subst a; trivial
  · exact checked2000
theorem derived2000 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2000 := by
  apply localUnsat_implies_entails f2000 [c71, c380, c1997, c77, c370, c84, c1981, c841, c368, c1988, c103, c1085, c95, c1998, c1999, c15, c1991, c154, c196, c1735, c1709, c295, c31, c57, c194, c335] c2000 unsat2000 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c1997 := derived1997 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c1981 := derived1981 a h
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c1988 := derived1988 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c1085 := derived1085 a h
  have h12 : Entails.eval a c95 := h 94 (by decide)
  have h13 : Entails.eval a c1998 := derived1998 a h
  have h14 : Entails.eval a c1999 := derived1999 a h
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c1991 := derived1991 a h
  have h17 : Entails.eval a c154 := h 153 (by decide)
  have h18 : Entails.eval a c196 := h 195 (by decide)
  have h19 : Entails.eval a c1735 := derived1735 a h
  have h20 : Entails.eval a c1709 := derived1709 a h
  have h21 : Entails.eval a c295 := h 294 (by decide)
  have h22 : Entails.eval a c31 := h 30 (by decide)
  have h23 : Entails.eval a c57 := h 56 (by decide)
  have h24 : Entails.eval a c194 := h 193 (by decide)
  have h25 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2001 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨35, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨40, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2001 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1709, some c267, some c293, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2001 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2001 : lratChecker f2001 p2001 = .success := by decide +kernel
theorem unsat2001 : Unsatisfiable (PosFin 57) f2001 := by
  apply lratCheckerSound f2001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2001
  · intro a ha; simp [p2001] at ha; subst a; trivial
  · exact checked2001
theorem derived2001 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2001 := by
  apply localUnsat_implies_entails f2001 [c1709, c267, c293] c2001 unsat2001 (by rfl) a
  have h0 : Entails.eval a c1709 := derived1709 a h
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2002 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2002 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c280, some c41, some c45, some c307, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2002 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2002 : lratChecker f2002 p2002 = .success := by decide +kernel
theorem unsat2002 : Unsatisfiable (PosFin 57) f2002 := by
  apply lratCheckerSound f2002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2002
  · intro a ha; simp [p2002] at ha; subst a; trivial
  · exact checked2002
theorem derived2002 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2002 := by
  apply localUnsat_implies_entails f2002 [c1946, c280, c41, c45, c307] c2002 unsat2002 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c280 := h 279 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2003 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2003 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c380, some c77, some c2002, some c1997, some c370, some c84, some c1981, some c2000, some c80, some c1226, some c152, some c103, some c1085, some c9, some c69, some c2001, some c162, some c1017, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2003 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2003 : lratChecker f2003 p2003 = .success := by decide +kernel
theorem unsat2003 : Unsatisfiable (PosFin 57) f2003 := by
  apply lratCheckerSound f2003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2003
  · intro a ha; simp [p2003] at ha; subst a; trivial
  · exact checked2003
theorem derived2003 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2003 := by
  apply localUnsat_implies_entails f2003 [c71, c380, c77, c2002, c1997, c370, c84, c1981, c2000, c80, c1226, c152, c103, c1085, c9, c69, c2001, c162, c1017] c2003 unsat2003 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c77 := h 76 (by decide)
  have h3 : Entails.eval a c2002 := derived2002 a h
  have h4 : Entails.eval a c1997 := derived1997 a h
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c1981 := derived1981 a h
  have h8 : Entails.eval a c2000 := derived2000 a h
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c1226 := derived1226 a h
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c1085 := derived1085 a h
  have h14 : Entails.eval a c9 := h 8 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c2001 := derived2001 a h
  have h17 : Entails.eval a c162 := h 161 (by decide)
  have h18 : Entails.eval a c1017 := derived1017 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2004 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2004 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1997, some c77, some c71, some c2003, some c968, some c376, some c103, some c85, some c80, some c1024, some c1974, some c318, some c331, some c55, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2004 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2004 : lratChecker f2004 p2004 = .success := by decide +kernel
theorem unsat2004 : Unsatisfiable (PosFin 57) f2004 := by
  apply lratCheckerSound f2004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2004
  · intro a ha; simp [p2004] at ha; subst a; trivial
  · exact checked2004
theorem derived2004 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2004 := by
  apply localUnsat_implies_entails f2004 [c1946, c1997, c77, c71, c2003, c968, c376, c103, c85, c80, c1024, c1974, c318, c331, c55] c2004 unsat2004 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1997 := derived1997 a h
  have h2 : Entails.eval a c77 := h 76 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c2003 := derived2003 a h
  have h5 : Entails.eval a c968 := derived968 a h
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c1024 := derived1024 a h
  have h11 : Entails.eval a c1974 := derived1974 a h
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c331 := h 330 (by decide)
  have h14 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2005 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2005 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c1988, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2005 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2005 : lratChecker f2005 p2005 = .success := by decide +kernel
theorem unsat2005 : Unsatisfiable (PosFin 57) f2005 := by
  apply lratCheckerSound f2005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2005
  · intro a ha; simp [p2005] at ha; subst a; trivial
  · exact checked2005
theorem derived2005 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2005 := by
  apply localUnsat_implies_entails f2005 [c80, c1988] c2005 unsat2005 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c1988 := derived1988 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2006 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨3, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2006 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1981, some c40, some c84, some c196, some c31, some c77, some c71, some c841, some c2005, some c103, some c1998, some c9, some c188, some c152, some c177, some c368, some c183, some c15, some c171, some c1866, some c166, some c1024, some c232, some c318, some c107, some c269, some c253, some c278, some c616, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2006 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2006 : lratChecker f2006 p2006 = .success := by decide +kernel
theorem unsat2006 : Unsatisfiable (PosFin 57) f2006 := by
  apply lratCheckerSound f2006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2006
  · intro a ha; simp [p2006] at ha; subst a; trivial
  · exact checked2006
theorem derived2006 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2006 := by
  apply localUnsat_implies_entails f2006 [c1946, c1981, c40, c84, c196, c31, c77, c71, c841, c2005, c103, c1998, c9, c188, c152, c177, c368, c183, c15, c171, c1866, c166, c1024, c232, c318, c107, c269, c253, c278, c616] c2006 unsat2006 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1981 := derived1981 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c841 := derived841 a h
  have h9 : Entails.eval a c2005 := derived2005 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c1998 := derived1998 a h
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c188 := h 187 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c177 := h 176 (by decide)
  have h16 : Entails.eval a c368 := h 367 (by decide)
  have h17 : Entails.eval a c183 := h 182 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c171 := h 170 (by decide)
  have h20 : Entails.eval a c1866 := derived1866 a h
  have h21 : Entails.eval a c166 := h 165 (by decide)
  have h22 : Entails.eval a c1024 := derived1024 a h
  have h23 : Entails.eval a c232 := h 231 (by decide)
  have h24 : Entails.eval a c318 := h 317 (by decide)
  have h25 : Entails.eval a c107 := h 106 (by decide)
  have h26 : Entails.eval a c269 := h 268 (by decide)
  have h27 : Entails.eval a c253 := h 252 (by decide)
  have h28 : Entails.eval a c278 := h 277 (by decide)
  have h29 : Entails.eval a c616 := derived616 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2007 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2007 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c77, some c71, some c841, some c80, some c368, some c956, some c85, some c1024, some c1974, some c318, some c331, some c55, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2007 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2007 : lratChecker f2007 p2007 = .success := by decide +kernel
theorem unsat2007 : Unsatisfiable (PosFin 57) f2007 := by
  apply lratCheckerSound f2007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2007
  · intro a ha; simp [p2007] at ha; subst a; trivial
  · exact checked2007
theorem derived2007 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2007 := by
  apply localUnsat_implies_entails f2007 [c1946, c77, c71, c841, c80, c368, c956, c85, c1024, c1974, c318, c331, c55] c2007 unsat2007 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c956 := derived956 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c1024 := derived1024 a h
  have h9 : Entails.eval a c1974 := derived1974 a h
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c331 := h 330 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2008 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2008 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c85, some c88, some c373, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p2008 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2008 : lratChecker f2008 p2008 = .success := by decide +kernel
theorem unsat2008 : Unsatisfiable (PosFin 57) f2008 := by
  apply lratCheckerSound f2008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2008
  · intro a ha; simp [p2008] at ha; subst a; trivial
  · exact checked2008
theorem derived2008 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2008 := by
  apply localUnsat_implies_entails f2008 [c1946, c85, c88, c373] c2008 unsat2008 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2009 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2009 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1981, some c71, some c841, some c77, some c370, some c84, some c1997, some c2002, some c40, some c196, some c228, some c2004, some c1118, some c2006, some c2007, some c103, some c9, some c2008, some c377, some c956, some c154, some c976, some c15, some c1491, some c164, some c179, some c597, some c277, some c267, some c143, some c317, some c57, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2009 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked2009 : lratChecker f2009 p2009 = .success := by decide +kernel
theorem unsat2009 : Unsatisfiable (PosFin 57) f2009 := by
  apply lratCheckerSound f2009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2009
  · intro a ha; simp [p2009] at ha; subst a; trivial
  · exact checked2009
theorem derived2009 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2009 := by
  apply localUnsat_implies_entails f2009 [c1981, c71, c841, c77, c370, c84, c1997, c2002, c40, c196, c228, c2004, c1118, c2006, c2007, c103, c9, c2008, c377, c956, c154, c976, c15, c1491, c164, c179, c597, c277, c267, c143, c317, c57] c2009 unsat2009 (by rfl) a
  have h0 : Entails.eval a c1981 := derived1981 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c1997 := derived1997 a h
  have h7 : Entails.eval a c2002 := derived2002 a h
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c2004 := derived2004 a h
  have h12 : Entails.eval a c1118 := derived1118 a h
  have h13 : Entails.eval a c2006 := derived2006 a h
  have h14 : Entails.eval a c2007 := derived2007 a h
  have h15 : Entails.eval a c103 := h 102 (by decide)
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c2008 := derived2008 a h
  have h18 : Entails.eval a c377 := h 376 (by decide)
  have h19 : Entails.eval a c956 := derived956 a h
  have h20 : Entails.eval a c154 := h 153 (by decide)
  have h21 : Entails.eval a c976 := derived976 a h
  have h22 : Entails.eval a c15 := h 14 (by decide)
  have h23 : Entails.eval a c1491 := derived1491 a h
  have h24 : Entails.eval a c164 := h 163 (by decide)
  have h25 : Entails.eval a c179 := h 178 (by decide)
  have h26 : Entails.eval a c597 := derived597 a h
  have h27 : Entails.eval a c277 := h 276 (by decide)
  have h28 : Entails.eval a c267 := h 266 (by decide)
  have h29 : Entails.eval a c143 := h 142 (by decide)
  have h30 : Entails.eval a c317 := h 316 (by decide)
  have h31 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2010 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2010 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c2009, some c71, some c841, some c1950, some c102, some c84, some c1664, some c366, some c370, some c80, some c1662, some c65, some c1660, some c596, some c373, some c1985, some c1665, some c159, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2010 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2010 : lratChecker f2010 p2010 = .success := by decide +kernel
theorem unsat2010 : Unsatisfiable (PosFin 57) f2010 := by
  apply lratCheckerSound f2010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2010
  · intro a ha; simp [p2010] at ha; subst a; trivial
  · exact checked2010
theorem derived2010 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2010 := by
  apply localUnsat_implies_entails f2010 [c1946, c2009, c71, c841, c1950, c102, c84, c1664, c366, c370, c80, c1662, c65, c1660, c596, c373, c1985, c1665, c159] c2010 unsat2010 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c2009 := derived2009 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c1950 := derived1950 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c1664 := derived1664 a h
  have h8 : Entails.eval a c366 := h 365 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c1662 := derived1662 a h
  have h12 : Entails.eval a c65 := h 64 (by decide)
  have h13 : Entails.eval a c1660 := derived1660 a h
  have h14 : Entails.eval a c596 := derived596 a h
  have h15 : Entails.eval a c373 := h 372 (by decide)
  have h16 : Entails.eval a c1985 := derived1985 a h
  have h17 : Entails.eval a c1665 := derived1665 a h
  have h18 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2011 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2011 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2009, some c2010, some c100, some c80, some c1981, some c71, some c841, some c370, some c368, some c84, some c102, some c40, some c1251, some c61, some c1956, some c1256, some c280, some c956, some c190, some c21, some c228, some c215, some c709, some c337, some c63, some c264, some c1118, some c300, some c1951, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2011 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2011 : lratChecker f2011 p2011 = .success := by decide +kernel
theorem unsat2011 : Unsatisfiable (PosFin 57) f2011 := by
  apply lratCheckerSound f2011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2011
  · intro a ha; simp [p2011] at ha; subst a; trivial
  · exact checked2011
theorem derived2011 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2011 := by
  apply localUnsat_implies_entails f2011 [c2009, c2010, c100, c80, c1981, c71, c841, c370, c368, c84, c102, c40, c1251, c61, c1956, c1256, c280, c956, c190, c21, c228, c215, c709, c337, c63, c264, c1118, c300, c1951] c2011 unsat2011 (by rfl) a
  have h0 : Entails.eval a c2009 := derived2009 a h
  have h1 : Entails.eval a c2010 := derived2010 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c80 := h 79 (by decide)
  have h4 : Entails.eval a c1981 := derived1981 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c1251 := derived1251 a h
  have h13 : Entails.eval a c61 := h 60 (by decide)
  have h14 : Entails.eval a c1956 := derived1956 a h
  have h15 : Entails.eval a c1256 := derived1256 a h
  have h16 : Entails.eval a c280 := h 279 (by decide)
  have h17 : Entails.eval a c956 := derived956 a h
  have h18 : Entails.eval a c190 := h 189 (by decide)
  have h19 : Entails.eval a c21 := h 20 (by decide)
  have h20 : Entails.eval a c228 := h 227 (by decide)
  have h21 : Entails.eval a c215 := h 214 (by decide)
  have h22 : Entails.eval a c709 := derived709 a h
  have h23 : Entails.eval a c337 := h 336 (by decide)
  have h24 : Entails.eval a c63 := h 62 (by decide)
  have h25 : Entails.eval a c264 := h 263 (by decide)
  have h26 : Entails.eval a c1118 := derived1118 a h
  have h27 : Entails.eval a c300 := h 299 (by decide)
  have h28 : Entails.eval a c1951 := derived1951 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2012 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2012 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c2009, some c2010, some c100, some c80, some c71, some c1251, some c87, some c102, some c84, some c946, some c1461, some c331, some c291, some c33, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2012 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2012 : lratChecker f2012 p2012 = .success := by decide +kernel
theorem unsat2012 : Unsatisfiable (PosFin 57) f2012 := by
  apply lratCheckerSound f2012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2012
  · intro a ha; simp [p2012] at ha; subst a; trivial
  · exact checked2012
theorem derived2012 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2012 := by
  apply localUnsat_implies_entails f2012 [c1946, c2009, c2010, c100, c80, c71, c1251, c87, c102, c84, c946, c1461, c331, c291, c33] c2012 unsat2012 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c2009 := derived2009 a h
  have h2 : Entails.eval a c2010 := derived2010 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c1251 := derived1251 a h
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c946 := derived946 a h
  have h11 : Entails.eval a c1461 := derived1461 a h
  have h12 : Entails.eval a c331 := h 330 (by decide)
  have h13 : Entails.eval a c291 := h 290 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2013 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2013 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c162, some c7, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2013 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2013 : lratChecker f2013 p2013 = .success := by decide +kernel
theorem unsat2013 : Unsatisfiable (PosFin 57) f2013 := by
  apply lratCheckerSound f2013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2013
  · intro a ha; simp [p2013] at ha; subst a; trivial
  · exact checked2013
theorem derived2013 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2013 := by
  apply localUnsat_implies_entails f2013 [c84, c162, c7] c2013 unsat2013 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2014 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨46, by decide⟩, false), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨48, by decide⟩, false), (⟨40, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2014 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c1956, some c1247, some c325, some c324, some c284, some c270, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2014 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2014 : lratChecker f2014 p2014 = .success := by decide +kernel
theorem unsat2014 : Unsatisfiable (PosFin 57) f2014 := by
  apply lratCheckerSound f2014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2014
  · intro a ha; simp [p2014] at ha; subst a; trivial
  · exact checked2014
theorem derived2014 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2014 := by
  apply localUnsat_implies_entails f2014 [c61, c1956, c1247, c325, c324, c284, c270] c2014 unsat2014 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c1247 := derived1247 a h
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2015 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨5, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2015 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2012, some c2011, some c2009, some c2010, some c100, some c80, some c1981, some c71, some c380, some c376, some c1951, some c356, some c150, some c1287, some c2013, some c2014, some c102, some c946, some c1461, some c1462, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2015 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2015 : lratChecker f2015 p2015 = .success := by decide +kernel
theorem unsat2015 : Unsatisfiable (PosFin 57) f2015 := by
  apply lratCheckerSound f2015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2015
  · intro a ha; simp [p2015] at ha; subst a; trivial
  · exact checked2015
theorem derived2015 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2015 := by
  apply localUnsat_implies_entails f2015 [c2012, c2011, c2009, c2010, c100, c80, c1981, c71, c380, c376, c1951, c356, c150, c1287, c2013, c2014, c102, c946, c1461, c1462] c2015 unsat2015 (by rfl) a
  have h0 : Entails.eval a c2012 := derived2012 a h
  have h1 : Entails.eval a c2011 := derived2011 a h
  have h2 : Entails.eval a c2009 := derived2009 a h
  have h3 : Entails.eval a c2010 := derived2010 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c1981 := derived1981 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c1951 := derived1951 a h
  have h11 : Entails.eval a c356 := h 355 (by decide)
  have h12 : Entails.eval a c150 := h 149 (by decide)
  have h13 : Entails.eval a c1287 := derived1287 a h
  have h14 : Entails.eval a c2013 := derived2013 a h
  have h15 : Entails.eval a c2014 := derived2014 a h
  have h16 : Entails.eval a c102 := h 101 (by decide)
  have h17 : Entails.eval a c946 := derived946 a h
  have h18 : Entails.eval a c1461 := derived1461 a h
  have h19 : Entails.eval a c1462 := derived1462 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2016 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2016 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2012, some c2011, some c2009, some c2010, some c100, some c80, some c71, some c841, some c2015, some c1118, some c5, some c10, some c1245, some c150, some c377, some c358, some c366, some c1697, some c157, some c1345, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2016 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2016 : lratChecker f2016 p2016 = .success := by decide +kernel
theorem unsat2016 : Unsatisfiable (PosFin 57) f2016 := by
  apply lratCheckerSound f2016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2016
  · intro a ha; simp [p2016] at ha; subst a; trivial
  · exact checked2016
theorem derived2016 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2016 := by
  apply localUnsat_implies_entails f2016 [c2012, c2011, c2009, c2010, c100, c80, c71, c841, c2015, c1118, c5, c10, c1245, c150, c377, c358, c366, c1697, c157, c1345] c2016 unsat2016 (by rfl) a
  have h0 : Entails.eval a c2012 := derived2012 a h
  have h1 : Entails.eval a c2011 := derived2011 a h
  have h2 : Entails.eval a c2009 := derived2009 a h
  have h3 : Entails.eval a c2010 := derived2010 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c2015 := derived2015 a h
  have h9 : Entails.eval a c1118 := derived1118 a h
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c1245 := derived1245 a h
  have h13 : Entails.eval a c150 := h 149 (by decide)
  have h14 : Entails.eval a c377 := h 376 (by decide)
  have h15 : Entails.eval a c358 := h 357 (by decide)
  have h16 : Entails.eval a c366 := h 365 (by decide)
  have h17 : Entails.eval a c1697 := derived1697 a h
  have h18 : Entails.eval a c157 := h 156 (by decide)
  have h19 : Entails.eval a c1345 := derived1345 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2017 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2017 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c841, some c2009, some c2010, some c100, some c80, some c2011, some c2012, some c2016, some c1394, some c95, some c102, some c84, some c946, some c1461, some c94, some c1462, some c377, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2017 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2017 : lratChecker f2017 p2017 = .success := by decide +kernel
theorem unsat2017 : Unsatisfiable (PosFin 57) f2017 := by
  apply lratCheckerSound f2017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2017
  · intro a ha; simp [p2017] at ha; subst a; trivial
  · exact checked2017
theorem derived2017 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2017 := by
  apply localUnsat_implies_entails f2017 [c71, c841, c2009, c2010, c100, c80, c2011, c2012, c2016, c1394, c95, c102, c84, c946, c1461, c94, c1462, c377] c2017 unsat2017 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c2009 := derived2009 a h
  have h3 : Entails.eval a c2010 := derived2010 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c2011 := derived2011 a h
  have h7 : Entails.eval a c2012 := derived2012 a h
  have h8 : Entails.eval a c2016 := derived2016 a h
  have h9 : Entails.eval a c1394 := derived1394 a h
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c946 := derived946 a h
  have h14 : Entails.eval a c1461 := derived1461 a h
  have h15 : Entails.eval a c94 := h 93 (by decide)
  have h16 : Entails.eval a c1462 := derived1462 a h
  have h17 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2018 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, true), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2018 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1146, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p2018 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2018 : lratChecker f2018 p2018 = .success := by decide +kernel
theorem unsat2018 : Unsatisfiable (PosFin 57) f2018 := by
  apply lratCheckerSound f2018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2018
  · intro a ha; simp [p2018] at ha; subst a; trivial
  · exact checked2018
theorem derived2018 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2018 := by
  apply localUnsat_implies_entails f2018 [c1946, c1146] c2018 unsat2018 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1146 := derived1146 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2019 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨8, by decide⟩, true), (⟨48, by decide⟩, false), (⟨5, by decide⟩, true), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2019 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1030, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2019 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2019 : lratChecker f2019 p2019 = .success := by decide +kernel
theorem unsat2019 : Unsatisfiable (PosFin 57) f2019 := by
  apply lratCheckerSound f2019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2019
  · intro a ha; simp [p2019] at ha; subst a; trivial
  · exact checked2019
theorem derived2019 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2019 := by
  apply localUnsat_implies_entails f2019 [c1946, c1030] c2019 unsat2019 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1030 := derived1030 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2020 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2020 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1148, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p2020 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2020 : lratChecker f2020 p2020 = .success := by decide +kernel
theorem unsat2020 : Unsatisfiable (PosFin 57) f2020 := by
  apply lratCheckerSound f2020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2020
  · intro a ha; simp [p2020] at ha; subst a; trivial
  · exact checked2020
theorem derived2020 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2020 := by
  apply localUnsat_implies_entails f2020 [c1946, c1148] c2020 unsat2020 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2021 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨42, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2021 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1042, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p2021 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2021 : lratChecker f2021 p2021 = .success := by decide +kernel
theorem unsat2021 : Unsatisfiable (PosFin 57) f2021 := by
  apply lratCheckerSound f2021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2021
  · intro a ha; simp [p2021] at ha; subst a; trivial
  · exact checked2021
theorem derived2021 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2021 := by
  apply localUnsat_implies_entails f2021 [c1946, c1042] c2021 unsat2021 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1042 := derived1042 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2022 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨33, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2022 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c827, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2022 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2022 : lratChecker f2022 p2022 = .success := by decide +kernel
theorem unsat2022 : Unsatisfiable (PosFin 57) f2022 := by
  apply lratCheckerSound f2022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2022
  · intro a ha; simp [p2022] at ha; subst a; trivial
  · exact checked2022
theorem derived2022 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2022 := by
  apply localUnsat_implies_entails f2022 [c1946, c827] c2022 unsat2022 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c827 := derived827 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2023 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2023 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c835, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2023 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2023 : lratChecker f2023 p2023 = .success := by decide +kernel
theorem unsat2023 : Unsatisfiable (PosFin 57) f2023 := by
  apply lratCheckerSound f2023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2023
  · intro a ha; simp [p2023] at ha; subst a; trivial
  · exact checked2023
theorem derived2023 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2023 := by
  apply localUnsat_implies_entails f2023 [c1946, c835] c2023 unsat2023 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c835 := derived835 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2024 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2024 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c978, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2024 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2024 : lratChecker f2024 p2024 = .success := by decide +kernel
theorem unsat2024 : Unsatisfiable (PosFin 57) f2024 := by
  apply lratCheckerSound f2024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2024
  · intro a ha; simp [p2024] at ha; subst a; trivial
  · exact checked2024
theorem derived2024 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2024 := by
  apply localUnsat_implies_entails f2024 [c1946, c978] c2024 unsat2024 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c978 := derived978 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2025 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2025 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c33, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p2025 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2025 : lratChecker f2025 p2025 = .success := by decide +kernel
theorem unsat2025 : Unsatisfiable (PosFin 57) f2025 := by
  apply lratCheckerSound f2025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2025
  · intro a ha; simp [p2025] at ha; subst a; trivial
  · exact checked2025
theorem derived2025 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2025 := by
  apply localUnsat_implies_entails f2025 [c1946, c33] c2025 unsat2025 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2026 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨33, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2026 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c54, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2026 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2026 : lratChecker f2026 p2026 = .success := by decide +kernel
theorem unsat2026 : Unsatisfiable (PosFin 57) f2026 := by
  apply lratCheckerSound f2026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2026
  · intro a ha; simp [p2026] at ha; subst a; trivial
  · exact checked2026
theorem derived2026 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2026 := by
  apply localUnsat_implies_entails f2026 [c1946, c54] c2026 unsat2026 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2027 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2027 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c74, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2027 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2027 : lratChecker f2027 p2027 = .success := by decide +kernel
theorem unsat2027 : Unsatisfiable (PosFin 57) f2027 := by
  apply lratCheckerSound f2027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2027
  · intro a ha; simp [p2027] at ha; subst a; trivial
  · exact checked2027
theorem derived2027 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2027 := by
  apply localUnsat_implies_entails f2027 [c1946, c74] c2027 unsat2027 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2028 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2028 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c885, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2028 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2028 : lratChecker f2028 p2028 = .success := by decide +kernel
theorem unsat2028 : Unsatisfiable (PosFin 57) f2028 := by
  apply lratCheckerSound f2028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2028
  · intro a ha; simp [p2028] at ha; subst a; trivial
  · exact checked2028
theorem derived2028 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2028 := by
  apply localUnsat_implies_entails f2028 [c1946, c885] c2028 unsat2028 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c885 := derived885 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2029 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨33, by decide⟩, true), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2029 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c843, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2029 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2029 : lratChecker f2029 p2029 = .success := by decide +kernel
theorem unsat2029 : Unsatisfiable (PosFin 57) f2029 := by
  apply lratCheckerSound f2029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2029
  · intro a ha; simp [p2029] at ha; subst a; trivial
  · exact checked2029
theorem derived2029 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2029 := by
  apply localUnsat_implies_entails f2029 [c1946, c843] c2029 unsat2029 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c843 := derived843 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2030 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2030 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1052, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p2030 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2030 : lratChecker f2030 p2030 = .success := by decide +kernel
theorem unsat2030 : Unsatisfiable (PosFin 57) f2030 := by
  apply lratCheckerSound f2030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2030
  · intro a ha; simp [p2030] at ha; subst a; trivial
  · exact checked2030
theorem derived2030 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2030 := by
  apply localUnsat_implies_entails f2030 [c1946, c1052] c2030 unsat2030 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1052 := derived1052 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2031 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2031 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c550, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p2031 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2031 : lratChecker f2031 p2031 = .success := by decide +kernel
theorem unsat2031 : Unsatisfiable (PosFin 57) f2031 := by
  apply lratCheckerSound f2031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2031
  · intro a ha; simp [p2031] at ha; subst a; trivial
  · exact checked2031
theorem derived2031 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2031 := by
  apply localUnsat_implies_entails f2031 [c1946, c550] c2031 unsat2031 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c550 := derived550 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2032 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨44, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2032 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c75, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p2032 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2032 : lratChecker f2032 p2032 = .success := by decide +kernel
theorem unsat2032 : Unsatisfiable (PosFin 57) f2032 := by
  apply lratCheckerSound f2032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2032
  · intro a ha; simp [p2032] at ha; subst a; trivial
  · exact checked2032
theorem derived2032 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2032 := by
  apply localUnsat_implies_entails f2032 [c1946, c75] c2032 unsat2032 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2033 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2033 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c55, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2033 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2033 : lratChecker f2033 p2033 = .success := by decide +kernel
theorem unsat2033 : Unsatisfiable (PosFin 57) f2033 := by
  apply lratCheckerSound f2033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2033
  · intro a ha; simp [p2033] at ha; subst a; trivial
  · exact checked2033
theorem derived2033 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2033 := by
  apply localUnsat_implies_entails f2033 [c1946, c55] c2033 unsat2033 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2034 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2034 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1053, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2034 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2034 : lratChecker f2034 p2034 = .success := by decide +kernel
theorem unsat2034 : Unsatisfiable (PosFin 57) f2034 := by
  apply lratCheckerSound f2034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2034
  · intro a ha; simp [p2034] at ha; subst a; trivial
  · exact checked2034
theorem derived2034 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2034 := by
  apply localUnsat_implies_entails f2034 [c1946, c1053] c2034 unsat2034 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1053 := derived1053 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2035 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2035 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c65, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2035 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2035 : lratChecker f2035 p2035 = .success := by decide +kernel
theorem unsat2035 : Unsatisfiable (PosFin 57) f2035 := by
  apply lratCheckerSound f2035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2035
  · intro a ha; simp [p2035] at ha; subst a; trivial
  · exact checked2035
theorem derived2035 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2035 := by
  apply localUnsat_implies_entails f2035 [c1946, c65] c2035 unsat2035 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2036 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨51, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2036 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c86, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2036 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2036 : lratChecker f2036 p2036 = .success := by decide +kernel
theorem unsat2036 : Unsatisfiable (PosFin 57) f2036 := by
  apply lratCheckerSound f2036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2036
  · intro a ha; simp [p2036] at ha; subst a; trivial
  · exact checked2036
theorem derived2036 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2036 := by
  apply localUnsat_implies_entails f2036 [c1946, c86] c2036 unsat2036 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2037 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2037 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c87, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2037 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2037 : lratChecker f2037 p2037 = .success := by decide +kernel
theorem unsat2037 : Unsatisfiable (PosFin 57) f2037 := by
  apply lratCheckerSound f2037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2037
  · intro a ha; simp [p2037] at ha; subst a; trivial
  · exact checked2037
theorem derived2037 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2037 := by
  apply localUnsat_implies_entails f2037 [c1946, c87] c2037 unsat2037 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2038 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨33, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2038 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c829, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2038 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2038 : lratChecker f2038 p2038 = .success := by decide +kernel
theorem unsat2038 : Unsatisfiable (PosFin 57) f2038 := by
  apply lratCheckerSound f2038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2038
  · intro a ha; simp [p2038] at ha; subst a; trivial
  · exact checked2038
theorem derived2038 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2038 := by
  apply localUnsat_implies_entails f2038 [c1946, c829] c2038 unsat2038 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c829 := derived829 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2039 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨49, by decide⟩, true), (⟨28, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2039 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c565, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p2039 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2039 : lratChecker f2039 p2039 = .success := by decide +kernel
theorem unsat2039 : Unsatisfiable (PosFin 57) f2039 := by
  apply lratCheckerSound f2039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2039
  · intro a ha; simp [p2039] at ha; subst a; trivial
  · exact checked2039
theorem derived2039 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2039 := by
  apply localUnsat_implies_entails f2039 [c1946, c565] c2039 unsat2039 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c565 := derived565 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2040 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨5, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2040 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1029, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p2040 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2040 : lratChecker f2040 p2040 = .success := by decide +kernel
theorem unsat2040 : Unsatisfiable (PosFin 57) f2040 := by
  apply lratCheckerSound f2040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2040
  · intro a ha; simp [p2040] at ha; subst a; trivial
  · exact checked2040
theorem derived2040 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2040 := by
  apply localUnsat_implies_entails f2040 [c1946, c1029] c2040 unsat2040 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1029 := derived1029 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2041 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2041 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1061, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p2041 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2041 : lratChecker f2041 p2041 = .success := by decide +kernel
theorem unsat2041 : Unsatisfiable (PosFin 57) f2041 := by
  apply lratCheckerSound f2041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2041
  · intro a ha; simp [p2041] at ha; subst a; trivial
  · exact checked2041
theorem derived2041 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2041 := by
  apply localUnsat_implies_entails f2041 [c1946, c1061] c2041 unsat2041 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1061 := derived1061 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2042 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨41, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2042 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1139, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2042 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2042 : lratChecker f2042 p2042 = .success := by decide +kernel
theorem unsat2042 : Unsatisfiable (PosFin 57) f2042 := by
  apply lratCheckerSound f2042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2042
  · intro a ha; simp [p2042] at ha; subst a; trivial
  · exact checked2042
theorem derived2042 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2042 := by
  apply localUnsat_implies_entails f2042 [c1946, c1139] c2042 unsat2042 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1139 := derived1139 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2043 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2043 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1043, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p2043 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2043 : lratChecker f2043 p2043 = .success := by decide +kernel
theorem unsat2043 : Unsatisfiable (PosFin 57) f2043 := by
  apply lratCheckerSound f2043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2043
  · intro a ha; simp [p2043] at ha; subst a; trivial
  · exact checked2043
theorem derived2043 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2043 := by
  apply localUnsat_implies_entails f2043 [c1946, c1043] c2043 unsat2043 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1043 := derived1043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2044 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨40, by decide⟩, true), (⟨8, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨47, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2044 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c991, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p2044 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2044 : lratChecker f2044 p2044 = .success := by decide +kernel
theorem unsat2044 : Unsatisfiable (PosFin 57) f2044 := by
  apply lratCheckerSound f2044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2044
  · intro a ha; simp [p2044] at ha; subst a; trivial
  · exact checked2044
theorem derived2044 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2044 := by
  apply localUnsat_implies_entails f2044 [c1946, c991] c2044 unsat2044 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c991 := derived991 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2045 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2045 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1013, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2045 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2045 : lratChecker f2045 p2045 = .success := by decide +kernel
theorem unsat2045 : Unsatisfiable (PosFin 57) f2045 := by
  apply lratCheckerSound f2045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2045
  · intro a ha; simp [p2045] at ha; subst a; trivial
  · exact checked2045
theorem derived2045 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2045 := by
  apply localUnsat_implies_entails f2045 [c1946, c1013] c2045 unsat2045 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1013 := derived1013 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2046 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨35, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2046 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1019, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p2046 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2046 : lratChecker f2046 p2046 = .success := by decide +kernel
theorem unsat2046 : Unsatisfiable (PosFin 57) f2046 := by
  apply lratCheckerSound f2046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2046
  · intro a ha; simp [p2046] at ha; subst a; trivial
  · exact checked2046
theorem derived2046 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2046 := by
  apply localUnsat_implies_entails f2046 [c1946, c1019] c2046 unsat2046 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1019 := derived1019 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2047 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2047 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c42, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2047 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2047 : lratChecker f2047 p2047 = .success := by decide +kernel
theorem unsat2047 : Unsatisfiable (PosFin 57) f2047 := by
  apply lratCheckerSound f2047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2047
  · intro a ha; simp [p2047] at ha; subst a; trivial
  · exact checked2047
theorem derived2047 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2047 := by
  apply localUnsat_implies_entails f2047 [c1946, c42] c2047 unsat2047 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2048 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2048 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1012, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2048 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2048 : lratChecker f2048 p2048 = .success := by decide +kernel
theorem unsat2048 : Unsatisfiable (PosFin 57) f2048 := by
  apply lratCheckerSound f2048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2048
  · intro a ha; simp [p2048] at ha; subst a; trivial
  · exact checked2048
theorem derived2048 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2048 := by
  apply localUnsat_implies_entails f2048 [c1946, c1012] c2048 unsat2048 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1012 := derived1012 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2049 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2049 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c919, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p2049 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2049 : lratChecker f2049 p2049 = .success := by decide +kernel
theorem unsat2049 : Unsatisfiable (PosFin 57) f2049 := by
  apply lratCheckerSound f2049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2049
  · intro a ha; simp [p2049] at ha; subst a; trivial
  · exact checked2049
theorem derived2049 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2049 := by
  apply localUnsat_implies_entails f2049 [c1946, c919] c2049 unsat2049 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c919 := derived919 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2050 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨33, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2050 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c53, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2050 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2050 : lratChecker f2050 p2050 = .success := by decide +kernel
theorem unsat2050 : Unsatisfiable (PosFin 57) f2050 := by
  apply lratCheckerSound f2050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2050
  · intro a ha; simp [p2050] at ha; subst a; trivial
  · exact checked2050
theorem derived2050 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2050 := by
  apply localUnsat_implies_entails f2050 [c1946, c53] c2050 unsat2050 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2051 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨42, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2051 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1018, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p2051 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2051 : lratChecker f2051 p2051 = .success := by decide +kernel
theorem unsat2051 : Unsatisfiable (PosFin 57) f2051 := by
  apply lratCheckerSound f2051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2051
  · intro a ha; simp [p2051] at ha; subst a; trivial
  · exact checked2051
theorem derived2051 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2051 := by
  apply localUnsat_implies_entails f2051 [c1946, c1018] c2051 unsat2051 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1018 := derived1018 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2052 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2052 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1024, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2052 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2052 : lratChecker f2052 p2052 = .success := by decide +kernel
theorem unsat2052 : Unsatisfiable (PosFin 57) f2052 := by
  apply lratCheckerSound f2052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2052
  · intro a ha; simp [p2052] at ha; subst a; trivial
  · exact checked2052
theorem derived2052 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2052 := by
  apply localUnsat_implies_entails f2052 [c1946, c1024] c2052 unsat2052 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1024 := derived1024 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2053 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨33, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2053 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1105, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p2053 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2053 : lratChecker f2053 p2053 = .success := by decide +kernel
theorem unsat2053 : Unsatisfiable (PosFin 57) f2053 := by
  apply lratCheckerSound f2053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2053
  · intro a ha; simp [p2053] at ha; subst a; trivial
  · exact checked2053
theorem derived2053 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2053 := by
  apply localUnsat_implies_entails f2053 [c1946, c1105] c2053 unsat2053 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1105 := derived1105 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2054 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2054 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c616, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p2054 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2054 : lratChecker f2054 p2054 = .success := by decide +kernel
theorem unsat2054 : Unsatisfiable (PosFin 57) f2054 := by
  apply lratCheckerSound f2054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2054
  · intro a ha; simp [p2054] at ha; subst a; trivial
  · exact checked2054
theorem derived2054 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2054 := by
  apply localUnsat_implies_entails f2054 [c1946, c616] c2054 unsat2054 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c616 := derived616 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2055 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨43, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2055 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c886, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2055 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2055 : lratChecker f2055 p2055 = .success := by decide +kernel
theorem unsat2055 : Unsatisfiable (PosFin 57) f2055 := by
  apply lratCheckerSound f2055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2055
  · intro a ha; simp [p2055] at ha; subst a; trivial
  · exact checked2055
theorem derived2055 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2055 := by
  apply localUnsat_implies_entails f2055 [c1946, c886] c2055 unsat2055 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c886 := derived886 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2056 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨9, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2056 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c961, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p2056 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2056 : lratChecker f2056 p2056 = .success := by decide +kernel
theorem unsat2056 : Unsatisfiable (PosFin 57) f2056 := by
  apply lratCheckerSound f2056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2056
  · intro a ha; simp [p2056] at ha; subst a; trivial
  · exact checked2056
theorem derived2056 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2056 := by
  apply localUnsat_implies_entails f2056 [c1946, c961] c2056 unsat2056 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c961 := derived961 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2057 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨51, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2057 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c887, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2057 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2057 : lratChecker f2057 p2057 = .success := by decide +kernel
theorem unsat2057 : Unsatisfiable (PosFin 57) f2057 := by
  apply lratCheckerSound f2057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2057
  · intro a ha; simp [p2057] at ha; subst a; trivial
  · exact checked2057
theorem derived2057 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2057 := by
  apply localUnsat_implies_entails f2057 [c1946, c887] c2057 unsat2057 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c887 := derived887 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2058 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨51, by decide⟩, true), (⟨48, by decide⟩, false), (⟨31, by decide⟩, false), (⟨43, by decide⟩, true), (⟨40, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2058 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c928, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2058 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2058 : lratChecker f2058 p2058 = .success := by decide +kernel
theorem unsat2058 : Unsatisfiable (PosFin 57) f2058 := by
  apply lratCheckerSound f2058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2058
  · intro a ha; simp [p2058] at ha; subst a; trivial
  · exact checked2058
theorem derived2058 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2058 := by
  apply localUnsat_implies_entails f2058 [c1946, c928] c2058 unsat2058 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c928 := derived928 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2059 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2059 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c43, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2059 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2059 : lratChecker f2059 p2059 = .success := by decide +kernel
theorem unsat2059 : Unsatisfiable (PosFin 57) f2059 := by
  apply lratCheckerSound f2059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2059
  · intro a ha; simp [p2059] at ha; subst a; trivial
  · exact checked2059
theorem derived2059 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2059 := by
  apply localUnsat_implies_entails f2059 [c1946, c43] c2059 unsat2059 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2060 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2060 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c865, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2060 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2060 : lratChecker f2060 p2060 = .success := by decide +kernel
theorem unsat2060 : Unsatisfiable (PosFin 57) f2060 := by
  apply lratCheckerSound f2060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2060
  · intro a ha; simp [p2060] at ha; subst a; trivial
  · exact checked2060
theorem derived2060 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2060 := by
  apply localUnsat_implies_entails f2060 [c1946, c865] c2060 unsat2060 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c865 := derived865 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2061 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2061 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c41, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2061 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2061 : lratChecker f2061 p2061 = .success := by decide +kernel
theorem unsat2061 : Unsatisfiable (PosFin 57) f2061 := by
  apply lratCheckerSound f2061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2061
  · intro a ha; simp [p2061] at ha; subst a; trivial
  · exact checked2061
theorem derived2061 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2061 := by
  apply localUnsat_implies_entails f2061 [c1946, c41] c2061 unsat2061 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2062 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2062 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c557, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2062 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2062 : lratChecker f2062 p2062 = .success := by decide +kernel
theorem unsat2062 : Unsatisfiable (PosFin 57) f2062 := by
  apply lratCheckerSound f2062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2062
  · intro a ha; simp [p2062] at ha; subst a; trivial
  · exact checked2062
theorem derived2062 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2062 := by
  apply localUnsat_implies_entails f2062 [c1946, c557] c2062 unsat2062 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c557 := derived557 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2063 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨49, by decide⟩, true), (⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2063 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c553, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p2063 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2063 : lratChecker f2063 p2063 = .success := by decide +kernel
theorem unsat2063 : Unsatisfiable (PosFin 57) f2063 := by
  apply lratCheckerSound f2063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2063
  · intro a ha; simp [p2063] at ha; subst a; trivial
  · exact checked2063
theorem derived2063 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2063 := by
  apply localUnsat_implies_entails f2063 [c1946, c553] c2063 unsat2063 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c553 := derived553 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2064 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨4, by decide⟩, true), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2064 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c951, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p2064 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2064 : lratChecker f2064 p2064 = .success := by decide +kernel
theorem unsat2064 : Unsatisfiable (PosFin 57) f2064 := by
  apply lratCheckerSound f2064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2064
  · intro a ha; simp [p2064] at ha; subst a; trivial
  · exact checked2064
theorem derived2064 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2064 := by
  apply localUnsat_implies_entails f2064 [c1946, c951] c2064 unsat2064 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c951 := derived951 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2065 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨45, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2065 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1020, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p2065 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2065 : lratChecker f2065 p2065 = .success := by decide +kernel
theorem unsat2065 : Unsatisfiable (PosFin 57) f2065 := by
  apply lratCheckerSound f2065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2065
  · intro a ha; simp [p2065] at ha; subst a; trivial
  · exact checked2065
theorem derived2065 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2065 := by
  apply localUnsat_implies_entails f2065 [c1946, c1020] c2065 unsat2065 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1020 := derived1020 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2066 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2066 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c85, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2066 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2066 : lratChecker f2066 p2066 = .success := by decide +kernel
theorem unsat2066 : Unsatisfiable (PosFin 57) f2066 := by
  apply lratCheckerSound f2066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2066
  · intro a ha; simp [p2066] at ha; subst a; trivial
  · exact checked2066
theorem derived2066 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2066 := by
  apply localUnsat_implies_entails f2066 [c1946, c85] c2066 unsat2066 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2067 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨30, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2067 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c621, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2067 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2067 : lratChecker f2067 p2067 = .success := by decide +kernel
theorem unsat2067 : Unsatisfiable (PosFin 57) f2067 := by
  apply lratCheckerSound f2067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2067
  · intro a ha; simp [p2067] at ha; subst a; trivial
  · exact checked2067
theorem derived2067 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2067 := by
  apply localUnsat_implies_entails f2067 [c1946, c621] c2067 unsat2067 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c621 := derived621 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2068 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨42, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2068 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c73, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2068 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2068 : lratChecker f2068 p2068 = .success := by decide +kernel
theorem unsat2068 : Unsatisfiable (PosFin 57) f2068 := by
  apply lratCheckerSound f2068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2068
  · intro a ha; simp [p2068] at ha; subst a; trivial
  · exact checked2068
theorem derived2068 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2068 := by
  apply localUnsat_implies_entails f2068 [c1946, c73] c2068 unsat2068 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2069 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2069 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1164, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2069 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2069 : lratChecker f2069 p2069 = .success := by decide +kernel
theorem unsat2069 : Unsatisfiable (PosFin 57) f2069 := by
  apply lratCheckerSound f2069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2069
  · intro a ha; simp [p2069] at ha; subst a; trivial
  · exact checked2069
theorem derived2069 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2069 := by
  apply localUnsat_implies_entails f2069 [c1946, c1164] c2069 unsat2069 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1164 := derived1164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2070 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2070 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1171, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2070 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2070 : lratChecker f2070 p2070 = .success := by decide +kernel
theorem unsat2070 : Unsatisfiable (PosFin 57) f2070 := by
  apply lratCheckerSound f2070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2070
  · intro a ha; simp [p2070] at ha; subst a; trivial
  · exact checked2070
theorem derived2070 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2070 := by
  apply localUnsat_implies_entails f2070 [c1946, c1171] c2070 unsat2070 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1171 := derived1171 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2071 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2071 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1181, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p2071 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2071 : lratChecker f2071 p2071 = .success := by decide +kernel
theorem unsat2071 : Unsatisfiable (PosFin 57) f2071 := by
  apply lratCheckerSound f2071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2071
  · intro a ha; simp [p2071] at ha; subst a; trivial
  · exact checked2071
theorem derived2071 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2071 := by
  apply localUnsat_implies_entails f2071 [c1946, c1181] c2071 unsat2071 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1181 := derived1181 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2072 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨46, by decide⟩, false), (⟨48, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2072 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1203, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p2072 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2072 : lratChecker f2072 p2072 = .success := by decide +kernel
theorem unsat2072 : Unsatisfiable (PosFin 57) f2072 := by
  apply lratCheckerSound f2072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2072
  · intro a ha; simp [p2072] at ha; subst a; trivial
  · exact checked2072
theorem derived2072 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2072 := by
  apply localUnsat_implies_entails f2072 [c1946, c1203] c2072 unsat2072 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2073 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨41, by decide⟩, false), (⟨46, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2073 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1204, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p2073 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2073 : lratChecker f2073 p2073 = .success := by decide +kernel
theorem unsat2073 : Unsatisfiable (PosFin 57) f2073 := by
  apply lratCheckerSound f2073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2073
  · intro a ha; simp [p2073] at ha; subst a; trivial
  · exact checked2073
theorem derived2073 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2073 := by
  apply localUnsat_implies_entails f2073 [c1946, c1204] c2073 unsat2073 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1204 := derived1204 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2074 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨56, by decide⟩, false), (⟨54, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2074 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1216, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2074 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2074 : lratChecker f2074 p2074 = .success := by decide +kernel
theorem unsat2074 : Unsatisfiable (PosFin 57) f2074 := by
  apply lratCheckerSound f2074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2074
  · intro a ha; simp [p2074] at ha; subst a; trivial
  · exact checked2074
theorem derived2074 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2074 := by
  apply localUnsat_implies_entails f2074 [c1946, c1216] c2074 unsat2074 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2075 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2075 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c2066, some c172, some c2052, some c137, some c2026, some c35, some c331, some c299, some c39, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2075 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2075 : lratChecker f2075 p2075 = .success := by decide +kernel
theorem unsat2075 : Unsatisfiable (PosFin 57) f2075 := by
  apply lratCheckerSound f2075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2075
  · intro a ha; simp [p2075] at ha; subst a; trivial
  · exact checked2075
theorem derived2075 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2075 := by
  apply localUnsat_implies_entails f2075 [c380, c2066, c172, c2052, c137, c2026, c35, c331, c299, c39] c2075 unsat2075 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c2066 := derived2066 a h
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c2052 := derived2052 a h
  have h4 : Entails.eval a c137 := h 136 (by decide)
  have h5 : Entails.eval a c2026 := derived2026 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2076 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2076 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c299, some c45, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2076 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2076 : lratChecker f2076 p2076 = .success := by decide +kernel
theorem unsat2076 : Unsatisfiable (PosFin 57) f2076 := by
  apply lratCheckerSound f2076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2076
  · intro a ha; simp [p2076] at ha; subst a; trivial
  · exact checked2076
theorem derived2076 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2076 := by
  apply localUnsat_implies_entails f2076 [c293, c299, c45] c2076 unsat2076 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2077 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2077 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2075, some c2076, some c35, some c339, some c333, some c57, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p2077 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2077 : lratChecker f2077 p2077 = .success := by decide +kernel
theorem unsat2077 : Unsatisfiable (PosFin 57) f2077 := by
  apply lratCheckerSound f2077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2077
  · intro a ha; simp [p2077] at ha; subst a; trivial
  · exact checked2077
theorem derived2077 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2077 := by
  apply localUnsat_implies_entails f2077 [c2075, c2076, c35, c339, c333, c57] c2077 unsat2077 (by rfl) a
  have h0 : Entails.eval a c2075 := derived2075 a h
  have h1 : Entails.eval a c2076 := derived2076 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c333 := h 332 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2078 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2078 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c77, some c71, some c841, some c2017, some c156, some c72, some c369, some c368, some c84, some c1960, some c67, some c1241, some c162, some c188, some c2077, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2078 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2078 : lratChecker f2078 p2078 = .success := by decide +kernel
theorem unsat2078 : Unsatisfiable (PosFin 57) f2078 := by
  apply lratCheckerSound f2078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2078
  · intro a ha; simp [p2078] at ha; subst a; trivial
  · exact checked2078
theorem derived2078 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2078 := by
  apply localUnsat_implies_entails f2078 [c77, c71, c841, c2017, c156, c72, c369, c368, c84, c1960, c67, c1241, c162, c188, c2077] c2078 unsat2078 (by rfl) a
  have h0 : Entails.eval a c77 := h 76 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c2017 := derived2017 a h
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c1960 := derived1960 a h
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c1241 := derived1241 a h
  have h12 : Entails.eval a c162 := h 161 (by decide)
  have h13 : Entails.eval a c188 := h 187 (by decide)
  have h14 : Entails.eval a c2077 := derived2077 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2079 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2079 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c1972, some c2066, some c39, some c331, some c339, some c2026, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2079 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2079 : lratChecker f2079 p2079 = .success := by decide +kernel
theorem unsat2079 : Unsatisfiable (PosFin 57) f2079 := by
  apply lratCheckerSound f2079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2079
  · intro a ha; simp [p2079] at ha; subst a; trivial
  · exact checked2079
theorem derived2079 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2079 := by
  apply localUnsat_implies_entails f2079 [c376, c1972, c2066, c39, c331, c339, c2026] c2079 unsat2079 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c1972 := derived1972 a h
  have h2 : Entails.eval a c2066 := derived2066 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c331 := h 330 (by decide)
  have h5 : Entails.eval a c339 := h 338 (by decide)
  have h6 : Entails.eval a c2026 := derived2026 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2080 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2080 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c77, some c2017, some c71, some c841, some c2078, some c361, some c1983, some c2079, some c2036, some c1025, some c84, some c1765, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2080 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2080 : lratChecker f2080 p2080 = .success := by decide +kernel
theorem unsat2080 : Unsatisfiable (PosFin 57) f2080 := by
  apply lratCheckerSound f2080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2080
  · intro a ha; simp [p2080] at ha; subst a; trivial
  · exact checked2080
theorem derived2080 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2080 := by
  apply localUnsat_implies_entails f2080 [c77, c2017, c71, c841, c2078, c361, c1983, c2079, c2036, c1025, c84, c1765] c2080 unsat2080 (by rfl) a
  have h0 : Entails.eval a c77 := h 76 (by decide)
  have h1 : Entails.eval a c2017 := derived2017 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c2078 := derived2078 a h
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c1983 := derived1983 a h
  have h7 : Entails.eval a c2079 := derived2079 a h
  have h8 : Entails.eval a c2036 := derived2036 a h
  have h9 : Entails.eval a c1025 := derived1025 a h
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c1765 := derived1765 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2080

end CochromaticTwenty.Certificates.B16_8_2
