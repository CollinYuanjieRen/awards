import MerLeanExperiment.Certificates.B16_2_2.Steps1500_1599

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1984 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1984 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1967, some c189, some c1983, some c188, some c1231, some c1982, some c1975, some c1921, some c8, some c183, some c1224, some c1531, some c245, some c1852, some c96, some c25, some c250, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1984 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1984 : lratChecker f1984 p1984 = .success := by decide +kernel
theorem unsat1984 : Unsatisfiable (PosFin 57) f1984 := by
  apply lratCheckerSound f1984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1984
  · intro a ha; simp [p1984] at ha; subst a; trivial
  · exact checked1984
theorem derived1984 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1984 := by
  apply localUnsat_implies_entails f1984 [c1668, c1817, c1967, c189, c1983, c188, c1231, c1982, c1975, c1921, c8, c183, c1224, c1531, c245, c1852, c96, c25, c250] c1984 unsat1984 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c1983 := derived1983 a h
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c1231 := derived1231 a h
  have h7 : Entails.eval a c1982 := derived1982 a h
  have h8 : Entails.eval a c1975 := derived1975 a h
  have h9 : Entails.eval a c1921 := derived1921 a h
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c1224 := derived1224 a h
  have h13 : Entails.eval a c1531 := derived1531 a h
  have h14 : Entails.eval a c245 := h 244 (by decide)
  have h15 : Entails.eval a c1852 := derived1852 a h
  have h16 : Entails.eval a c96 := h 95 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1985 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1985 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1967, some c1975, some c189, some c1921, some c1980, some c1982, some c260, some c1983, some c188, some c1231, some c1984, some c1692, some c120, some c237, some c1943, some c1569, some c362, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1985 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1985 : lratChecker f1985 p1985 = .success := by decide +kernel
theorem unsat1985 : Unsatisfiable (PosFin 57) f1985 := by
  apply lratCheckerSound f1985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1985
  · intro a ha; simp [p1985] at ha; subst a; trivial
  · exact checked1985
theorem derived1985 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1985 := by
  apply localUnsat_implies_entails f1985 [c1668, c1967, c1975, c189, c1921, c1980, c1982, c260, c1983, c188, c1231, c1984, c1692, c120, c237, c1943, c1569, c362] c1985 unsat1985 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1967 := derived1967 a h
  have h2 : Entails.eval a c1975 := derived1975 a h
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c1980 := derived1980 a h
  have h6 : Entails.eval a c1982 := derived1982 a h
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c1983 := derived1983 a h
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c1231 := derived1231 a h
  have h11 : Entails.eval a c1984 := derived1984 a h
  have h12 : Entails.eval a c1692 := derived1692 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c237 := h 236 (by decide)
  have h15 : Entails.eval a c1943 := derived1943 a h
  have h16 : Entails.eval a c1569 := derived1569 a h
  have h17 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1986 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1986 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c94, some c75, some c447, some c1768, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1986 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1986 : lratChecker f1986 p1986 = .success := by decide +kernel
theorem unsat1986 : Unsatisfiable (PosFin 57) f1986 := by
  apply lratCheckerSound f1986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1986
  · intro a ha; simp [p1986] at ha; subst a; trivial
  · exact checked1986
theorem derived1986 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1986 := by
  apply localUnsat_implies_entails f1986 [c1668, c1921, c94, c75, c447, c1768] c1986 unsat1986 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c447 := derived447 a h
  have h5 : Entails.eval a c1768 := derived1768 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1987 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1987 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1967, some c1975, some c189, some c1921, some c1985, some c1516, some c184, some c246, some c248, some c1231, some c188, some c1531, some c1955, some c1769, some c1986, some c1527, some c31, some c24, some c114, some c1612, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1987 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1987 : lratChecker f1987 p1987 = .success := by decide +kernel
theorem unsat1987 : Unsatisfiable (PosFin 57) f1987 := by
  apply lratCheckerSound f1987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1987
  · intro a ha; simp [p1987] at ha; subst a; trivial
  · exact checked1987
theorem derived1987 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1987 := by
  apply localUnsat_implies_entails f1987 [c1817, c1668, c1967, c1975, c189, c1921, c1985, c1516, c184, c246, c248, c1231, c188, c1531, c1955, c1769, c1986, c1527, c31, c24, c114, c1612] c1987 unsat1987 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c1975 := derived1975 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c1921 := derived1921 a h
  have h6 : Entails.eval a c1985 := derived1985 a h
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c1231 := derived1231 a h
  have h12 : Entails.eval a c188 := h 187 (by decide)
  have h13 : Entails.eval a c1531 := derived1531 a h
  have h14 : Entails.eval a c1955 := derived1955 a h
  have h15 : Entails.eval a c1769 := derived1769 a h
  have h16 : Entails.eval a c1986 := derived1986 a h
  have h17 : Entails.eval a c1527 := derived1527 a h
  have h18 : Entails.eval a c31 := h 30 (by decide)
  have h19 : Entails.eval a c24 := h 23 (by decide)
  have h20 : Entails.eval a c114 := h 113 (by decide)
  have h21 : Entails.eval a c1612 := derived1612 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1988 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1988 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1231, some c1921, some c1967, some c189, some c1985, some c1516, some c184, some c1531, some c1975, some c248, some c246, some c1987, some c122, some c25, some c170, some c161, some c361, some c81, some c1711, some c372, some c237, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1988 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1988 : lratChecker f1988 p1988 = .success := by decide +kernel
theorem unsat1988 : Unsatisfiable (PosFin 57) f1988 := by
  apply lratCheckerSound f1988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1988
  · intro a ha; simp [p1988] at ha; subst a; trivial
  · exact checked1988
theorem derived1988 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1988 := by
  apply localUnsat_implies_entails f1988 [c1668, c1231, c1921, c1967, c189, c1985, c1516, c184, c1531, c1975, c248, c246, c1987, c122, c25, c170, c161, c361, c81, c1711, c372, c237] c1988 unsat1988 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c1985 := derived1985 a h
  have h6 : Entails.eval a c1516 := derived1516 a h
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c1531 := derived1531 a h
  have h9 : Entails.eval a c1975 := derived1975 a h
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c246 := h 245 (by decide)
  have h12 : Entails.eval a c1987 := derived1987 a h
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c170 := h 169 (by decide)
  have h16 : Entails.eval a c161 := h 160 (by decide)
  have h17 : Entails.eval a c361 := h 360 (by decide)
  have h18 : Entails.eval a c81 := h 80 (by decide)
  have h19 : Entails.eval a c1711 := derived1711 a h
  have h20 : Entails.eval a c372 := h 371 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1989 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1989 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1985, some c1967, some c1975, some c189, some c1231, some c188, some c1988, some c74, some c2, some c1877, some c117, some c1755, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1989 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1989 : lratChecker f1989 p1989 = .success := by decide +kernel
theorem unsat1989 : Unsatisfiable (PosFin 57) f1989 := by
  apply lratCheckerSound f1989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1989
  · intro a ha; simp [p1989] at ha; subst a; trivial
  · exact checked1989
theorem derived1989 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1989 := by
  apply localUnsat_implies_entails f1989 [c1668, c1985, c1967, c1975, c189, c1231, c188, c1988, c74, c2, c1877, c117, c1755] c1989 unsat1989 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1985 := derived1985 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c1975 := derived1975 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c1988 := derived1988 a h
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c1877 := derived1877 a h
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c1755 := derived1755 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1990 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1990 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c30, some c1920, some c113, some c25, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1990 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1990 : lratChecker f1990 p1990 = .success := by decide +kernel
theorem unsat1990 : Unsatisfiable (PosFin 57) f1990 := by
  apply lratCheckerSound f1990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1990
  · intro a ha; simp [p1990] at ha; subst a; trivial
  · exact checked1990
theorem derived1990 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1990 := by
  apply localUnsat_implies_entails f1990 [c1668, c30, c1920, c113, c25] c1990 unsat1990 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c1920 := derived1920 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1991 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1991 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c1733, some c31, some c161, some c113, some c25, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1991 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1991 : lratChecker f1991 p1991 = .success := by decide +kernel
theorem unsat1991 : Unsatisfiable (PosFin 57) f1991 := by
  apply lratCheckerSound f1991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1991
  · intro a ha; simp [p1991] at ha; subst a; trivial
  · exact checked1991
theorem derived1991 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1991 := by
  apply localUnsat_implies_entails f1991 [c1668, c1921, c1733, c31, c161, c113, c25] c1991 unsat1991 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c1733 := derived1733 a h
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1992 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1992 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c189, some c1990, some c1527, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1992 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1992 : lratChecker f1992 p1992 = .success := by decide +kernel
theorem unsat1992 : Unsatisfiable (PosFin 57) f1992 := by
  apply lratCheckerSound f1992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1992
  · intro a ha; simp [p1992] at ha; subst a; trivial
  · exact checked1992
theorem derived1992 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1992 := by
  apply localUnsat_implies_entails f1992 [c1817, c189, c1990, c1527] c1992 unsat1992 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c1990 := derived1990 a h
  have h3 : Entails.eval a c1527 := derived1527 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1993 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1993 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1921, some c1531, some c1516, some c1975, some c380, some c246, some c1991, some c1992, some c122, some c25, some c170, some c361, some c362, some c1711, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1993 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1993 : lratChecker f1993 p1993 = .success := by decide +kernel
theorem unsat1993 : Unsatisfiable (PosFin 57) f1993 := by
  apply lratCheckerSound f1993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1993
  · intro a ha; simp [p1993] at ha; subst a; trivial
  · exact checked1993
theorem derived1993 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1993 := by
  apply localUnsat_implies_entails f1993 [c1921, c1531, c1516, c1975, c380, c246, c1991, c1992, c122, c25, c170, c361, c362, c1711] c1993 unsat1993 (by rfl) a
  have h0 : Entails.eval a c1921 := derived1921 a h
  have h1 : Entails.eval a c1531 := derived1531 a h
  have h2 : Entails.eval a c1516 := derived1516 a h
  have h3 : Entails.eval a c1975 := derived1975 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c246 := h 245 (by decide)
  have h6 : Entails.eval a c1991 := derived1991 a h
  have h7 : Entails.eval a c1992 := derived1992 a h
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c362 := h 361 (by decide)
  have h13 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1994 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1994 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1967, some c1921, some c189, some c1975, some c1985, some c1516, some c184, some c1531, some c1989, some c1993, some c74, some c2, some c93, some c1877, some c117, some c362, some c1992, some c1755, some c1711, some c188, some c234, some c1793, some c253, some c31, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1994 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1994 : lratChecker f1994 p1994 = .success := by decide +kernel
theorem unsat1994 : Unsatisfiable (PosFin 57) f1994 := by
  apply lratCheckerSound f1994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1994
  · intro a ha; simp [p1994] at ha; subst a; trivial
  · exact checked1994
theorem derived1994 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1994 := by
  apply localUnsat_implies_entails f1994 [c1668, c1967, c1921, c189, c1975, c1985, c1516, c184, c1531, c1989, c1993, c74, c2, c93, c1877, c117, c362, c1992, c1755, c1711, c188, c234, c1793, c253, c31] c1994 unsat1994 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1967 := derived1967 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c1975 := derived1975 a h
  have h5 : Entails.eval a c1985 := derived1985 a h
  have h6 : Entails.eval a c1516 := derived1516 a h
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c1531 := derived1531 a h
  have h9 : Entails.eval a c1989 := derived1989 a h
  have h10 : Entails.eval a c1993 := derived1993 a h
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c1877 := derived1877 a h
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c362 := h 361 (by decide)
  have h17 : Entails.eval a c1992 := derived1992 a h
  have h18 : Entails.eval a c1755 := derived1755 a h
  have h19 : Entails.eval a c1711 := derived1711 a h
  have h20 : Entails.eval a c188 := h 187 (by decide)
  have h21 : Entails.eval a c234 := h 233 (by decide)
  have h22 : Entails.eval a c1793 := derived1793 a h
  have h23 : Entails.eval a c253 := h 252 (by decide)
  have h24 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1995 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1995 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1994, some c10, some c1, some c1967, some c1921, some c248, some c1955, some c1763, some c174, some c67, some c77, some c25, some c126, some c241, some c203, some c21, some c51, some c279, some c138, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1995 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1995 : lratChecker f1995 p1995 = .success := by decide +kernel
theorem unsat1995 : Unsatisfiable (PosFin 57) f1995 := by
  apply lratCheckerSound f1995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1995
  · intro a ha; simp [p1995] at ha; subst a; trivial
  · exact checked1995
theorem derived1995 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1995 := by
  apply localUnsat_implies_entails f1995 [c1668, c1817, c1994, c10, c1, c1967, c1921, c248, c1955, c1763, c174, c67, c77, c25, c126, c241, c203, c21, c51, c279, c138] c1995 unsat1995 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1994 := derived1994 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1967 := derived1967 a h
  have h6 : Entails.eval a c1921 := derived1921 a h
  have h7 : Entails.eval a c248 := h 247 (by decide)
  have h8 : Entails.eval a c1955 := derived1955 a h
  have h9 : Entails.eval a c1763 := derived1763 a h
  have h10 : Entails.eval a c174 := h 173 (by decide)
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c77 := h 76 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c241 := h 240 (by decide)
  have h16 : Entails.eval a c203 := h 202 (by decide)
  have h17 : Entails.eval a c21 := h 20 (by decide)
  have h18 : Entails.eval a c51 := h 50 (by decide)
  have h19 : Entails.eval a c279 := h 278 (by decide)
  have h20 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1996 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨42, by decide⟩, false), (⟨18, by decide⟩, false), (⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1996 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c10, some c1, some c194, some c193, some c167, some c119, some c1755, some c1931, some c11, some c367, some c67, some c320, some c1636, some c387, some c244, some c143, some c1227, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1996 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1996 : lratChecker f1996 p1996 = .success := by decide +kernel
theorem unsat1996 : Unsatisfiable (PosFin 57) f1996 := by
  apply lratCheckerSound f1996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1996
  · intro a ha; simp [p1996] at ha; subst a; trivial
  · exact checked1996
theorem derived1996 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1996 := by
  apply localUnsat_implies_entails f1996 [c1668, c1817, c10, c1, c194, c193, c167, c119, c1755, c1931, c11, c367, c67, c320, c1636, c387, c244, c143, c1227] c1996 unsat1996 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c167 := h 166 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c1755 := derived1755 a h
  have h9 : Entails.eval a c1931 := derived1931 a h
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c320 := h 319 (by decide)
  have h14 : Entails.eval a c1636 := derived1636 a h
  have h15 : Entails.eval a c387 := derived387 a h
  have h16 : Entails.eval a c244 := h 243 (by decide)
  have h17 : Entails.eval a c143 := h 142 (by decide)
  have h18 : Entails.eval a c1227 := derived1227 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1997 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨14, by decide⟩, true), (⟨42, by decide⟩, false), (⟨18, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1997 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c118, some c166, some c1978, some c76, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1997 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1997 : lratChecker f1997 p1997 = .success := by decide +kernel
theorem unsat1997 : Unsatisfiable (PosFin 57) f1997 := by
  apply lratCheckerSound f1997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1997
  · intro a ha; simp [p1997] at ha; subst a; trivial
  · exact checked1997
theorem derived1997 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1997 := by
  apply localUnsat_implies_entails f1997 [c1254, c118, c166, c1978, c76] c1997 unsat1997 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c1978 := derived1978 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1998 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1998 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c1994, some c9, some c10, some c1932, some c1531, some c1231, some c1254, some c1995, some c74, some c1996, some c1997, some c11, some c1773, some c132, some c65, some c69, some c154, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1998 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1998 : lratChecker f1998 p1998 = .success := by decide +kernel
theorem unsat1998 : Unsatisfiable (PosFin 57) f1998 := by
  apply lratCheckerSound f1998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1998
  · intro a ha; simp [p1998] at ha; subst a; trivial
  · exact checked1998
theorem derived1998 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1998 := by
  apply localUnsat_implies_entails f1998 [c1668, c1921, c1994, c9, c10, c1932, c1531, c1231, c1254, c1995, c74, c1996, c1997, c11, c1773, c132, c65, c69, c154] c1998 unsat1998 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c1994 := derived1994 a h
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c1932 := derived1932 a h
  have h6 : Entails.eval a c1531 := derived1531 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c1254 := derived1254 a h
  have h9 : Entails.eval a c1995 := derived1995 a h
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c1996 := derived1996 a h
  have h12 : Entails.eval a c1997 := derived1997 a h
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c1773 := derived1773 a h
  have h15 : Entails.eval a c132 := h 131 (by decide)
  have h16 : Entails.eval a c65 := h 64 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1999 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1999 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1994, some c10, some c9, some c1, some c1967, some c1921, some c1231, some c1932, some c1531, some c1998, some c22, some c1762, some c77, some c174, some c646, some c363, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1999 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1999 : lratChecker f1999 p1999 = .success := by decide +kernel
theorem unsat1999 : Unsatisfiable (PosFin 57) f1999 := by
  apply lratCheckerSound f1999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1999
  · intro a ha; simp [p1999] at ha; subst a; trivial
  · exact checked1999
theorem derived1999 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1999 := by
  apply localUnsat_implies_entails f1999 [c1668, c1994, c10, c9, c1, c1967, c1921, c1231, c1932, c1531, c1998, c22, c1762, c77, c174, c646, c363] c1999 unsat1999 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1994 := derived1994 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1967 := derived1967 a h
  have h6 : Entails.eval a c1921 := derived1921 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c1932 := derived1932 a h
  have h9 : Entails.eval a c1531 := derived1531 a h
  have h10 : Entails.eval a c1998 := derived1998 a h
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c1762 := derived1762 a h
  have h13 : Entails.eval a c77 := h 76 (by decide)
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c646 := derived646 a h
  have h16 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2000 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2000 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c193, some c185, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p2000 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2000 : lratChecker f2000 p2000 = .success := by decide +kernel
theorem unsat2000 : Unsatisfiable (PosFin 57) f2000 := by
  apply lratCheckerSound f2000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2000
  · intro a ha; simp [p2000] at ha; subst a; trivial
  · exact checked2000
theorem derived2000 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2000 := by
  apply localUnsat_implies_entails f2000 [c194, c193, c185] c2000 unsat2000 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2001 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨14, by decide⟩, true), (⟨52, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2001 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1994, some c10, some c9, some c1254, some c1967, some c1921, some c118, some c1997, some c1978, some c84, some c652, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2001 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2001 : lratChecker f2001 p2001 = .success := by decide +kernel
theorem unsat2001 : Unsatisfiable (PosFin 57) f2001 := by
  apply lratCheckerSound f2001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2001
  · intro a ha; simp [p2001] at ha; subst a; trivial
  · exact checked2001
theorem derived2001 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2001 := by
  apply localUnsat_implies_entails f2001 [c1668, c1994, c10, c9, c1254, c1967, c1921, c118, c1997, c1978, c84, c652] c2001 unsat2001 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1994 := derived1994 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c1967 := derived1967 a h
  have h6 : Entails.eval a c1921 := derived1921 a h
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c1997 := derived1997 a h
  have h9 : Entails.eval a c1978 := derived1978 a h
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c652 := derived652 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2002 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2002 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1994, some c10, some c9, some c1254, some c2000, some c2001, some c11, some c1773, some c132, some c65, some c69, some c154, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2002 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2002 : lratChecker f2002 p2002 = .success := by decide +kernel
theorem unsat2002 : Unsatisfiable (PosFin 57) f2002 := by
  apply lratCheckerSound f2002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2002
  · intro a ha; simp [p2002] at ha; subst a; trivial
  · exact checked2002
theorem derived2002 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2002 := by
  apply localUnsat_implies_entails f2002 [c1668, c1994, c10, c9, c1254, c2000, c2001, c11, c1773, c132, c65, c69, c154] c2002 unsat2002 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1994 := derived1994 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c2000 := derived2000 a h
  have h6 : Entails.eval a c2001 := derived2001 a h
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c1773 := derived1773 a h
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2003 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨56, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2003 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1994, some c10, some c9, some c1254, some c1, some c1921, some c2002, some c1531, some c1776, some c183, some c74, some c194, some c168, some c182, some c1123, some c1761, some c11, some c1773, some c65, some c132, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2003 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2003 : lratChecker f2003 p2003 = .success := by decide +kernel
theorem unsat2003 : Unsatisfiable (PosFin 57) f2003 := by
  apply lratCheckerSound f2003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2003
  · intro a ha; simp [p2003] at ha; subst a; trivial
  · exact checked2003
theorem derived2003 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2003 := by
  apply localUnsat_implies_entails f2003 [c1668, c1994, c10, c9, c1254, c1, c1921, c2002, c1531, c1776, c183, c74, c194, c168, c182, c1123, c1761, c11, c1773, c65, c132] c2003 unsat2003 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1994 := derived1994 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1921 := derived1921 a h
  have h7 : Entails.eval a c2002 := derived2002 a h
  have h8 : Entails.eval a c1531 := derived1531 a h
  have h9 : Entails.eval a c1776 := derived1776 a h
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c194 := h 193 (by decide)
  have h13 : Entails.eval a c168 := h 167 (by decide)
  have h14 : Entails.eval a c182 := h 181 (by decide)
  have h15 : Entails.eval a c1123 := derived1123 a h
  have h16 : Entails.eval a c1761 := derived1761 a h
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c1773 := derived1773 a h
  have h19 : Entails.eval a c65 := h 64 (by decide)
  have h20 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2004 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2004 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1994, some c9, some c1, some c1967, some c1921, some c1999, some c2003, some c22, some c29, some c1762, some c77, some c96, some c174, some c1776, some c363, some c646, some c1612, some c242, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2004 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2004 : lratChecker f2004 p2004 = .success := by decide +kernel
theorem unsat2004 : Unsatisfiable (PosFin 57) f2004 := by
  apply lratCheckerSound f2004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2004
  · intro a ha; simp [p2004] at ha; subst a; trivial
  · exact checked2004
theorem derived2004 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2004 := by
  apply localUnsat_implies_entails f2004 [c1668, c1994, c9, c1, c1967, c1921, c1999, c2003, c22, c29, c1762, c77, c96, c174, c1776, c363, c646, c1612, c242] c2004 unsat2004 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1994 := derived1994 a h
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c1921 := derived1921 a h
  have h6 : Entails.eval a c1999 := derived1999 a h
  have h7 : Entails.eval a c2003 := derived2003 a h
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c1762 := derived1762 a h
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c174 := h 173 (by decide)
  have h14 : Entails.eval a c1776 := derived1776 a h
  have h15 : Entails.eval a c363 := h 362 (by decide)
  have h16 : Entails.eval a c646 := derived646 a h
  have h17 : Entails.eval a c1612 := derived1612 a h
  have h18 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2005 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2005 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1994, some c10, some c9, some c1921, some c1231, some c1932, some c188, some c1531, some c193, some c184, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2005 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2005 : lratChecker f2005 p2005 = .success := by decide +kernel
theorem unsat2005 : Unsatisfiable (PosFin 57) f2005 := by
  apply lratCheckerSound f2005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2005
  · intro a ha; simp [p2005] at ha; subst a; trivial
  · exact checked2005
theorem derived2005 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2005 := by
  apply localUnsat_implies_entails f2005 [c1668, c1994, c10, c9, c1921, c1231, c1932, c188, c1531, c193, c184] c2005 unsat2005 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1994 := derived1994 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c1932 := derived1932 a h
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c1531 := derived1531 a h
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2006 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2006 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1994, some c10, some c9, some c1, some c1921, some c2004, some c2005, some c2003, some c22, some c1762, some c96, some c103, some c1776, some c1224, some c1941, some c168, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2006 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2006 : lratChecker f2006 p2006 = .success := by decide +kernel
theorem unsat2006 : Unsatisfiable (PosFin 57) f2006 := by
  apply lratCheckerSound f2006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2006
  · intro a ha; simp [p2006] at ha; subst a; trivial
  · exact checked2006
theorem derived2006 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2006 := by
  apply localUnsat_implies_entails f2006 [c1668, c1817, c1994, c10, c9, c1, c1921, c2004, c2005, c2003, c22, c1762, c96, c103, c1776, c1224, c1941, c168] c2006 unsat2006 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1994 := derived1994 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1921 := derived1921 a h
  have h7 : Entails.eval a c2004 := derived2004 a h
  have h8 : Entails.eval a c2005 := derived2005 a h
  have h9 : Entails.eval a c2003 := derived2003 a h
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c1762 := derived1762 a h
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c1776 := derived1776 a h
  have h15 : Entails.eval a c1224 := derived1224 a h
  have h16 : Entails.eval a c1941 := derived1941 a h
  have h17 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2007 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2007 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c2006, some c1994, some c10, some c9, some c1967, some c1921, some c1231, some c1932, some c1531, some c1847, some c1576, some c25, some c174, some c646, some c363, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2007 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2007 : lratChecker f2007 p2007 = .success := by decide +kernel
theorem unsat2007 : Unsatisfiable (PosFin 57) f2007 := by
  apply lratCheckerSound f2007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2007
  · intro a ha; simp [p2007] at ha; subst a; trivial
  · exact checked2007
theorem derived2007 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2007 := by
  apply localUnsat_implies_entails f2007 [c1668, c1817, c2006, c1994, c10, c9, c1967, c1921, c1231, c1932, c1531, c1847, c1576, c25, c174, c646, c363] c2007 unsat2007 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c2006 := derived2006 a h
  have h3 : Entails.eval a c1994 := derived1994 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c1967 := derived1967 a h
  have h7 : Entails.eval a c1921 := derived1921 a h
  have h8 : Entails.eval a c1231 := derived1231 a h
  have h9 : Entails.eval a c1932 := derived1932 a h
  have h10 : Entails.eval a c1531 := derived1531 a h
  have h11 : Entails.eval a c1847 := derived1847 a h
  have h12 : Entails.eval a c1576 := derived1576 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c646 := derived646 a h
  have h16 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2008 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2008 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c2006, some c1994, some c10, some c1, some c1967, some c1921, some c32, some c1762, some c263, some c1245, some c77, some c627, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2008 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2008 : lratChecker f2008 p2008 = .success := by decide +kernel
theorem unsat2008 : Unsatisfiable (PosFin 57) f2008 := by
  apply lratCheckerSound f2008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2008
  · intro a ha; simp [p2008] at ha; subst a; trivial
  · exact checked2008
theorem derived2008 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2008 := by
  apply localUnsat_implies_entails f2008 [c1817, c1668, c2006, c1994, c10, c1, c1967, c1921, c32, c1762, c263, c1245, c77, c627] c2008 unsat2008 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c2006 := derived2006 a h
  have h3 : Entails.eval a c1994 := derived1994 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1967 := derived1967 a h
  have h7 : Entails.eval a c1921 := derived1921 a h
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c1762 := derived1762 a h
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c1245 := derived1245 a h
  have h12 : Entails.eval a c77 := h 76 (by decide)
  have h13 : Entails.eval a c627 := derived627 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2009 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2009 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c2006, some c2008, some c260, some c1994, some c9, some c1921, some c2002, some c1531, some c1776, some c183, some c74, some c120, some c168, some c658, some c237, some c1569, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2009 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2009 : lratChecker f2009 p2009 = .success := by decide +kernel
theorem unsat2009 : Unsatisfiable (PosFin 57) f2009 := by
  apply lratCheckerSound f2009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2009
  · intro a ha; simp [p2009] at ha; subst a; trivial
  · exact checked2009
theorem derived2009 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2009 := by
  apply localUnsat_implies_entails f2009 [c1668, c2006, c2008, c260, c1994, c9, c1921, c2002, c1531, c1776, c183, c74, c120, c168, c658, c237, c1569] c2009 unsat2009 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c2008 := derived2008 a h
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c1994 := derived1994 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c1921 := derived1921 a h
  have h7 : Entails.eval a c2002 := derived2002 a h
  have h8 : Entails.eval a c1531 := derived1531 a h
  have h9 : Entails.eval a c1776 := derived1776 a h
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c120 := h 119 (by decide)
  have h13 : Entails.eval a c168 := h 167 (by decide)
  have h14 : Entails.eval a c658 := derived658 a h
  have h15 : Entails.eval a c237 := h 236 (by decide)
  have h16 : Entails.eval a c1569 := derived1569 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2010 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2010 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2005, some c2007, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2010 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2010 : lratChecker f2010 p2010 = .success := by decide +kernel
theorem unsat2010 : Unsatisfiable (PosFin 57) f2010 := by
  apply lratCheckerSound f2010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2010
  · intro a ha; simp [p2010] at ha; subst a; trivial
  · exact checked2010
theorem derived2010 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2010 := by
  apply localUnsat_implies_entails f2010 [c2005, c2007] c2010 unsat2010 (by rfl) a
  have h0 : Entails.eval a c2005 := derived2005 a h
  have h1 : Entails.eval a c2007 := derived2007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2011 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2011 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2009, some c2010, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2011 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2011 : lratChecker f2011 p2011 = .success := by decide +kernel
theorem unsat2011 : Unsatisfiable (PosFin 57) f2011 := by
  apply lratCheckerSound f2011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2011
  · intro a ha; simp [p2011] at ha; subst a; trivial
  · exact checked2011
theorem derived2011 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2011 := by
  apply localUnsat_implies_entails f2011 [c2009, c2010] c2011 unsat2011 (by rfl) a
  have h0 : Entails.eval a c2009 := derived2009 a h
  have h1 : Entails.eval a c2010 := derived2010 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2012 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2012 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c2011, some c1994, some c9, some c1967, some c1921, some c170, some c165, some c84, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2012 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2012 : lratChecker f2012 p2012 = .success := by decide +kernel
theorem unsat2012 : Unsatisfiable (PosFin 57) f2012 := by
  apply lratCheckerSound f2012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2012
  · intro a ha; simp [p2012] at ha; subst a; trivial
  · exact checked2012
theorem derived2012 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2012 := by
  apply localUnsat_implies_entails f2012 [c1668, c2011, c1994, c9, c1967, c1921, c170, c165, c84] c2012 unsat2012 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c2011 := derived2011 a h
  have h2 : Entails.eval a c1994 := derived1994 a h
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c1921 := derived1921 a h
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2013 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2013 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1921, some c1967, some c1994, some c9, some c2011, some c1516, some c196, some c184, some c11, some c1531, some c2012, some c75, some c1527, some c122, some c117, some c32, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2013 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2013 : lratChecker f2013 p2013 = .success := by decide +kernel
theorem unsat2013 : Unsatisfiable (PosFin 57) f2013 := by
  apply lratCheckerSound f2013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2013
  · intro a ha; simp [p2013] at ha; subst a; trivial
  · exact checked2013
theorem derived2013 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2013 := by
  apply localUnsat_implies_entails f2013 [c1668, c1817, c1921, c1967, c1994, c9, c2011, c1516, c196, c184, c11, c1531, c2012, c75, c1527, c122, c117, c32] c2013 unsat2013 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c1994 := derived1994 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c2011 := derived2011 a h
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c1531 := derived1531 a h
  have h12 : Entails.eval a c2012 := derived2012 a h
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c1527 := derived1527 a h
  have h15 : Entails.eval a c122 := h 121 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2014 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨14, by decide⟩, true), (⟨45, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2014 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c10, some c1978, some c627, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p2014 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2014 : lratChecker f2014 p2014 = .success := by decide +kernel
theorem unsat2014 : Unsatisfiable (PosFin 57) f2014 := by
  apply lratCheckerSound f2014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2014
  · intro a ha; simp [p2014] at ha; subst a; trivial
  · exact checked2014
theorem derived2014 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2014 := by
  apply localUnsat_implies_entails f2014 [c1668, c10, c1978, c627] c2014 unsat2014 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c1978 := derived1978 a h
  have h3 : Entails.eval a c627 := derived627 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2015 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2015 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c10, some c11, some c1773, some c132, some c65, some c69, some c154, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2015 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2015 : lratChecker f2015 p2015 = .success := by decide +kernel
theorem unsat2015 : Unsatisfiable (PosFin 57) f2015 := by
  apply lratCheckerSound f2015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2015
  · intro a ha; simp [p2015] at ha; subst a; trivial
  · exact checked2015
theorem derived2015 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2015 := by
  apply localUnsat_implies_entails f2015 [c1668, c10, c11, c1773, c132, c65, c69, c154] c2015 unsat2015 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c1773 := derived1773 a h
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2016 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2016 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c2013, some c1003, some c1921, some c1, some c9, some c378, some c376, some c1254, some c77, some c96, some c1776, some c2000, some c2014, some c2015, some c118, some c124, some c32, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2016 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2016 : lratChecker f2016 p2016 = .success := by decide +kernel
theorem unsat2016 : Unsatisfiable (PosFin 57) f2016 := by
  apply lratCheckerSound f2016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2016
  · intro a ha; simp [p2016] at ha; subst a; trivial
  · exact checked2016
theorem derived2016 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2016 := by
  apply localUnsat_implies_entails f2016 [c1668, c2013, c1003, c1921, c1, c9, c378, c376, c1254, c77, c96, c1776, c2000, c2014, c2015, c118, c124, c32] c2016 unsat2016 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c2013 := derived2013 a h
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c1921 := derived1921 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c1254 := derived1254 a h
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c1776 := derived1776 a h
  have h12 : Entails.eval a c2000 := derived2000 a h
  have h13 : Entails.eval a c2014 := derived2014 a h
  have h14 : Entails.eval a c2015 := derived2015 a h
  have h15 : Entails.eval a c118 := h 117 (by decide)
  have h16 : Entails.eval a c124 := h 123 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2017 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨24, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨9, by decide⟩, false), (⟨23, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2017 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c614, some c622, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p2017 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2017 : lratChecker f2017 p2017 = .success := by decide +kernel
theorem unsat2017 : Unsatisfiable (PosFin 57) f2017 := by
  apply lratCheckerSound f2017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2017
  · intro a ha; simp [p2017] at ha; subst a; trivial
  · exact checked2017
theorem derived2017 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2017 := by
  apply localUnsat_implies_entails f2017 [c1817, c614, c622] c2017 unsat2017 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c614 := derived614 a h
  have h2 : Entails.eval a c622 := derived622 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2018 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2018 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c2013, some c1003, some c2016, some c1975, some c1921, some c378, some c73, some c515, some c93, some c161, some c705, some c248, some c25, some c604, some c190, some c2017, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2018 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2018 : lratChecker f2018 p2018 = .success := by decide +kernel
theorem unsat2018 : Unsatisfiable (PosFin 57) f2018 := by
  apply lratCheckerSound f2018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2018
  · intro a ha; simp [p2018] at ha; subst a; trivial
  · exact checked2018
theorem derived2018 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2018 := by
  apply localUnsat_implies_entails f2018 [c1668, c1817, c2013, c1003, c2016, c1975, c1921, c378, c73, c515, c93, c161, c705, c248, c25, c604, c190, c2017] c2018 unsat2018 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c2013 := derived2013 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c2016 := derived2016 a h
  have h5 : Entails.eval a c1975 := derived1975 a h
  have h6 : Entails.eval a c1921 := derived1921 a h
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c515 := derived515 a h
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c705 := derived705 a h
  have h13 : Entails.eval a c248 := h 247 (by decide)
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c604 := derived604 a h
  have h16 : Entails.eval a c190 := h 189 (by decide)
  have h17 : Entails.eval a c2017 := derived2017 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2019 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2019 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c2016, some c2013, some c1003, some c1921, some c77, some c25, some c254, some c1039, some c124, some c1203, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2019 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2019 : lratChecker f2019 p2019 = .success := by decide +kernel
theorem unsat2019 : Unsatisfiable (PosFin 57) f2019 := by
  apply lratCheckerSound f2019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2019
  · intro a ha; simp [p2019] at ha; subst a; trivial
  · exact checked2019
theorem derived2019 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2019 := by
  apply localUnsat_implies_entails f2019 [c1668, c1817, c2016, c2013, c1003, c1921, c77, c25, c254, c1039, c124, c1203] c2019 unsat2019 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c2016 := derived2016 a h
  have h3 : Entails.eval a c2013 := derived2013 a h
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c1921 := derived1921 a h
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c1039 := derived1039 a h
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2020 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2020 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c2, some c2013, some c1003, some c2016, some c1975, some c189, some c1872, some c2018, some c183, some c190, some c182, some c247, some c380, some c3, some c2019, some c161, some c172, some c73, some c21, some c364, some c243, some c1711, some c234, some c240, some c375, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2020 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2020 : lratChecker f2020 p2020 = .success := by decide +kernel
theorem unsat2020 : Unsatisfiable (PosFin 57) f2020 := by
  apply lratCheckerSound f2020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2020
  · intro a ha; simp [p2020] at ha; subst a; trivial
  · exact checked2020
theorem derived2020 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2020 := by
  apply localUnsat_implies_entails f2020 [c1668, c2, c2013, c1003, c2016, c1975, c189, c1872, c2018, c183, c190, c182, c247, c380, c3, c2019, c161, c172, c73, c21, c364, c243, c1711, c234, c240, c375] c2020 unsat2020 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c2013 := derived2013 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c2016 := derived2016 a h
  have h5 : Entails.eval a c1975 := derived1975 a h
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c1872 := derived1872 a h
  have h8 : Entails.eval a c2018 := derived2018 a h
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c190 := h 189 (by decide)
  have h11 : Entails.eval a c182 := h 181 (by decide)
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c2019 := derived2019 a h
  have h16 : Entails.eval a c161 := h 160 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  have h18 : Entails.eval a c73 := h 72 (by decide)
  have h19 : Entails.eval a c21 := h 20 (by decide)
  have h20 : Entails.eval a c364 := h 363 (by decide)
  have h21 : Entails.eval a c243 := h 242 (by decide)
  have h22 : Entails.eval a c1711 := derived1711 a h
  have h23 : Entails.eval a c234 := h 233 (by decide)
  have h24 : Entails.eval a c240 := h 239 (by decide)
  have h25 : Entails.eval a c375 := h 374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2021 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2021 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c4, some c1557, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2021 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2021 : lratChecker f2021 p2021 = .success := by decide +kernel
theorem unsat2021 : Unsatisfiable (PosFin 57) f2021 := by
  apply lratCheckerSound f2021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2021
  · intro a ha; simp [p2021] at ha; subst a; trivial
  · exact checked2021
theorem derived2021 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2021 := by
  apply localUnsat_implies_entails f2021 [c1817, c4, c1557] c2021 unsat2021 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c1557 := derived1557 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2022 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2022 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c2018, some c2013, some c1003, some c2016, some c1975, some c189, some c1921, some c2, some c1872, some c3, some c183, some c190, some c182, some c380, some c247, some c2021, some c2019, some c2020, some c161, some c260, some c21, some c1979, some c113, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2022 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2022 : lratChecker f2022 p2022 = .success := by decide +kernel
theorem unsat2022 : Unsatisfiable (PosFin 57) f2022 := by
  apply lratCheckerSound f2022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2022
  · intro a ha; simp [p2022] at ha; subst a; trivial
  · exact checked2022
theorem derived2022 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2022 := by
  apply localUnsat_implies_entails f2022 [c1668, c2018, c2013, c1003, c2016, c1975, c189, c1921, c2, c1872, c3, c183, c190, c182, c380, c247, c2021, c2019, c2020, c161, c260, c21, c1979, c113] c2022 unsat2022 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c2018 := derived2018 a h
  have h2 : Entails.eval a c2013 := derived2013 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c2016 := derived2016 a h
  have h5 : Entails.eval a c1975 := derived1975 a h
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c1921 := derived1921 a h
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c1872 := derived1872 a h
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c182 := h 181 (by decide)
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c247 := h 246 (by decide)
  have h16 : Entails.eval a c2021 := derived2021 a h
  have h17 : Entails.eval a c2019 := derived2019 a h
  have h18 : Entails.eval a c2020 := derived2020 a h
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c260 := h 259 (by decide)
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c1979 := derived1979 a h
  have h23 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2023 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2023 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c2022, some c2018, some c2013, some c1003, some c2016, some c1975, some c1921, some c3, some c1866, some c23, some c30, some c383, some c161, some c515, some c81, some c243, some c1233, some c1158, some c185, some c118, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2023 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2023 : lratChecker f2023 p2023 = .success := by decide +kernel
theorem unsat2023 : Unsatisfiable (PosFin 57) f2023 := by
  apply lratCheckerSound f2023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2023
  · intro a ha; simp [p2023] at ha; subst a; trivial
  · exact checked2023
theorem derived2023 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2023 := by
  apply localUnsat_implies_entails f2023 [c1668, c2022, c2018, c2013, c1003, c2016, c1975, c1921, c3, c1866, c23, c30, c383, c161, c515, c81, c243, c1233, c1158, c185, c118] c2023 unsat2023 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c2022 := derived2022 a h
  have h2 : Entails.eval a c2018 := derived2018 a h
  have h3 : Entails.eval a c2013 := derived2013 a h
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c2016 := derived2016 a h
  have h6 : Entails.eval a c1975 := derived1975 a h
  have h7 : Entails.eval a c1921 := derived1921 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c1866 := derived1866 a h
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c383 := h 382 (by decide)
  have h13 : Entails.eval a c161 := h 160 (by decide)
  have h14 : Entails.eval a c515 := derived515 a h
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c243 := h 242 (by decide)
  have h17 : Entails.eval a c1233 := derived1233 a h
  have h18 : Entails.eval a c1158 := derived1158 a h
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2024 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2024 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2022, some c2018, some c2000, some c1254, some c2013, some c1003, some c2016, some c1975, some c189, some c2021, some c118, some c2019, some c1978, some c652, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2024 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2024 : lratChecker f2024 p2024 = .success := by decide +kernel
theorem unsat2024 : Unsatisfiable (PosFin 57) f2024 := by
  apply lratCheckerSound f2024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2024
  · intro a ha; simp [p2024] at ha; subst a; trivial
  · exact checked2024
theorem derived2024 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2024 := by
  apply localUnsat_implies_entails f2024 [c2022, c2018, c2000, c1254, c2013, c1003, c2016, c1975, c189, c2021, c118, c2019, c1978, c652] c2024 unsat2024 (by rfl) a
  have h0 : Entails.eval a c2022 := derived2022 a h
  have h1 : Entails.eval a c2018 := derived2018 a h
  have h2 : Entails.eval a c2000 := derived2000 a h
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c2013 := derived2013 a h
  have h5 : Entails.eval a c1003 := derived1003 a h
  have h6 : Entails.eval a c2016 := derived2016 a h
  have h7 : Entails.eval a c1975 := derived1975 a h
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c2021 := derived2021 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c2019 := derived2019 a h
  have h12 : Entails.eval a c1978 := derived1978 a h
  have h13 : Entails.eval a c652 := derived652 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2025 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2025 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2013, some c1003, some c2016, some c1975, some c1921, some c2024, some c3, some c2023, some c383, some c245, some c96, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2025 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2025 : lratChecker f2025 p2025 = .success := by decide +kernel
theorem unsat2025 : Unsatisfiable (PosFin 57) f2025 := by
  apply lratCheckerSound f2025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2025
  · intro a ha; simp [p2025] at ha; subst a; trivial
  · exact checked2025
theorem derived2025 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2025 := by
  apply localUnsat_implies_entails f2025 [c2013, c1003, c2016, c1975, c1921, c2024, c3, c2023, c383, c245, c96] c2025 unsat2025 (by rfl) a
  have h0 : Entails.eval a c2013 := derived2013 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c2016 := derived2016 a h
  have h3 : Entails.eval a c1975 := derived1975 a h
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c2024 := derived2024 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c2023 := derived2023 a h
  have h8 : Entails.eval a c383 := h 382 (by decide)
  have h9 : Entails.eval a c245 := h 244 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2026 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2026 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c2013, some c1921, some c96, some c93, some c376, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2026 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2026 : lratChecker f2026 p2026 = .success := by decide +kernel
theorem unsat2026 : Unsatisfiable (PosFin 57) f2026 := by
  apply lratCheckerSound f2026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2026
  · intro a ha; simp [p2026] at ha; subst a; trivial
  · exact checked2026
theorem derived2026 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2026 := by
  apply localUnsat_implies_entails f2026 [c1668, c2013, c1921, c96, c93, c376] c2026 unsat2026 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c2013 := derived2013 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2027 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2027 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2026, some c1921, some c2018, some c2022, some c2025, some c1776, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2027 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2027 : lratChecker f2027 p2027 = .success := by decide +kernel
theorem unsat2027 : Unsatisfiable (PosFin 57) f2027 := by
  apply lratCheckerSound f2027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2027
  · intro a ha; simp [p2027] at ha; subst a; trivial
  · exact checked2027
theorem derived2027 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2027 := by
  apply localUnsat_implies_entails f2027 [c2026, c1921, c2018, c2022, c2025, c1776] c2027 unsat2027 (by rfl) a
  have h0 : Entails.eval a c2026 := derived2026 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c2018 := derived2018 a h
  have h3 : Entails.eval a c2022 := derived2022 a h
  have h4 : Entails.eval a c2025 := derived2025 a h
  have h5 : Entails.eval a c1776 := derived1776 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2028 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2028 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1921, some c2027, some c1516, some c4, some c2013, some c1003, some c196, some c2026, some c1975, some c1992, some c122, some c260, some c245, some c25, some c170, some c161, some c73, some c21, some c378, some c376, some c243, some c185, some c362, some c1806, some c103, some c190, some c116, some c1711, some c677, some c361, some c72, some c247, some c227, some c240, some c329, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2028 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked2028 : lratChecker f2028 p2028 = .success := by decide +kernel
theorem unsat2028 : Unsatisfiable (PosFin 57) f2028 := by
  apply lratCheckerSound f2028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2028
  · intro a ha; simp [p2028] at ha; subst a; trivial
  · exact checked2028
theorem derived2028 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2028 := by
  apply localUnsat_implies_entails f2028 [c1668, c1817, c1921, c2027, c1516, c4, c2013, c1003, c196, c2026, c1975, c1992, c122, c260, c245, c25, c170, c161, c73, c21, c378, c376, c243, c185, c362, c1806, c103, c190, c116, c1711, c677, c361, c72, c247, c227, c240, c329] c2028 unsat2028 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c2027 := derived2027 a h
  have h4 : Entails.eval a c1516 := derived1516 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c2013 := derived2013 a h
  have h7 : Entails.eval a c1003 := derived1003 a h
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c2026 := derived2026 a h
  have h10 : Entails.eval a c1975 := derived1975 a h
  have h11 : Entails.eval a c1992 := derived1992 a h
  have h12 : Entails.eval a c122 := h 121 (by decide)
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c161 := h 160 (by decide)
  have h18 : Entails.eval a c73 := h 72 (by decide)
  have h19 : Entails.eval a c21 := h 20 (by decide)
  have h20 : Entails.eval a c378 := h 377 (by decide)
  have h21 : Entails.eval a c376 := h 375 (by decide)
  have h22 : Entails.eval a c243 := h 242 (by decide)
  have h23 : Entails.eval a c185 := h 184 (by decide)
  have h24 : Entails.eval a c362 := h 361 (by decide)
  have h25 : Entails.eval a c1806 := derived1806 a h
  have h26 : Entails.eval a c103 := h 102 (by decide)
  have h27 : Entails.eval a c190 := h 189 (by decide)
  have h28 : Entails.eval a c116 := h 115 (by decide)
  have h29 : Entails.eval a c1711 := derived1711 a h
  have h30 : Entails.eval a c677 := derived677 a h
  have h31 : Entails.eval a c361 := h 360 (by decide)
  have h32 : Entails.eval a c72 := h 71 (by decide)
  have h33 : Entails.eval a c247 := h 246 (by decide)
  have h34 : Entails.eval a c227 := h 226 (by decide)
  have h35 : Entails.eval a c240 := h 239 (by decide)
  have h36 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2029 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2029 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1921, some c2027, some c2013, some c2028, some c1, some c376, some c447, some c1516, some c4, some c1003, some c196, some c23, some c1527, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2029 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2029 : lratChecker f2029 p2029 = .success := by decide +kernel
theorem unsat2029 : Unsatisfiable (PosFin 57) f2029 := by
  apply lratCheckerSound f2029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2029
  · intro a ha; simp [p2029] at ha; subst a; trivial
  · exact checked2029
theorem derived2029 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2029 := by
  apply localUnsat_implies_entails f2029 [c1668, c1817, c1921, c2027, c2013, c2028, c1, c376, c447, c1516, c4, c1003, c196, c23, c1527] c2029 unsat2029 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c2027 := derived2027 a h
  have h4 : Entails.eval a c2013 := derived2013 a h
  have h5 : Entails.eval a c2028 := derived2028 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c447 := derived447 a h
  have h9 : Entails.eval a c1516 := derived1516 a h
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c1003 := derived1003 a h
  have h12 : Entails.eval a c196 := h 195 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c1527 := derived1527 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2030 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2030 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c2027, some c2013, some c1003, some c1921, some c2028, some c9, some c2029, some c122, some c117, some c32, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2030 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2030 : lratChecker f2030 p2030 = .success := by decide +kernel
theorem unsat2030 : Unsatisfiable (PosFin 57) f2030 := by
  apply lratCheckerSound f2030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2030
  · intro a ha; simp [p2030] at ha; subst a; trivial
  · exact checked2030
theorem derived2030 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2030 := by
  apply localUnsat_implies_entails f2030 [c1668, c2027, c2013, c1003, c1921, c2028, c9, c2029, c122, c117, c32] c2030 unsat2030 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c2027 := derived2027 a h
  have h2 : Entails.eval a c2013 := derived2013 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c2028 := derived2028 a h
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c2029 := derived2029 a h
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2031 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2031 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c2030, some c2013, some c1003, some c2027, some c196, some c2026, some c9, some c1975, some c1993, some c248, some c799, some c800, some c204, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2031 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2031 : lratChecker f2031 p2031 = .success := by decide +kernel
theorem unsat2031 : Unsatisfiable (PosFin 57) f2031 := by
  apply lratCheckerSound f2031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2031
  · intro a ha; simp [p2031] at ha; subst a; trivial
  · exact checked2031
theorem derived2031 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2031 := by
  apply localUnsat_implies_entails f2031 [c1668, c2030, c2013, c1003, c2027, c196, c2026, c9, c1975, c1993, c248, c799, c800, c204] c2031 unsat2031 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c2030 := derived2030 a h
  have h2 : Entails.eval a c2013 := derived2013 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c2027 := derived2027 a h
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c2026 := derived2026 a h
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c1975 := derived1975 a h
  have h9 : Entails.eval a c1993 := derived1993 a h
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c799 := derived799 a h
  have h12 : Entails.eval a c800 := derived800 a h
  have h13 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2032 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2032 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2031, some c2026, some c2030, some c380, some c1921, some c1531, some c2027, some c1516, some c2013, some c1003, some c1975, some c117, some c246, some c1992, some c1991, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2032 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2032 : lratChecker f2032 p2032 = .success := by decide +kernel
theorem unsat2032 : Unsatisfiable (PosFin 57) f2032 := by
  apply lratCheckerSound f2032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2032
  · intro a ha; simp [p2032] at ha; subst a; trivial
  · exact checked2032
theorem derived2032 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2032 := by
  apply localUnsat_implies_entails f2032 [c2031, c2026, c2030, c380, c1921, c1531, c2027, c1516, c2013, c1003, c1975, c117, c246, c1992, c1991] c2032 unsat2032 (by rfl) a
  have h0 : Entails.eval a c2031 := derived2031 a h
  have h1 : Entails.eval a c2026 := derived2026 a h
  have h2 : Entails.eval a c2030 := derived2030 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c1531 := derived1531 a h
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c2013 := derived2013 a h
  have h9 : Entails.eval a c1003 := derived1003 a h
  have h10 : Entails.eval a c1975 := derived1975 a h
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c246 := h 245 (by decide)
  have h13 : Entails.eval a c1992 := derived1992 a h
  have h14 : Entails.eval a c1991 := derived1991 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2033 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2033 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c2013, some c2026, some c2027, some c2030, some c1531, some c380, some c2032, some c1, some c378, some c376, some c447, some c362, some c361, some c1711, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2033 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2033 : lratChecker f2033 p2033 = .success := by decide +kernel
theorem unsat2033 : Unsatisfiable (PosFin 57) f2033 := by
  apply lratCheckerSound f2033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2033
  · intro a ha; simp [p2033] at ha; subst a; trivial
  · exact checked2033
theorem derived2033 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2033 := by
  apply localUnsat_implies_entails f2033 [c1668, c1921, c2013, c2026, c2027, c2030, c1531, c380, c2032, c1, c378, c376, c447, c362, c361, c1711] c2033 unsat2033 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c2013 := derived2013 a h
  have h3 : Entails.eval a c2026 := derived2026 a h
  have h4 : Entails.eval a c2027 := derived2027 a h
  have h5 : Entails.eval a c2030 := derived2030 a h
  have h6 : Entails.eval a c1531 := derived1531 a h
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c2032 := derived2032 a h
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c376 := h 375 (by decide)
  have h12 : Entails.eval a c447 := derived447 a h
  have h13 : Entails.eval a c362 := h 361 (by decide)
  have h14 : Entails.eval a c361 := h 360 (by decide)
  have h15 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2034 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2034 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c2033, some c112, some c10, some c503, some c1838, some c110, some c14, some c34, some c114, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2034 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2034 : lratChecker f2034 p2034 = .success := by decide +kernel
theorem unsat2034 : Unsatisfiable (PosFin 57) f2034 := by
  apply lratCheckerSound f2034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2034
  · intro a ha; simp [p2034] at ha; subst a; trivial
  · exact checked2034
theorem derived2034 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2034 := by
  apply localUnsat_implies_entails f2034 [c1668, c1817, c2033, c112, c10, c503, c1838, c110, c14, c34, c114] c2034 unsat2034 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c2033 := derived2033 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c503 := derived503 a h
  have h6 : Entails.eval a c1838 := derived1838 a h
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2035 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2035 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c2033, some c1668, some c2034, some c112, some c3, some c245, some c260, some c181, some c853, some c1819, some c31, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2035 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2035 : lratChecker f2035 p2035 = .success := by decide +kernel
theorem unsat2035 : Unsatisfiable (PosFin 57) f2035 := by
  apply lratCheckerSound f2035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2035
  · intro a ha; simp [p2035] at ha; subst a; trivial
  · exact checked2035
theorem derived2035 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2035 := by
  apply localUnsat_implies_entails f2035 [c1817, c2033, c1668, c2034, c112, c3, c245, c260, c181, c853, c1819, c31] c2035 unsat2035 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c2033 := derived2033 a h
  have h2 : Entails.eval a c1668 := derived1668 a h
  have h3 : Entails.eval a c2034 := derived2034 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c181 := h 180 (by decide)
  have h9 : Entails.eval a c853 := derived853 a h
  have h10 : Entails.eval a c1819 := derived1819 a h
  have h11 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2036 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2036 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c2033, some c1668, some c2034, some c112, some c10, some c1819, some c191, some c21, some c15, some c163, some c110, some c363, some c14, some c1010, some c374, some c371, some c754, some c162, some c687, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2036 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2036 : lratChecker f2036 p2036 = .success := by decide +kernel
theorem unsat2036 : Unsatisfiable (PosFin 57) f2036 := by
  apply lratCheckerSound f2036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2036
  · intro a ha; simp [p2036] at ha; subst a; trivial
  · exact checked2036
theorem derived2036 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2036 := by
  apply localUnsat_implies_entails f2036 [c1817, c2033, c1668, c2034, c112, c10, c1819, c191, c21, c15, c163, c110, c363, c14, c1010, c374, c371, c754, c162, c687] c2036 unsat2036 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c2033 := derived2033 a h
  have h2 : Entails.eval a c1668 := derived1668 a h
  have h3 : Entails.eval a c2034 := derived2034 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c1819 := derived1819 a h
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c163 := h 162 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c1010 := derived1010 a h
  have h15 : Entails.eval a c374 := h 373 (by decide)
  have h16 : Entails.eval a c371 := h 370 (by decide)
  have h17 : Entails.eval a c754 := derived754 a h
  have h18 : Entails.eval a c162 := h 161 (by decide)
  have h19 : Entails.eval a c687 := derived687 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2037 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2037 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c112, some c10, some c2035, some c2036, some c181, some c1823, some c381, some c190, some c188, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2037 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2037 : lratChecker f2037 p2037 = .success := by decide +kernel
theorem unsat2037 : Unsatisfiable (PosFin 57) f2037 := by
  apply lratCheckerSound f2037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2037
  · intro a ha; simp [p2037] at ha; subst a; trivial
  · exact checked2037
theorem derived2037 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2037 := by
  apply localUnsat_implies_entails f2037 [c1817, c1668, c112, c10, c2035, c2036, c181, c1823, c381, c190, c188] c2037 unsat2037 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2036 := derived2036 a h
  have h6 : Entails.eval a c181 := h 180 (by decide)
  have h7 : Entails.eval a c1823 := derived1823 a h
  have h8 : Entails.eval a c381 := h 380 (by decide)
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2038 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2038 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c2033, some c1668, some c2034, some c112, some c10, some c3, some c2037, some c1852, some c189, some c181, some c381, some c245, some c188, some c190, some c15, some c110, some c78, some c162, some c861, some c21, some c244, some c113, some c239, some c232, some c373, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2038 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2038 : lratChecker f2038 p2038 = .success := by decide +kernel
theorem unsat2038 : Unsatisfiable (PosFin 57) f2038 := by
  apply lratCheckerSound f2038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2038
  · intro a ha; simp [p2038] at ha; subst a; trivial
  · exact checked2038
theorem derived2038 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2038 := by
  apply localUnsat_implies_entails f2038 [c1817, c2033, c1668, c2034, c112, c10, c3, c2037, c1852, c189, c181, c381, c245, c188, c190, c15, c110, c78, c162, c861, c21, c244, c113, c239, c232, c373] c2038 unsat2038 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c2033 := derived2033 a h
  have h2 : Entails.eval a c1668 := derived1668 a h
  have h3 : Entails.eval a c2034 := derived2034 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c2037 := derived2037 a h
  have h8 : Entails.eval a c1852 := derived1852 a h
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c181 := h 180 (by decide)
  have h11 : Entails.eval a c381 := h 380 (by decide)
  have h12 : Entails.eval a c245 := h 244 (by decide)
  have h13 : Entails.eval a c188 := h 187 (by decide)
  have h14 : Entails.eval a c190 := h 189 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c78 := h 77 (by decide)
  have h18 : Entails.eval a c162 := h 161 (by decide)
  have h19 : Entails.eval a c861 := derived861 a h
  have h20 : Entails.eval a c21 := h 20 (by decide)
  have h21 : Entails.eval a c244 := h 243 (by decide)
  have h22 : Entails.eval a c113 := h 112 (by decide)
  have h23 : Entails.eval a c239 := h 238 (by decide)
  have h24 : Entails.eval a c232 := h 231 (by decide)
  have h25 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2039 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2039 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c109, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2039 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2039 : lratChecker f2039 p2039 = .success := by decide +kernel
theorem unsat2039 : Unsatisfiable (PosFin 57) f2039 := by
  apply lratCheckerSound f2039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2039
  · intro a ha; simp [p2039] at ha; subst a; trivial
  · exact checked2039
theorem derived2039 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2039 := by
  apply localUnsat_implies_entails f2039 [c2033, c109] c2039 unsat2039 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2040 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2040 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c826, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2040 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2040 : lratChecker f2040 p2040 = .success := by decide +kernel
theorem unsat2040 : Unsatisfiable (PosFin 57) f2040 := by
  apply lratCheckerSound f2040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2040
  · intro a ha; simp [p2040] at ha; subst a; trivial
  · exact checked2040
theorem derived2040 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2040 := by
  apply localUnsat_implies_entails f2040 [c2033, c826] c2040 unsat2040 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c826 := derived826 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2041 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2041 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c833, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2041 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2041 : lratChecker f2041 p2041 = .success := by decide +kernel
theorem unsat2041 : Unsatisfiable (PosFin 57) f2041 := by
  apply lratCheckerSound f2041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2041
  · intro a ha; simp [p2041] at ha; subst a; trivial
  · exact checked2041
theorem derived2041 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2041 := by
  apply localUnsat_implies_entails f2041 [c2033, c833] c2041 unsat2041 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c833 := derived833 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2042 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2042 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c853, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2042 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2042 : lratChecker f2042 p2042 = .success := by decide +kernel
theorem unsat2042 : Unsatisfiable (PosFin 57) f2042 := by
  apply lratCheckerSound f2042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2042
  · intro a ha; simp [p2042] at ha; subst a; trivial
  · exact checked2042
theorem derived2042 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2042 := by
  apply localUnsat_implies_entails f2042 [c2033, c853] c2042 unsat2042 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c853 := derived853 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2043 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2043 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c715, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2043 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2043 : lratChecker f2043 p2043 = .success := by decide +kernel
theorem unsat2043 : Unsatisfiable (PosFin 57) f2043 := by
  apply lratCheckerSound f2043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2043
  · intro a ha; simp [p2043] at ha; subst a; trivial
  · exact checked2043
theorem derived2043 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2043 := by
  apply localUnsat_implies_entails f2043 [c2033, c715] c2043 unsat2043 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c715 := derived715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2044 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2044 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c759, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2044 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2044 : lratChecker f2044 p2044 = .success := by decide +kernel
theorem unsat2044 : Unsatisfiable (PosFin 57) f2044 := by
  apply lratCheckerSound f2044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2044
  · intro a ha; simp [p2044] at ha; subst a; trivial
  · exact checked2044
theorem derived2044 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2044 := by
  apply localUnsat_implies_entails f2044 [c2033, c759] c2044 unsat2044 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c759 := derived759 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2045 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2045 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c843, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p2045 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2045 : lratChecker f2045 p2045 = .success := by decide +kernel
theorem unsat2045 : Unsatisfiable (PosFin 57) f2045 := by
  apply lratCheckerSound f2045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2045
  · intro a ha; simp [p2045] at ha; subst a; trivial
  · exact checked2045
theorem derived2045 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2045 := by
  apply localUnsat_implies_entails f2045 [c2033, c843] c2045 unsat2045 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c843 := derived843 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2046 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2046 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c110, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p2046 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2046 : lratChecker f2046 p2046 = .success := by decide +kernel
theorem unsat2046 : Unsatisfiable (PosFin 57) f2046 := by
  apply lratCheckerSound f2046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2046
  · intro a ha; simp [p2046] at ha; subst a; trivial
  · exact checked2046
theorem derived2046 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2046 := by
  apply localUnsat_implies_entails f2046 [c2033, c110] c2046 unsat2046 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2047 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2047 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c522, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2047 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2047 : lratChecker f2047 p2047 = .success := by decide +kernel
theorem unsat2047 : Unsatisfiable (PosFin 57) f2047 := by
  apply lratCheckerSound f2047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2047
  · intro a ha; simp [p2047] at ha; subst a; trivial
  · exact checked2047
theorem derived2047 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2047 := by
  apply localUnsat_implies_entails f2047 [c2033, c522] c2047 unsat2047 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c522 := derived522 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2048 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2048 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c108, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2048 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2048 : lratChecker f2048 p2048 = .success := by decide +kernel
theorem unsat2048 : Unsatisfiable (PosFin 57) f2048 := by
  apply lratCheckerSound f2048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2048
  · intro a ha; simp [p2048] at ha; subst a; trivial
  · exact checked2048
theorem derived2048 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2048 := by
  apply localUnsat_implies_entails f2048 [c2033, c108] c2048 unsat2048 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2049 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨21, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2049 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c714, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2049 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2049 : lratChecker f2049 p2049 = .success := by decide +kernel
theorem unsat2049 : Unsatisfiable (PosFin 57) f2049 := by
  apply lratCheckerSound f2049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2049
  · intro a ha; simp [p2049] at ha; subst a; trivial
  · exact checked2049
theorem derived2049 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2049 := by
  apply localUnsat_implies_entails f2049 [c1817, c714] c2049 unsat2049 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c714 := derived714 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2050 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2050 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1113, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2050 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2050 : lratChecker f2050 p2050 = .success := by decide +kernel
theorem unsat2050 : Unsatisfiable (PosFin 57) f2050 := by
  apply lratCheckerSound f2050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2050
  · intro a ha; simp [p2050] at ha; subst a; trivial
  · exact checked2050
theorem derived2050 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2050 := by
  apply localUnsat_implies_entails f2050 [c1817, c1113] c2050 unsat2050 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1113 := derived1113 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2051 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2051 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c112, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p2051 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2051 : lratChecker f2051 p2051 = .success := by decide +kernel
theorem unsat2051 : Unsatisfiable (PosFin 57) f2051 := by
  apply lratCheckerSound f2051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2051
  · intro a ha; simp [p2051] at ha; subst a; trivial
  · exact checked2051
theorem derived2051 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2051 := by
  apply localUnsat_implies_entails f2051 [c1817, c112] c2051 unsat2051 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2052 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true), (⟨3, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2052 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c716, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p2052 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2052 : lratChecker f2052 p2052 = .success := by decide +kernel
theorem unsat2052 : Unsatisfiable (PosFin 57) f2052 := by
  apply lratCheckerSound f2052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2052
  · intro a ha; simp [p2052] at ha; subst a; trivial
  · exact checked2052
theorem derived2052 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2052 := by
  apply localUnsat_implies_entails f2052 [c1668, c716] c2052 unsat2052 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c716 := derived716 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2053 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2053 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c11, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p2053 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2053 : lratChecker f2053 p2053 = .success := by decide +kernel
theorem unsat2053 : Unsatisfiable (PosFin 57) f2053 := by
  apply lratCheckerSound f2053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2053
  · intro a ha; simp [p2053] at ha; subst a; trivial
  · exact checked2053
theorem derived2053 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2053 := by
  apply localUnsat_implies_entails f2053 [c1668, c11] c2053 unsat2053 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2054 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨9, by decide⟩, true), (⟨45, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2054 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1045, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2054 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2054 : lratChecker f2054 p2054 = .success := by decide +kernel
theorem unsat2054 : Unsatisfiable (PosFin 57) f2054 := by
  apply lratCheckerSound f2054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2054
  · intro a ha; simp [p2054] at ha; subst a; trivial
  · exact checked2054
theorem derived2054 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2054 := by
  apply localUnsat_implies_entails f2054 [c1668, c1045] c2054 unsat2054 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1045 := derived1045 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2055 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2055 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c861, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p2055 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2055 : lratChecker f2055 p2055 = .success := by decide +kernel
theorem unsat2055 : Unsatisfiable (PosFin 57) f2055 := by
  apply lratCheckerSound f2055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2055
  · intro a ha; simp [p2055] at ha; subst a; trivial
  · exact checked2055
theorem derived2055 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2055 := by
  apply localUnsat_implies_entails f2055 [c1668, c861] c2055 unsat2055 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c861 := derived861 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2056 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2056 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2056 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2056 : lratChecker f2056 p2056 = .success := by decide +kernel
theorem unsat2056 : Unsatisfiable (PosFin 57) f2056 := by
  apply lratCheckerSound f2056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2056
  · intro a ha; simp [p2056] at ha; subst a; trivial
  · exact checked2056
theorem derived2056 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2056 := by
  apply localUnsat_implies_entails f2056 [c1668, c1] c2056 unsat2056 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2057 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2057 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c95, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p2057 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2057 : lratChecker f2057 p2057 = .success := by decide +kernel
theorem unsat2057 : Unsatisfiable (PosFin 57) f2057 := by
  apply lratCheckerSound f2057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2057
  · intro a ha; simp [p2057] at ha; subst a; trivial
  · exact checked2057
theorem derived2057 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2057 := by
  apply localUnsat_implies_entails f2057 [c1668, c95] c2057 unsat2057 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2058 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2058 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c73, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2058 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2058 : lratChecker f2058 p2058 = .success := by decide +kernel
theorem unsat2058 : Unsatisfiable (PosFin 57) f2058 := by
  apply lratCheckerSound f2058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2058
  · intro a ha; simp [p2058] at ha; subst a; trivial
  · exact checked2058
theorem derived2058 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2058 := by
  apply localUnsat_implies_entails f2058 [c1668, c73] c2058 unsat2058 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2059 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2059 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c515, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p2059 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2059 : lratChecker f2059 p2059 = .success := by decide +kernel
theorem unsat2059 : Unsatisfiable (PosFin 57) f2059 := by
  apply lratCheckerSound f2059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2059
  · intro a ha; simp [p2059] at ha; subst a; trivial
  · exact checked2059
theorem derived2059 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2059 := by
  apply localUnsat_implies_entails f2059 [c1668, c515] c2059 unsat2059 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c515 := derived515 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2060 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2060 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1027, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p2060 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2060 : lratChecker f2060 p2060 = .success := by decide +kernel
theorem unsat2060 : Unsatisfiable (PosFin 57) f2060 := by
  apply lratCheckerSound f2060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2060
  · intro a ha; simp [p2060] at ha; subst a; trivial
  · exact checked2060
theorem derived2060 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2060 := by
  apply localUnsat_implies_entails f2060 [c1668, c1027] c2060 unsat2060 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1027 := derived1027 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2061 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2061 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c10, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2061 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2061 : lratChecker f2061 p2061 = .success := by decide +kernel
theorem unsat2061 : Unsatisfiable (PosFin 57) f2061 := by
  apply lratCheckerSound f2061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2061
  · intro a ha; simp [p2061] at ha; subst a; trivial
  · exact checked2061
theorem derived2061 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2061 := by
  apply localUnsat_implies_entails f2061 [c1668, c10] c2061 unsat2061 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2062 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨4, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2062 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1039, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p2062 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2062 : lratChecker f2062 p2062 = .success := by decide +kernel
theorem unsat2062 : Unsatisfiable (PosFin 57) f2062 := by
  apply lratCheckerSound f2062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2062
  · intro a ha; simp [p2062] at ha; subst a; trivial
  · exact checked2062
theorem derived2062 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2062 := by
  apply localUnsat_implies_entails f2062 [c1668, c1039] c2062 unsat2062 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2063 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨43, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2063 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1010, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p2063 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2063 : lratChecker f2063 p2063 = .success := by decide +kernel
theorem unsat2063 : Unsatisfiable (PosFin 57) f2063 := by
  apply lratCheckerSound f2063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2063
  · intro a ha; simp [p2063] at ha; subst a; trivial
  · exact checked2063
theorem derived2063 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2063 := by
  apply localUnsat_implies_entails f2063 [c1668, c1010] c2063 unsat2063 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1010 := derived1010 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2064 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2064 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c627, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p2064 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2064 : lratChecker f2064 p2064 = .success := by decide +kernel
theorem unsat2064 : Unsatisfiable (PosFin 57) f2064 := by
  apply lratCheckerSound f2064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2064
  · intro a ha; simp [p2064] at ha; subst a; trivial
  · exact checked2064
theorem derived2064 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2064 := by
  apply localUnsat_implies_entails f2064 [c1668, c627] c2064 unsat2064 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c627 := derived627 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2065 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨43, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2065 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c82, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2065 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2065 : lratChecker f2065 p2065 = .success := by decide +kernel
theorem unsat2065 : Unsatisfiable (PosFin 57) f2065 := by
  apply lratCheckerSound f2065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2065
  · intro a ha; simp [p2065] at ha; subst a; trivial
  · exact checked2065
theorem derived2065 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2065 := by
  apply localUnsat_implies_entails f2065 [c1668, c82] c2065 unsat2065 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2066 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨45, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2066 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c655, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p2066 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2066 : lratChecker f2066 p2066 = .success := by decide +kernel
theorem unsat2066 : Unsatisfiable (PosFin 57) f2066 := by
  apply lratCheckerSound f2066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2066
  · intro a ha; simp [p2066] at ha; subst a; trivial
  · exact checked2066
theorem derived2066 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2066 := by
  apply localUnsat_implies_entails f2066 [c1668, c655] c2066 unsat2066 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c655 := derived655 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2067 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2067 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c31, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p2067 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2067 : lratChecker f2067 p2067 = .success := by decide +kernel
theorem unsat2067 : Unsatisfiable (PosFin 57) f2067 := by
  apply lratCheckerSound f2067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2067
  · intro a ha; simp [p2067] at ha; subst a; trivial
  · exact checked2067
theorem derived2067 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2067 := by
  apply localUnsat_implies_entails f2067 [c1668, c31] c2067 unsat2067 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2068 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨50, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2068 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1043, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2068 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2068 : lratChecker f2068 p2068 = .success := by decide +kernel
theorem unsat2068 : Unsatisfiable (PosFin 57) f2068 := by
  apply lratCheckerSound f2068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2068
  · intro a ha; simp [p2068] at ha; subst a; trivial
  · exact checked2068
theorem derived2068 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2068 := by
  apply localUnsat_implies_entails f2068 [c1668, c1043] c2068 unsat2068 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1043 := derived1043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2069 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨4, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2069 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c83, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p2069 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2069 : lratChecker f2069 p2069 = .success := by decide +kernel
theorem unsat2069 : Unsatisfiable (PosFin 57) f2069 := by
  apply lratCheckerSound f2069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2069
  · intro a ha; simp [p2069] at ha; subst a; trivial
  · exact checked2069
theorem derived2069 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2069 := by
  apply localUnsat_implies_entails f2069 [c1668, c83] c2069 unsat2069 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2070 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2070 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c21, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p2070 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2070 : lratChecker f2070 p2070 = .success := by decide +kernel
theorem unsat2070 : Unsatisfiable (PosFin 57) f2070 := by
  apply lratCheckerSound f2070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2070
  · intro a ha; simp [p2070] at ha; subst a; trivial
  · exact checked2070
theorem derived2070 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2070 := by
  apply localUnsat_implies_entails f2070 [c1668, c21] c2070 unsat2070 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2071 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨45, by decide⟩, false), (⟨3, by decide⟩, true), (⟨44, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2071 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c711, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2071 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2071 : lratChecker f2071 p2071 = .success := by decide +kernel
theorem unsat2071 : Unsatisfiable (PosFin 57) f2071 := by
  apply lratCheckerSound f2071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2071
  · intro a ha; simp [p2071] at ha; subst a; trivial
  · exact checked2071
theorem derived2071 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2071 := by
  apply localUnsat_implies_entails f2071 [c1668, c711] c2071 unsat2071 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c711 := derived711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2072 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2072 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c62, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2072 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2072 : lratChecker f2072 p2072 = .success := by decide +kernel
theorem unsat2072 : Unsatisfiable (PosFin 57) f2072 := by
  apply lratCheckerSound f2072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2072
  · intro a ha; simp [p2072] at ha; subst a; trivial
  · exact checked2072
theorem derived2072 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2072 := by
  apply localUnsat_implies_entails f2072 [c2033, c62] c2072 unsat2072 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2073 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2073 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1041, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2073 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2073 : lratChecker f2073 p2073 = .success := by decide +kernel
theorem unsat2073 : Unsatisfiable (PosFin 57) f2073 := by
  apply lratCheckerSound f2073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2073
  · intro a ha; simp [p2073] at ha; subst a; trivial
  · exact checked2073
theorem derived2073 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2073 := by
  apply localUnsat_implies_entails f2073 [c1668, c1041] c2073 unsat2073 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1041 := derived1041 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2074 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2074 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c503, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2074 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2074 : lratChecker f2074 p2074 = .success := by decide +kernel
theorem unsat2074 : Unsatisfiable (PosFin 57) f2074 := by
  apply lratCheckerSound f2074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2074
  · intro a ha; simp [p2074] at ha; subst a; trivial
  · exact checked2074
theorem derived2074 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2074 := by
  apply localUnsat_implies_entails f2074 [c1817, c503] c2074 unsat2074 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c503 := derived503 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2075 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2075 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c30, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2075 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2075 : lratChecker f2075 p2075 = .success := by decide +kernel
theorem unsat2075 : Unsatisfiable (PosFin 57) f2075 := by
  apply lratCheckerSound f2075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2075
  · intro a ha; simp [p2075] at ha; subst a; trivial
  · exact checked2075
theorem derived2075 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2075 := by
  apply localUnsat_implies_entails f2075 [c1668, c30] c2075 unsat2075 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2076 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨49, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2076 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c94, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p2076 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2076 : lratChecker f2076 p2076 = .success := by decide +kernel
theorem unsat2076 : Unsatisfiable (PosFin 57) f2076 := by
  apply lratCheckerSound f2076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2076
  · intro a ha; simp [p2076] at ha; subst a; trivial
  · exact checked2076
theorem derived2076 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2076 := by
  apply localUnsat_implies_entails f2076 [c1668, c94] c2076 unsat2076 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2077 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2077 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1011, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p2077 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2077 : lratChecker f2077 p2077 = .success := by decide +kernel
theorem unsat2077 : Unsatisfiable (PosFin 57) f2077 := by
  apply lratCheckerSound f2077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2077
  · intro a ha; simp [p2077] at ha; subst a; trivial
  · exact checked2077
theorem derived2077 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2077 := by
  apply localUnsat_implies_entails f2077 [c1668, c1011] c2077 unsat2077 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1011 := derived1011 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2078 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨37, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2078 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c70, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2078 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2078 : lratChecker f2078 p2078 = .success := by decide +kernel
theorem unsat2078 : Unsatisfiable (PosFin 57) f2078 := by
  apply lratCheckerSound f2078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2078
  · intro a ha; simp [p2078] at ha; subst a; trivial
  · exact checked2078
theorem derived2078 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2078 := by
  apply localUnsat_implies_entails f2078 [c1817, c70] c2078 unsat2078 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2079 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨47, by decide⟩, false), (⟨51, by decide⟩, false), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨3, by decide⟩, true), (⟨50, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2079 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1166, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p2079 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2079 : lratChecker f2079 p2079 = .success := by decide +kernel
theorem unsat2079 : Unsatisfiable (PosFin 57) f2079 := by
  apply lratCheckerSound f2079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2079
  · intro a ha; simp [p2079] at ha; subst a; trivial
  · exact checked2079
theorem derived2079 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2079 := by
  apply localUnsat_implies_entails f2079 [c1668, c1166] c2079 unsat2079 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1166 := derived1166 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2080 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2080 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1195, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p2080 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2080 : lratChecker f2080 p2080 = .success := by decide +kernel
theorem unsat2080 : Unsatisfiable (PosFin 57) f2080 := by
  apply lratCheckerSound f2080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2080
  · intro a ha; simp [p2080] at ha; subst a; trivial
  · exact checked2080
theorem derived2080 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2080 := by
  apply localUnsat_implies_entails f2080 [c1668, c1195] c2080 unsat2080 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2081 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2081 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1265, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p2081 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2081 : lratChecker f2081 p2081 = .success := by decide +kernel
theorem unsat2081 : Unsatisfiable (PosFin 57) f2081 := by
  apply lratCheckerSound f2081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2081
  · intro a ha; simp [p2081] at ha; subst a; trivial
  · exact checked2081
theorem derived2081 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2081 := by
  apply localUnsat_implies_entails f2081 [c2033, c1265] c2081 unsat2081 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1265 := derived1265 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2082 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2082 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1267, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2082 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2082 : lratChecker f2082 p2082 = .success := by decide +kernel
theorem unsat2082 : Unsatisfiable (PosFin 57) f2082 := by
  apply lratCheckerSound f2082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2082
  · intro a ha; simp [p2082] at ha; subst a; trivial
  · exact checked2082
theorem derived2082 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2082 := by
  apply localUnsat_implies_entails f2082 [c2033, c1267] c2082 unsat2082 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1267 := derived1267 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2083 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2083 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2033, some c1270, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2083 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2083 : lratChecker f2083 p2083 = .success := by decide +kernel
theorem unsat2083 : Unsatisfiable (PosFin 57) f2083 := by
  apply lratCheckerSound f2083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2083
  · intro a ha; simp [p2083] at ha; subst a; trivial
  · exact checked2083
theorem derived2083 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2083 := by
  apply localUnsat_implies_entails f2083 [c2033, c1270] c2083 unsat2083 (by rfl) a
  have h0 : Entails.eval a c2033 := derived2033 a h
  have h1 : Entails.eval a c1270 := derived1270 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived2083

end CochromaticTwenty.Certificates.B16_2_2
