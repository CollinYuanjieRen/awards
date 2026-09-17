import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps1500_1599

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2014 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2014 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c2011, some c266, some c2009, some c2010, some c263, some c108, some c110, some c2013, some c222, some c1100, some c228, some c353, some c115, some c2012, some c45, some c112, some c134, some c75, some c81, some c236, some c168, some c175, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2014 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2014 : lratChecker f2014 p2014 = .success := by decide +kernel
theorem unsat2014 : Unsatisfiable (PosFin 57) f2014 := by
  apply lratCheckerSound f2014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2014
  · intro a ha; simp [p2014] at ha; subst a; trivial
  · exact checked2014
theorem derived2014 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2014 := by
  apply localUnsat_implies_entails f2014 [c2006, c2011, c266, c2009, c2010, c263, c108, c110, c2013, c222, c1100, c228, c353, c115, c2012, c45, c112, c134, c75, c81, c236, c168, c175] c2014 unsat2014 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c2011 := derived2011 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2009 := derived2009 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c2013 := derived2013 a h
  have h9 : Entails.eval a c222 := h 221 (by decide)
  have h10 : Entails.eval a c1100 := derived1100 a h
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c2012 := derived2012 a h
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c112 := h 111 (by decide)
  have h17 : Entails.eval a c134 := h 133 (by decide)
  have h18 : Entails.eval a c75 := h 74 (by decide)
  have h19 : Entails.eval a c81 := h 80 (by decide)
  have h20 : Entails.eval a c236 := h 235 (by decide)
  have h21 : Entails.eval a c168 := h 167 (by decide)
  have h22 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2015 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2015 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c2009, some c2010, some c108, some c1147, some c2014, some c26, some c1335, some c112, some c820, some c1909, some c11, some c154, some c57, some c245, some c182, some c102, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2015 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2015 : lratChecker f2015 p2015 = .success := by decide +kernel
theorem unsat2015 : Unsatisfiable (PosFin 57) f2015 := by
  apply lratCheckerSound f2015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2015
  · intro a ha; simp [p2015] at ha; subst a; trivial
  · exact checked2015
theorem derived2015 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2015 := by
  apply localUnsat_implies_entails f2015 [c2006, c1829, c266, c2009, c2010, c108, c1147, c2014, c26, c1335, c112, c820, c1909, c11, c154, c57, c245, c182, c102] c2015 unsat2015 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2009 := derived2009 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c2014 := derived2014 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1335 := derived1335 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c820 := derived820 a h
  have h12 : Entails.eval a c1909 := derived1909 a h
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c154 := h 153 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c245 := h 244 (by decide)
  have h17 : Entails.eval a c182 := h 181 (by decide)
  have h18 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2016 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2016 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c1147, some c108, some c2009, some c2010, some c263, some c2011, some c2015, some c264, some c1024, some c1229, some c26, some c228, some c110, some c1541, some c1137, some c1731, some c140, some c168, some c64, some c75, some c248, some c639, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2016 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2016 : lratChecker f2016 p2016 = .success := by decide +kernel
theorem unsat2016 : Unsatisfiable (PosFin 57) f2016 := by
  apply lratCheckerSound f2016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2016
  · intro a ha; simp [p2016] at ha; subst a; trivial
  · exact checked2016
theorem derived2016 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2016 := by
  apply localUnsat_implies_entails f2016 [c2006, c1829, c266, c1147, c108, c2009, c2010, c263, c2011, c2015, c264, c1024, c1229, c26, c228, c110, c1541, c1137, c1731, c140, c168, c64, c75, c248, c639] c2016 unsat2016 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c2009 := derived2009 a h
  have h6 : Entails.eval a c2010 := derived2010 a h
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c2011 := derived2011 a h
  have h9 : Entails.eval a c2015 := derived2015 a h
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c1024 := derived1024 a h
  have h12 : Entails.eval a c1229 := derived1229 a h
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c1541 := derived1541 a h
  have h17 : Entails.eval a c1137 := derived1137 a h
  have h18 : Entails.eval a c1731 := derived1731 a h
  have h19 : Entails.eval a c140 := h 139 (by decide)
  have h20 : Entails.eval a c168 := h 167 (by decide)
  have h21 : Entails.eval a c64 := h 63 (by decide)
  have h22 : Entails.eval a c75 := h 74 (by decide)
  have h23 : Entails.eval a c248 := h 247 (by decide)
  have h24 : Entails.eval a c639 := derived639 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2017 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2017 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c115, some c51, some c139, some c87, some c1778, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2017 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2017 : lratChecker f2017 p2017 = .success := by decide +kernel
theorem unsat2017 : Unsatisfiable (PosFin 57) f2017 := by
  apply lratCheckerSound f2017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2017
  · intro a ha; simp [p2017] at ha; subst a; trivial
  · exact checked2017
theorem derived2017 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2017 := by
  apply localUnsat_implies_entails f2017 [c2006, c115, c51, c139, c87, c1778] c2017 unsat2017 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c115 := h 114 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c1778 := derived1778 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2018 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, true), (⟨35, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2018 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c68, some c58, some c352, some c250, some c60, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2018 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2018 : lratChecker f2018 p2018 = .success := by decide +kernel
theorem unsat2018 : Unsatisfiable (PosFin 57) f2018 := by
  apply lratCheckerSound f2018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2018
  · intro a ha; simp [p2018] at ha; subst a; trivial
  · exact checked2018
theorem derived2018 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2018 := by
  apply localUnsat_implies_entails f2018 [c2006, c68, c58, c352, c250, c60] c2018 unsat2018 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c250 := h 249 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2019 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨4, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2019 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c31, some c266, some c1, some c1161, some c2016, some c1147, some c201, some c16, some c112, some c2018, some c157, some c115, some c2017, some c51, some c119, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2019 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2019 : lratChecker f2019 p2019 = .success := by decide +kernel
theorem unsat2019 : Unsatisfiable (PosFin 57) f2019 := by
  apply lratCheckerSound f2019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2019
  · intro a ha; simp [p2019] at ha; subst a; trivial
  · exact checked2019
theorem derived2019 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2019 := by
  apply localUnsat_implies_entails f2019 [c2006, c1829, c31, c266, c1, c1161, c2016, c1147, c201, c16, c112, c2018, c157, c115, c2017, c51, c119] c2019 unsat2019 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1161 := derived1161 a h
  have h6 : Entails.eval a c2016 := derived2016 a h
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c2018 := derived2018 a h
  have h12 : Entails.eval a c157 := h 156 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c2017 := derived2017 a h
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2020 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2020 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c1, some c1161, some c21, some c2016, some c31, some c2019, some c13, some c112, some c1896, some c2018, some c12, some c349, some c153, some c60, some c61, some c256, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2020 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2020 : lratChecker f2020 p2020 = .success := by decide +kernel
theorem unsat2020 : Unsatisfiable (PosFin 57) f2020 := by
  apply lratCheckerSound f2020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2020
  · intro a ha; simp [p2020] at ha; subst a; trivial
  · exact checked2020
theorem derived2020 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2020 := by
  apply localUnsat_implies_entails f2020 [c2006, c1829, c266, c1, c1161, c21, c2016, c31, c2019, c13, c112, c1896, c2018, c12, c349, c153, c60, c61, c256] c2020 unsat2020 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1161 := derived1161 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c2016 := derived2016 a h
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c2019 := derived2019 a h
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c1896 := derived1896 a h
  have h12 : Entails.eval a c2018 := derived2018 a h
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c349 := h 348 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c60 := h 59 (by decide)
  have h17 : Entails.eval a c61 := h 60 (by decide)
  have h18 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2021 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2021 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2006, some c266, some c1147, some c201, some c2020, some c111, some c1896, some c963, some c26, some c1, some c198, some c715, some c49, some c1645, some c116, some c136, some c149, some c55, some c240, some c89, some c294, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2021 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2021 : lratChecker f2021 p2021 = .success := by decide +kernel
theorem unsat2021 : Unsatisfiable (PosFin 57) f2021 := by
  apply lratCheckerSound f2021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2021
  · intro a ha; simp [p2021] at ha; subst a; trivial
  · exact checked2021
theorem derived2021 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2021 := by
  apply localUnsat_implies_entails f2021 [c1829, c2006, c266, c1147, c201, c2020, c111, c1896, c963, c26, c1, c198, c715, c49, c1645, c116, c136, c149, c55, c240, c89, c294] c2021 unsat2021 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c2020 := derived2020 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c1896 := derived1896 a h
  have h8 : Entails.eval a c963 := derived963 a h
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c715 := derived715 a h
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c1645 := derived1645 a h
  have h15 : Entails.eval a c116 := h 115 (by decide)
  have h16 : Entails.eval a c136 := h 135 (by decide)
  have h17 : Entails.eval a c149 := h 148 (by decide)
  have h18 : Entails.eval a c55 := h 54 (by decide)
  have h19 : Entails.eval a c240 := h 239 (by decide)
  have h20 : Entails.eval a c89 := h 88 (by decide)
  have h21 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2022 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2022 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1147, some c963, some c26, some c1, some c198, some c210, some c206, some c53, some c313, some c149, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2022 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2022 : lratChecker f2022 p2022 = .success := by decide +kernel
theorem unsat2022 : Unsatisfiable (PosFin 57) f2022 := by
  apply lratCheckerSound f2022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2022
  · intro a ha; simp [p2022] at ha; subst a; trivial
  · exact checked2022
theorem derived2022 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2022 := by
  apply localUnsat_implies_entails f2022 [c1829, c1147, c963, c26, c1, c198, c210, c206, c53, c313, c149] c2022 unsat2022 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c198 := h 197 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2023 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2023 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c2020, some c266, some c1147, some c201, some c2022, some c49, some c2021, some c148, some c51, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2023 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2023 : lratChecker f2023 p2023 = .success := by decide +kernel
theorem unsat2023 : Unsatisfiable (PosFin 57) f2023 := by
  apply lratCheckerSound f2023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2023
  · intro a ha; simp [p2023] at ha; subst a; trivial
  · exact checked2023
theorem derived2023 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2023 := by
  apply localUnsat_implies_entails f2023 [c2006, c2020, c266, c1147, c201, c2022, c49, c2021, c148, c51] c2023 unsat2023 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c2020 := derived2020 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c2022 := derived2022 a h
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c2021 := derived2021 a h
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2024 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2024 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2016, some c2023, some c13, some c1, some c115, some c2017, some c51, some c119, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2024 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2024 : lratChecker f2024 p2024 = .success := by decide +kernel
theorem unsat2024 : Unsatisfiable (PosFin 57) f2024 := by
  apply lratCheckerSound f2024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2024
  · intro a ha; simp [p2024] at ha; subst a; trivial
  · exact checked2024
theorem derived2024 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2024 := by
  apply localUnsat_implies_entails f2024 [c1829, c2016, c2023, c13, c1, c115, c2017, c51, c119] c2024 unsat2024 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2016 := derived2016 a h
  have h2 : Entails.eval a c2023 := derived2023 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c2017 := derived2017 a h
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2025 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2025 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c2016, some c266, some c2020, some c111, some c2023, some c13, some c12, some c2024, some c1665, some c203, some c2022, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2025 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2025 : lratChecker f2025 p2025 = .success := by decide +kernel
theorem unsat2025 : Unsatisfiable (PosFin 57) f2025 := by
  apply lratCheckerSound f2025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2025
  · intro a ha; simp [p2025] at ha; subst a; trivial
  · exact checked2025
theorem derived2025 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2025 := by
  apply localUnsat_implies_entails f2025 [c2006, c2016, c266, c2020, c111, c2023, c13, c12, c2024, c1665, c203, c2022] c2025 unsat2025 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c2016 := derived2016 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2020 := derived2020 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c2023 := derived2023 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c2024 := derived2024 a h
  have h9 : Entails.eval a c1665 := derived1665 a h
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c2022 := derived2022 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2026 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨16, by decide⟩, true), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, true), (⟨17, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2026 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c263, some c266, some c7, some c119, some c1147, some c850, some c128, some c1445, some c56, some c149, some c140, some c316, some c236, some c232, some c92, some c285, some c176, some c312, some c1002, some c288, some c67, some c240, some c330, some c25, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2026 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2026 : lratChecker f2026 p2026 = .success := by decide +kernel
theorem unsat2026 : Unsatisfiable (PosFin 57) f2026 := by
  apply lratCheckerSound f2026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2026
  · intro a ha; simp [p2026] at ha; subst a; trivial
  · exact checked2026
theorem derived2026 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2026 := by
  apply localUnsat_implies_entails f2026 [c2006, c1829, c263, c266, c7, c119, c1147, c850, c128, c1445, c56, c149, c140, c316, c236, c232, c92, c285, c176, c312, c1002, c288, c67, c240, c330, c25] c2026 unsat2026 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c850 := derived850 a h
  have h8 : Entails.eval a c128 := h 127 (by decide)
  have h9 : Entails.eval a c1445 := derived1445 a h
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c149 := h 148 (by decide)
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c236 := h 235 (by decide)
  have h15 : Entails.eval a c232 := h 231 (by decide)
  have h16 : Entails.eval a c92 := h 91 (by decide)
  have h17 : Entails.eval a c285 := h 284 (by decide)
  have h18 : Entails.eval a c176 := h 175 (by decide)
  have h19 : Entails.eval a c312 := h 311 (by decide)
  have h20 : Entails.eval a c1002 := derived1002 a h
  have h21 : Entails.eval a c288 := h 287 (by decide)
  have h22 : Entails.eval a c67 := h 66 (by decide)
  have h23 : Entails.eval a c240 := h 239 (by decide)
  have h24 : Entails.eval a c330 := h 329 (by decide)
  have h25 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2027 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2027 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c252, some c248, some c93, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2027 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2027 : lratChecker f2027 p2027 = .success := by decide +kernel
theorem unsat2027 : Unsatisfiable (PosFin 57) f2027 := by
  apply lratCheckerSound f2027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2027
  · intro a ha; simp [p2027] at ha; subst a; trivial
  · exact checked2027
theorem derived2027 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2027 := by
  apply localUnsat_implies_entails f2027 [c2006, c1829, c252, c248, c93] c2027 unsat2027 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c252 := h 251 (by decide)
  have h3 : Entails.eval a c248 := h 247 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2028 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨16, by decide⟩, true), (⟨56, by decide⟩, true), (⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2028 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c19, some c103, some c64, some c181, some c973, some c57, some c228, some c1638, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2028 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2028 : lratChecker f2028 p2028 = .success := by decide +kernel
theorem unsat2028 : Unsatisfiable (PosFin 57) f2028 := by
  apply lratCheckerSound f2028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2028
  · intro a ha; simp [p2028] at ha; subst a; trivial
  · exact checked2028
theorem derived2028 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2028 := by
  apply localUnsat_implies_entails f2028 [c1829, c19, c103, c64, c181, c973, c57, c228, c1638] c2028 unsat2028 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c181 := h 180 (by decide)
  have h5 : Entails.eval a c973 := derived973 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c1638 := derived1638 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2029 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨30, by decide⟩, false), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2029 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c1147, some c202, some c149, some c140, some c316, some c53, some c236, some c232, some c26, some c1678, some c285, some c270, some c65, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2029 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2029 : lratChecker f2029 p2029 = .success := by decide +kernel
theorem unsat2029 : Unsatisfiable (PosFin 57) f2029 := by
  apply lratCheckerSound f2029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2029
  · intro a ha; simp [p2029] at ha; subst a; trivial
  · exact checked2029
theorem derived2029 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2029 := by
  apply localUnsat_implies_entails f2029 [c2006, c1829, c266, c1147, c202, c149, c140, c316, c53, c236, c232, c26, c1678, c285, c270, c65] c2029 unsat2029 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  have h7 : Entails.eval a c316 := h 315 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c236 := h 235 (by decide)
  have h10 : Entails.eval a c232 := h 231 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c1678 := derived1678 a h
  have h13 : Entails.eval a c285 := h 284 (by decide)
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2030 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨56, by decide⟩, true), (⟨30, by decide⟩, false), (⟨31, by decide⟩, false), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2030 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c56, some c928, some c64, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2030 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2030 : lratChecker f2030 p2030 = .success := by decide +kernel
theorem unsat2030 : Unsatisfiable (PosFin 57) f2030 := by
  apply lratCheckerSound f2030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2030
  · intro a ha; simp [p2030] at ha; subst a; trivial
  · exact checked2030
theorem derived2030 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2030 := by
  apply localUnsat_implies_entails f2030 [c56, c928, c64] c2030 unsat2030 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c928 := derived928 a h
  have h2 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2031 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2031 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c2016, some c266, some c1147, some c2025, some c263, some c7, some c119, some c112, some c51, some c210, some c115, some c850, some c2027, some c2030, some c819, some c2029, some c202, some c2026, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2031 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2031 : lratChecker f2031 p2031 = .success := by decide +kernel
theorem unsat2031 : Unsatisfiable (PosFin 57) f2031 := by
  apply lratCheckerSound f2031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2031
  · intro a ha; simp [p2031] at ha; subst a; trivial
  · exact checked2031
theorem derived2031 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2031 := by
  apply localUnsat_implies_entails f2031 [c2006, c2016, c266, c1147, c2025, c263, c7, c119, c112, c51, c210, c115, c850, c2027, c2030, c819, c2029, c202, c2026] c2031 unsat2031 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c2016 := derived2016 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c2025 := derived2025 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c210 := h 209 (by decide)
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c850 := derived850 a h
  have h13 : Entails.eval a c2027 := derived2027 a h
  have h14 : Entails.eval a c2030 := derived2030 a h
  have h15 : Entails.eval a c819 := derived819 a h
  have h16 : Entails.eval a c2029 := derived2029 a h
  have h17 : Entails.eval a c202 := h 201 (by decide)
  have h18 : Entails.eval a c2026 := derived2026 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2032 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2032 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c2031, some c264, some c2016, some c266, some c1147, some c1, some c21, some c963, some c31, some c111, some c1896, some c1787, some c268, some c201, some c7, some c119, some c228, some c819, some c12, some c1638, some c56, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2032 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2032 : lratChecker f2032 p2032 = .success := by decide +kernel
theorem unsat2032 : Unsatisfiable (PosFin 57) f2032 := by
  apply lratCheckerSound f2032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2032
  · intro a ha; simp [p2032] at ha; subst a; trivial
  · exact checked2032
theorem derived2032 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2032 := by
  apply localUnsat_implies_entails f2032 [c2006, c1829, c2031, c264, c2016, c266, c1147, c1, c21, c963, c31, c111, c1896, c1787, c268, c201, c7, c119, c228, c819, c12, c1638, c56] c2032 unsat2032 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c2031 := derived2031 a h
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c2016 := derived2016 a h
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c963 := derived963 a h
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c1896 := derived1896 a h
  have h13 : Entails.eval a c1787 := derived1787 a h
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c7 := h 6 (by decide)
  have h17 : Entails.eval a c119 := h 118 (by decide)
  have h18 : Entails.eval a c228 := h 227 (by decide)
  have h19 : Entails.eval a c819 := derived819 a h
  have h20 : Entails.eval a c12 := h 11 (by decide)
  have h21 : Entails.eval a c1638 := derived1638 a h
  have h22 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2033 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2033 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c266, some c1147, some c2031, some c264, some c2032, some c263, some c7, some c119, some c128, some c51, some c850, some c201, some c135, some c1777, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2033 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2033 : lratChecker f2033 p2033 = .success := by decide +kernel
theorem unsat2033 : Unsatisfiable (PosFin 57) f2033 := by
  apply lratCheckerSound f2033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2033
  · intro a ha; simp [p2033] at ha; subst a; trivial
  · exact checked2033
theorem derived2033 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2033 := by
  apply localUnsat_implies_entails f2033 [c2006, c266, c1147, c2031, c264, c2032, c263, c7, c119, c128, c51, c850, c201, c135, c1777] c2033 unsat2033 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c2031 := derived2031 a h
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c2032 := derived2032 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c128 := h 127 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c850 := derived850 a h
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c135 := h 134 (by decide)
  have h14 : Entails.eval a c1777 := derived1777 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2034 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨39, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2034 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1147, some c201, some c11, some c155, some c65, some c67, some c159, some c349, some c222, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2034 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2034 : lratChecker f2034 p2034 = .success := by decide +kernel
theorem unsat2034 : Unsatisfiable (PosFin 57) f2034 := by
  apply lratCheckerSound f2034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2034
  · intro a ha; simp [p2034] at ha; subst a; trivial
  · exact checked2034
theorem derived2034 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2034 := by
  apply localUnsat_implies_entails f2034 [c1829, c1147, c201, c11, c155, c65, c67, c159, c349, c222] c2034 unsat2034 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c159 := h 158 (by decide)
  have h8 : Entails.eval a c349 := h 348 (by decide)
  have h9 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2035 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2035 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c2016, some c2033, some c2010, some c263, some c27, some c2034, some c111, some c1147, some c201, some c202, some c40, some c2027, some c115, some c49, some c116, some c136, some c85, some c89, some c175, some c232, some c170, some c197, some c2028, some c155, some c5, some c1189, some c57, some c245, some c240, some c363, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2035 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked2035 : lratChecker f2035 p2035 = .success := by decide +kernel
theorem unsat2035 : Unsatisfiable (PosFin 57) f2035 := by
  apply lratCheckerSound f2035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2035
  · intro a ha; simp [p2035] at ha; subst a; trivial
  · exact checked2035
theorem derived2035 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2035 := by
  apply localUnsat_implies_entails f2035 [c2006, c1829, c266, c2016, c2033, c2010, c263, c27, c2034, c111, c1147, c201, c202, c40, c2027, c115, c49, c116, c136, c85, c89, c175, c232, c170, c197, c2028, c155, c5, c1189, c57, c245, c240, c363] c2035 unsat2035 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2016 := derived2016 a h
  have h4 : Entails.eval a c2033 := derived2033 a h
  have h5 : Entails.eval a c2010 := derived2010 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c2034 := derived2034 a h
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c1147 := derived1147 a h
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c40 := h 39 (by decide)
  have h14 : Entails.eval a c2027 := derived2027 a h
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c116 := h 115 (by decide)
  have h18 : Entails.eval a c136 := h 135 (by decide)
  have h19 : Entails.eval a c85 := h 84 (by decide)
  have h20 : Entails.eval a c89 := h 88 (by decide)
  have h21 : Entails.eval a c175 := h 174 (by decide)
  have h22 : Entails.eval a c232 := h 231 (by decide)
  have h23 : Entails.eval a c170 := h 169 (by decide)
  have h24 : Entails.eval a c197 := h 196 (by decide)
  have h25 : Entails.eval a c2028 := derived2028 a h
  have h26 : Entails.eval a c155 := h 154 (by decide)
  have h27 : Entails.eval a c5 := h 4 (by decide)
  have h28 : Entails.eval a c1189 := derived1189 a h
  have h29 : Entails.eval a c57 := h 56 (by decide)
  have h30 : Entails.eval a c245 := h 244 (by decide)
  have h31 : Entails.eval a c240 := h 239 (by decide)
  have h32 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2036 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2036 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c2033, some c2010, some c263, some c27, some c2016, some c2027, some c1147, some c2035, some c1100, some c163, some c973, some c159, some c340, some c58, some c185, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2036 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2036 : lratChecker f2036 p2036 = .success := by decide +kernel
theorem unsat2036 : Unsatisfiable (PosFin 57) f2036 := by
  apply lratCheckerSound f2036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2036
  · intro a ha; simp [p2036] at ha; subst a; trivial
  · exact checked2036
theorem derived2036 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2036 := by
  apply localUnsat_implies_entails f2036 [c2006, c1829, c266, c2033, c2010, c263, c27, c2016, c2027, c1147, c2035, c1100, c163, c973, c159, c340, c58, c185] c2036 unsat2036 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2033 := derived2033 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c2016 := derived2016 a h
  have h8 : Entails.eval a c2027 := derived2027 a h
  have h9 : Entails.eval a c1147 := derived1147 a h
  have h10 : Entails.eval a c2035 := derived2035 a h
  have h11 : Entails.eval a c1100 := derived1100 a h
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c973 := derived973 a h
  have h14 : Entails.eval a c159 := h 158 (by decide)
  have h15 : Entails.eval a c340 := h 339 (by decide)
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2037 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2037 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2006, some c266, some c2033, some c2010, some c263, some c2016, some c27, some c2036, some c9, some c197, some c155, some c12, some c57, some c1024, some c111, some c183, some c97, some c100, some c250, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2037 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2037 : lratChecker f2037 p2037 = .success := by decide +kernel
theorem unsat2037 : Unsatisfiable (PosFin 57) f2037 := by
  apply lratCheckerSound f2037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2037
  · intro a ha; simp [p2037] at ha; subst a; trivial
  · exact checked2037
theorem derived2037 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2037 := by
  apply localUnsat_implies_entails f2037 [c1829, c2006, c266, c2033, c2010, c263, c2016, c27, c2036, c9, c197, c155, c12, c57, c1024, c111, c183, c97, c100, c250] c2037 unsat2037 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2033 := derived2033 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c2016 := derived2016 a h
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c2036 := derived2036 a h
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c1024 := derived1024 a h
  have h15 : Entails.eval a c111 := h 110 (by decide)
  have h16 : Entails.eval a c183 := h 182 (by decide)
  have h17 : Entails.eval a c97 := h 96 (by decide)
  have h18 : Entails.eval a c100 := h 99 (by decide)
  have h19 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2038 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, true), (⟨15, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2038 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1147, some c201, some c11, some c2034, some c228, some c159, some c154, some c65, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2038 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2038 : lratChecker f2038 p2038 = .success := by decide +kernel
theorem unsat2038 : Unsatisfiable (PosFin 57) f2038 := by
  apply lratCheckerSound f2038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2038
  · intro a ha; simp [p2038] at ha; subst a; trivial
  · exact checked2038
theorem derived2038 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2038 := by
  apply localUnsat_implies_entails f2038 [c1829, c1147, c201, c11, c2034, c228, c159, c154, c65] c2038 unsat2038 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c2034 := derived2034 a h
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c159 := h 158 (by decide)
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2039 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2039 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c266, some c2016, some c2033, some c2010, some c263, some c2038, some c1147, some c201, some c202, some c2037, some c115, some c49, some c51, some c1783, some c1382, some c136, some c216, some c85, some c234, some c317, some c313, some c175, some c285, some c232, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2039 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2039 : lratChecker f2039 p2039 = .success := by decide +kernel
theorem unsat2039 : Unsatisfiable (PosFin 57) f2039 := by
  apply lratCheckerSound f2039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2039
  · intro a ha; simp [p2039] at ha; subst a; trivial
  · exact checked2039
theorem derived2039 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2039 := by
  apply localUnsat_implies_entails f2039 [c2006, c266, c2016, c2033, c2010, c263, c2038, c1147, c201, c202, c2037, c115, c49, c51, c1783, c1382, c136, c216, c85, c234, c317, c313, c175, c285, c232] c2039 unsat2039 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c2016 := derived2016 a h
  have h3 : Entails.eval a c2033 := derived2033 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c2038 := derived2038 a h
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c2037 := derived2037 a h
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c1783 := derived1783 a h
  have h15 : Entails.eval a c1382 := derived1382 a h
  have h16 : Entails.eval a c136 := h 135 (by decide)
  have h17 : Entails.eval a c216 := h 215 (by decide)
  have h18 : Entails.eval a c85 := h 84 (by decide)
  have h19 : Entails.eval a c234 := h 233 (by decide)
  have h20 : Entails.eval a c317 := h 316 (by decide)
  have h21 : Entails.eval a c313 := h 312 (by decide)
  have h22 : Entails.eval a c175 := h 174 (by decide)
  have h23 : Entails.eval a c285 := h 284 (by decide)
  have h24 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2040 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2040 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c2033, some c2010, some c263, some c2016, some c1147, some c2039, some c1100, some c159, some c154, some c65, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2040 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2040 : lratChecker f2040 p2040 = .success := by decide +kernel
theorem unsat2040 : Unsatisfiable (PosFin 57) f2040 := by
  apply lratCheckerSound f2040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2040
  · intro a ha; simp [p2040] at ha; subst a; trivial
  · exact checked2040
theorem derived2040 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2040 := by
  apply localUnsat_implies_entails f2040 [c2006, c1829, c266, c2033, c2010, c263, c2016, c1147, c2039, c1100, c159, c154, c65] c2040 unsat2040 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2033 := derived2033 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c2016 := derived2016 a h
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c2039 := derived2039 a h
  have h9 : Entails.eval a c1100 := derived1100 a h
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c154 := h 153 (by decide)
  have h12 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2041 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2041 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c51, some c149, some c143, some c216, some c313, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2041 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2041 : lratChecker f2041 p2041 = .success := by decide +kernel
theorem unsat2041 : Unsatisfiable (PosFin 57) f2041 := by
  apply lratCheckerSound f2041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2041
  · intro a ha; simp [p2041] at ha; subst a; trivial
  · exact checked2041
theorem derived2041 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2041 := by
  apply localUnsat_implies_entails f2041 [c49, c51, c149, c143, c216, c313] c2041 unsat2041 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c149 := h 148 (by decide)
  have h3 : Entails.eval a c143 := h 142 (by decide)
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2042 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2042 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c2037, some c112, some c266, some c2033, some c2010, some c263, some c2016, some c1147, some c202, some c201, some c2038, some c2040, some c2041, some c210, some c115, some c2029, some c313, some c204, some c133, some c5, some c232, some c229, some c179, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2042 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2042 : lratChecker f2042 p2042 = .success := by decide +kernel
theorem unsat2042 : Unsatisfiable (PosFin 57) f2042 := by
  apply lratCheckerSound f2042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2042
  · intro a ha; simp [p2042] at ha; subst a; trivial
  · exact checked2042
theorem derived2042 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2042 := by
  apply localUnsat_implies_entails f2042 [c2006, c2037, c112, c266, c2033, c2010, c263, c2016, c1147, c202, c201, c2038, c2040, c2041, c210, c115, c2029, c313, c204, c133, c5, c232, c229, c179] c2042 unsat2042 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c2037 := derived2037 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c2033 := derived2033 a h
  have h5 : Entails.eval a c2010 := derived2010 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c2016 := derived2016 a h
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c2038 := derived2038 a h
  have h12 : Entails.eval a c2040 := derived2040 a h
  have h13 : Entails.eval a c2041 := derived2041 a h
  have h14 : Entails.eval a c210 := h 209 (by decide)
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c2029 := derived2029 a h
  have h17 : Entails.eval a c313 := h 312 (by decide)
  have h18 : Entails.eval a c204 := h 203 (by decide)
  have h19 : Entails.eval a c133 := h 132 (by decide)
  have h20 : Entails.eval a c5 := h 4 (by decide)
  have h21 : Entails.eval a c232 := h 231 (by decide)
  have h22 : Entails.eval a c229 := h 228 (by decide)
  have h23 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2043 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2043 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2033, some c2016, some c2037, some c112, some c2042, some c9, some c12, some c197, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2043 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2043 : lratChecker f2043 p2043 = .success := by decide +kernel
theorem unsat2043 : Unsatisfiable (PosFin 57) f2043 := by
  apply lratCheckerSound f2043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2043
  · intro a ha; simp [p2043] at ha; subst a; trivial
  · exact checked2043
theorem derived2043 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2043 := by
  apply localUnsat_implies_entails f2043 [c1829, c2033, c2016, c2037, c112, c2042, c9, c12, c197] c2043 unsat2043 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2033 := derived2033 a h
  have h2 : Entails.eval a c2016 := derived2016 a h
  have h3 : Entails.eval a c2037 := derived2037 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c2042 := derived2042 a h
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2044 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨5, by decide⟩, true), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨23, by decide⟩, true), (⟨15, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2044 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2006, some c27, some c40, some c1147, some c202, some c264, some c2010, some c197, some c2028, some c155, some c5, some c1254, some c1189, some c57, some c183, some c245, some c97, some c61, some c249, some c353, some c339, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2044 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2044 : lratChecker f2044 p2044 = .success := by decide +kernel
theorem unsat2044 : Unsatisfiable (PosFin 57) f2044 := by
  apply lratCheckerSound f2044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2044
  · intro a ha; simp [p2044] at ha; subst a; trivial
  · exact checked2044
theorem derived2044 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2044 := by
  apply localUnsat_implies_entails f2044 [c1829, c2006, c27, c40, c1147, c202, c264, c2010, c197, c2028, c155, c5, c1254, c1189, c57, c183, c245, c97, c61, c249, c353, c339] c2044 unsat2044 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c2010 := derived2010 a h
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c2028 := derived2028 a h
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c1254 := derived1254 a h
  have h13 : Entails.eval a c1189 := derived1189 a h
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c183 := h 182 (by decide)
  have h16 : Entails.eval a c245 := h 244 (by decide)
  have h17 : Entails.eval a c97 := h 96 (by decide)
  have h18 : Entails.eval a c61 := h 60 (by decide)
  have h19 : Entails.eval a c249 := h 248 (by decide)
  have h20 : Entails.eval a c353 := h 352 (by decide)
  have h21 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2045 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨31, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2045 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c142, some c314, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p2045 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2045 : lratChecker f2045 p2045 = .success := by decide +kernel
theorem unsat2045 : Unsatisfiable (PosFin 57) f2045 := by
  apply lratCheckerSound f2045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2045
  · intro a ha; simp [p2045] at ha; subst a; trivial
  · exact checked2045
theorem derived2045 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2045 := by
  apply localUnsat_implies_entails f2045 [c147, c142, c314] c2045 unsat2045 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2046 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨31, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2046 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c151, some c232, some c312, some c133, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2046 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2046 : lratChecker f2046 p2046 = .success := by decide +kernel
theorem unsat2046 : Unsatisfiable (PosFin 57) f2046 := by
  apply lratCheckerSound f2046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2046
  · intro a ha; simp [p2046] at ha; subst a; trivial
  · exact checked2046
theorem derived2046 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2046 := by
  apply localUnsat_implies_entails f2046 [c140, c151, c232, c312, c133] c2046 unsat2046 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  have h3 : Entails.eval a c312 := h 311 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2047 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2047 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c2043, some c264, some c266, some c1147, some c201, some c4, some c116, some c49, some c202, some c2033, some c2010, some c263, some c1024, some c2016, some c2027, some c40, some c53, some c216, some c2044, some c2045, some c204, some c5, some c2046, some c314, some c133, some c232, some c229, some c179, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2047 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2047 : lratChecker f2047 p2047 = .success := by decide +kernel
theorem unsat2047 : Unsatisfiable (PosFin 57) f2047 := by
  apply lratCheckerSound f2047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2047
  · intro a ha; simp [p2047] at ha; subst a; trivial
  · exact checked2047
theorem derived2047 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2047 := by
  apply localUnsat_implies_entails f2047 [c2006, c2043, c264, c266, c1147, c201, c4, c116, c49, c202, c2033, c2010, c263, c1024, c2016, c2027, c40, c53, c216, c2044, c2045, c204, c5, c2046, c314, c133, c232, c229, c179] c2047 unsat2047 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c2043 := derived2043 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c2033 := derived2033 a h
  have h11 : Entails.eval a c2010 := derived2010 a h
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c1024 := derived1024 a h
  have h14 : Entails.eval a c2016 := derived2016 a h
  have h15 : Entails.eval a c2027 := derived2027 a h
  have h16 : Entails.eval a c40 := h 39 (by decide)
  have h17 : Entails.eval a c53 := h 52 (by decide)
  have h18 : Entails.eval a c216 := h 215 (by decide)
  have h19 : Entails.eval a c2044 := derived2044 a h
  have h20 : Entails.eval a c2045 := derived2045 a h
  have h21 : Entails.eval a c204 := h 203 (by decide)
  have h22 : Entails.eval a c5 := h 4 (by decide)
  have h23 : Entails.eval a c2046 := derived2046 a h
  have h24 : Entails.eval a c314 := h 313 (by decide)
  have h25 : Entails.eval a c133 := h 132 (by decide)
  have h26 : Entails.eval a c232 := h 231 (by decide)
  have h27 : Entails.eval a c229 := h 228 (by decide)
  have h28 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2048 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨56, by decide⟩, true), (⟨23, by decide⟩, true), (⟨15, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2048 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2010, some c197, some c2028, some c5, some c1254, some c26, some c228, some c53, some c155, some c216, some c57, some c56, some c245, some c1004, some c61, some c282, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2048 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2048 : lratChecker f2048 p2048 = .success := by decide +kernel
theorem unsat2048 : Unsatisfiable (PosFin 57) f2048 := by
  apply lratCheckerSound f2048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2048
  · intro a ha; simp [p2048] at ha; subst a; trivial
  · exact checked2048
theorem derived2048 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2048 := by
  apply localUnsat_implies_entails f2048 [c1829, c2010, c197, c2028, c5, c1254, c26, c228, c53, c155, c216, c57, c56, c245, c1004, c61, c282] c2048 unsat2048 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2010 := derived2010 a h
  have h2 : Entails.eval a c197 := h 196 (by decide)
  have h3 : Entails.eval a c2028 := derived2028 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1254 := derived1254 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c155 := h 154 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c245 := h 244 (by decide)
  have h14 : Entails.eval a c1004 := derived1004 a h
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2049 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2049 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c142, some c2045, some c313, some c216, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2049 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2049 : lratChecker f2049 p2049 = .success := by decide +kernel
theorem unsat2049 : Unsatisfiable (PosFin 57) f2049 := by
  apply lratCheckerSound f2049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2049
  · intro a ha; simp [p2049] at ha; subst a; trivial
  · exact checked2049
theorem derived2049 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2049 := by
  apply localUnsat_implies_entails f2049 [c147, c142, c2045, c313, c216] c2049 unsat2049 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c2045 := derived2045 a h
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2050 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2050 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c266, some c2033, some c2010, some c263, some c2043, some c264, some c1024, some c2016, some c2027, some c1147, some c202, some c201, some c4, some c116, some c49, some c2047, some c2048, some c2049, some c204, some c19, some c1254, some c26, some c53, some c216, some c56, some c2046, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2050 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2050 : lratChecker f2050 p2050 = .success := by decide +kernel
theorem unsat2050 : Unsatisfiable (PosFin 57) f2050 := by
  apply lratCheckerSound f2050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2050
  · intro a ha; simp [p2050] at ha; subst a; trivial
  · exact checked2050
theorem derived2050 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2050 := by
  apply localUnsat_implies_entails f2050 [c2006, c266, c2033, c2010, c263, c2043, c264, c1024, c2016, c2027, c1147, c202, c201, c4, c116, c49, c2047, c2048, c2049, c204, c19, c1254, c26, c53, c216, c56, c2046] c2050 unsat2050 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c2033 := derived2033 a h
  have h3 : Entails.eval a c2010 := derived2010 a h
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c2043 := derived2043 a h
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c1024 := derived1024 a h
  have h8 : Entails.eval a c2016 := derived2016 a h
  have h9 : Entails.eval a c2027 := derived2027 a h
  have h10 : Entails.eval a c1147 := derived1147 a h
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c116 := h 115 (by decide)
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c2047 := derived2047 a h
  have h17 : Entails.eval a c2048 := derived2048 a h
  have h18 : Entails.eval a c2049 := derived2049 a h
  have h19 : Entails.eval a c204 := h 203 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c1254 := derived1254 a h
  have h22 : Entails.eval a c26 := h 25 (by decide)
  have h23 : Entails.eval a c53 := h 52 (by decide)
  have h24 : Entails.eval a c216 := h 215 (by decide)
  have h25 : Entails.eval a c56 := h 55 (by decide)
  have h26 : Entails.eval a c2046 := derived2046 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2051 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2051 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c2016, some c2033, some c2010, some c263, some c2043, some c264, some c1024, some c2050, some c9, some c12, some c197, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2051 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2051 : lratChecker f2051 p2051 = .success := by decide +kernel
theorem unsat2051 : Unsatisfiable (PosFin 57) f2051 := by
  apply lratCheckerSound f2051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2051
  · intro a ha; simp [p2051] at ha; subst a; trivial
  · exact checked2051
theorem derived2051 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2051 := by
  apply localUnsat_implies_entails f2051 [c2006, c1829, c266, c2016, c2033, c2010, c263, c2043, c264, c1024, c2050, c9, c12, c197] c2051 unsat2051 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2016 := derived2016 a h
  have h4 : Entails.eval a c2033 := derived2033 a h
  have h5 : Entails.eval a c2010 := derived2010 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c2043 := derived2043 a h
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c1024 := derived1024 a h
  have h10 : Entails.eval a c2050 := derived2050 a h
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2052 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2052 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c2051, some c266, some c1147, some c34, some c26, some c264, some c963, some c128, some c263, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2052 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2052 : lratChecker f2052 p2052 = .success := by decide +kernel
theorem unsat2052 : Unsatisfiable (PosFin 57) f2052 := by
  apply lratCheckerSound f2052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2052
  · intro a ha; simp [p2052] at ha; subst a; trivial
  · exact checked2052
theorem derived2052 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2052 := by
  apply localUnsat_implies_entails f2052 [c2006, c1829, c2051, c266, c1147, c34, c26, c264, c963, c128, c263] c2052 unsat2052 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c2051 := derived2051 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c963 := derived963 a h
  have h9 : Entails.eval a c128 := h 127 (by decide)
  have h10 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2053 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2053 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c1147, some c201, some c2052, some c1607, some c202, some c2051, some c30, some c3, some c23, some c1987, some c263, some c1669, some c58, some c7, some c119, some c185, some c187, some c56, some c94, some c140, some c91, some c92, some c359, some c176, some c365, some c372, some c374, some c363, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2053 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked2053 : lratChecker f2053 p2053 = .success := by decide +kernel
theorem unsat2053 : Unsatisfiable (PosFin 57) f2053 := by
  apply lratCheckerSound f2053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2053
  · intro a ha; simp [p2053] at ha; subst a; trivial
  · exact checked2053
theorem derived2053 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2053 := by
  apply localUnsat_implies_entails f2053 [c2006, c1829, c266, c1147, c201, c2052, c1607, c202, c2051, c30, c3, c23, c1987, c263, c1669, c58, c7, c119, c185, c187, c56, c94, c140, c91, c92, c359, c176, c365, c372, c374, c363] c2053 unsat2053 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c2052 := derived2052 a h
  have h6 : Entails.eval a c1607 := derived1607 a h
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c2051 := derived2051 a h
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c1987 := derived1987 a h
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c1669 := derived1669 a h
  have h15 : Entails.eval a c58 := h 57 (by decide)
  have h16 : Entails.eval a c7 := h 6 (by decide)
  have h17 : Entails.eval a c119 := h 118 (by decide)
  have h18 : Entails.eval a c185 := h 184 (by decide)
  have h19 : Entails.eval a c187 := h 186 (by decide)
  have h20 : Entails.eval a c56 := h 55 (by decide)
  have h21 : Entails.eval a c94 := h 93 (by decide)
  have h22 : Entails.eval a c140 := h 139 (by decide)
  have h23 : Entails.eval a c91 := h 90 (by decide)
  have h24 : Entails.eval a c92 := h 91 (by decide)
  have h25 : Entails.eval a c359 := h 358 (by decide)
  have h26 : Entails.eval a c176 := h 175 (by decide)
  have h27 : Entails.eval a c365 := h 364 (by decide)
  have h28 : Entails.eval a c372 := h 371 (by decide)
  have h29 : Entails.eval a c374 := h 373 (by decide)
  have h30 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2054 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2054 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c266, some c1147, some c201, some c2052, some c2053, some c264, some c1744, some c1787, some c4, some c116, some c52, some c53, some c214, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2054 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2054 : lratChecker f2054 p2054 = .success := by decide +kernel
theorem unsat2054 : Unsatisfiable (PosFin 57) f2054 := by
  apply lratCheckerSound f2054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2054
  · intro a ha; simp [p2054] at ha; subst a; trivial
  · exact checked2054
theorem derived2054 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2054 := by
  apply localUnsat_implies_entails f2054 [c2006, c266, c1147, c201, c2052, c2053, c264, c1744, c1787, c4, c116, c52, c53, c214] c2054 unsat2054 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c2052 := derived2052 a h
  have h5 : Entails.eval a c2053 := derived2053 a h
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c1744 := derived1744 a h
  have h8 : Entails.eval a c1787 := derived1787 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2055 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2055 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c2054, some c819, some c2051, some c266, some c30, some c34, some c263, some c1292, some c7, some c119, some c2027, some c56, some c64, some c973, some c284, some c228, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2055 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2055 : lratChecker f2055 p2055 = .success := by decide +kernel
theorem unsat2055 : Unsatisfiable (PosFin 57) f2055 := by
  apply lratCheckerSound f2055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2055
  · intro a ha; simp [p2055] at ha; subst a; trivial
  · exact checked2055
theorem derived2055 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2055 := by
  apply localUnsat_implies_entails f2055 [c2006, c1829, c2054, c819, c2051, c266, c30, c34, c263, c1292, c7, c119, c2027, c56, c64, c973, c284, c228] c2055 unsat2055 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c2054 := derived2054 a h
  have h3 : Entails.eval a c819 := derived819 a h
  have h4 : Entails.eval a c2051 := derived2051 a h
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c1292 := derived1292 a h
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c2027 := derived2027 a h
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c973 := derived973 a h
  have h16 : Entails.eval a c284 := h 283 (by decide)
  have h17 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2056 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2056 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c2054, some c819, some c2051, some c266, some c1147, some c26, some c2052, some c963, some c263, some c1335, some c119, some c850, some c56, some c10, some c1524, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2056 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2056 : lratChecker f2056 p2056 = .success := by decide +kernel
theorem unsat2056 : Unsatisfiable (PosFin 57) f2056 := by
  apply lratCheckerSound f2056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2056
  · intro a ha; simp [p2056] at ha; subst a; trivial
  · exact checked2056
theorem derived2056 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2056 := by
  apply localUnsat_implies_entails f2056 [c2006, c1829, c2054, c819, c2051, c266, c1147, c26, c2052, c963, c263, c1335, c119, c850, c56, c10, c1524] c2056 unsat2056 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c2054 := derived2054 a h
  have h3 : Entails.eval a c819 := derived819 a h
  have h4 : Entails.eval a c2051 := derived2051 a h
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c2052 := derived2052 a h
  have h9 : Entails.eval a c963 := derived963 a h
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c1335 := derived1335 a h
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c850 := derived850 a h
  have h14 : Entails.eval a c56 := h 55 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c1524 := derived1524 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2057 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2057 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c31, some c1147, some c963, some c21, some c1896, some c226, some c153, some c117, some c52, some c269, some c207, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2057 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2057 : lratChecker f2057 p2057 = .success := by decide +kernel
theorem unsat2057 : Unsatisfiable (PosFin 57) f2057 := by
  apply lratCheckerSound f2057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2057
  · intro a ha; simp [p2057] at ha; subst a; trivial
  · exact checked2057
theorem derived2057 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2057 := by
  apply localUnsat_implies_entails f2057 [c1829, c31, c1147, c963, c21, c1896, c226, c153, c117, c52, c269, c207] c2057 unsat2057 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c1896 := derived1896 a h
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2058 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2058 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2006, some c266, some c1147, some c2054, some c819, some c2056, some c1292, some c9, some c198, some c13, some c2055, some c2051, some c1744, some c268, some c119, some c850, some c56, some c15, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2058 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2058 : lratChecker f2058 p2058 = .success := by decide +kernel
theorem unsat2058 : Unsatisfiable (PosFin 57) f2058 := by
  apply lratCheckerSound f2058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2058
  · intro a ha; simp [p2058] at ha; subst a; trivial
  · exact checked2058
theorem derived2058 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2058 := by
  apply localUnsat_implies_entails f2058 [c1829, c2006, c266, c1147, c2054, c819, c2056, c1292, c9, c198, c13, c2055, c2051, c1744, c268, c119, c850, c56, c15] c2058 unsat2058 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c2054 := derived2054 a h
  have h5 : Entails.eval a c819 := derived819 a h
  have h6 : Entails.eval a c2056 := derived2056 a h
  have h7 : Entails.eval a c1292 := derived1292 a h
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c2055 := derived2055 a h
  have h12 : Entails.eval a c2051 := derived2051 a h
  have h13 : Entails.eval a c1744 := derived1744 a h
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c119 := h 118 (by decide)
  have h16 : Entails.eval a c850 := derived850 a h
  have h17 : Entails.eval a c56 := h 55 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2059 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2059 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c2051, some c266, some c1147, some c2054, some c819, some c2055, some c264, some c2056, some c1292, some c13, some c9, some c198, some c2058, some c2057, some c263, some c119, some c706, some c850, some c56, some c15, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2059 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2059 : lratChecker f2059 p2059 = .success := by decide +kernel
theorem unsat2059 : Unsatisfiable (PosFin 57) f2059 := by
  apply lratCheckerSound f2059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2059
  · intro a ha; simp [p2059] at ha; subst a; trivial
  · exact checked2059
theorem derived2059 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2059 := by
  apply localUnsat_implies_entails f2059 [c2006, c1829, c2051, c266, c1147, c2054, c819, c2055, c264, c2056, c1292, c13, c9, c198, c2058, c2057, c263, c119, c706, c850, c56, c15] c2059 unsat2059 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c2051 := derived2051 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c2054 := derived2054 a h
  have h6 : Entails.eval a c819 := derived819 a h
  have h7 : Entails.eval a c2055 := derived2055 a h
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c2056 := derived2056 a h
  have h10 : Entails.eval a c1292 := derived1292 a h
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c198 := h 197 (by decide)
  have h14 : Entails.eval a c2058 := derived2058 a h
  have h15 : Entails.eval a c2057 := derived2057 a h
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c119 := h 118 (by decide)
  have h18 : Entails.eval a c706 := derived706 a h
  have h19 : Entails.eval a c850 := derived850 a h
  have h20 : Entails.eval a c56 := h 55 (by decide)
  have h21 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2060 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2060 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c266, some c2059, some c2010, some c263, some c2051, some c3, some c34, some c1100, some c109, some c110, some c2013, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2060 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2060 : lratChecker f2060 p2060 = .success := by decide +kernel
theorem unsat2060 : Unsatisfiable (PosFin 57) f2060 := by
  apply lratCheckerSound f2060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2060
  · intro a ha; simp [p2060] at ha; subst a; trivial
  · exact checked2060
theorem derived2060 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2060 := by
  apply localUnsat_implies_entails f2060 [c2006, c266, c2059, c2010, c263, c2051, c3, c34, c1100, c109, c110, c2013] c2060 unsat2060 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c2059 := derived2059 a h
  have h3 : Entails.eval a c2010 := derived2010 a h
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c2051 := derived2051 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c1100 := derived1100 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c2013 := derived2013 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2061 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2061 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c2059, some c2010, some c263, some c2051, some c1967, some c1147, some c2060, some c264, some c1254, some c26, some c109, some c110, some c4, some c24, some c844, some c10, some c15, some c199, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2061 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2061 : lratChecker f2061 p2061 = .success := by decide +kernel
theorem unsat2061 : Unsatisfiable (PosFin 57) f2061 := by
  apply lratCheckerSound f2061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2061
  · intro a ha; simp [p2061] at ha; subst a; trivial
  · exact checked2061
theorem derived2061 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2061 := by
  apply localUnsat_implies_entails f2061 [c2006, c1829, c266, c2059, c2010, c263, c2051, c1967, c1147, c2060, c264, c1254, c26, c109, c110, c4, c24, c844, c10, c15, c199] c2061 unsat2061 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2059 := derived2059 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c2051 := derived2051 a h
  have h7 : Entails.eval a c1967 := derived1967 a h
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c2060 := derived2060 a h
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c1254 := derived1254 a h
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c109 := h 108 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c24 := h 23 (by decide)
  have h17 : Entails.eval a c844 := derived844 a h
  have h18 : Entails.eval a c10 := h 9 (by decide)
  have h19 : Entails.eval a c15 := h 14 (by decide)
  have h20 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2062 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2062 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2006, some c266, some c2059, some c2010, some c2061, some c2027, some c263, some c2051, some c3, some c1100, some c973, some c64, some c23, some c163, some c27, some c34, some c1147, some c202, some c201, some c1987, some c2038, some c971, some c58, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2062 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2062 : lratChecker f2062 p2062 = .success := by decide +kernel
theorem unsat2062 : Unsatisfiable (PosFin 57) f2062 := by
  apply lratCheckerSound f2062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2062
  · intro a ha; simp [p2062] at ha; subst a; trivial
  · exact checked2062
theorem derived2062 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2062 := by
  apply localUnsat_implies_entails f2062 [c1829, c2006, c266, c2059, c2010, c2061, c2027, c263, c2051, c3, c1100, c973, c64, c23, c163, c27, c34, c1147, c202, c201, c1987, c2038, c971, c58] c2062 unsat2062 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2059 := derived2059 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c2061 := derived2061 a h
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c2051 := derived2051 a h
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1100 := derived1100 a h
  have h11 : Entails.eval a c973 := derived973 a h
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c163 := h 162 (by decide)
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c34 := h 33 (by decide)
  have h17 : Entails.eval a c1147 := derived1147 a h
  have h18 : Entails.eval a c202 := h 201 (by decide)
  have h19 : Entails.eval a c201 := h 200 (by decide)
  have h20 : Entails.eval a c1987 := derived1987 a h
  have h21 : Entails.eval a c2038 := derived2038 a h
  have h22 : Entails.eval a c971 := derived971 a h
  have h23 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2063 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2063 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2006, some c266, some c2059, some c2010, some c2061, some c2027, some c263, some c2051, some c1967, some c1147, some c3, some c23, some c34, some c1100, some c163, some c973, some c27, some c64, some c2062, some c12, some c9, some c812, some c1236, some c154, some c216, some c65, some c55, some c275, some c140, some c134, some c236, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2063 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked2063 : lratChecker f2063 p2063 = .success := by decide +kernel
theorem unsat2063 : Unsatisfiable (PosFin 57) f2063 := by
  apply lratCheckerSound f2063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2063
  · intro a ha; simp [p2063] at ha; subst a; trivial
  · exact checked2063
theorem derived2063 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2063 := by
  apply localUnsat_implies_entails f2063 [c1829, c2006, c266, c2059, c2010, c2061, c2027, c263, c2051, c1967, c1147, c3, c23, c34, c1100, c163, c973, c27, c64, c2062, c12, c9, c812, c1236, c154, c216, c65, c55, c275, c140, c134, c236] c2063 unsat2063 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2059 := derived2059 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c2061 := derived2061 a h
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c2051 := derived2051 a h
  have h9 : Entails.eval a c1967 := derived1967 a h
  have h10 : Entails.eval a c1147 := derived1147 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c1100 := derived1100 a h
  have h15 : Entails.eval a c163 := h 162 (by decide)
  have h16 : Entails.eval a c973 := derived973 a h
  have h17 : Entails.eval a c27 := h 26 (by decide)
  have h18 : Entails.eval a c64 := h 63 (by decide)
  have h19 : Entails.eval a c2062 := derived2062 a h
  have h20 : Entails.eval a c12 := h 11 (by decide)
  have h21 : Entails.eval a c9 := h 8 (by decide)
  have h22 : Entails.eval a c812 := derived812 a h
  have h23 : Entails.eval a c1236 := derived1236 a h
  have h24 : Entails.eval a c154 := h 153 (by decide)
  have h25 : Entails.eval a c216 := h 215 (by decide)
  have h26 : Entails.eval a c65 := h 64 (by decide)
  have h27 : Entails.eval a c55 := h 54 (by decide)
  have h28 : Entails.eval a c275 := h 274 (by decide)
  have h29 : Entails.eval a c140 := h 139 (by decide)
  have h30 : Entails.eval a c134 := h 133 (by decide)
  have h31 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2064 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2064 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c266, some c2051, some c2059, some c1967, some c2063, some c264, some c1254, some c26, some c1147, some c201, some c4, some c116, some c53, some c202, some c2010, some c2061, some c2027, some c263, some c2044, some c52, some c1004, some c924, some c986, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2064 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2064 : lratChecker f2064 p2064 = .success := by decide +kernel
theorem unsat2064 : Unsatisfiable (PosFin 57) f2064 := by
  apply lratCheckerSound f2064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2064
  · intro a ha; simp [p2064] at ha; subst a; trivial
  · exact checked2064
theorem derived2064 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2064 := by
  apply localUnsat_implies_entails f2064 [c2006, c266, c2051, c2059, c1967, c2063, c264, c1254, c26, c1147, c201, c4, c116, c53, c202, c2010, c2061, c2027, c263, c2044, c52, c1004, c924, c986] c2064 unsat2064 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c2051 := derived2051 a h
  have h3 : Entails.eval a c2059 := derived2059 a h
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c2063 := derived2063 a h
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c1254 := derived1254 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1147 := derived1147 a h
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c2010 := derived2010 a h
  have h16 : Entails.eval a c2061 := derived2061 a h
  have h17 : Entails.eval a c2027 := derived2027 a h
  have h18 : Entails.eval a c263 := h 262 (by decide)
  have h19 : Entails.eval a c2044 := derived2044 a h
  have h20 : Entails.eval a c52 := h 51 (by decide)
  have h21 : Entails.eval a c1004 := derived1004 a h
  have h22 : Entails.eval a c924 := derived924 a h
  have h23 : Entails.eval a c986 := derived986 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2065 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2065 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2006, some c266, some c2059, some c2010, some c263, some c2051, some c1967, some c2063, some c264, some c1254, some c228, some c2061, some c2064, some c10, some c163, some c59, some c249, some c191, some c97, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2065 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2065 : lratChecker f2065 p2065 = .success := by decide +kernel
theorem unsat2065 : Unsatisfiable (PosFin 57) f2065 := by
  apply lratCheckerSound f2065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2065
  · intro a ha; simp [p2065] at ha; subst a; trivial
  · exact checked2065
theorem derived2065 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2065 := by
  apply localUnsat_implies_entails f2065 [c1829, c2006, c266, c2059, c2010, c263, c2051, c1967, c2063, c264, c1254, c228, c2061, c2064, c10, c163, c59, c249, c191, c97] c2065 unsat2065 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2059 := derived2059 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c2051 := derived2051 a h
  have h7 : Entails.eval a c1967 := derived1967 a h
  have h8 : Entails.eval a c2063 := derived2063 a h
  have h9 : Entails.eval a c264 := h 263 (by decide)
  have h10 : Entails.eval a c1254 := derived1254 a h
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c2061 := derived2061 a h
  have h13 : Entails.eval a c2064 := derived2064 a h
  have h14 : Entails.eval a c10 := h 9 (by decide)
  have h15 : Entails.eval a c163 := h 162 (by decide)
  have h16 : Entails.eval a c59 := h 58 (by decide)
  have h17 : Entails.eval a c249 := h 248 (by decide)
  have h18 : Entails.eval a c191 := h 190 (by decide)
  have h19 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2066 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2066 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c2065, some c266, some c2059, some c2010, some c263, some c2051, some c1967, some c2063, some c264, some c1254, some c26, some c1147, some c201, some c4, some c116, some c53, some c216, some c202, some c228, some c2061, some c2027, some c155, some c2048, some c65, some c1236, some c1971, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2066 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2066 : lratChecker f2066 p2066 = .success := by decide +kernel
theorem unsat2066 : Unsatisfiable (PosFin 57) f2066 := by
  apply lratCheckerSound f2066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2066
  · intro a ha; simp [p2066] at ha; subst a; trivial
  · exact checked2066
theorem derived2066 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2066 := by
  apply localUnsat_implies_entails f2066 [c2006, c1829, c2065, c266, c2059, c2010, c263, c2051, c1967, c2063, c264, c1254, c26, c1147, c201, c4, c116, c53, c216, c202, c228, c2061, c2027, c155, c2048, c65, c1236, c1971] c2066 unsat2066 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c2065 := derived2065 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c2059 := derived2059 a h
  have h5 : Entails.eval a c2010 := derived2010 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c2051 := derived2051 a h
  have h8 : Entails.eval a c1967 := derived1967 a h
  have h9 : Entails.eval a c2063 := derived2063 a h
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c1254 := derived1254 a h
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c1147 := derived1147 a h
  have h14 : Entails.eval a c201 := h 200 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c116 := h 115 (by decide)
  have h17 : Entails.eval a c53 := h 52 (by decide)
  have h18 : Entails.eval a c216 := h 215 (by decide)
  have h19 : Entails.eval a c202 := h 201 (by decide)
  have h20 : Entails.eval a c228 := h 227 (by decide)
  have h21 : Entails.eval a c2061 := derived2061 a h
  have h22 : Entails.eval a c2027 := derived2027 a h
  have h23 : Entails.eval a c155 := h 154 (by decide)
  have h24 : Entails.eval a c2048 := derived2048 a h
  have h25 : Entails.eval a c65 := h 64 (by decide)
  have h26 : Entails.eval a c1236 := derived1236 a h
  have h27 : Entails.eval a c1971 := derived1971 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2067 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2067 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c266, some c2059, some c2010, some c263, some c2051, some c1967, some c2063, some c264, some c1254, some c228, some c26, some c2061, some c2027, some c1147, some c202, some c201, some c4, some c116, some c53, some c216, some c2065, some c2066, some c2046, some c56, some c284, some c64, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2067 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2067 : lratChecker f2067 p2067 = .success := by decide +kernel
theorem unsat2067 : Unsatisfiable (PosFin 57) f2067 := by
  apply lratCheckerSound f2067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2067
  · intro a ha; simp [p2067] at ha; subst a; trivial
  · exact checked2067
theorem derived2067 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2067 := by
  apply localUnsat_implies_entails f2067 [c2006, c266, c2059, c2010, c263, c2051, c1967, c2063, c264, c1254, c228, c26, c2061, c2027, c1147, c202, c201, c4, c116, c53, c216, c2065, c2066, c2046, c56, c284, c64] c2067 unsat2067 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c2059 := derived2059 a h
  have h3 : Entails.eval a c2010 := derived2010 a h
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c2051 := derived2051 a h
  have h6 : Entails.eval a c1967 := derived1967 a h
  have h7 : Entails.eval a c2063 := derived2063 a h
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c1254 := derived1254 a h
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c2061 := derived2061 a h
  have h13 : Entails.eval a c2027 := derived2027 a h
  have h14 : Entails.eval a c1147 := derived1147 a h
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c116 := h 115 (by decide)
  have h19 : Entails.eval a c53 := h 52 (by decide)
  have h20 : Entails.eval a c216 := h 215 (by decide)
  have h21 : Entails.eval a c2065 := derived2065 a h
  have h22 : Entails.eval a c2066 := derived2066 a h
  have h23 : Entails.eval a c2046 := derived2046 a h
  have h24 : Entails.eval a c56 := h 55 (by decide)
  have h25 : Entails.eval a c284 := h 283 (by decide)
  have h26 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2068 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2068 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c1147, some c2051, some c2059, some c2010, some c1967, some c263, some c2061, some c2063, some c264, some c1254, some c228, some c2067, some c9, some c155, some c66, some c57, some c353, some c182, some c226, some c343, some c245, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2068 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2068 : lratChecker f2068 p2068 = .success := by decide +kernel
theorem unsat2068 : Unsatisfiable (PosFin 57) f2068 := by
  apply lratCheckerSound f2068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2068
  · intro a ha; simp [p2068] at ha; subst a; trivial
  · exact checked2068
theorem derived2068 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2068 := by
  apply localUnsat_implies_entails f2068 [c2006, c1829, c266, c1147, c2051, c2059, c2010, c1967, c263, c2061, c2063, c264, c1254, c228, c2067, c9, c155, c66, c57, c353, c182, c226, c343, c245] c2068 unsat2068 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c2051 := derived2051 a h
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c2010 := derived2010 a h
  have h7 : Entails.eval a c1967 := derived1967 a h
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c2061 := derived2061 a h
  have h10 : Entails.eval a c2063 := derived2063 a h
  have h11 : Entails.eval a c264 := h 263 (by decide)
  have h12 : Entails.eval a c1254 := derived1254 a h
  have h13 : Entails.eval a c228 := h 227 (by decide)
  have h14 : Entails.eval a c2067 := derived2067 a h
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c155 := h 154 (by decide)
  have h17 : Entails.eval a c66 := h 65 (by decide)
  have h18 : Entails.eval a c57 := h 56 (by decide)
  have h19 : Entails.eval a c353 := h 352 (by decide)
  have h20 : Entails.eval a c182 := h 181 (by decide)
  have h21 : Entails.eval a c226 := h 225 (by decide)
  have h22 : Entails.eval a c343 := h 342 (by decide)
  have h23 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2069 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2069 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c265, some c2007, some c108, some c31, some c4, some c24, some c1974, some c112, some c20, some c604, some c62, some c193, some c246, some c95, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2069 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2069 : lratChecker f2069 p2069 = .success := by decide +kernel
theorem unsat2069 : Unsatisfiable (PosFin 57) f2069 := by
  apply lratCheckerSound f2069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2069
  · intro a ha; simp [p2069] at ha; subst a; trivial
  · exact checked2069
theorem derived2069 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2069 := by
  apply localUnsat_implies_entails f2069 [c2006, c1829, c265, c2007, c108, c31, c4, c24, c1974, c112, c20, c604, c62, c193, c246, c95] c2069 unsat2069 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c2007 := derived2007 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c1974 := derived1974 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c20 := h 19 (by decide)
  have h11 : Entails.eval a c604 := derived604 a h
  have h12 : Entails.eval a c62 := h 61 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  have h15 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2070 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨21, by decide⟩, true), (⟨35, by decide⟩, false), (⟨17, by decide⟩, false), (⟨8, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2070 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1829, some c20, some c1908, some c52, some c215, some c117, some c56, some c162, some c152, some c227, some c283, some c156, some c62, some c57, some c246, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2070 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2070 : lratChecker f2070 p2070 = .success := by decide +kernel
theorem unsat2070 : Unsatisfiable (PosFin 57) f2070 := by
  apply lratCheckerSound f2070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2070
  · intro a ha; simp [p2070] at ha; subst a; trivial
  · exact checked2070
theorem derived2070 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2070 := by
  apply localUnsat_implies_entails f2070 [c2068, c1829, c20, c1908, c52, c215, c117, c56, c162, c152, c227, c283, c156, c62, c57, c246] c2070 unsat2070 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c1908 := derived1908 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c215 := h 214 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c162 := h 161 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  have h11 : Entails.eval a c283 := h 282 (by decide)
  have h12 : Entails.eval a c156 := h 155 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2071 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2071 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c56, some c139, some c152, some c727, some c313, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2071 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2071 : lratChecker f2071 p2071 = .success := by decide +kernel
theorem unsat2071 : Unsatisfiable (PosFin 57) f2071 := by
  apply lratCheckerSound f2071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2071
  · intro a ha; simp [p2071] at ha; subst a; trivial
  · exact checked2071
theorem derived2071 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2071 := by
  apply localUnsat_implies_entails f2071 [c56, c139, c152, c727, c313] c2071 unsat2071 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c727 := derived727 a h
  have h4 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2072 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2072 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c2068, some c265, some c1931, some c116, some c4, some c1498, some c896, some c14, some c20, some c35, some c30, some c23, some c261, some c2070, some c2071, some c211, some c215, some c715, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2072 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2072 : lratChecker f2072 p2072 = .success := by decide +kernel
theorem unsat2072 : Unsatisfiable (PosFin 57) f2072 := by
  apply lratCheckerSound f2072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2072
  · intro a ha; simp [p2072] at ha; subst a; trivial
  · exact checked2072
theorem derived2072 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2072 := by
  apply localUnsat_implies_entails f2072 [c2006, c1829, c2068, c265, c1931, c116, c4, c1498, c896, c14, c20, c35, c30, c23, c261, c2070, c2071, c211, c215, c715] c2072 unsat2072 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c2068 := derived2068 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c1931 := derived1931 a h
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c1498 := derived1498 a h
  have h8 : Entails.eval a c896 := derived896 a h
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c20 := h 19 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c261 := h 260 (by decide)
  have h15 : Entails.eval a c2070 := derived2070 a h
  have h16 : Entails.eval a c2071 := derived2071 a h
  have h17 : Entails.eval a c211 := h 210 (by decide)
  have h18 : Entails.eval a c215 := h 214 (by decide)
  have h19 : Entails.eval a c715 := derived715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2073 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2073 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2068, some c1, some c21, some c1896, some c1952, some c52, some c227, some c117, some c153, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p2073 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2073 : lratChecker f2073 p2073 = .success := by decide +kernel
theorem unsat2073 : Unsatisfiable (PosFin 57) f2073 := by
  apply lratCheckerSound f2073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2073
  · intro a ha; simp [p2073] at ha; subst a; trivial
  · exact checked2073
theorem derived2073 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2073 := by
  apply localUnsat_implies_entails f2073 [c1829, c2068, c1, c21, c1896, c1952, c52, c227, c117, c153] c2073 unsat2073 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2068 := derived2068 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c1896 := derived1896 a h
  have h5 : Entails.eval a c1952 := derived1952 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2074 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2074 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1829, some c2006, some c1931, some c1498, some c265, some c896, some c14, some c28, some c982, some c156, some c66, some c57, some c162, some c246, some c181, some c98, some c337, some c249, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2074 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2074 : lratChecker f2074 p2074 = .success := by decide +kernel
theorem unsat2074 : Unsatisfiable (PosFin 57) f2074 := by
  apply lratCheckerSound f2074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2074
  · intro a ha; simp [p2074] at ha; subst a; trivial
  · exact checked2074
theorem derived2074 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2074 := by
  apply localUnsat_implies_entails f2074 [c2068, c1829, c2006, c1931, c1498, c265, c896, c14, c28, c982, c156, c66, c57, c162, c246, c181, c98, c337, c249] c2074 unsat2074 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c2006 := derived2006 a h
  have h3 : Entails.eval a c1931 := derived1931 a h
  have h4 : Entails.eval a c1498 := derived1498 a h
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c896 := derived896 a h
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c982 := derived982 a h
  have h10 : Entails.eval a c156 := h 155 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  have h15 : Entails.eval a c181 := h 180 (by decide)
  have h16 : Entails.eval a c98 := h 97 (by decide)
  have h17 : Entails.eval a c337 := h 336 (by decide)
  have h18 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2075 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2075 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c2068, some c1931, some c1498, some c265, some c4, some c116, some c2073, some c896, some c14, some c20, some c1908, some c52, some c215, some c117, some c2074, some c2070, some c56, some c66, some c70, some c152, some c156, some c281, some c225, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2075 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2075 : lratChecker f2075 p2075 = .success := by decide +kernel
theorem unsat2075 : Unsatisfiable (PosFin 57) f2075 := by
  apply lratCheckerSound f2075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2075
  · intro a ha; simp [p2075] at ha; subst a; trivial
  · exact checked2075
theorem derived2075 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2075 := by
  apply localUnsat_implies_entails f2075 [c2006, c1829, c2068, c1931, c1498, c265, c4, c116, c2073, c896, c14, c20, c1908, c52, c215, c117, c2074, c2070, c56, c66, c70, c152, c156, c281, c225] c2075 unsat2075 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c2068 := derived2068 a h
  have h3 : Entails.eval a c1931 := derived1931 a h
  have h4 : Entails.eval a c1498 := derived1498 a h
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c2073 := derived2073 a h
  have h9 : Entails.eval a c896 := derived896 a h
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c1908 := derived1908 a h
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c215 := h 214 (by decide)
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c2074 := derived2074 a h
  have h17 : Entails.eval a c2070 := derived2070 a h
  have h18 : Entails.eval a c56 := h 55 (by decide)
  have h19 : Entails.eval a c66 := h 65 (by decide)
  have h20 : Entails.eval a c70 := h 69 (by decide)
  have h21 : Entails.eval a c152 := h 151 (by decide)
  have h22 : Entails.eval a c156 := h 155 (by decide)
  have h23 : Entails.eval a c281 := h 280 (by decide)
  have h24 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2076 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2076 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c133, some c727, some c230, some c180, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2076 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2076 : lratChecker f2076 p2076 = .success := by decide +kernel
theorem unsat2076 : Unsatisfiable (PosFin 57) f2076 := by
  apply lratCheckerSound f2076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2076
  · intro a ha; simp [p2076] at ha; subst a; trivial
  · exact checked2076
theorem derived2076 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2076 := by
  apply localUnsat_implies_entails f2076 [c133, c727, c230, c180] c2076 unsat2076 (by rfl) a
  have h0 : Entails.eval a c133 := h 132 (by decide)
  have h1 : Entails.eval a c727 := derived727 a h
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2077 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2077 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c314, some c152, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2077 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2077 : lratChecker f2077 p2077 = .success := by decide +kernel
theorem unsat2077 : Unsatisfiable (PosFin 57) f2077 := by
  apply lratCheckerSound f2077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2077
  · intro a ha; simp [p2077] at ha; subst a; trivial
  · exact checked2077
theorem derived2077 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2077 := by
  apply localUnsat_implies_entails f2077 [c313, c314, c152] c2077 unsat2077 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c314 := h 313 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2078 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2078 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c2068, some c2069, some c265, some c2007, some c896, some c1931, some c20, some c1498, some c4, some c116, some c2072, some c1929, some c2073, some c2075, some c2076, some c2077, some c215, some c312, some c52, some c318, some c139, some c1380, some c707, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2078 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2078 : lratChecker f2078 p2078 = .success := by decide +kernel
theorem unsat2078 : Unsatisfiable (PosFin 57) f2078 := by
  apply lratCheckerSound f2078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2078
  · intro a ha; simp [p2078] at ha; subst a; trivial
  · exact checked2078
theorem derived2078 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2078 := by
  apply localUnsat_implies_entails f2078 [c2006, c2068, c2069, c265, c2007, c896, c1931, c20, c1498, c4, c116, c2072, c1929, c2073, c2075, c2076, c2077, c215, c312, c52, c318, c139, c1380, c707] c2078 unsat2078 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c2068 := derived2068 a h
  have h2 : Entails.eval a c2069 := derived2069 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c2007 := derived2007 a h
  have h5 : Entails.eval a c896 := derived896 a h
  have h6 : Entails.eval a c1931 := derived1931 a h
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c1498 := derived1498 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c2072 := derived2072 a h
  have h12 : Entails.eval a c1929 := derived1929 a h
  have h13 : Entails.eval a c2073 := derived2073 a h
  have h14 : Entails.eval a c2075 := derived2075 a h
  have h15 : Entails.eval a c2076 := derived2076 a h
  have h16 : Entails.eval a c2077 := derived2077 a h
  have h17 : Entails.eval a c215 := h 214 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c52 := h 51 (by decide)
  have h20 : Entails.eval a c318 := h 317 (by decide)
  have h21 : Entails.eval a c139 := h 138 (by decide)
  have h22 : Entails.eval a c1380 := derived1380 a h
  have h23 : Entails.eval a c707 := derived707 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2079 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2079 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c39, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p2079 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2079 : lratChecker f2079 p2079 = .success := by decide +kernel
theorem unsat2079 : Unsatisfiable (PosFin 57) f2079 := by
  apply lratCheckerSound f2079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2079
  · intro a ha; simp [p2079] at ha; subst a; trivial
  · exact checked2079
theorem derived2079 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2079 := by
  apply localUnsat_implies_entails f2079 [c2068, c39] c2079 unsat2079 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2080 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2080 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c21, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p2080 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2080 : lratChecker f2080 p2080 = .success := by decide +kernel
theorem unsat2080 : Unsatisfiable (PosFin 57) f2080 := by
  apply lratCheckerSound f2080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2080
  · intro a ha; simp [p2080] at ha; subst a; trivial
  · exact checked2080
theorem derived2080 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2080 := by
  apply localUnsat_implies_entails f2080 [c1829, c21] c2080 unsat2080 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2081 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2081 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c57, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p2081 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2081 : lratChecker f2081 p2081 = .success := by decide +kernel
theorem unsat2081 : Unsatisfiable (PosFin 57) f2081 := by
  apply lratCheckerSound f2081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2081
  · intro a ha; simp [p2081] at ha; subst a; trivial
  · exact checked2081
theorem derived2081 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2081 := by
  apply localUnsat_implies_entails f2081 [c1829, c57] c2081 unsat2081 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2082 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2082 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c66, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2082 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2082 : lratChecker f2082 p2082 = .success := by decide +kernel
theorem unsat2082 : Unsatisfiable (PosFin 57) f2082 := by
  apply lratCheckerSound f2082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2082
  · intro a ha; simp [p2082] at ha; subst a; trivial
  · exact checked2082
theorem derived2082 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2082 := by
  apply localUnsat_implies_entails f2082 [c1829, c66] c2082 unsat2082 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2083 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨4, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2083 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c67, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p2083 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2083 : lratChecker f2083 p2083 = .success := by decide +kernel
theorem unsat2083 : Unsatisfiable (PosFin 57) f2083 := by
  apply lratCheckerSound f2083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2083
  · intro a ha; simp [p2083] at ha; subst a; trivial
  · exact checked2083
theorem derived2083 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2083 := by
  apply localUnsat_implies_entails f2083 [c1829, c67] c2083 unsat2083 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2084 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨34, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2084 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c65, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2084 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2084 : lratChecker f2084 p2084 = .success := by decide +kernel
theorem unsat2084 : Unsatisfiable (PosFin 57) f2084 := by
  apply lratCheckerSound f2084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2084
  · intro a ha; simp [p2084] at ha; subst a; trivial
  · exact checked2084
theorem derived2084 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2084 := by
  apply localUnsat_implies_entails f2084 [c1829, c65] c2084 unsat2084 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2085 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2085 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c265, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2085 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2085 : lratChecker f2085 p2085 = .success := by decide +kernel
theorem unsat2085 : Unsatisfiable (PosFin 57) f2085 := by
  apply lratCheckerSound f2085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2085
  · intro a ha; simp [p2085] at ha; subst a; trivial
  · exact checked2085
theorem derived2085 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2085 := by
  apply localUnsat_implies_entails f2085 [c2006, c265] c2085 unsat2085 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2086 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2086 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c264, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p2086 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2086 : lratChecker f2086 p2086 = .success := by decide +kernel
theorem unsat2086 : Unsatisfiable (PosFin 57) f2086 := by
  apply lratCheckerSound f2086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2086
  · intro a ha; simp [p2086] at ha; subst a; trivial
  · exact checked2086
theorem derived2086 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2086 := by
  apply localUnsat_implies_entails f2086 [c2006, c264] c2086 unsat2086 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2087 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨30, by decide⟩, true), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨31, by decide⟩, true), (⟨15, by decide⟩, false), (⟨17, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2087 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c511, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2087 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2087 : lratChecker f2087 p2087 = .success := by decide +kernel
theorem unsat2087 : Unsatisfiable (PosFin 57) f2087 := by
  apply lratCheckerSound f2087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2087
  · intro a ha; simp [p2087] at ha; subst a; trivial
  · exact checked2087
theorem derived2087 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2087 := by
  apply localUnsat_implies_entails f2087 [c2068, c511] c2087 unsat2087 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c511 := derived511 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2088 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨46, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨9, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2088 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c2006, some c893, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p2088 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2088 : lratChecker f2088 p2088 = .success := by decide +kernel
theorem unsat2088 : Unsatisfiable (PosFin 57) f2088 := by
  apply lratCheckerSound f2088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2088
  · intro a ha; simp [p2088] at ha; subst a; trivial
  · exact checked2088
theorem derived2088 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2088 := by
  apply localUnsat_implies_entails f2088 [c2068, c2006, c893] c2088 unsat2088 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c893 := derived893 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2089 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨40, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2089 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c545, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p2089 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2089 : lratChecker f2089 p2089 = .success := by decide +kernel
theorem unsat2089 : Unsatisfiable (PosFin 57) f2089 := by
  apply lratCheckerSound f2089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2089
  · intro a ha; simp [p2089] at ha; subst a; trivial
  · exact checked2089
theorem derived2089 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2089 := by
  apply localUnsat_implies_entails f2089 [c2068, c545] c2089 unsat2089 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c545 := derived545 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2090 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2090 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c127, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p2090 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2090 : lratChecker f2090 p2090 = .success := by decide +kernel
theorem unsat2090 : Unsatisfiable (PosFin 57) f2090 := by
  apply lratCheckerSound f2090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2090
  · intro a ha; simp [p2090] at ha; subst a; trivial
  · exact checked2090
theorem derived2090 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2090 := by
  apply localUnsat_implies_entails f2090 [c2068, c127] c2090 unsat2090 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2091 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2091 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c120, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p2091 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2091 : lratChecker f2091 p2091 = .success := by decide +kernel
theorem unsat2091 : Unsatisfiable (PosFin 57) f2091 := by
  apply lratCheckerSound f2091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2091
  · intro a ha; simp [p2091] at ha; subst a; trivial
  · exact checked2091
theorem derived2091 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2091 := by
  apply localUnsat_implies_entails f2091 [c2068, c120] c2091 unsat2091 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2092 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2092 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c131, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p2092 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2092 : lratChecker f2092 p2092 = .success := by decide +kernel
theorem unsat2092 : Unsatisfiable (PosFin 57) f2092 := by
  apply lratCheckerSound f2092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2092
  · intro a ha; simp [p2092] at ha; subst a; trivial
  · exact checked2092
theorem derived2092 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2092 := by
  apply localUnsat_implies_entails f2092 [c2068, c131] c2092 unsat2092 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2093 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2093 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c8, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p2093 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2093 : lratChecker f2093 p2093 = .success := by decide +kernel
theorem unsat2093 : Unsatisfiable (PosFin 57) f2093 := by
  apply lratCheckerSound f2093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2093
  · intro a ha; simp [p2093] at ha; subst a; trivial
  · exact checked2093
theorem derived2093 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2093 := by
  apply localUnsat_implies_entails f2093 [c2068, c8] c2093 unsat2093 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2094 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2094 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c896, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2094 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2094 : lratChecker f2094 p2094 = .success := by decide +kernel
theorem unsat2094 : Unsatisfiable (PosFin 57) f2094 := by
  apply lratCheckerSound f2094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2094
  · intro a ha; simp [p2094] at ha; subst a; trivial
  · exact checked2094
theorem derived2094 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2094 := by
  apply localUnsat_implies_entails f2094 [c2068, c896] c2094 unsat2094 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c896 := derived896 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2095 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2095 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c982, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p2095 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2095 : lratChecker f2095 p2095 = .success := by decide +kernel
theorem unsat2095 : Unsatisfiable (PosFin 57) f2095 := by
  apply lratCheckerSound f2095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2095
  · intro a ha; simp [p2095] at ha; subst a; trivial
  · exact checked2095
theorem derived2095 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2095 := by
  apply localUnsat_implies_entails f2095 [c2068, c982] c2095 unsat2095 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c982 := derived982 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2096 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2096 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c11, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2096 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2096 : lratChecker f2096 p2096 = .success := by decide +kernel
theorem unsat2096 : Unsatisfiable (PosFin 57) f2096 := by
  apply lratCheckerSound f2096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2096
  · intro a ha; simp [p2096] at ha; subst a; trivial
  · exact checked2096
theorem derived2096 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2096 := by
  apply localUnsat_implies_entails f2096 [c1829, c11] c2096 unsat2096 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2097 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2097 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c129, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2097 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2097 : lratChecker f2097 p2097 = .success := by decide +kernel
theorem unsat2097 : Unsatisfiable (PosFin 57) f2097 := by
  apply lratCheckerSound f2097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2097
  · intro a ha; simp [p2097] at ha; subst a; trivial
  · exact checked2097
theorem derived2097 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2097 := by
  apply localUnsat_implies_entails f2097 [c2068, c129] c2097 unsat2097 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2098 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨9, by decide⟩, true), (⟨20, by decide⟩, true), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2098 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1005, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p2098 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2098 : lratChecker f2098 p2098 = .success := by decide +kernel
theorem unsat2098 : Unsatisfiable (PosFin 57) f2098 := by
  apply lratCheckerSound f2098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2098
  · intro a ha; simp [p2098] at ha; subst a; trivial
  · exact checked2098
theorem derived2098 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2098 := by
  apply localUnsat_implies_entails f2098 [c1829, c1005] c2098 unsat2098 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1005 := derived1005 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2099 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨38, by decide⟩, false), (⟨4, by decide⟩, true), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2099 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c967, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p2099 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2099 : lratChecker f2099 p2099 = .success := by decide +kernel
theorem unsat2099 : Unsatisfiable (PosFin 57) f2099 := by
  apply lratCheckerSound f2099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2099
  · intro a ha; simp [p2099] at ha; subst a; trivial
  · exact checked2099
theorem derived2099 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2099 := by
  apply localUnsat_implies_entails f2099 [c1829, c967] c2099 unsat2099 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c967 := derived967 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2100 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2100 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c885, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p2100 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2100 : lratChecker f2100 p2100 = .success := by decide +kernel
theorem unsat2100 : Unsatisfiable (PosFin 57) f2100 := by
  apply lratCheckerSound f2100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2100
  · intro a ha; simp [p2100] at ha; subst a; trivial
  · exact checked2100
theorem derived2100 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2100 := by
  apply localUnsat_implies_entails f2100 [c2068, c885] c2100 unsat2100 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c885 := derived885 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2101 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2101 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c35, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2101 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2101 : lratChecker f2101 p2101 = .success := by decide +kernel
theorem unsat2101 : Unsatisfiable (PosFin 57) f2101 := by
  apply lratCheckerSound f2101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2101
  · intro a ha; simp [p2101] at ha; subst a; trivial
  · exact checked2101
theorem derived2101 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2101 := by
  apply localUnsat_implies_entails f2101 [c2068, c35] c2101 unsat2101 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2102 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, false), (⟨31, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2102 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c902, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2102 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2102 : lratChecker f2102 p2102 = .success := by decide +kernel
theorem unsat2102 : Unsatisfiable (PosFin 57) f2102 := by
  apply lratCheckerSound f2102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2102
  · intro a ha; simp [p2102] at ha; subst a; trivial
  · exact checked2102
theorem derived2102 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2102 := by
  apply localUnsat_implies_entails f2102 [c2068, c902] c2102 unsat2102 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c902 := derived902 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2103 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2103 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c468, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p2103 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2103 : lratChecker f2103 p2103 = .success := by decide +kernel
theorem unsat2103 : Unsatisfiable (PosFin 57) f2103 := by
  apply lratCheckerSound f2103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2103
  · intro a ha; simp [p2103] at ha; subst a; trivial
  · exact checked2103
theorem derived2103 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2103 := by
  apply localUnsat_implies_entails f2103 [c1829, c468] c2103 unsat2103 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c468 := derived468 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2104 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2104 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c30, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2104 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2104 : lratChecker f2104 p2104 = .success := by decide +kernel
theorem unsat2104 : Unsatisfiable (PosFin 57) f2104 := by
  apply lratCheckerSound f2104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2104
  · intro a ha; simp [p2104] at ha; subst a; trivial
  · exact checked2104
theorem derived2104 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2104 := by
  apply localUnsat_implies_entails f2104 [c1829, c30] c2104 unsat2104 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2105 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2105 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c250, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p2105 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2105 : lratChecker f2105 p2105 = .success := by decide +kernel
theorem unsat2105 : Unsatisfiable (PosFin 57) f2105 := by
  apply lratCheckerSound f2105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2105
  · intro a ha; simp [p2105] at ha; subst a; trivial
  · exact checked2105
theorem derived2105 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2105 := by
  apply localUnsat_implies_entails f2105 [c2006, c250] c2105 unsat2105 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2106 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨51, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2106 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c94, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2106 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2106 : lratChecker f2106 p2106 = .success := by decide +kernel
theorem unsat2106 : Unsatisfiable (PosFin 57) f2106 := by
  apply lratCheckerSound f2106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2106
  · intro a ha; simp [p2106] at ha; subst a; trivial
  · exact checked2106
theorem derived2106 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2106 := by
  apply localUnsat_implies_entails f2106 [c1829, c94] c2106 unsat2106 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2107 : DefaultClause 57 := directClause ((⟨49, by decide⟩, true) :: (⟨46, by decide⟩, true) :: (⟨2, by decide⟩, false) :: (⟨4, by decide⟩, false) :: (⟨6, by decide⟩, true) :: (⟨7, by decide⟩, false) :: (⟨8, by decide⟩, false) :: (⟨3, by decide⟩, true) :: (⟨5, by decide⟩, true) :: (⟨11, by decide⟩, false) :: (⟨54, by decide⟩, true) :: (⟨9, by decide⟩, true) :: (⟨10, by decide⟩, true) :: (⟨15, by decide⟩, false) :: (⟨14, by decide⟩, false) :: (⟨17, by decide⟩, false) :: (⟨16, by decide⟩, false) :: (⟨19, by decide⟩, true) :: (⟨20, by decide⟩, true) :: (⟨21, by decide⟩, false) :: (⟨13, by decide⟩, true) :: (⟨23, by decide⟩, true) :: (⟨26, by decide⟩, true) :: (⟨12, by decide⟩, true) :: (⟨27, by decide⟩, true) :: (⟨29, by decide⟩, false) :: (⟨25, by decide⟩, false) :: (⟨31, by decide⟩, true) :: (⟨32, by decide⟩, false) :: (⟨28, by decide⟩, false) :: (⟨22, by decide⟩, false) :: (⟨30, by decide⟩, true) :: (⟨35, by decide⟩, false) :: (⟨34, by decide⟩, true) :: (⟨33, by decide⟩, false) :: (⟨38, by decide⟩, false) :: (⟨39, by decide⟩, true) :: (⟨52, by decide⟩, true) :: (⟨40, by decide⟩, true) :: (⟨42, by decide⟩, false) :: (⟨36, by decide⟩, false) :: (⟨41, by decide⟩, false) :: (⟨37, by decide⟩, true) :: (⟨47, by decide⟩, false) :: (⟨44, by decide⟩, true) :: (⟨45, by decide⟩, true) :: (⟨43, by decide⟩, false) :: (⟨48, by decide⟩, true) :: (⟨51, by decide⟩, false) :: (⟨53, by decide⟩, false) :: (⟨50, by decide⟩, false) :: (⟨55, by decide⟩, true) :: (⟨56, by decide⟩, false) :: []) (by decide +kernel) (by decide +kernel)
def f2107 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2068, some c2006, some c413, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p2107 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2107 : lratChecker f2107 p2107 = .success := by decide +kernel
theorem unsat2107 : Unsatisfiable (PosFin 57) f2107 := by
  apply lratCheckerSound f2107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2107
  · intro a ha; simp [p2107] at ha; subst a; trivial
  · exact checked2107
theorem derived2107 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2107 := by
  apply localUnsat_implies_entails f2107 [c1829, c2068, c2006, c413] c2107 unsat2107 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2068 := derived2068 a h
  have h2 : Entails.eval a c2006 := derived2006 a h
  have h3 : Entails.eval a c413 := h 412 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2108 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2108 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c93, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2108 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2108 : lratChecker f2108 p2108 = .success := by decide +kernel
theorem unsat2108 : Unsatisfiable (PosFin 57) f2108 := by
  apply lratCheckerSound f2108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2108
  · intro a ha; simp [p2108] at ha; subst a; trivial
  · exact checked2108
theorem derived2108 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2108 := by
  apply localUnsat_implies_entails f2108 [c1829, c93] c2108 unsat2108 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2109 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2109 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c976, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p2109 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2109 : lratChecker f2109 p2109 = .success := by decide +kernel
theorem unsat2109 : Unsatisfiable (PosFin 57) f2109 := by
  apply lratCheckerSound f2109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2109
  · intro a ha; simp [p2109] at ha; subst a; trivial
  · exact checked2109
theorem derived2109 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2109 := by
  apply localUnsat_implies_entails f2109 [c2068, c976] c2109 unsat2109 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c976 := derived976 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2110 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2110 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c973, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2110 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2110 : lratChecker f2110 p2110 = .success := by decide +kernel
theorem unsat2110 : Unsatisfiable (PosFin 57) f2110 := by
  apply lratCheckerSound f2110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2110
  · intro a ha; simp [p2110] at ha; subst a; trivial
  · exact checked2110
theorem derived2110 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2110 := by
  apply localUnsat_implies_entails f2110 [c1829, c973] c2110 unsat2110 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c973 := derived973 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2111 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨36, by decide⟩, false), (⟨2, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, false), (⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2111 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c550, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p2111 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2111 : lratChecker f2111 p2111 = .success := by decide +kernel
theorem unsat2111 : Unsatisfiable (PosFin 57) f2111 := by
  apply lratCheckerSound f2111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2111
  · intro a ha; simp [p2111] at ha; subst a; trivial
  · exact checked2111
theorem derived2111 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2111 := by
  apply localUnsat_implies_entails f2111 [c1829, c550] c2111 unsat2111 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c550 := derived550 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2112 : DefaultClause 57 := directClause ((⟨43, by decide⟩, false) :: (⟨42, by decide⟩, false) :: (⟨3, by decide⟩, false) :: (⟨54, by decide⟩, true) :: (⟨6, by decide⟩, false) :: (⟨4, by decide⟩, true) :: (⟨5, by decide⟩, true) :: (⟨7, by decide⟩, false) :: (⟨2, by decide⟩, true) :: (⟨10, by decide⟩, false) :: (⟨12, by decide⟩, false) :: (⟨11, by decide⟩, true) :: (⟨8, by decide⟩, false) :: (⟨15, by decide⟩, false) :: (⟨9, by decide⟩, true) :: (⟨16, by decide⟩, false) :: (⟨14, by decide⟩, true) :: (⟨19, by decide⟩, true) :: (⟨21, by decide⟩, false) :: (⟨17, by decide⟩, false) :: (⟨23, by decide⟩, true) :: (⟨22, by decide⟩, false) :: (⟨25, by decide⟩, false) :: (⟨26, by decide⟩, true) :: (⟨27, by decide⟩, false) :: (⟨29, by decide⟩, true) :: (⟨20, by decide⟩, true) :: (⟨56, by decide⟩, true) :: (⟨13, by decide⟩, true) :: (⟨31, by decide⟩, true) :: (⟨30, by decide⟩, false) :: (⟨35, by decide⟩, true) :: (⟨36, by decide⟩, false) :: (⟨28, by decide⟩, false) :: (⟨32, by decide⟩, true) :: (⟨33, by decide⟩, false) :: (⟨40, by decide⟩, false) :: (⟨34, by decide⟩, true) :: (⟨41, by decide⟩, true) :: (⟨37, by decide⟩, false) :: (⟨44, by decide⟩, true) :: (⟨45, by decide⟩, false) :: (⟨38, by decide⟩, true) :: (⟨46, by decide⟩, true) :: (⟨48, by decide⟩, false) :: (⟨49, by decide⟩, false) :: (⟨39, by decide⟩, true) :: (⟨47, by decide⟩, true) :: (⟨52, by decide⟩, true) :: (⟨51, by decide⟩, false) :: (⟨53, by decide⟩, true) :: (⟨50, by decide⟩, false) :: (⟨55, by decide⟩, false) :: []) (by decide +kernel) (by decide +kernel)
def f2112 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2006, some c2068, some c412, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p2112 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2112 : lratChecker f2112 p2112 = .success := by decide +kernel
theorem unsat2112 : Unsatisfiable (PosFin 57) f2112 := by
  apply lratCheckerSound f2112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2112
  · intro a ha; simp [p2112] at ha; subst a; trivial
  · exact checked2112
theorem derived2112 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2112 := by
  apply localUnsat_implies_entails f2112 [c1829, c2006, c2068, c412] c2112 unsat2112 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c2068 := derived2068 a h
  have h3 : Entails.eval a c412 := h 411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2113 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨17, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2113 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c963, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p2113 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2113 : lratChecker f2113 p2113 = .success := by decide +kernel
theorem unsat2113 : Unsatisfiable (PosFin 57) f2113 := by
  apply lratCheckerSound f2113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2113
  · intro a ha; simp [p2113] at ha; subst a; trivial
  · exact checked2113
theorem derived2113 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2113 := by
  apply localUnsat_implies_entails f2113 [c1829, c963] c2113 unsat2113 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c963 := derived963 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived2113

end CochromaticTwenty.Certificates.B16_0_2Enumerating
