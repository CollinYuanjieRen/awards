import MerLeanExperiment.Certificates.B16_8_2.Steps1400_1499

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1881 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1874, some c1779, some c98, some c1860, some c97, some c71, some c841, some c72, some c1671, some c77, some c1873, some c320, some c1872, some c347, some c370, some c352, some c342, some c1877, some c1880, some c168, some c210, some c209, some c2, some c13, some c256, some c107, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1881 : lratChecker f1881 p1881 = .success := by decide +kernel
theorem unsat1881 : Unsatisfiable (PosFin 57) f1881 := by
  apply lratCheckerSound f1881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1881
  · intro a ha; simp [p1881] at ha; subst a; trivial
  · exact checked1881
theorem derived1881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1881 := by
  apply localUnsat_implies_entails f1881 [c1874, c1779, c98, c1860, c97, c71, c841, c72, c1671, c77, c1873, c320, c1872, c347, c370, c352, c342, c1877, c1880, c168, c210, c209, c2, c13, c256, c107] c1881 unsat1881 (by rfl) a
  have h0 : Entails.eval a c1874 := derived1874 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1860 := derived1860 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c1671 := derived1671 a h
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c1873 := derived1873 a h
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c1872 := derived1872 a h
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c370 := h 369 (by decide)
  have h15 : Entails.eval a c352 := h 351 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c1877 := derived1877 a h
  have h18 : Entails.eval a c1880 := derived1880 a h
  have h19 : Entails.eval a c168 := h 167 (by decide)
  have h20 : Entails.eval a c210 := h 209 (by decide)
  have h21 : Entails.eval a c209 := h 208 (by decide)
  have h22 : Entails.eval a c2 := h 1 (by decide)
  have h23 : Entails.eval a c13 := h 12 (by decide)
  have h24 : Entails.eval a c256 := h 255 (by decide)
  have h25 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1882 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c97, some c71, some c841, some c1779, some c98, some c1874, some c103, some c91, some c380, some c1881, some c1671, some c72, some c77, some c1873, some c320, some c34, some c280, some c47, some c308, some c277, some c370, some c17, some c18, some c212, some c218, some c1866, some c228, some c147, some c205, some c179, some c226, some c256, some c1491, some c111, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1882 : lratChecker f1882 p1882 = .success := by decide +kernel
theorem unsat1882 : Unsatisfiable (PosFin 57) f1882 := by
  apply lratCheckerSound f1882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1882
  · intro a ha; simp [p1882] at ha; subst a; trivial
  · exact checked1882
theorem derived1882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1882 := by
  apply localUnsat_implies_entails f1882 [c1860, c97, c71, c841, c1779, c98, c1874, c103, c91, c380, c1881, c1671, c72, c77, c1873, c320, c34, c280, c47, c308, c277, c370, c17, c18, c212, c218, c1866, c228, c147, c205, c179, c226, c256, c1491, c111] c1882 unsat1882 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c1779 := derived1779 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c1874 := derived1874 a h
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c1881 := derived1881 a h
  have h11 : Entails.eval a c1671 := derived1671 a h
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c77 := h 76 (by decide)
  have h14 : Entails.eval a c1873 := derived1873 a h
  have h15 : Entails.eval a c320 := h 319 (by decide)
  have h16 : Entails.eval a c34 := h 33 (by decide)
  have h17 : Entails.eval a c280 := h 279 (by decide)
  have h18 : Entails.eval a c47 := h 46 (by decide)
  have h19 : Entails.eval a c308 := h 307 (by decide)
  have h20 : Entails.eval a c277 := h 276 (by decide)
  have h21 : Entails.eval a c370 := h 369 (by decide)
  have h22 : Entails.eval a c17 := h 16 (by decide)
  have h23 : Entails.eval a c18 := h 17 (by decide)
  have h24 : Entails.eval a c212 := h 211 (by decide)
  have h25 : Entails.eval a c218 := h 217 (by decide)
  have h26 : Entails.eval a c1866 := derived1866 a h
  have h27 : Entails.eval a c228 := h 227 (by decide)
  have h28 : Entails.eval a c147 := h 146 (by decide)
  have h29 : Entails.eval a c205 := h 204 (by decide)
  have h30 : Entails.eval a c179 := h 178 (by decide)
  have h31 : Entails.eval a c226 := h 225 (by decide)
  have h32 : Entails.eval a c256 := h 255 (by decide)
  have h33 : Entails.eval a c1491 := derived1491 a h
  have h34 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1883 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1779, some c98, some c1671, some c97, some c71, some c77, some c841, some c72, some c1872, some c1873, some c347, some c320, some c34, some c280, some c1874, some c103, some c47, some c91, some c308, some c299, some c339, some c1882, some c210, some c209, some c247, some c256, some c204, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1883 : lratChecker f1883 p1883 = .success := by decide +kernel
theorem unsat1883 : Unsatisfiable (PosFin 57) f1883 := by
  apply lratCheckerSound f1883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1883
  · intro a ha; simp [p1883] at ha; subst a; trivial
  · exact checked1883
theorem derived1883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1883 := by
  apply localUnsat_implies_entails f1883 [c1860, c1779, c98, c1671, c97, c71, c77, c841, c72, c1872, c1873, c347, c320, c34, c280, c1874, c103, c47, c91, c308, c299, c339, c1882, c210, c209, c247, c256, c204] c1883 unsat1883 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c1872 := derived1872 a h
  have h10 : Entails.eval a c1873 := derived1873 a h
  have h11 : Entails.eval a c347 := h 346 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c280 := h 279 (by decide)
  have h15 : Entails.eval a c1874 := derived1874 a h
  have h16 : Entails.eval a c103 := h 102 (by decide)
  have h17 : Entails.eval a c47 := h 46 (by decide)
  have h18 : Entails.eval a c91 := h 90 (by decide)
  have h19 : Entails.eval a c308 := h 307 (by decide)
  have h20 : Entails.eval a c299 := h 298 (by decide)
  have h21 : Entails.eval a c339 := h 338 (by decide)
  have h22 : Entails.eval a c1882 := derived1882 a h
  have h23 : Entails.eval a c210 := h 209 (by decide)
  have h24 : Entails.eval a c209 := h 208 (by decide)
  have h25 : Entails.eval a c247 := h 246 (by decide)
  have h26 : Entails.eval a c256 := h 255 (by decide)
  have h27 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1884 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨22, by decide⟩, true), (⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1860, some c1779, some c98, some c1671, some c88, some c95, some c980, some c336, some c378, some c841, some c366, some c370, some c327, some c34, some c71, some c155, some c194, some c3, some c146, some c157, some c178, some c123, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1884 : lratChecker f1884 p1884 = .success := by decide +kernel
theorem unsat1884 : Unsatisfiable (PosFin 57) f1884 := by
  apply lratCheckerSound f1884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1884
  · intro a ha; simp [p1884] at ha; subst a; trivial
  · exact checked1884
theorem derived1884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1884 := by
  apply localUnsat_implies_entails f1884 [c1883, c1860, c1779, c98, c1671, c88, c95, c980, c336, c378, c841, c366, c370, c327, c34, c71, c155, c194, c3, c146, c157, c178, c123] c1884 unsat1884 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c980 := derived980 a h
  have h8 : Entails.eval a c336 := h 335 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c366 := h 365 (by decide)
  have h12 : Entails.eval a c370 := h 369 (by decide)
  have h13 : Entails.eval a c327 := h 326 (by decide)
  have h14 : Entails.eval a c34 := h 33 (by decide)
  have h15 : Entails.eval a c71 := h 70 (by decide)
  have h16 : Entails.eval a c155 := h 154 (by decide)
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c3 := h 2 (by decide)
  have h19 : Entails.eval a c146 := h 145 (by decide)
  have h20 : Entails.eval a c157 := h 156 (by decide)
  have h21 : Entails.eval a c178 := h 177 (by decide)
  have h22 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1885 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c155, some c71, some c1779, some c98, some c1118, some c91, some c11, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1885 : lratChecker f1885 p1885 = .success := by decide +kernel
theorem unsat1885 : Unsatisfiable (PosFin 57) f1885 := by
  apply lratCheckerSound f1885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1885
  · intro a ha; simp [p1885] at ha; subst a; trivial
  · exact checked1885
theorem derived1885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1885 := by
  apply localUnsat_implies_entails f1885 [c1860, c155, c71, c1779, c98, c1118, c91, c11] c1885 unsat1885 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c155 := h 154 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c1118 := derived1118 a h
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1886 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, false), (⟨22, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c237, some c986, some c366, some c221, some c166, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1886 : lratChecker f1886 p1886 = .success := by decide +kernel
theorem unsat1886 : Unsatisfiable (PosFin 57) f1886 := by
  apply lratCheckerSound f1886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1886
  · intro a ha; simp [p1886] at ha; subst a; trivial
  · exact checked1886
theorem derived1886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1886 := by
  apply localUnsat_implies_entails f1886 [c114, c237, c986, c366, c221, c166] c1886 unsat1886 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c237 := h 236 (by decide)
  have h2 : Entails.eval a c986 := derived986 a h
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1887 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨14, by decide⟩, false), (⟨16, by decide⟩, true), (⟨55, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1779, some c98, some c1671, some c1885, some c968, some c93, some c177, some c13, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1887 : lratChecker f1887 p1887 = .success := by decide +kernel
theorem unsat1887 : Unsatisfiable (PosFin 57) f1887 := by
  apply lratCheckerSound f1887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1887
  · intro a ha; simp [p1887] at ha; subst a; trivial
  · exact checked1887
theorem derived1887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1887 := by
  apply localUnsat_implies_entails f1887 [c1883, c1779, c98, c1671, c1885, c968, c93, c177, c13] c1887 unsat1887 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c1885 := derived1885 a h
  have h5 : Entails.eval a c968 := derived968 a h
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1888 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨53, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c240, some c237, some c115, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1888 : lratChecker f1888 p1888 = .success := by decide +kernel
theorem unsat1888 : Unsatisfiable (PosFin 57) f1888 := by
  apply lratCheckerSound f1888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1888
  · intro a ha; simp [p1888] at ha; subst a; trivial
  · exact checked1888
theorem derived1888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1888 := by
  apply localUnsat_implies_entails f1888 [c240, c237, c115] c1888 unsat1888 (by rfl) a
  have h0 : Entails.eval a c240 := h 239 (by decide)
  have h1 : Entails.eval a c237 := h 236 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1889 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨21, by decide⟩, false), (⟨24, by decide⟩, true), (⟨49, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c171, some c113, some c248, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1889 : lratChecker f1889 p1889 = .success := by decide +kernel
theorem unsat1889 : Unsatisfiable (PosFin 57) f1889 := by
  apply lratCheckerSound f1889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1889
  · intro a ha; simp [p1889] at ha; subst a; trivial
  · exact checked1889
theorem derived1889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1889 := by
  apply localUnsat_implies_entails f1889 [c171, c113, c248] c1889 unsat1889 (by rfl) a
  have h0 : Entails.eval a c171 := h 170 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1890 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨17, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c18, some c1860, some c1884, some c342, some c71, some c155, some c3, some c146, some c148, some c1886, some c1887, some c1888, some c986, some c224, some c366, some c115, some c1445, some c1889, some c185, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1890 : lratChecker f1890 p1890 = .success := by decide +kernel
theorem unsat1890 : Unsatisfiable (PosFin 57) f1890 := by
  apply lratCheckerSound f1890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1890
  · intro a ha; simp [p1890] at ha; subst a; trivial
  · exact checked1890
theorem derived1890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1890 := by
  apply localUnsat_implies_entails f1890 [c1779, c18, c1860, c1884, c342, c71, c155, c3, c146, c148, c1886, c1887, c1888, c986, c224, c366, c115, c1445, c1889, c185] c1890 unsat1890 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c1860 := derived1860 a h
  have h3 : Entails.eval a c1884 := derived1884 a h
  have h4 : Entails.eval a c342 := h 341 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c1886 := derived1886 a h
  have h11 : Entails.eval a c1887 := derived1887 a h
  have h12 : Entails.eval a c1888 := derived1888 a h
  have h13 : Entails.eval a c986 := derived986 a h
  have h14 : Entails.eval a c224 := h 223 (by decide)
  have h15 : Entails.eval a c366 := h 365 (by decide)
  have h16 : Entails.eval a c115 := h 114 (by decide)
  have h17 : Entails.eval a c1445 := derived1445 a h
  have h18 : Entails.eval a c1889 := derived1889 a h
  have h19 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1891 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨48, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c163, some c11, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1891 : lratChecker f1891 p1891 = .success := by decide +kernel
theorem unsat1891 : Unsatisfiable (PosFin 57) f1891 := by
  apply lratCheckerSound f1891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1891
  · intro a ha; simp [p1891] at ha; subst a; trivial
  · exact checked1891
theorem derived1891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1891 := by
  apply localUnsat_implies_entails f1891 [c79, c163, c11] c1891 unsat1891 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c163 := h 162 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1892 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c352, some c347, some c1883, some c1860, some c1779, some c98, some c1671, some c18, some c1890, some c72, some c1117, some c83, some c841, some c71, some c155, some c146, some c148, some c1891, some c976, some c360, some c81, some c165, some c968, some c13, some c1118, some c114, some c11, some c184, some c221, some c230, some c35, some c1637, some c986, some c157, some c214, some c413, some c292, some c277, some c649, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]]
theorem checked1892 : lratChecker f1892 p1892 = .success := by decide +kernel
theorem unsat1892 : Unsatisfiable (PosFin 57) f1892 := by
  apply lratCheckerSound f1892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1892
  · intro a ha; simp [p1892] at ha; subst a; trivial
  · exact checked1892
theorem derived1892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1892 := by
  apply localUnsat_implies_entails f1892 [c352, c347, c1883, c1860, c1779, c98, c1671, c18, c1890, c72, c1117, c83, c841, c71, c155, c146, c148, c1891, c976, c360, c81, c165, c968, c13, c1118, c114, c11, c184, c221, c230, c35, c1637, c986, c157, c214, c413, c292, c277, c649] c1892 unsat1892 (by rfl) a
  have h0 : Entails.eval a c352 := h 351 (by decide)
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c1883 := derived1883 a h
  have h3 : Entails.eval a c1860 := derived1860 a h
  have h4 : Entails.eval a c1779 := derived1779 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c1890 := derived1890 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c1117 := derived1117 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c841 := derived841 a h
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c148 := h 147 (by decide)
  have h17 : Entails.eval a c1891 := derived1891 a h
  have h18 : Entails.eval a c976 := derived976 a h
  have h19 : Entails.eval a c360 := h 359 (by decide)
  have h20 : Entails.eval a c81 := h 80 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c968 := derived968 a h
  have h23 : Entails.eval a c13 := h 12 (by decide)
  have h24 : Entails.eval a c1118 := derived1118 a h
  have h25 : Entails.eval a c114 := h 113 (by decide)
  have h26 : Entails.eval a c11 := h 10 (by decide)
  have h27 : Entails.eval a c184 := h 183 (by decide)
  have h28 : Entails.eval a c221 := h 220 (by decide)
  have h29 : Entails.eval a c230 := h 229 (by decide)
  have h30 : Entails.eval a c35 := h 34 (by decide)
  have h31 : Entails.eval a c1637 := derived1637 a h
  have h32 : Entails.eval a c986 := derived986 a h
  have h33 : Entails.eval a c157 := h 156 (by decide)
  have h34 : Entails.eval a c214 := h 213 (by decide)
  have h35 : Entails.eval a c413 := derived413 a h
  have h36 : Entails.eval a c292 := h 291 (by decide)
  have h37 : Entails.eval a c277 := h 276 (by decide)
  have h38 : Entails.eval a c649 := derived649 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1893 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1779, some c98, some c841, some c342, some c95, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1893 : lratChecker f1893 p1893 = .success := by decide +kernel
theorem unsat1893 : Unsatisfiable (PosFin 57) f1893 := by
  apply lratCheckerSound f1893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1893
  · intro a ha; simp [p1893] at ha; subst a; trivial
  · exact checked1893
theorem derived1893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1893 := by
  apply localUnsat_implies_entails f1893 [c1883, c1779, c98, c841, c342, c95] c1893 unsat1893 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c342 := h 341 (by decide)
  have h5 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1894 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1860, some c1779, some c98, some c1671, some c95, some c1885, some c1887, some c968, some c246, some c360, some c93, some c114, some c115, some c29, some c258, some c211, some c209, some c868, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1894 : lratChecker f1894 p1894 = .success := by decide +kernel
theorem unsat1894 : Unsatisfiable (PosFin 57) f1894 := by
  apply lratCheckerSound f1894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1894
  · intro a ha; simp [p1894] at ha; subst a; trivial
  · exact checked1894
theorem derived1894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1894 := by
  apply localUnsat_implies_entails f1894 [c1883, c1860, c1779, c98, c1671, c95, c1885, c1887, c968, c246, c360, c93, c114, c115, c29, c258, c211, c209, c868] c1894 unsat1894 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c1885 := derived1885 a h
  have h7 : Entails.eval a c1887 := derived1887 a h
  have h8 : Entails.eval a c968 := derived968 a h
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c360 := h 359 (by decide)
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c258 := h 257 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  have h17 : Entails.eval a c209 := h 208 (by decide)
  have h18 : Entails.eval a c868 := derived868 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1895 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨56, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, true), (⟨35, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1860, some c1671, some c88, some c980, some c336, some c378, some c366, some c370, some c327, some c209, some c178, some c157, some c879, some c185, some c107, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1895 : lratChecker f1895 p1895 = .success := by decide +kernel
theorem unsat1895 : Unsatisfiable (PosFin 57) f1895 := by
  apply lratCheckerSound f1895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1895
  · intro a ha; simp [p1895] at ha; subst a; trivial
  · exact checked1895
theorem derived1895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1895 := by
  apply localUnsat_implies_entails f1895 [c1883, c1860, c1671, c88, c980, c336, c378, c366, c370, c327, c209, c178, c157, c879, c185, c107] c1895 unsat1895 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c980 := derived980 a h
  have h5 : Entails.eval a c336 := h 335 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c327 := h 326 (by decide)
  have h10 : Entails.eval a c209 := h 208 (by decide)
  have h11 : Entails.eval a c178 := h 177 (by decide)
  have h12 : Entails.eval a c157 := h 156 (by decide)
  have h13 : Entails.eval a c879 := derived879 a h
  have h14 : Entails.eval a c185 := h 184 (by decide)
  have h15 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1896 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨56, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨17, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c71, some c155, some c3, some c189, some c1883, some c1779, some c98, some c1671, some c1895, some c1078, some c986, some c366, some c276, some c364, some c980, some c1445, some c51, some c343, some c66, some c1771, some c320, some c166, some c209, some c185, some c879, some c107, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1896 : lratChecker f1896 p1896 = .success := by decide +kernel
theorem unsat1896 : Unsatisfiable (PosFin 57) f1896 := by
  apply lratCheckerSound f1896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1896
  · intro a ha; simp [p1896] at ha; subst a; trivial
  · exact checked1896
theorem derived1896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1896 := by
  apply localUnsat_implies_entails f1896 [c1860, c71, c155, c3, c189, c1883, c1779, c98, c1671, c1895, c1078, c986, c366, c276, c364, c980, c1445, c51, c343, c66, c1771, c320, c166, c209, c185, c879, c107] c1896 unsat1896 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c155 := h 154 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c1883 := derived1883 a h
  have h6 : Entails.eval a c1779 := derived1779 a h
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c1671 := derived1671 a h
  have h9 : Entails.eval a c1895 := derived1895 a h
  have h10 : Entails.eval a c1078 := derived1078 a h
  have h11 : Entails.eval a c986 := derived986 a h
  have h12 : Entails.eval a c366 := h 365 (by decide)
  have h13 : Entails.eval a c276 := h 275 (by decide)
  have h14 : Entails.eval a c364 := h 363 (by decide)
  have h15 : Entails.eval a c980 := derived980 a h
  have h16 : Entails.eval a c1445 := derived1445 a h
  have h17 : Entails.eval a c51 := h 50 (by decide)
  have h18 : Entails.eval a c343 := h 342 (by decide)
  have h19 : Entails.eval a c66 := h 65 (by decide)
  have h20 : Entails.eval a c1771 := derived1771 a h
  have h21 : Entails.eval a c320 := h 319 (by decide)
  have h22 : Entails.eval a c166 := h 165 (by decide)
  have h23 : Entails.eval a c209 := h 208 (by decide)
  have h24 : Entails.eval a c185 := h 184 (by decide)
  have h25 : Entails.eval a c879 := derived879 a h
  have h26 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1897 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c1883, some c1860, some c1779, some c98, some c1671, some c352, some c1892, some c210, some c1893, some c71, some c155, some c146, some c148, some c1894, some c1896, some c167, some c1891, some c976, some c230, some c360, some c81, some c165, some c115, some c968, some c13, some c1118, some c114, some c184, some c258, some c108, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1897 : lratChecker f1897 p1897 = .success := by decide +kernel
theorem unsat1897 : Unsatisfiable (PosFin 57) f1897 := by
  apply lratCheckerSound f1897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1897
  · intro a ha; simp [p1897] at ha; subst a; trivial
  · exact checked1897
theorem derived1897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1897 := by
  apply localUnsat_implies_entails f1897 [c347, c1883, c1860, c1779, c98, c1671, c352, c1892, c210, c1893, c71, c155, c146, c148, c1894, c1896, c167, c1891, c976, c230, c360, c81, c165, c115, c968, c13, c1118, c114, c184, c258, c108] c1897 unsat1897 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1860 := derived1860 a h
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c352 := h 351 (by decide)
  have h7 : Entails.eval a c1892 := derived1892 a h
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c1893 := derived1893 a h
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c146 := h 145 (by decide)
  have h13 : Entails.eval a c148 := h 147 (by decide)
  have h14 : Entails.eval a c1894 := derived1894 a h
  have h15 : Entails.eval a c1896 := derived1896 a h
  have h16 : Entails.eval a c167 := h 166 (by decide)
  have h17 : Entails.eval a c1891 := derived1891 a h
  have h18 : Entails.eval a c976 := derived976 a h
  have h19 : Entails.eval a c230 := h 229 (by decide)
  have h20 : Entails.eval a c360 := h 359 (by decide)
  have h21 : Entails.eval a c81 := h 80 (by decide)
  have h22 : Entails.eval a c165 := h 164 (by decide)
  have h23 : Entails.eval a c115 := h 114 (by decide)
  have h24 : Entails.eval a c968 := derived968 a h
  have h25 : Entails.eval a c13 := h 12 (by decide)
  have h26 : Entails.eval a c1118 := derived1118 a h
  have h27 : Entails.eval a c114 := h 113 (by decide)
  have h28 : Entails.eval a c184 := h 183 (by decide)
  have h29 : Entails.eval a c258 := h 257 (by decide)
  have h30 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1898 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1883, some c1897, some c1779, some c98, some c72, some c1005, some c76, some c66, some c1860, some c77, some c95, some c56, some c37, some c347, some c380, some c1118, some c91, some c11, some c161, some c140, some c184, some c177, some c164, some c300, some c334, some c976, some c263, some c1697, some c273, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1898 : lratChecker f1898 p1898 = .success := by decide +kernel
theorem unsat1898 : Unsatisfiable (PosFin 57) f1898 := by
  apply lratCheckerSound f1898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1898
  · intro a ha; simp [p1898] at ha; subst a; trivial
  · exact checked1898
theorem derived1898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1898 := by
  apply localUnsat_implies_entails f1898 [c1671, c1883, c1897, c1779, c98, c72, c1005, c76, c66, c1860, c77, c95, c56, c37, c347, c380, c1118, c91, c11, c161, c140, c184, c177, c164, c300, c334, c976, c263, c1697, c273] c1898 unsat1898 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1897 := derived1897 a h
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c1005 := derived1005 a h
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c1860 := derived1860 a h
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c347 := h 346 (by decide)
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c1118 := derived1118 a h
  have h17 : Entails.eval a c91 := h 90 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c140 := h 139 (by decide)
  have h21 : Entails.eval a c184 := h 183 (by decide)
  have h22 : Entails.eval a c177 := h 176 (by decide)
  have h23 : Entails.eval a c164 := h 163 (by decide)
  have h24 : Entails.eval a c300 := h 299 (by decide)
  have h25 : Entails.eval a c334 := h 333 (by decide)
  have h26 : Entails.eval a c976 := derived976 a h
  have h27 : Entails.eval a c263 := h 262 (by decide)
  have h28 : Entails.eval a c1697 := derived1697 a h
  have h29 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1899 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1671, some c1897, some c56, some c37, some c347, some c1860, some c1779, some c98, some c95, some c72, some c1005, some c77, some c66, some c76, some c1898, some c1885, some c968, some c298, some c333, some c360, some c93, some c35, some c262, some c191, some c762, some c284, some c305, some c25, some c204, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1899 : lratChecker f1899 p1899 = .success := by decide +kernel
theorem unsat1899 : Unsatisfiable (PosFin 57) f1899 := by
  apply lratCheckerSound f1899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1899
  · intro a ha; simp [p1899] at ha; subst a; trivial
  · exact checked1899
theorem derived1899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1899 := by
  apply localUnsat_implies_entails f1899 [c1883, c1671, c1897, c56, c37, c347, c1860, c1779, c98, c95, c72, c1005, c77, c66, c76, c1898, c1885, c968, c298, c333, c360, c93, c35, c262, c191, c762, c284, c305, c25, c204] c1899 unsat1899 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c1897 := derived1897 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c347 := h 346 (by decide)
  have h6 : Entails.eval a c1860 := derived1860 a h
  have h7 : Entails.eval a c1779 := derived1779 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c1005 := derived1005 a h
  have h12 : Entails.eval a c77 := h 76 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c1898 := derived1898 a h
  have h16 : Entails.eval a c1885 := derived1885 a h
  have h17 : Entails.eval a c968 := derived968 a h
  have h18 : Entails.eval a c298 := h 297 (by decide)
  have h19 : Entails.eval a c333 := h 332 (by decide)
  have h20 : Entails.eval a c360 := h 359 (by decide)
  have h21 : Entails.eval a c93 := h 92 (by decide)
  have h22 : Entails.eval a c35 := h 34 (by decide)
  have h23 : Entails.eval a c262 := h 261 (by decide)
  have h24 : Entails.eval a c191 := h 190 (by decide)
  have h25 : Entails.eval a c762 := derived762 a h
  have h26 : Entails.eval a c284 := h 283 (by decide)
  have h27 : Entails.eval a c305 := h 304 (by decide)
  have h28 : Entails.eval a c25 := h 24 (by decide)
  have h29 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1900 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1860, some c1779, some c98, some c1671, some c347, some c1897, some c37, some c56, some c1899, some c841, some c774, some c336, some c71, some c155, some c66, some c148, some c320, some c1891, some c83, some c976, some c317, some c282, some c360, some c81, some c35, some c262, some c191, some c762, some c300, some c305, some c25, some c204, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1900 : lratChecker f1900 p1900 = .success := by decide +kernel
theorem unsat1900 : Unsatisfiable (PosFin 57) f1900 := by
  apply lratCheckerSound f1900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1900
  · intro a ha; simp [p1900] at ha; subst a; trivial
  · exact checked1900
theorem derived1900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1900 := by
  apply localUnsat_implies_entails f1900 [c1883, c1860, c1779, c98, c1671, c347, c1897, c37, c56, c1899, c841, c774, c336, c71, c155, c66, c148, c320, c1891, c83, c976, c317, c282, c360, c81, c35, c262, c191, c762, c300, c305, c25, c204] c1900 unsat1900 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c347 := h 346 (by decide)
  have h6 : Entails.eval a c1897 := derived1897 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c1899 := derived1899 a h
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c774 := derived774 a h
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c148 := h 147 (by decide)
  have h17 : Entails.eval a c320 := h 319 (by decide)
  have h18 : Entails.eval a c1891 := derived1891 a h
  have h19 : Entails.eval a c83 := h 82 (by decide)
  have h20 : Entails.eval a c976 := derived976 a h
  have h21 : Entails.eval a c317 := h 316 (by decide)
  have h22 : Entails.eval a c282 := h 281 (by decide)
  have h23 : Entails.eval a c360 := h 359 (by decide)
  have h24 : Entails.eval a c81 := h 80 (by decide)
  have h25 : Entails.eval a c35 := h 34 (by decide)
  have h26 : Entails.eval a c262 := h 261 (by decide)
  have h27 : Entails.eval a c191 := h 190 (by decide)
  have h28 : Entails.eval a c762 := derived762 a h
  have h29 : Entails.eval a c300 := h 299 (by decide)
  have h30 : Entails.eval a c305 := h 304 (by decide)
  have h31 : Entails.eval a c25 := h 24 (by decide)
  have h32 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1901 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1900, some c1860, some c1671, some c77, some c57, some c320, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1901 : lratChecker f1901 p1901 = .success := by decide +kernel
theorem unsat1901 : Unsatisfiable (PosFin 57) f1901 := by
  apply lratCheckerSound f1901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1901
  · intro a ha; simp [p1901] at ha; subst a; trivial
  · exact checked1901
theorem derived1901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1901 := by
  apply localUnsat_implies_entails f1901 [c1900, c1860, c1671, c77, c57, c320] c1901 unsat1901 (by rfl) a
  have h0 : Entails.eval a c1900 := derived1900 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1902 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨7, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨39, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c1883, some c1779, some c1671, some c18, some c19, some c195, some c116, some c302, some c2, some c1004, some c1758, some c149, some c76, some c206, some c221, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1902 : lratChecker f1902 p1902 = .success := by decide +kernel
theorem unsat1902 : Unsatisfiable (PosFin 57) f1902 := by
  apply lratCheckerSound f1902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1902
  · intro a ha; simp [p1902] at ha; subst a; trivial
  · exact checked1902
theorem derived1902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1902 := by
  apply localUnsat_implies_entails f1902 [c373, c1883, c1779, c1671, c18, c19, c195, c116, c302, c2, c1004, c1758, c149, c76, c206, c221] c1902 unsat1902 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c302 := h 301 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c1004 := derived1004 a h
  have h11 : Entails.eval a c1758 := derived1758 a h
  have h12 : Entails.eval a c149 := h 148 (by decide)
  have h13 : Entails.eval a c76 := h 75 (by decide)
  have h14 : Entails.eval a c206 := h 205 (by decide)
  have h15 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1903 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨55, by decide⟩, false), (⟨37, by decide⟩, false), (⟨56, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1900, some c1883, some c1779, some c98, some c95, some c72, some c1901, some c1860, some c380, some c1118, some c91, some c11, some c1902, some c1671, some c316, some c189, some c276, some c51, some c302, some c1771, some c195, some c76, some c27, some c320, some c210, some c209, some c351, some c228, some c268, some c404, some c413, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1903 : lratChecker f1903 p1903 = .success := by decide +kernel
theorem unsat1903 : Unsatisfiable (PosFin 57) f1903 := by
  apply lratCheckerSound f1903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1903
  · intro a ha; simp [p1903] at ha; subst a; trivial
  · exact checked1903
theorem derived1903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1903 := by
  apply localUnsat_implies_entails f1903 [c1900, c1883, c1779, c98, c95, c72, c1901, c1860, c380, c1118, c91, c11, c1902, c1671, c316, c189, c276, c51, c302, c1771, c195, c76, c27, c320, c210, c209, c351, c228, c268, c404, c413] c1903 unsat1903 (by rfl) a
  have h0 : Entails.eval a c1900 := derived1900 a h
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c1901 := derived1901 a h
  have h7 : Entails.eval a c1860 := derived1860 a h
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c1118 := derived1118 a h
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c1902 := derived1902 a h
  have h13 : Entails.eval a c1671 := derived1671 a h
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c276 := h 275 (by decide)
  have h17 : Entails.eval a c51 := h 50 (by decide)
  have h18 : Entails.eval a c302 := h 301 (by decide)
  have h19 : Entails.eval a c1771 := derived1771 a h
  have h20 : Entails.eval a c195 := h 194 (by decide)
  have h21 : Entails.eval a c76 := h 75 (by decide)
  have h22 : Entails.eval a c27 := h 26 (by decide)
  have h23 : Entails.eval a c320 := h 319 (by decide)
  have h24 : Entails.eval a c210 := h 209 (by decide)
  have h25 : Entails.eval a c209 := h 208 (by decide)
  have h26 : Entails.eval a c351 := h 350 (by decide)
  have h27 : Entails.eval a c228 := h 227 (by decide)
  have h28 : Entails.eval a c268 := h 267 (by decide)
  have h29 : Entails.eval a c404 := derived404 a h
  have h30 : Entails.eval a c413 := derived413 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1904 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨37, by decide⟩, false), (⟨56, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c72, some c1901, some c1883, some c95, some c1860, some c1671, some c380, some c373, some c1118, some c91, some c11, some c1903, some c1697, some c149, some c976, some c2, some c164, some c168, some c184, some c370, some c161, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1904 : lratChecker f1904 p1904 = .success := by decide +kernel
theorem unsat1904 : Unsatisfiable (PosFin 57) f1904 := by
  apply lratCheckerSound f1904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1904
  · intro a ha; simp [p1904] at ha; subst a; trivial
  · exact checked1904
theorem derived1904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1904 := by
  apply localUnsat_implies_entails f1904 [c1779, c98, c72, c1901, c1883, c95, c1860, c1671, c380, c373, c1118, c91, c11, c1903, c1697, c149, c976, c2, c164, c168, c184, c370, c161] c1904 unsat1904 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1901 := derived1901 a h
  have h4 : Entails.eval a c1883 := derived1883 a h
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c1860 := derived1860 a h
  have h7 : Entails.eval a c1671 := derived1671 a h
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c373 := h 372 (by decide)
  have h10 : Entails.eval a c1118 := derived1118 a h
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c1903 := derived1903 a h
  have h14 : Entails.eval a c1697 := derived1697 a h
  have h15 : Entails.eval a c149 := h 148 (by decide)
  have h16 : Entails.eval a c976 := derived976 a h
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  have h19 : Entails.eval a c168 := h 167 (by decide)
  have h20 : Entails.eval a c184 := h 183 (by decide)
  have h21 : Entails.eval a c370 := h 369 (by decide)
  have h22 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1905 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c155, some c1779, some c98, some c1887, some c1074, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1905 : lratChecker f1905 p1905 = .success := by decide +kernel
theorem unsat1905 : Unsatisfiable (PosFin 57) f1905 := by
  apply lratCheckerSound f1905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1905
  · intro a ha; simp [p1905] at ha; subst a; trivial
  · exact checked1905
theorem derived1905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1905 := by
  apply localUnsat_implies_entails f1905 [c1860, c155, c1779, c98, c1887, c1074] c1905 unsat1905 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c155 := h 154 (by decide)
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1887 := derived1887 a h
  have h5 : Entails.eval a c1074 := derived1074 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1906 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1883, some c1860, some c1885, some c968, some c360, some c976, some c155, some c1779, some c98, some c72, some c1901, some c95, some c1900, some c18, some c19, some c220, some c327, some c1905, some c1886, some c162, some c1480, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1906 : lratChecker f1906 p1906 = .success := by decide +kernel
theorem unsat1906 : Unsatisfiable (PosFin 57) f1906 := by
  apply lratCheckerSound f1906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1906
  · intro a ha; simp [p1906] at ha; subst a; trivial
  · exact checked1906
theorem derived1906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1906 := by
  apply localUnsat_implies_entails f1906 [c1671, c1883, c1860, c1885, c968, c360, c976, c155, c1779, c98, c72, c1901, c95, c1900, c18, c19, c220, c327, c1905, c1886, c162, c1480] c1906 unsat1906 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1860 := derived1860 a h
  have h3 : Entails.eval a c1885 := derived1885 a h
  have h4 : Entails.eval a c968 := derived968 a h
  have h5 : Entails.eval a c360 := h 359 (by decide)
  have h6 : Entails.eval a c976 := derived976 a h
  have h7 : Entails.eval a c155 := h 154 (by decide)
  have h8 : Entails.eval a c1779 := derived1779 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c1901 := derived1901 a h
  have h12 : Entails.eval a c95 := h 94 (by decide)
  have h13 : Entails.eval a c1900 := derived1900 a h
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c220 := h 219 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  have h18 : Entails.eval a c1905 := derived1905 a h
  have h19 : Entails.eval a c1886 := derived1886 a h
  have h20 : Entails.eval a c162 := h 161 (by decide)
  have h21 : Entails.eval a c1480 := derived1480 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1907 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨37, by decide⟩, false), (⟨56, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1904, some c1906, some c1779, some c98, some c1883, some c1671, some c1885, some c968, some c93, some c95, some c338, some c72, some c1901, some c1860, some c155, some c3, some c1887, some c13, some c147, some c186, some c107, some c105, some c879, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1907 : lratChecker f1907 p1907 = .success := by decide +kernel
theorem unsat1907 : Unsatisfiable (PosFin 57) f1907 := by
  apply lratCheckerSound f1907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1907
  · intro a ha; simp [p1907] at ha; subst a; trivial
  · exact checked1907
theorem derived1907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1907 := by
  apply localUnsat_implies_entails f1907 [c1904, c1906, c1779, c98, c1883, c1671, c1885, c968, c93, c95, c338, c72, c1901, c1860, c155, c3, c1887, c13, c147, c186, c107, c105, c879] c1907 unsat1907 (by rfl) a
  have h0 : Entails.eval a c1904 := derived1904 a h
  have h1 : Entails.eval a c1906 := derived1906 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1883 := derived1883 a h
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c1885 := derived1885 a h
  have h7 : Entails.eval a c968 := derived968 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c338 := h 337 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c1901 := derived1901 a h
  have h13 : Entails.eval a c1860 := derived1860 a h
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c1887 := derived1887 a h
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c147 := h 146 (by decide)
  have h19 : Entails.eval a c186 := h 185 (by decide)
  have h20 : Entails.eval a c107 := h 106 (by decide)
  have h21 : Entails.eval a c105 := h 104 (by decide)
  have h22 : Entails.eval a c879 := derived879 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1908 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨14, by decide⟩, true), (⟨43, by decide⟩, true), (⟨35, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1671, some c370, some c1004, some c162, some c298, some c11, some c35, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1908 : lratChecker f1908 p1908 = .success := by decide +kernel
theorem unsat1908 : Unsatisfiable (PosFin 57) f1908 := by
  apply lratCheckerSound f1908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1908
  · intro a ha; simp [p1908] at ha; subst a; trivial
  · exact checked1908
theorem derived1908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1908 := by
  apply localUnsat_implies_entails f1908 [c1883, c1671, c370, c1004, c162, c298, c11, c35] c1908 unsat1908 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c1004 := derived1004 a h
  have h4 : Entails.eval a c162 := h 161 (by decide)
  have h5 : Entails.eval a c298 := h 297 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1909 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1671, some c293, some c298, some c44, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1909 : lratChecker f1909 p1909 = .success := by decide +kernel
theorem unsat1909 : Unsatisfiable (PosFin 57) f1909 := by
  apply lratCheckerSound f1909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1909
  · intro a ha; simp [p1909] at ha; subst a; trivial
  · exact checked1909
theorem derived1909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1909 := by
  apply localUnsat_implies_entails f1909 [c1883, c1671, c293, c298, c44] c1909 unsat1909 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c293 := h 292 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1910 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨56, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c72, some c1901, some c1883, some c95, some c1900, some c1860, some c1671, some c1904, some c155, some c1885, some c968, some c338, some c360, some c93, some c976, some c1907, some c1908, some c66, some c76, some c324, some c1909, some c35, some c191, some c762, some c25, some c216, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1910 : lratChecker f1910 p1910 = .success := by decide +kernel
theorem unsat1910 : Unsatisfiable (PosFin 57) f1910 := by
  apply lratCheckerSound f1910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1910
  · intro a ha; simp [p1910] at ha; subst a; trivial
  · exact checked1910
theorem derived1910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1910 := by
  apply localUnsat_implies_entails f1910 [c1779, c98, c72, c1901, c1883, c95, c1900, c1860, c1671, c1904, c155, c1885, c968, c338, c360, c93, c976, c1907, c1908, c66, c76, c324, c1909, c35, c191, c762, c25, c216] c1910 unsat1910 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1901 := derived1901 a h
  have h4 : Entails.eval a c1883 := derived1883 a h
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c1900 := derived1900 a h
  have h7 : Entails.eval a c1860 := derived1860 a h
  have h8 : Entails.eval a c1671 := derived1671 a h
  have h9 : Entails.eval a c1904 := derived1904 a h
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c1885 := derived1885 a h
  have h12 : Entails.eval a c968 := derived968 a h
  have h13 : Entails.eval a c338 := h 337 (by decide)
  have h14 : Entails.eval a c360 := h 359 (by decide)
  have h15 : Entails.eval a c93 := h 92 (by decide)
  have h16 : Entails.eval a c976 := derived976 a h
  have h17 : Entails.eval a c1907 := derived1907 a h
  have h18 : Entails.eval a c1908 := derived1908 a h
  have h19 : Entails.eval a c66 := h 65 (by decide)
  have h20 : Entails.eval a c76 := h 75 (by decide)
  have h21 : Entails.eval a c324 := h 323 (by decide)
  have h22 : Entails.eval a c1909 := derived1909 a h
  have h23 : Entails.eval a c35 := h 34 (by decide)
  have h24 : Entails.eval a c191 := h 190 (by decide)
  have h25 : Entails.eval a c762 := derived762 a h
  have h26 : Entails.eval a c25 := h 24 (by decide)
  have h27 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1911 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1883, some c1779, some c98, some c72, some c1910, some c1005, some c76, some c56, some c37, some c1901, some c95, some c1900, some c1860, some c380, some c302, some c1118, some c91, some c195, some c11, some c19, some c27, some c161, some c137, some c762, some c210, some c282, some c316, some c1697, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1911 : lratChecker f1911 p1911 = .success := by decide +kernel
theorem unsat1911 : Unsatisfiable (PosFin 57) f1911 := by
  apply lratCheckerSound f1911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1911
  · intro a ha; simp [p1911] at ha; subst a; trivial
  · exact checked1911
theorem derived1911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1911 := by
  apply localUnsat_implies_entails f1911 [c1671, c1883, c1779, c98, c72, c1910, c1005, c76, c56, c37, c1901, c95, c1900, c1860, c380, c302, c1118, c91, c195, c11, c19, c27, c161, c137, c762, c210, c282, c316, c1697] c1911 unsat1911 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c1910 := derived1910 a h
  have h6 : Entails.eval a c1005 := derived1005 a h
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c1901 := derived1901 a h
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c1900 := derived1900 a h
  have h13 : Entails.eval a c1860 := derived1860 a h
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c1118 := derived1118 a h
  have h17 : Entails.eval a c91 := h 90 (by decide)
  have h18 : Entails.eval a c195 := h 194 (by decide)
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c27 := h 26 (by decide)
  have h22 : Entails.eval a c161 := h 160 (by decide)
  have h23 : Entails.eval a c137 := h 136 (by decide)
  have h24 : Entails.eval a c762 := derived762 a h
  have h25 : Entails.eval a c210 := h 209 (by decide)
  have h26 : Entails.eval a c282 := h 281 (by decide)
  have h27 : Entails.eval a c316 := h 315 (by decide)
  have h28 : Entails.eval a c1697 := derived1697 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1912 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1900, some c1883, some c1860, some c1779, some c98, some c1671, some c95, some c72, some c1901, some c1910, some c37, some c56, some c1005, some c66, some c76, some c1911, some c1885, some c1906, some c968, some c298, some c333, some c360, some c93, some c35, some c762, some c191, some c284, some c195, some c25, some c305, some c199, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1912 : lratChecker f1912 p1912 = .success := by decide +kernel
theorem unsat1912 : Unsatisfiable (PosFin 57) f1912 := by
  apply lratCheckerSound f1912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1912
  · intro a ha; simp [p1912] at ha; subst a; trivial
  · exact checked1912
theorem derived1912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1912 := by
  apply localUnsat_implies_entails f1912 [c1900, c1883, c1860, c1779, c98, c1671, c95, c72, c1901, c1910, c37, c56, c1005, c66, c76, c1911, c1885, c1906, c968, c298, c333, c360, c93, c35, c762, c191, c284, c195, c25, c305, c199] c1912 unsat1912 (by rfl) a
  have h0 : Entails.eval a c1900 := derived1900 a h
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1860 := derived1860 a h
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c1901 := derived1901 a h
  have h9 : Entails.eval a c1910 := derived1910 a h
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c1005 := derived1005 a h
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c1911 := derived1911 a h
  have h16 : Entails.eval a c1885 := derived1885 a h
  have h17 : Entails.eval a c1906 := derived1906 a h
  have h18 : Entails.eval a c968 := derived968 a h
  have h19 : Entails.eval a c298 := h 297 (by decide)
  have h20 : Entails.eval a c333 := h 332 (by decide)
  have h21 : Entails.eval a c360 := h 359 (by decide)
  have h22 : Entails.eval a c93 := h 92 (by decide)
  have h23 : Entails.eval a c35 := h 34 (by decide)
  have h24 : Entails.eval a c762 := derived762 a h
  have h25 : Entails.eval a c191 := h 190 (by decide)
  have h26 : Entails.eval a c284 := h 283 (by decide)
  have h27 : Entails.eval a c195 := h 194 (by decide)
  have h28 : Entails.eval a c25 := h 24 (by decide)
  have h29 : Entails.eval a c305 := h 304 (by decide)
  have h30 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1913 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨29, by decide⟩, false), (⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1912, some c841, some c71, some c1900, some c272, some c1833, some c305, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1913 : lratChecker f1913 p1913 = .success := by decide +kernel
theorem unsat1913 : Unsatisfiable (PosFin 57) f1913 := by
  apply lratCheckerSound f1913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1913
  · intro a ha; simp [p1913] at ha; subst a; trivial
  · exact checked1913
theorem derived1913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1913 := by
  apply localUnsat_implies_entails f1913 [c1860, c1912, c841, c71, c1900, c272, c1833, c305] c1913 unsat1913 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1912 := derived1912 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c1900 := derived1900 a h
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c1833 := derived1833 a h
  have h7 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1914 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1912, some c841, some c71, some c155, some c3, some c1900, some c1883, some c1779, some c98, some c1671, some c88, some c69, some c980, some c336, some c378, some c366, some c370, some c327, some c34, some c986, some c157, some c296, some c332, some c51, some c1913, some c309, some c123, some c769, some c178, some c305, some c1745, some c268, some c159, some c144, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1914 : lratChecker f1914 p1914 = .success := by decide +kernel
theorem unsat1914 : Unsatisfiable (PosFin 57) f1914 := by
  apply lratCheckerSound f1914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1914
  · intro a ha; simp [p1914] at ha; subst a; trivial
  · exact checked1914
theorem derived1914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1914 := by
  apply localUnsat_implies_entails f1914 [c1860, c1912, c841, c71, c155, c3, c1900, c1883, c1779, c98, c1671, c88, c69, c980, c336, c378, c366, c370, c327, c34, c986, c157, c296, c332, c51, c1913, c309, c123, c769, c178, c305, c1745, c268, c159, c144] c1914 unsat1914 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1912 := derived1912 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1900 := derived1900 a h
  have h7 : Entails.eval a c1883 := derived1883 a h
  have h8 : Entails.eval a c1779 := derived1779 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c1671 := derived1671 a h
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c980 := derived980 a h
  have h14 : Entails.eval a c336 := h 335 (by decide)
  have h15 : Entails.eval a c378 := h 377 (by decide)
  have h16 : Entails.eval a c366 := h 365 (by decide)
  have h17 : Entails.eval a c370 := h 369 (by decide)
  have h18 : Entails.eval a c327 := h 326 (by decide)
  have h19 : Entails.eval a c34 := h 33 (by decide)
  have h20 : Entails.eval a c986 := derived986 a h
  have h21 : Entails.eval a c157 := h 156 (by decide)
  have h22 : Entails.eval a c296 := h 295 (by decide)
  have h23 : Entails.eval a c332 := h 331 (by decide)
  have h24 : Entails.eval a c51 := h 50 (by decide)
  have h25 : Entails.eval a c1913 := derived1913 a h
  have h26 : Entails.eval a c309 := h 308 (by decide)
  have h27 : Entails.eval a c123 := h 122 (by decide)
  have h28 : Entails.eval a c769 := derived769 a h
  have h29 : Entails.eval a c178 := h 177 (by decide)
  have h30 : Entails.eval a c305 := h 304 (by decide)
  have h31 : Entails.eval a c1745 := derived1745 a h
  have h32 : Entails.eval a c268 := h 267 (by decide)
  have h33 : Entails.eval a c159 := h 158 (by decide)
  have h34 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1915 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨14, by decide⟩, false), (⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1912, some c841, some c71, some c155, some c3, some c1883, some c1671, some c320, some c370, some c1004, some c34, some c364, some c1039, some c1445, some c123, some c343, some c986, some c1913, some c316, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1915 : lratChecker f1915 p1915 = .success := by decide +kernel
theorem unsat1915 : Unsatisfiable (PosFin 57) f1915 := by
  apply lratCheckerSound f1915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1915
  · intro a ha; simp [p1915] at ha; subst a; trivial
  · exact checked1915
theorem derived1915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1915 := by
  apply localUnsat_implies_entails f1915 [c1860, c1912, c841, c71, c155, c3, c1883, c1671, c320, c370, c1004, c34, c364, c1039, c1445, c123, c343, c986, c1913, c316] c1915 unsat1915 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1912 := derived1912 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1883 := derived1883 a h
  have h7 : Entails.eval a c1671 := derived1671 a h
  have h8 : Entails.eval a c320 := h 319 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c1004 := derived1004 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c364 := h 363 (by decide)
  have h13 : Entails.eval a c1039 := derived1039 a h
  have h14 : Entails.eval a c1445 := derived1445 a h
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c343 := h 342 (by decide)
  have h17 : Entails.eval a c986 := derived986 a h
  have h18 : Entails.eval a c1913 := derived1913 a h
  have h19 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1916 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1912, some c841, some c71, some c155, some c3, some c1883, some c1779, some c98, some c1671, some c1915, some c66, some c980, some c336, some c366, some c327, some c34, some c986, some c157, some c296, some c123, some c332, some c51, some c1913, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1916 : lratChecker f1916 p1916 = .success := by decide +kernel
theorem unsat1916 : Unsatisfiable (PosFin 57) f1916 := by
  apply lratCheckerSound f1916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1916
  · intro a ha; simp [p1916] at ha; subst a; trivial
  · exact checked1916
theorem derived1916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1916 := by
  apply localUnsat_implies_entails f1916 [c1860, c1912, c841, c71, c155, c3, c1883, c1779, c98, c1671, c1915, c66, c980, c336, c366, c327, c34, c986, c157, c296, c123, c332, c51, c1913] c1916 unsat1916 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1912 := derived1912 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1883 := derived1883 a h
  have h7 : Entails.eval a c1779 := derived1779 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c1915 := derived1915 a h
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c980 := derived980 a h
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c327 := h 326 (by decide)
  have h16 : Entails.eval a c34 := h 33 (by decide)
  have h17 : Entails.eval a c986 := derived986 a h
  have h18 : Entails.eval a c157 := h 156 (by decide)
  have h19 : Entails.eval a c296 := h 295 (by decide)
  have h20 : Entails.eval a c123 := h 122 (by decide)
  have h21 : Entails.eval a c332 := h 331 (by decide)
  have h22 : Entails.eval a c51 := h 50 (by decide)
  have h23 : Entails.eval a c1913 := derived1913 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1917 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1916, some c1914, some c1860, some c1912, some c841, some c155, some c71, some c1900, some c1883, some c1671, some c320, some c370, some c1004, some c34, some c364, some c1039, some c343, some c986, some c316, some c1913, some c309, some c769, some c305, some c273, some c195, some c166, some c1746, some c188, some c1118, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1917 : lratChecker f1917 p1917 = .success := by decide +kernel
theorem unsat1917 : Unsatisfiable (PosFin 57) f1917 := by
  apply lratCheckerSound f1917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1917
  · intro a ha; simp [p1917] at ha; subst a; trivial
  · exact checked1917
theorem derived1917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1917 := by
  apply localUnsat_implies_entails f1917 [c1916, c1914, c1860, c1912, c841, c155, c71, c1900, c1883, c1671, c320, c370, c1004, c34, c364, c1039, c343, c986, c316, c1913, c309, c769, c305, c273, c195, c166, c1746, c188, c1118] c1917 unsat1917 (by rfl) a
  have h0 : Entails.eval a c1916 := derived1916 a h
  have h1 : Entails.eval a c1914 := derived1914 a h
  have h2 : Entails.eval a c1860 := derived1860 a h
  have h3 : Entails.eval a c1912 := derived1912 a h
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c1900 := derived1900 a h
  have h8 : Entails.eval a c1883 := derived1883 a h
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c320 := h 319 (by decide)
  have h11 : Entails.eval a c370 := h 369 (by decide)
  have h12 : Entails.eval a c1004 := derived1004 a h
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c364 := h 363 (by decide)
  have h15 : Entails.eval a c1039 := derived1039 a h
  have h16 : Entails.eval a c343 := h 342 (by decide)
  have h17 : Entails.eval a c986 := derived986 a h
  have h18 : Entails.eval a c316 := h 315 (by decide)
  have h19 : Entails.eval a c1913 := derived1913 a h
  have h20 : Entails.eval a c309 := h 308 (by decide)
  have h21 : Entails.eval a c769 := derived769 a h
  have h22 : Entails.eval a c305 := h 304 (by decide)
  have h23 : Entails.eval a c273 := h 272 (by decide)
  have h24 : Entails.eval a c195 := h 194 (by decide)
  have h25 : Entails.eval a c166 := h 165 (by decide)
  have h26 : Entails.eval a c1746 := derived1746 a h
  have h27 : Entails.eval a c188 := h 187 (by decide)
  have h28 : Entails.eval a c1118 := derived1118 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1918 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1912, some c841, some c155, some c71, some c1900, some c1883, some c1779, some c98, some c1671, some c1914, some c1917, some c66, some c980, some c336, some c366, some c327, some c34, some c986, some c296, some c332, some c1078, some c51, some c1913, some c769, some c309, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1918 : lratChecker f1918 p1918 = .success := by decide +kernel
theorem unsat1918 : Unsatisfiable (PosFin 57) f1918 := by
  apply lratCheckerSound f1918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1918
  · intro a ha; simp [p1918] at ha; subst a; trivial
  · exact checked1918
theorem derived1918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1918 := by
  apply localUnsat_implies_entails f1918 [c1860, c1912, c841, c155, c71, c1900, c1883, c1779, c98, c1671, c1914, c1917, c66, c980, c336, c366, c327, c34, c986, c296, c332, c1078, c51, c1913, c769, c309] c1918 unsat1918 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1912 := derived1912 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c155 := h 154 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c1900 := derived1900 a h
  have h6 : Entails.eval a c1883 := derived1883 a h
  have h7 : Entails.eval a c1779 := derived1779 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c1914 := derived1914 a h
  have h11 : Entails.eval a c1917 := derived1917 a h
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c980 := derived980 a h
  have h14 : Entails.eval a c336 := h 335 (by decide)
  have h15 : Entails.eval a c366 := h 365 (by decide)
  have h16 : Entails.eval a c327 := h 326 (by decide)
  have h17 : Entails.eval a c34 := h 33 (by decide)
  have h18 : Entails.eval a c986 := derived986 a h
  have h19 : Entails.eval a c296 := h 295 (by decide)
  have h20 : Entails.eval a c332 := h 331 (by decide)
  have h21 : Entails.eval a c1078 := derived1078 a h
  have h22 : Entails.eval a c51 := h 50 (by decide)
  have h23 : Entails.eval a c1913 := derived1913 a h
  have h24 : Entails.eval a c769 := derived769 a h
  have h25 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1919 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1912, some c1883, some c1779, some c98, some c1671, some c1918, some c56, some c1005, some c336, some c66, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1919 : lratChecker f1919 p1919 = .success := by decide +kernel
theorem unsat1919 : Unsatisfiable (PosFin 57) f1919 := by
  apply lratCheckerSound f1919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1919
  · intro a ha; simp [p1919] at ha; subst a; trivial
  · exact checked1919
theorem derived1919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1919 := by
  apply localUnsat_implies_entails f1919 [c1912, c1883, c1779, c98, c1671, c1918, c56, c1005, c336, c66] c1919 unsat1919 (by rfl) a
  have h0 : Entails.eval a c1912 := derived1912 a h
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c1918 := derived1918 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c1005 := derived1005 a h
  have h8 : Entails.eval a c336 := h 335 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1920 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨42, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1779, some c98, some c1919, some c83, some c1860, some c1912, some c841, some c155, some c71, some c1671, some c980, some c336, some c369, some c34, some c360, some c296, some c968, some c1118, some c11, some c79, some c1637, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1920 : lratChecker f1920 p1920 = .success := by decide +kernel
theorem unsat1920 : Unsatisfiable (PosFin 57) f1920 := by
  apply lratCheckerSound f1920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1920
  · intro a ha; simp [p1920] at ha; subst a; trivial
  · exact checked1920
theorem derived1920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1920 := by
  apply localUnsat_implies_entails f1920 [c1883, c1779, c98, c1919, c83, c1860, c1912, c841, c155, c71, c1671, c980, c336, c369, c34, c360, c296, c968, c1118, c11, c79, c1637] c1920 unsat1920 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1919 := derived1919 a h
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c1860 := derived1860 a h
  have h6 : Entails.eval a c1912 := derived1912 a h
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c1671 := derived1671 a h
  have h11 : Entails.eval a c980 := derived980 a h
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c369 := h 368 (by decide)
  have h14 : Entails.eval a c34 := h 33 (by decide)
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c968 := derived968 a h
  have h18 : Entails.eval a c1118 := derived1118 a h
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c79 := h 78 (by decide)
  have h21 : Entails.eval a c1637 := derived1637 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1921 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1919, some c1860, some c1912, some c841, some c155, some c71, some c1883, some c1779, some c98, some c1671, some c186, some c185, some c1891, some c165, some c976, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1921 : lratChecker f1921 p1921 = .success := by decide +kernel
theorem unsat1921 : Unsatisfiable (PosFin 57) f1921 := by
  apply lratCheckerSound f1921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1921
  · intro a ha; simp [p1921] at ha; subst a; trivial
  · exact checked1921
theorem derived1921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1921 := by
  apply localUnsat_implies_entails f1921 [c1919, c1860, c1912, c841, c155, c71, c1883, c1779, c98, c1671, c186, c185, c1891, c165, c976] c1921 unsat1921 (by rfl) a
  have h0 : Entails.eval a c1919 := derived1919 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1912 := derived1912 a h
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c1883 := derived1883 a h
  have h7 : Entails.eval a c1779 := derived1779 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c186 := h 185 (by decide)
  have h11 : Entails.eval a c185 := h 184 (by decide)
  have h12 : Entails.eval a c1891 := derived1891 a h
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c976 := derived976 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1922 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨46, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1779, some c98, some c1919, some c83, some c1860, some c1912, some c841, some c155, some c71, some c1039, some c986, some c313, some c364, some c343, some c1671, some c34, some c1900, some c1913, some c273, some c309, some c769, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1922 : lratChecker f1922 p1922 = .success := by decide +kernel
theorem unsat1922 : Unsatisfiable (PosFin 57) f1922 := by
  apply lratCheckerSound f1922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1922
  · intro a ha; simp [p1922] at ha; subst a; trivial
  · exact checked1922
theorem derived1922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1922 := by
  apply localUnsat_implies_entails f1922 [c1883, c1779, c98, c1919, c83, c1860, c1912, c841, c155, c71, c1039, c986, c313, c364, c343, c1671, c34, c1900, c1913, c273, c309, c769] c1922 unsat1922 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1919 := derived1919 a h
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c1860 := derived1860 a h
  have h6 : Entails.eval a c1912 := derived1912 a h
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c1039 := derived1039 a h
  have h11 : Entails.eval a c986 := derived986 a h
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c364 := h 363 (by decide)
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c1671 := derived1671 a h
  have h16 : Entails.eval a c34 := h 33 (by decide)
  have h17 : Entails.eval a c1900 := derived1900 a h
  have h18 : Entails.eval a c1913 := derived1913 a h
  have h19 : Entails.eval a c273 := h 272 (by decide)
  have h20 : Entails.eval a c309 := h 308 (by decide)
  have h21 : Entails.eval a c769 := derived769 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1923 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1779, some c98, some c1919, some c83, some c1860, some c1912, some c841, some c155, some c71, some c1900, some c364, some c1039, some c343, some c986, some c313, some c1922, some c418, some c1758, some c272, some c194, some c307, some c18, some c189, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1923 : lratChecker f1923 p1923 = .success := by decide +kernel
theorem unsat1923 : Unsatisfiable (PosFin 57) f1923 := by
  apply lratCheckerSound f1923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1923
  · intro a ha; simp [p1923] at ha; subst a; trivial
  · exact checked1923
theorem derived1923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1923 := by
  apply localUnsat_implies_entails f1923 [c1883, c1779, c98, c1919, c83, c1860, c1912, c841, c155, c71, c1900, c364, c1039, c343, c986, c313, c1922, c418, c1758, c272, c194, c307, c18, c189] c1923 unsat1923 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1919 := derived1919 a h
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c1860 := derived1860 a h
  have h6 : Entails.eval a c1912 := derived1912 a h
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c1900 := derived1900 a h
  have h11 : Entails.eval a c364 := h 363 (by decide)
  have h12 : Entails.eval a c1039 := derived1039 a h
  have h13 : Entails.eval a c343 := h 342 (by decide)
  have h14 : Entails.eval a c986 := derived986 a h
  have h15 : Entails.eval a c313 := h 312 (by decide)
  have h16 : Entails.eval a c1922 := derived1922 a h
  have h17 : Entails.eval a c418 := derived418 a h
  have h18 : Entails.eval a c1758 := derived1758 a h
  have h19 : Entails.eval a c272 := h 271 (by decide)
  have h20 : Entails.eval a c194 := h 193 (by decide)
  have h21 : Entails.eval a c307 := h 306 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1924 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨42, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1779, some c98, some c1919, some c83, some c1860, some c1912, some c841, some c155, some c71, some c1671, some c34, some c1923, some c369, some c360, some c968, some c1118, some c11, some c79, some c322, some c277, some c35, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1924 : lratChecker f1924 p1924 = .success := by decide +kernel
theorem unsat1924 : Unsatisfiable (PosFin 57) f1924 := by
  apply lratCheckerSound f1924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1924
  · intro a ha; simp [p1924] at ha; subst a; trivial
  · exact checked1924
theorem derived1924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1924 := by
  apply localUnsat_implies_entails f1924 [c1883, c1779, c98, c1919, c83, c1860, c1912, c841, c155, c71, c1671, c34, c1923, c369, c360, c968, c1118, c11, c79, c322, c277, c35] c1924 unsat1924 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1919 := derived1919 a h
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c1860 := derived1860 a h
  have h6 : Entails.eval a c1912 := derived1912 a h
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c1671 := derived1671 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c1923 := derived1923 a h
  have h13 : Entails.eval a c369 := h 368 (by decide)
  have h14 : Entails.eval a c360 := h 359 (by decide)
  have h15 : Entails.eval a c968 := derived968 a h
  have h16 : Entails.eval a c1118 := derived1118 a h
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c79 := h 78 (by decide)
  have h19 : Entails.eval a c322 := h 321 (by decide)
  have h20 : Entails.eval a c277 := h 276 (by decide)
  have h21 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1925 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1919, some c1860, some c1912, some c841, some c155, some c71, some c1883, some c1779, some c98, some c1671, some c140, some c1891, some c976, some c360, some c165, some c968, some c184, some c1118, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1925 : lratChecker f1925 p1925 = .success := by decide +kernel
theorem unsat1925 : Unsatisfiable (PosFin 57) f1925 := by
  apply lratCheckerSound f1925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1925
  · intro a ha; simp [p1925] at ha; subst a; trivial
  · exact checked1925
theorem derived1925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1925 := by
  apply localUnsat_implies_entails f1925 [c1919, c1860, c1912, c841, c155, c71, c1883, c1779, c98, c1671, c140, c1891, c976, c360, c165, c968, c184, c1118] c1925 unsat1925 (by rfl) a
  have h0 : Entails.eval a c1919 := derived1919 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1912 := derived1912 a h
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c1883 := derived1883 a h
  have h7 : Entails.eval a c1779 := derived1779 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c1891 := derived1891 a h
  have h12 : Entails.eval a c976 := derived976 a h
  have h13 : Entails.eval a c360 := h 359 (by decide)
  have h14 : Entails.eval a c165 := h 164 (by decide)
  have h15 : Entails.eval a c968 := derived968 a h
  have h16 : Entails.eval a c184 := h 183 (by decide)
  have h17 : Entails.eval a c1118 := derived1118 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1926 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1912, some c841, some c71, some c155, some c3, some c1900, some c1883, some c1779, some c98, some c1671, some c1920, some c88, some c1924, some c350, some c1925, some c169, some c332, some c1078, some c189, some c18, some c19, some c220, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1926 : lratChecker f1926 p1926 = .success := by decide +kernel
theorem unsat1926 : Unsatisfiable (PosFin 57) f1926 := by
  apply lratCheckerSound f1926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1926
  · intro a ha; simp [p1926] at ha; subst a; trivial
  · exact checked1926
theorem derived1926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1926 := by
  apply localUnsat_implies_entails f1926 [c1860, c1912, c841, c71, c155, c3, c1900, c1883, c1779, c98, c1671, c1920, c88, c1924, c350, c1925, c169, c332, c1078, c189, c18, c19, c220] c1926 unsat1926 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1912 := derived1912 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1900 := derived1900 a h
  have h7 : Entails.eval a c1883 := derived1883 a h
  have h8 : Entails.eval a c1779 := derived1779 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c1671 := derived1671 a h
  have h11 : Entails.eval a c1920 := derived1920 a h
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c1924 := derived1924 a h
  have h14 : Entails.eval a c350 := h 349 (by decide)
  have h15 : Entails.eval a c1925 := derived1925 a h
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c332 := h 331 (by decide)
  have h18 : Entails.eval a c1078 := derived1078 a h
  have h19 : Entails.eval a c189 := h 188 (by decide)
  have h20 : Entails.eval a c18 := h 17 (by decide)
  have h21 : Entails.eval a c19 := h 18 (by decide)
  have h22 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1927 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1779, some c98, some c1671, some c1926, some c66, some c1912, some c336, some c34, some c296, some c51, some c1919, some c83, some c1860, some c841, some c71, some c1900, some c313, some c273, some c1833, some c769, some c309, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1927 : lratChecker f1927 p1927 = .success := by decide +kernel
theorem unsat1927 : Unsatisfiable (PosFin 57) f1927 := by
  apply lratCheckerSound f1927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1927
  · intro a ha; simp [p1927] at ha; subst a; trivial
  · exact checked1927
theorem derived1927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1927 := by
  apply localUnsat_implies_entails f1927 [c1883, c1779, c98, c1671, c1926, c66, c1912, c336, c34, c296, c51, c1919, c83, c1860, c841, c71, c1900, c313, c273, c1833, c769, c309] c1927 unsat1927 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c1926 := derived1926 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c1912 := derived1912 a h
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c1919 := derived1919 a h
  have h12 : Entails.eval a c83 := h 82 (by decide)
  have h13 : Entails.eval a c1860 := derived1860 a h
  have h14 : Entails.eval a c841 := derived841 a h
  have h15 : Entails.eval a c71 := h 70 (by decide)
  have h16 : Entails.eval a c1900 := derived1900 a h
  have h17 : Entails.eval a c313 := h 312 (by decide)
  have h18 : Entails.eval a c273 := h 272 (by decide)
  have h19 : Entails.eval a c1833 := derived1833 a h
  have h20 : Entails.eval a c769 := derived769 a h
  have h21 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1928 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1779, some c98, some c1671, some c1926, some c66, some c1912, some c336, some c34, some c296, some c51, some c1919, some c83, some c1860, some c841, some c155, some c1900, some c130, some c188, some c1745, some c1118, some c360, some c968, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1928 : lratChecker f1928 p1928 = .success := by decide +kernel
theorem unsat1928 : Unsatisfiable (PosFin 57) f1928 := by
  apply lratCheckerSound f1928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1928
  · intro a ha; simp [p1928] at ha; subst a; trivial
  · exact checked1928
theorem derived1928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1928 := by
  apply localUnsat_implies_entails f1928 [c1883, c1779, c98, c1671, c1926, c66, c1912, c336, c34, c296, c51, c1919, c83, c1860, c841, c155, c1900, c130, c188, c1745, c1118, c360, c968] c1928 unsat1928 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c1926 := derived1926 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c1912 := derived1912 a h
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c1919 := derived1919 a h
  have h12 : Entails.eval a c83 := h 82 (by decide)
  have h13 : Entails.eval a c1860 := derived1860 a h
  have h14 : Entails.eval a c841 := derived841 a h
  have h15 : Entails.eval a c155 := h 154 (by decide)
  have h16 : Entails.eval a c1900 := derived1900 a h
  have h17 : Entails.eval a c130 := h 129 (by decide)
  have h18 : Entails.eval a c188 := h 187 (by decide)
  have h19 : Entails.eval a c1745 := derived1745 a h
  have h20 : Entails.eval a c1118 := derived1118 a h
  have h21 : Entails.eval a c360 := h 359 (by decide)
  have h22 : Entails.eval a c968 := derived968 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1929 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1912, some c841, some c71, some c155, some c3, some c1900, some c1883, some c1779, some c98, some c1671, some c1926, some c66, some c336, some c378, some c34, some c296, some c51, some c1927, some c986, some c157, some c332, some c1921, some c1928, some c178, some c1078, some c1833, some c769, some c309, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1929 : lratChecker f1929 p1929 = .success := by decide +kernel
theorem unsat1929 : Unsatisfiable (PosFin 57) f1929 := by
  apply lratCheckerSound f1929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1929
  · intro a ha; simp [p1929] at ha; subst a; trivial
  · exact checked1929
theorem derived1929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1929 := by
  apply localUnsat_implies_entails f1929 [c1860, c1912, c841, c71, c155, c3, c1900, c1883, c1779, c98, c1671, c1926, c66, c336, c378, c34, c296, c51, c1927, c986, c157, c332, c1921, c1928, c178, c1078, c1833, c769, c309] c1929 unsat1929 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1912 := derived1912 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1900 := derived1900 a h
  have h7 : Entails.eval a c1883 := derived1883 a h
  have h8 : Entails.eval a c1779 := derived1779 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c1671 := derived1671 a h
  have h11 : Entails.eval a c1926 := derived1926 a h
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c378 := h 377 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c51 := h 50 (by decide)
  have h18 : Entails.eval a c1927 := derived1927 a h
  have h19 : Entails.eval a c986 := derived986 a h
  have h20 : Entails.eval a c157 := h 156 (by decide)
  have h21 : Entails.eval a c332 := h 331 (by decide)
  have h22 : Entails.eval a c1921 := derived1921 a h
  have h23 : Entails.eval a c1928 := derived1928 a h
  have h24 : Entails.eval a c178 := h 177 (by decide)
  have h25 : Entails.eval a c1078 := derived1078 a h
  have h26 : Entails.eval a c1833 := derived1833 a h
  have h27 : Entails.eval a c769 := derived769 a h
  have h28 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1930 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1860, some c1779, some c98, some c1671, some c1912, some c841, some c71, some c155, some c3, some c1929, some c56, some c1759, some c774, some c336, some c1925, some c169, some c332, some c1078, some c189, some c18, some c237, some c218, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1930 : lratChecker f1930 p1930 = .success := by decide +kernel
theorem unsat1930 : Unsatisfiable (PosFin 57) f1930 := by
  apply lratCheckerSound f1930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1930
  · intro a ha; simp [p1930] at ha; subst a; trivial
  · exact checked1930
theorem derived1930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1930 := by
  apply localUnsat_implies_entails f1930 [c1883, c1860, c1779, c98, c1671, c1912, c841, c71, c155, c3, c1929, c56, c1759, c774, c336, c1925, c169, c332, c1078, c189, c18, c237, c218] c1930 unsat1930 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c1912 := derived1912 a h
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1929 := derived1929 a h
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c1759 := derived1759 a h
  have h13 : Entails.eval a c774 := derived774 a h
  have h14 : Entails.eval a c336 := h 335 (by decide)
  have h15 : Entails.eval a c1925 := derived1925 a h
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c332 := h 331 (by decide)
  have h18 : Entails.eval a c1078 := derived1078 a h
  have h19 : Entails.eval a c189 := h 188 (by decide)
  have h20 : Entails.eval a c18 := h 17 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  have h22 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1931 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1930, some c40, some c1883, some c1860, some c1671, some c71, some c77, some c841, some c95, some c72, some c597, some c280, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1931 : lratChecker f1931 p1931 = .success := by decide +kernel
theorem unsat1931 : Unsatisfiable (PosFin 57) f1931 := by
  apply lratCheckerSound f1931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1931
  · intro a ha; simp [p1931] at ha; subst a; trivial
  · exact checked1931
theorem derived1931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1931 := by
  apply localUnsat_implies_entails f1931 [c1779, c98, c1930, c40, c1883, c1860, c1671, c71, c77, c841, c95, c72, c597, c280] c1931 unsat1931 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1930 := derived1930 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c1883 := derived1883 a h
  have h5 : Entails.eval a c1860 := derived1860 a h
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c597 := derived597 a h
  have h13 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1932 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1883, some c1779, some c98, some c95, some c155, some c380, some c1118, some c72, some c1930, some c40, some c1671, some c280, some c66, some c161, some c124, some c184, some c177, some c164, some c377, some c976, some c1697, some c358, some c366, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1932 : lratChecker f1932 p1932 = .success := by decide +kernel
theorem unsat1932 : Unsatisfiable (PosFin 57) f1932 := by
  apply lratCheckerSound f1932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1932
  · intro a ha; simp [p1932] at ha; subst a; trivial
  · exact checked1932
theorem derived1932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1932 := by
  apply localUnsat_implies_entails f1932 [c1860, c1883, c1779, c98, c95, c155, c380, c1118, c72, c1930, c40, c1671, c280, c66, c161, c124, c184, c177, c164, c377, c976, c1697, c358, c366] c1932 unsat1932 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c1118 := derived1118 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c1930 := derived1930 a h
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c1671 := derived1671 a h
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c184 := h 183 (by decide)
  have h17 : Entails.eval a c177 := h 176 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  have h19 : Entails.eval a c377 := h 376 (by decide)
  have h20 : Entails.eval a c976 := derived976 a h
  have h21 : Entails.eval a c1697 := derived1697 a h
  have h22 : Entails.eval a c358 := h 357 (by decide)
  have h23 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1933 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨31, by decide⟩, true), (⟨26, by decide⟩, true), (⟨17, by decide⟩, true), (⟨39, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1931, some c1883, some c1671, some c198, some c413, some c268, some c591, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1933 : lratChecker f1933 p1933 = .success := by decide +kernel
theorem unsat1933 : Unsatisfiable (PosFin 57) f1933 := by
  apply lratCheckerSound f1933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1933
  · intro a ha; simp [p1933] at ha; subst a; trivial
  · exact checked1933
theorem derived1933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1933 := by
  apply localUnsat_implies_entails f1933 [c1931, c1883, c1671, c198, c413, c268, c591] c1933 unsat1933 (by rfl) a
  have h0 : Entails.eval a c1931 := derived1931 a h
  have h1 : Entails.eval a c1883 := derived1883 a h
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c413 := derived413 a h
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c591 := derived591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1934 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c72, some c1883, some c95, some c1931, some c1930, some c63, some c40, some c1860, some c1671, some c155, some c1893, some c380, some c1902, some c1118, some c91, some c1932, some c34, some c44, some c302, some c195, some c27, some c1933, some c276, some c306, some c1697, some c272, some c976, some c349, some c164, some c61, some c9, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1934 : lratChecker f1934 p1934 = .success := by decide +kernel
theorem unsat1934 : Unsatisfiable (PosFin 57) f1934 := by
  apply lratCheckerSound f1934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1934
  · intro a ha; simp [p1934] at ha; subst a; trivial
  · exact checked1934
theorem derived1934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1934 := by
  apply localUnsat_implies_entails f1934 [c1779, c98, c72, c1883, c95, c1931, c1930, c63, c40, c1860, c1671, c155, c1893, c380, c1902, c1118, c91, c1932, c34, c44, c302, c195, c27, c1933, c276, c306, c1697, c272, c976, c349, c164, c61, c9] c1934 unsat1934 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1883 := derived1883 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c1931 := derived1931 a h
  have h6 : Entails.eval a c1930 := derived1930 a h
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c1860 := derived1860 a h
  have h10 : Entails.eval a c1671 := derived1671 a h
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c1893 := derived1893 a h
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c1902 := derived1902 a h
  have h15 : Entails.eval a c1118 := derived1118 a h
  have h16 : Entails.eval a c91 := h 90 (by decide)
  have h17 : Entails.eval a c1932 := derived1932 a h
  have h18 : Entails.eval a c34 := h 33 (by decide)
  have h19 : Entails.eval a c44 := h 43 (by decide)
  have h20 : Entails.eval a c302 := h 301 (by decide)
  have h21 : Entails.eval a c195 := h 194 (by decide)
  have h22 : Entails.eval a c27 := h 26 (by decide)
  have h23 : Entails.eval a c1933 := derived1933 a h
  have h24 : Entails.eval a c276 := h 275 (by decide)
  have h25 : Entails.eval a c306 := h 305 (by decide)
  have h26 : Entails.eval a c1697 := derived1697 a h
  have h27 : Entails.eval a c272 := h 271 (by decide)
  have h28 : Entails.eval a c976 := derived976 a h
  have h29 : Entails.eval a c349 := h 348 (by decide)
  have h30 : Entails.eval a c164 := h 163 (by decide)
  have h31 : Entails.eval a c61 := h 60 (by decide)
  have h32 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1935 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1934, some c1931, some c1860, some c1779, some c98, some c1118, some c91, some c11, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1935 : lratChecker f1935 p1935 = .success := by decide +kernel
theorem unsat1935 : Unsatisfiable (PosFin 57) f1935 := by
  apply lratCheckerSound f1935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1935
  · intro a ha; simp [p1935] at ha; subst a; trivial
  · exact checked1935
theorem derived1935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1935 := by
  apply localUnsat_implies_entails f1935 [c1934, c1931, c1860, c1779, c98, c1118, c91, c11] c1935 unsat1935 (by rfl) a
  have h0 : Entails.eval a c1934 := derived1934 a h
  have h1 : Entails.eval a c1931 := derived1931 a h
  have h2 : Entails.eval a c1860 := derived1860 a h
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c1118 := derived1118 a h
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1936 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1931, some c1779, some c98, some c1883, some c1930, some c63, some c1860, some c1671, some c95, some c72, some c1934, some c3, some c1935, some c968, some c380, some c338, some c360, some c93, some c59, some c976, some c11, some c158, some c366, some c162, some c1887, some c13, some c186, some c1068, some c18, some c19, some c1905, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1936 : lratChecker f1936 p1936 = .success := by decide +kernel
theorem unsat1936 : Unsatisfiable (PosFin 57) f1936 := by
  apply lratCheckerSound f1936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1936
  · intro a ha; simp [p1936] at ha; subst a; trivial
  · exact checked1936
theorem derived1936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1936 := by
  apply localUnsat_implies_entails f1936 [c1931, c1779, c98, c1883, c1930, c63, c1860, c1671, c95, c72, c1934, c3, c1935, c968, c380, c338, c360, c93, c59, c976, c11, c158, c366, c162, c1887, c13, c186, c1068, c18, c19, c1905] c1936 unsat1936 (by rfl) a
  have h0 : Entails.eval a c1931 := derived1931 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1883 := derived1883 a h
  have h4 : Entails.eval a c1930 := derived1930 a h
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c1860 := derived1860 a h
  have h7 : Entails.eval a c1671 := derived1671 a h
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c1934 := derived1934 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c1935 := derived1935 a h
  have h13 : Entails.eval a c968 := derived968 a h
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c338 := h 337 (by decide)
  have h16 : Entails.eval a c360 := h 359 (by decide)
  have h17 : Entails.eval a c93 := h 92 (by decide)
  have h18 : Entails.eval a c59 := h 58 (by decide)
  have h19 : Entails.eval a c976 := derived976 a h
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c158 := h 157 (by decide)
  have h22 : Entails.eval a c366 := h 365 (by decide)
  have h23 : Entails.eval a c162 := h 161 (by decide)
  have h24 : Entails.eval a c1887 := derived1887 a h
  have h25 : Entails.eval a c13 := h 12 (by decide)
  have h26 : Entails.eval a c186 := h 185 (by decide)
  have h27 : Entails.eval a c1068 := derived1068 a h
  have h28 : Entails.eval a c18 := h 17 (by decide)
  have h29 : Entails.eval a c19 := h 18 (by decide)
  have h30 : Entails.eval a c1905 := derived1905 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1937 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1779, some c98, some c1930, some c40, some c1936, some c296, some c34, some c1931, some c1860, some c841, some c155, some c3, some c1883, some c968, some c333, some c360, some c59, some c976, some c11, some c158, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1937 : lratChecker f1937 p1937 = .success := by decide +kernel
theorem unsat1937 : Unsatisfiable (PosFin 57) f1937 := by
  apply lratCheckerSound f1937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1937
  · intro a ha; simp [p1937] at ha; subst a; trivial
  · exact checked1937
theorem derived1937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1937 := by
  apply localUnsat_implies_entails f1937 [c1671, c1779, c98, c1930, c40, c1936, c296, c34, c1931, c1860, c841, c155, c3, c1883, c968, c333, c360, c59, c976, c11, c158] c1937 unsat1937 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1930 := derived1930 a h
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c1936 := derived1936 a h
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c1931 := derived1931 a h
  have h9 : Entails.eval a c1860 := derived1860 a h
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c1883 := derived1883 a h
  have h14 : Entails.eval a c968 := derived968 a h
  have h15 : Entails.eval a c333 := h 332 (by decide)
  have h16 : Entails.eval a c360 := h 359 (by decide)
  have h17 : Entails.eval a c59 := h 58 (by decide)
  have h18 : Entails.eval a c976 := derived976 a h
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1938 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1779, some c98, some c1930, some c40, some c1936, some c296, some c34, some c1860, some c980, some c1931, some c841, some c155, some c3, some c366, some c370, some c157, some c1937, some c1118, some c11, some c137, some c59, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1938 : lratChecker f1938 p1938 = .success := by decide +kernel
theorem unsat1938 : Unsatisfiable (PosFin 57) f1938 := by
  apply lratCheckerSound f1938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1938
  · intro a ha; simp [p1938] at ha; subst a; trivial
  · exact checked1938
theorem derived1938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1938 := by
  apply localUnsat_implies_entails f1938 [c1671, c1779, c98, c1930, c40, c1936, c296, c34, c1860, c980, c1931, c841, c155, c3, c366, c370, c157, c1937, c1118, c11, c137, c59] c1938 unsat1938 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1930 := derived1930 a h
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c1936 := derived1936 a h
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c1860 := derived1860 a h
  have h9 : Entails.eval a c980 := derived980 a h
  have h10 : Entails.eval a c1931 := derived1931 a h
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c155 := h 154 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c370 := h 369 (by decide)
  have h16 : Entails.eval a c157 := h 156 (by decide)
  have h17 : Entails.eval a c1937 := derived1937 a h
  have h18 : Entails.eval a c1118 := derived1118 a h
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1939 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨41, by decide⟩, false), (⟨29, by decide⟩, false), (⟨45, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c273, some c324, some c1869, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1939 : lratChecker f1939 p1939 = .success := by decide +kernel
theorem unsat1939 : Unsatisfiable (PosFin 57) f1939 := by
  apply lratCheckerSound f1939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1939
  · intro a ha; simp [p1939] at ha; subst a; trivial
  · exact checked1939
theorem derived1939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1939 := by
  apply localUnsat_implies_entails f1939 [c273, c324, c1869] c1939 unsat1939 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c324 := h 323 (by decide)
  have h2 : Entails.eval a c1869 := derived1869 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1940 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1671, some c88, some c1938, some c69, some c1779, some c98, some c1930, some c63, some c79, some c59, some c322, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1940 : lratChecker f1940 p1940 = .success := by decide +kernel
theorem unsat1940 : Unsatisfiable (PosFin 57) f1940 := by
  apply lratCheckerSound f1940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1940
  · intro a ha; simp [p1940] at ha; subst a; trivial
  · exact checked1940
theorem derived1940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1940 := by
  apply localUnsat_implies_entails f1940 [c1883, c1671, c88, c1938, c69, c1779, c98, c1930, c63, c79, c59, c322] c1940 unsat1940 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c1938 := derived1938 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c1779 := derived1779 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c1930 := derived1930 a h
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1941 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1936, some c841, some c155, some c1931, some c1779, some c98, some c1883, some c1930, some c63, some c40, some c1671, some c88, some c69, some c296, some c44, some c1940, some c11, some c1118, some c968, some c1937, some c360, some c1939, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1941 : lratChecker f1941 p1941 = .success := by decide +kernel
theorem unsat1941 : Unsatisfiable (PosFin 57) f1941 := by
  apply lratCheckerSound f1941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1941
  · intro a ha; simp [p1941] at ha; subst a; trivial
  · exact checked1941
theorem derived1941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1941 := by
  apply localUnsat_implies_entails f1941 [c1860, c1936, c841, c155, c1931, c1779, c98, c1883, c1930, c63, c40, c1671, c88, c69, c296, c44, c1940, c11, c1118, c968, c1937, c360, c1939] c1941 unsat1941 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1936 := derived1936 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c155 := h 154 (by decide)
  have h4 : Entails.eval a c1931 := derived1931 a h
  have h5 : Entails.eval a c1779 := derived1779 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c1883 := derived1883 a h
  have h8 : Entails.eval a c1930 := derived1930 a h
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c1671 := derived1671 a h
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c44 := h 43 (by decide)
  have h16 : Entails.eval a c1940 := derived1940 a h
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c1118 := derived1118 a h
  have h19 : Entails.eval a c968 := derived968 a h
  have h20 : Entails.eval a c1937 := derived1937 a h
  have h21 : Entails.eval a c360 := h 359 (by decide)
  have h22 : Entails.eval a c1939 := derived1939 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1942 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨48, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c1936, some c1671, some c1938, some c66, some c370, some c1039, some c1779, some c98, some c1930, some c40, some c280, some c34, some c1941, some c1931, some c841, some c155, some c3, some c1883, some c63, some c968, some c338, some c360, some c171, some c976, some c1256, some c13, some c1908, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1942 : lratChecker f1942 p1942 = .success := by decide +kernel
theorem unsat1942 : Unsatisfiable (PosFin 57) f1942 := by
  apply lratCheckerSound f1942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1942
  · intro a ha; simp [p1942] at ha; subst a; trivial
  · exact checked1942
theorem derived1942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1942 := by
  apply localUnsat_implies_entails f1942 [c1860, c1936, c1671, c1938, c66, c370, c1039, c1779, c98, c1930, c40, c280, c34, c1941, c1931, c841, c155, c3, c1883, c63, c968, c338, c360, c171, c976, c1256, c13, c1908] c1942 unsat1942 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c1936 := derived1936 a h
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1938 := derived1938 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c1039 := derived1039 a h
  have h7 : Entails.eval a c1779 := derived1779 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c1930 := derived1930 a h
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c280 := h 279 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c1941 := derived1941 a h
  have h14 : Entails.eval a c1931 := derived1931 a h
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c155 := h 154 (by decide)
  have h17 : Entails.eval a c3 := h 2 (by decide)
  have h18 : Entails.eval a c1883 := derived1883 a h
  have h19 : Entails.eval a c63 := h 62 (by decide)
  have h20 : Entails.eval a c968 := derived968 a h
  have h21 : Entails.eval a c338 := h 337 (by decide)
  have h22 : Entails.eval a c360 := h 359 (by decide)
  have h23 : Entails.eval a c171 := h 170 (by decide)
  have h24 : Entails.eval a c976 := derived976 a h
  have h25 : Entails.eval a c1256 := derived1256 a h
  have h26 : Entails.eval a c13 := h 12 (by decide)
  have h27 : Entails.eval a c1908 := derived1908 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1943 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1931, some c1860, some c1936, some c841, some c155, some c3, some c1779, some c98, some c1930, some c40, some c1671, some c1938, some c66, some c280, some c370, some c34, some c1445, some c1942, some c1118, some c11, some c137, some c59, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1943 : lratChecker f1943 p1943 = .success := by decide +kernel
theorem unsat1943 : Unsatisfiable (PosFin 57) f1943 := by
  apply lratCheckerSound f1943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1943
  · intro a ha; simp [p1943] at ha; subst a; trivial
  · exact checked1943
theorem derived1943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1943 := by
  apply localUnsat_implies_entails f1943 [c1931, c1860, c1936, c841, c155, c3, c1779, c98, c1930, c40, c1671, c1938, c66, c280, c370, c34, c1445, c1942, c1118, c11, c137, c59] c1943 unsat1943 (by rfl) a
  have h0 : Entails.eval a c1931 := derived1931 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1936 := derived1936 a h
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1779 := derived1779 a h
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c1930 := derived1930 a h
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c1671 := derived1671 a h
  have h11 : Entails.eval a c1938 := derived1938 a h
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c280 := h 279 (by decide)
  have h14 : Entails.eval a c370 := h 369 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c1445 := derived1445 a h
  have h17 : Entails.eval a c1942 := derived1942 a h
  have h18 : Entails.eval a c1118 := derived1118 a h
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1944 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1883, some c1779, some c98, some c1943, some c83, some c1941, some c1931, some c1860, some c1936, some c841, some c155, some c3, some c1930, some c63, some c40, some c1671, some c968, some c338, some c360, some c59, some c976, some c11, some c163, some c158, some c1939, some c44, some c296, some c124, some c66, some c1445, some c369, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1944 : lratChecker f1944 p1944 = .success := by decide +kernel
theorem unsat1944 : Unsatisfiable (PosFin 57) f1944 := by
  apply lratCheckerSound f1944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1944
  · intro a ha; simp [p1944] at ha; subst a; trivial
  · exact checked1944
theorem derived1944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1944 := by
  apply localUnsat_implies_entails f1944 [c1883, c1779, c98, c1943, c83, c1941, c1931, c1860, c1936, c841, c155, c3, c1930, c63, c40, c1671, c968, c338, c360, c59, c976, c11, c163, c158, c1939, c44, c296, c124, c66, c1445, c369] c1944 unsat1944 (by rfl) a
  have h0 : Entails.eval a c1883 := derived1883 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1943 := derived1943 a h
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c1941 := derived1941 a h
  have h6 : Entails.eval a c1931 := derived1931 a h
  have h7 : Entails.eval a c1860 := derived1860 a h
  have h8 : Entails.eval a c1936 := derived1936 a h
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c1930 := derived1930 a h
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c1671 := derived1671 a h
  have h16 : Entails.eval a c968 := derived968 a h
  have h17 : Entails.eval a c338 := h 337 (by decide)
  have h18 : Entails.eval a c360 := h 359 (by decide)
  have h19 : Entails.eval a c59 := h 58 (by decide)
  have h20 : Entails.eval a c976 := derived976 a h
  have h21 : Entails.eval a c11 := h 10 (by decide)
  have h22 : Entails.eval a c163 := h 162 (by decide)
  have h23 : Entails.eval a c158 := h 157 (by decide)
  have h24 : Entails.eval a c1939 := derived1939 a h
  have h25 : Entails.eval a c44 := h 43 (by decide)
  have h26 : Entails.eval a c296 := h 295 (by decide)
  have h27 : Entails.eval a c124 := h 123 (by decide)
  have h28 : Entails.eval a c66 := h 65 (by decide)
  have h29 : Entails.eval a c1445 := derived1445 a h
  have h30 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1945 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c1860, some c1883, some c1930, some c63, some c1931, some c1936, some c841, some c155, some c1943, some c83, some c1944, some c1118, some c11, some c79, some c59, some c322, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1945 : lratChecker f1945 p1945 = .success := by decide +kernel
theorem unsat1945 : Unsatisfiable (PosFin 57) f1945 := by
  apply lratCheckerSound f1945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1945
  · intro a ha; simp [p1945] at ha; subst a; trivial
  · exact checked1945
theorem derived1945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1945 := by
  apply localUnsat_implies_entails f1945 [c98, c1860, c1883, c1930, c63, c1931, c1936, c841, c155, c1943, c83, c1944, c1118, c11, c79, c59, c322] c1945 unsat1945 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c1883 := derived1883 a h
  have h3 : Entails.eval a c1930 := derived1930 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c1931 := derived1931 a h
  have h6 : Entails.eval a c1936 := derived1936 a h
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c1943 := derived1943 a h
  have h10 : Entails.eval a c83 := h 82 (by decide)
  have h11 : Entails.eval a c1944 := derived1944 a h
  have h12 : Entails.eval a c1118 := derived1118 a h
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c79 := h 78 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1946 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c1945, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1946 : lratChecker f1946 p1946 = .success := by decide +kernel
theorem unsat1946 : Unsatisfiable (PosFin 57) f1946 := by
  apply lratCheckerSound f1946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1946
  · intro a ha; simp [p1946] at ha; subst a; trivial
  · exact checked1946
theorem derived1946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1946 := by
  apply localUnsat_implies_entails f1946 [c1779, c1945] c1946 unsat1946 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c1945 := derived1945 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1947 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c77, some c320, some c53, some c57, some c345, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1947 : lratChecker f1947 p1947 = .success := by decide +kernel
theorem unsat1947 : Unsatisfiable (PosFin 57) f1947 := by
  apply lratCheckerSound f1947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1947
  · intro a ha; simp [p1947] at ha; subst a; trivial
  · exact checked1947
theorem derived1947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1947 := by
  apply localUnsat_implies_entails f1947 [c1946, c77, c320, c53, c57, c345] c1947 unsat1947 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1948 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨42, by decide⟩, false), (⟨34, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨2, by decide⟩, false), (⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c101, some c370, some c316, some c33, some c55, some c276, some c324, some c49, some c362, some c1289, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1948 : lratChecker f1948 p1948 = .success := by decide +kernel
theorem unsat1948 : Unsatisfiable (PosFin 57) f1948 := by
  apply lratCheckerSound f1948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1948
  · intro a ha; simp [p1948] at ha; subst a; trivial
  · exact checked1948
theorem derived1948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1948 := by
  apply localUnsat_implies_entails f1948 [c1946, c101, c370, c316, c33, c55, c276, c324, c49, c362, c1289] c1948 unsat1948 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c362 := h 361 (by decide)
  have h10 : Entails.eval a c1289 := derived1289 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1949 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨11, by decide⟩, true), (⟨34, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c71, some c841, some c72, some c1947, some c370, some c84, some c168, some c101, some c7, some c1645, some c1251, some c80, some c709, some c368, some c1322, some c1948, some c65, some c158, some c133, some c55, some c1341, some c324, some c48, some c362, some c1289, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1949 : lratChecker f1949 p1949 = .success := by decide +kernel
theorem unsat1949 : Unsatisfiable (PosFin 57) f1949 := by
  apply lratCheckerSound f1949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1949
  · intro a ha; simp [p1949] at ha; subst a; trivial
  · exact checked1949
theorem derived1949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1949 := by
  apply localUnsat_implies_entails f1949 [c1946, c71, c841, c72, c1947, c370, c84, c168, c101, c7, c1645, c1251, c80, c709, c368, c1322, c1948, c65, c158, c133, c55, c1341, c324, c48, c362, c1289] c1949 unsat1949 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c1947 := derived1947 a h
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c1645 := derived1645 a h
  have h11 : Entails.eval a c1251 := derived1251 a h
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c709 := derived709 a h
  have h14 : Entails.eval a c368 := h 367 (by decide)
  have h15 : Entails.eval a c1322 := derived1322 a h
  have h16 : Entails.eval a c1948 := derived1948 a h
  have h17 : Entails.eval a c65 := h 64 (by decide)
  have h18 : Entails.eval a c158 := h 157 (by decide)
  have h19 : Entails.eval a c133 := h 132 (by decide)
  have h20 : Entails.eval a c55 := h 54 (by decide)
  have h21 : Entails.eval a c1341 := derived1341 a h
  have h22 : Entails.eval a c324 := h 323 (by decide)
  have h23 : Entails.eval a c48 := h 47 (by decide)
  have h24 : Entails.eval a c362 := h 361 (by decide)
  have h25 : Entails.eval a c1289 := derived1289 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1950 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c841, some c72, some c1633, some c1645, some c101, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1950 : lratChecker f1950 p1950 = .success := by decide +kernel
theorem unsat1950 : Unsatisfiable (PosFin 57) f1950 := by
  apply lratCheckerSound f1950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1950
  · intro a ha; simp [p1950] at ha; subst a; trivial
  · exact checked1950
theorem derived1950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1950 := by
  apply localUnsat_implies_entails f1950 [c71, c841, c72, c1633, c1645, c101] c1950 unsat1950 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1633 := derived1633 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1951 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c10, some c172, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1951 : lratChecker f1951 p1951 = .success := by decide +kernel
theorem unsat1951 : Unsatisfiable (PosFin 57) f1951 := by
  apply lratCheckerSound f1951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1951
  · intro a ha; simp [p1951] at ha; subst a; trivial
  · exact checked1951
theorem derived1951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1951 := by
  apply localUnsat_implies_entails f1951 [c5, c10, c172] c1951 unsat1951 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1952 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c55, some c60, some c345, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1952 : lratChecker f1952 p1952 = .success := by decide +kernel
theorem unsat1952 : Unsatisfiable (PosFin 57) f1952 := by
  apply lratCheckerSound f1952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1952
  · intro a ha; simp [p1952] at ha; subst a; trivial
  · exact checked1952
theorem derived1952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1952 := by
  apply localUnsat_implies_entails f1952 [c1946, c55, c60, c345] c1952 unsat1952 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1953 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c841, some c72, some c1947, some c1950, some c100, some c80, some c1952, some c324, some c1251, some c153, some c10, some c1118, some c376, some c356, some c320, some c1949, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1953 : lratChecker f1953 p1953 = .success := by decide +kernel
theorem unsat1953 : Unsatisfiable (PosFin 57) f1953 := by
  apply lratCheckerSound f1953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1953
  · intro a ha; simp [p1953] at ha; subst a; trivial
  · exact checked1953
theorem derived1953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1953 := by
  apply localUnsat_implies_entails f1953 [c71, c841, c72, c1947, c1950, c100, c80, c1952, c324, c1251, c153, c10, c1118, c376, c356, c320, c1949] c1953 unsat1953 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1947 := derived1947 a h
  have h4 : Entails.eval a c1950 := derived1950 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c1952 := derived1952 a h
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c1251 := derived1251 a h
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c1118 := derived1118 a h
  have h13 : Entails.eval a c376 := h 375 (by decide)
  have h14 : Entails.eval a c356 := h 355 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  have h16 : Entails.eval a c1949 := derived1949 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1954 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c841, some c72, some c1947, some c1950, some c100, some c1251, some c1952, some c1953, some c340, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1954 : lratChecker f1954 p1954 = .success := by decide +kernel
theorem unsat1954 : Unsatisfiable (PosFin 57) f1954 := by
  apply lratCheckerSound f1954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1954
  · intro a ha; simp [p1954] at ha; subst a; trivial
  · exact checked1954
theorem derived1954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1954 := by
  apply localUnsat_implies_entails f1954 [c71, c841, c72, c1947, c1950, c100, c1251, c1952, c1953, c340] c1954 unsat1954 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1947 := derived1947 a h
  have h4 : Entails.eval a c1950 := derived1950 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c1251 := derived1251 a h
  have h7 : Entails.eval a c1952 := derived1952 a h
  have h8 : Entails.eval a c1953 := derived1953 a h
  have h9 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1955 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c77, some c320, some c53, some c57, some c347, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1955 : lratChecker f1955 p1955 = .success := by decide +kernel
theorem unsat1955 : Unsatisfiable (PosFin 57) f1955 := by
  apply lratCheckerSound f1955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1955
  · intro a ha; simp [p1955] at ha; subst a; trivial
  · exact checked1955
theorem derived1955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1955 := by
  apply localUnsat_implies_entails f1955 [c1946, c77, c320, c53, c57, c347] c1955 unsat1955 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1956 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c43, some c48, some c49, some c307, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1956 : lratChecker f1956 p1956 = .success := by decide +kernel
theorem unsat1956 : Unsatisfiable (PosFin 57) f1956 := by
  apply lratCheckerSound f1956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1956
  · intro a ha; simp [p1956] at ha; subst a; trivial
  · exact checked1956
theorem derived1956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1956 := by
  apply localUnsat_implies_entails f1956 [c1946, c43, c48, c49, c307] c1956 unsat1956 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1957 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨53, by decide⟩, true), (⟨28, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨37, by decide⟩, true), (⟨48, by decide⟩, false), (⟨5, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1955, some c100, some c80, some c71, some c841, some c320, some c370, some c368, some c278, some c84, some c956, some c190, some c264, some c1951, some c21, some c23, some c284, some c1118, some c1408, some c362, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1957 : lratChecker f1957 p1957 = .success := by decide +kernel
theorem unsat1957 : Unsatisfiable (PosFin 57) f1957 := by
  apply lratCheckerSound f1957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1957
  · intro a ha; simp [p1957] at ha; subst a; trivial
  · exact checked1957
theorem derived1957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1957 := by
  apply localUnsat_implies_entails f1957 [c1955, c100, c80, c71, c841, c320, c370, c368, c278, c84, c956, c190, c264, c1951, c21, c23, c284, c1118, c1408, c362] c1957 unsat1957 (by rfl) a
  have h0 : Entails.eval a c1955 := derived1955 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c956 := derived956 a h
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c1951 := derived1951 a h
  have h14 : Entails.eval a c21 := h 20 (by decide)
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c284 := h 283 (by decide)
  have h17 : Entails.eval a c1118 := derived1118 a h
  have h18 : Entails.eval a c1408 := derived1408 a h
  have h19 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1958 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c841, some c72, some c1955, some c1950, some c100, some c1956, some c80, some c1251, some c1954, some c1957, some c161, some c5, some c1118, some c376, some c297, some c356, some c284, some c193, some c26, some c191, some c339, some c337, some c60, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1958 : lratChecker f1958 p1958 = .success := by decide +kernel
theorem unsat1958 : Unsatisfiable (PosFin 57) f1958 := by
  apply lratCheckerSound f1958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1958
  · intro a ha; simp [p1958] at ha; subst a; trivial
  · exact checked1958
theorem derived1958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1958 := by
  apply localUnsat_implies_entails f1958 [c71, c841, c72, c1955, c1950, c100, c1956, c80, c1251, c1954, c1957, c161, c5, c1118, c376, c297, c356, c284, c193, c26, c191, c339, c337, c60] c1958 unsat1958 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1955 := derived1955 a h
  have h4 : Entails.eval a c1950 := derived1950 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c1956 := derived1956 a h
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c1251 := derived1251 a h
  have h9 : Entails.eval a c1954 := derived1954 a h
  have h10 : Entails.eval a c1957 := derived1957 a h
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c1118 := derived1118 a h
  have h14 : Entails.eval a c376 := h 375 (by decide)
  have h15 : Entails.eval a c297 := h 296 (by decide)
  have h16 : Entails.eval a c356 := h 355 (by decide)
  have h17 : Entails.eval a c284 := h 283 (by decide)
  have h18 : Entails.eval a c193 := h 192 (by decide)
  have h19 : Entails.eval a c26 := h 25 (by decide)
  have h20 : Entails.eval a c191 := h 190 (by decide)
  have h21 : Entails.eval a c339 := h 338 (by decide)
  have h22 : Entails.eval a c337 := h 336 (by decide)
  have h23 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1959 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c71, some c841, some c72, some c1955, some c1950, some c100, some c1251, some c80, some c1956, some c1958, some c380, some c373, some c1118, some c65, some c5, some c10, some c316, some c366, some c1245, some c55, some c358, some c1277, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1959 : lratChecker f1959 p1959 = .success := by decide +kernel
theorem unsat1959 : Unsatisfiable (PosFin 57) f1959 := by
  apply lratCheckerSound f1959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1959
  · intro a ha; simp [p1959] at ha; subst a; trivial
  · exact checked1959
theorem derived1959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1959 := by
  apply localUnsat_implies_entails f1959 [c1946, c71, c841, c72, c1955, c1950, c100, c1251, c80, c1956, c1958, c380, c373, c1118, c65, c5, c10, c316, c366, c1245, c55, c358, c1277] c1959 unsat1959 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c1955 := derived1955 a h
  have h5 : Entails.eval a c1950 := derived1950 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c1251 := derived1251 a h
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c1956 := derived1956 a h
  have h10 : Entails.eval a c1958 := derived1958 a h
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c373 := h 372 (by decide)
  have h13 : Entails.eval a c1118 := derived1118 a h
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c5 := h 4 (by decide)
  have h16 : Entails.eval a c10 := h 9 (by decide)
  have h17 : Entails.eval a c316 := h 315 (by decide)
  have h18 : Entails.eval a c366 := h 365 (by decide)
  have h19 : Entails.eval a c1245 := derived1245 a h
  have h20 : Entails.eval a c55 := h 54 (by decide)
  have h21 : Entails.eval a c358 := h 357 (by decide)
  have h22 : Entails.eval a c1277 := derived1277 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1960 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨15, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c168, some c15, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1960 : lratChecker f1960 p1960 = .success := by decide +kernel
theorem unsat1960 : Unsatisfiable (PosFin 57) f1960 := by
  apply lratCheckerSound f1960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1960
  · intro a ha; simp [p1960] at ha; subst a; trivial
  · exact checked1960
theorem derived1960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1960 := by
  apply localUnsat_implies_entails f1960 [c84, c168, c15] c1960 unsat1960 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1961 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false), (⟨16, by decide⟩, false), (⟨2, by decide⟩, true), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c178, some c377, some c85, some c172, some c1024, some c140, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1961 : lratChecker f1961 p1961 = .success := by decide +kernel
theorem unsat1961 : Unsatisfiable (PosFin 57) f1961 := by
  apply lratCheckerSound f1961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1961
  · intro a ha; simp [p1961] at ha; subst a; trivial
  · exact checked1961
theorem derived1961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1961 := by
  apply localUnsat_implies_entails f1961 [c1946, c178, c377, c85, c172, c1024, c140] c1961 unsat1961 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c377 := h 376 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c1024 := derived1024 a h
  have h6 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1962 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1959, some c71, some c841, some c77, some c1955, some c156, some c1960, some c369, some c80, some c361, some c164, some c103, some c12, some c1765, some c15, some c1961, some c380, some c373, some c86, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1962 : lratChecker f1962 p1962 = .success := by decide +kernel
theorem unsat1962 : Unsatisfiable (PosFin 57) f1962 := by
  apply lratCheckerSound f1962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1962
  · intro a ha; simp [p1962] at ha; subst a; trivial
  · exact checked1962
theorem derived1962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1962 := by
  apply localUnsat_implies_entails f1962 [c1946, c1959, c71, c841, c77, c1955, c156, c1960, c369, c80, c361, c164, c103, c12, c1765, c15, c1961, c380, c373, c86] c1962 unsat1962 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1959 := derived1959 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c1955 := derived1955 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c1960 := derived1960 a h
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c1765 := derived1765 a h
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c1961 := derived1961 a h
  have h17 : Entails.eval a c380 := h 379 (by decide)
  have h18 : Entails.eval a c373 := h 372 (by decide)
  have h19 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1963 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨54, by decide⟩, true), (⟨38, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1963 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c90, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1963 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1963 : lratChecker f1963 p1963 = .success := by decide +kernel
theorem unsat1963 : Unsatisfiable (PosFin 57) f1963 := by
  apply lratCheckerSound f1963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1963
  · intro a ha; simp [p1963] at ha; subst a; trivial
  · exact checked1963
theorem derived1963 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1963 := by
  apply localUnsat_implies_entails f1963 [c1632, c90] c1963 unsat1963 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1964 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1964 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c84, some c71, some c327, some c366, some c64, some c38, some c65, some c347, some c33, some c291, some c290, some c1963, some c100, some c80, some c1461, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1964 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1964 : lratChecker f1964 p1964 = .success := by decide +kernel
theorem unsat1964 : Unsatisfiable (PosFin 57) f1964 := by
  apply lratCheckerSound f1964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1964
  · intro a ha; simp [p1964] at ha; subst a; trivial
  · exact checked1964
theorem derived1964 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1964 := by
  apply localUnsat_implies_entails f1964 [c1946, c84, c71, c327, c366, c64, c38, c65, c347, c33, c291, c290, c1963, c100, c80, c1461] c1964 unsat1964 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c347 := h 346 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c291 := h 290 (by decide)
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c1963 := derived1963 a h
  have h13 : Entails.eval a c100 := h 99 (by decide)
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c1461 := derived1461 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1965 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨16, by decide⟩, false), (⟨2, by decide⟩, false), (⟨8, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1965 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c102, some c71, some c841, some c1345, some c172, some c1670, some c377, some c52, some c708, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1965 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1965 : lratChecker f1965 p1965 = .success := by decide +kernel
theorem unsat1965 : Unsatisfiable (PosFin 57) f1965 := by
  apply lratCheckerSound f1965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1965
  · intro a ha; simp [p1965] at ha; subst a; trivial
  · exact checked1965
theorem derived1965 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1965 := by
  apply localUnsat_implies_entails f1965 [c8, c102, c71, c841, c1345, c172, c1670, c377, c52, c708] c1965 unsat1965 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c1345 := derived1345 a h
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c1670 := derived1670 a h
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c708 := derived708 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1966 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1966 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c71, some c841, some c1959, some c1962, some c102, some c84, some c1964, some c156, some c8, some c161, some c369, some c80, some c361, some c164, some c100, some c12, some c1965, some c380, some c373, some c86, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1966 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1966 : lratChecker f1966 p1966 = .success := by decide +kernel
theorem unsat1966 : Unsatisfiable (PosFin 57) f1966 := by
  apply lratCheckerSound f1966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1966
  · intro a ha; simp [p1966] at ha; subst a; trivial
  · exact checked1966
theorem derived1966 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1966 := by
  apply localUnsat_implies_entails f1966 [c1946, c71, c841, c1959, c1962, c102, c84, c1964, c156, c8, c161, c369, c80, c361, c164, c100, c12, c1965, c380, c373, c86] c1966 unsat1966 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c1959 := derived1959 a h
  have h4 : Entails.eval a c1962 := derived1962 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c1964 := derived1964 a h
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c369 := h 368 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c361 := h 360 (by decide)
  have h14 : Entails.eval a c164 := h 163 (by decide)
  have h15 : Entails.eval a c100 := h 99 (by decide)
  have h16 : Entails.eval a c12 := h 11 (by decide)
  have h17 : Entails.eval a c1965 := derived1965 a h
  have h18 : Entails.eval a c380 := h 379 (by decide)
  have h19 : Entails.eval a c373 := h 372 (by decide)
  have h20 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1967 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1967 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c841, some c72, some c95, some c1955, some c1964, some c101, some c1251, some c1394, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1967 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1967 : lratChecker f1967 p1967 = .success := by decide +kernel
theorem unsat1967 : Unsatisfiable (PosFin 57) f1967 := by
  apply lratCheckerSound f1967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1967
  · intro a ha; simp [p1967] at ha; subst a; trivial
  · exact checked1967
theorem derived1967 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1967 := by
  apply localUnsat_implies_entails f1967 [c71, c841, c72, c95, c1955, c1964, c101, c1251, c1394] c1967 unsat1967 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c1955 := derived1955 a h
  have h5 : Entails.eval a c1964 := derived1964 a h
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c1251 := derived1251 a h
  have h8 : Entails.eval a c1394 := derived1394 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1968 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1968 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1966, some c1967, some c71, some c841, some c77, some c1955, some c156, some c1960, some c369, some c80, some c361, some c164, some c968, some c1118, some c359, some c9, some c1765, some c86, some c1025, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1968 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1968 : lratChecker f1968 p1968 = .success := by decide +kernel
theorem unsat1968 : Unsatisfiable (PosFin 57) f1968 := by
  apply lratCheckerSound f1968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1968
  · intro a ha; simp [p1968] at ha; subst a; trivial
  · exact checked1968
theorem derived1968 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1968 := by
  apply localUnsat_implies_entails f1968 [c1946, c1966, c1967, c71, c841, c77, c1955, c156, c1960, c369, c80, c361, c164, c968, c1118, c359, c9, c1765, c86, c1025] c1968 unsat1968 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1966 := derived1966 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c1955 := derived1955 a h
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c1960 := derived1960 a h
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c164 := h 163 (by decide)
  have h13 : Entails.eval a c968 := derived968 a h
  have h14 : Entails.eval a c1118 := derived1118 a h
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c1765 := derived1765 a h
  have h18 : Entails.eval a c86 := h 85 (by decide)
  have h19 : Entails.eval a c1025 := derived1025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1969 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨33, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1969 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c33, some c305, some c291, some c37, some c843, some c65, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p1969 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1969 : lratChecker f1969 p1969 = .success := by decide +kernel
theorem unsat1969 : Unsatisfiable (PosFin 57) f1969 := by
  apply lratCheckerSound f1969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1969
  · intro a ha; simp [p1969] at ha; subst a; trivial
  · exact checked1969
theorem derived1969 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1969 := by
  apply localUnsat_implies_entails f1969 [c1946, c33, c305, c291, c37, c843, c65] c1969 unsat1969 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c291 := h 290 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c843 := derived843 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1970 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1970 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c71, some c841, some c1966, some c1967, some c1968, some c102, some c84, some c1964, some c156, some c8, some c161, some c369, some c80, some c100, some c596, some c1663, some c346, some c33, some c54, some c1969, some c39, some c52, some c339, some c290, some c86, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1970 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1970 : lratChecker f1970 p1970 = .success := by decide +kernel
theorem unsat1970 : Unsatisfiable (PosFin 57) f1970 := by
  apply lratCheckerSound f1970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1970
  · intro a ha; simp [p1970] at ha; subst a; trivial
  · exact checked1970
theorem derived1970 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1970 := by
  apply localUnsat_implies_entails f1970 [c1946, c71, c841, c1966, c1967, c1968, c102, c84, c1964, c156, c8, c161, c369, c80, c100, c596, c1663, c346, c33, c54, c1969, c39, c52, c339, c290, c86] c1970 unsat1970 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c1966 := derived1966 a h
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c1968 := derived1968 a h
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c1964 := derived1964 a h
  have h9 : Entails.eval a c156 := h 155 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c369 := h 368 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c100 := h 99 (by decide)
  have h15 : Entails.eval a c596 := derived596 a h
  have h16 : Entails.eval a c1663 := derived1663 a h
  have h17 : Entails.eval a c346 := h 345 (by decide)
  have h18 : Entails.eval a c33 := h 32 (by decide)
  have h19 : Entails.eval a c54 := h 53 (by decide)
  have h20 : Entails.eval a c1969 := derived1969 a h
  have h21 : Entails.eval a c39 := h 38 (by decide)
  have h22 : Entails.eval a c52 := h 51 (by decide)
  have h23 : Entails.eval a c339 := h 338 (by decide)
  have h24 : Entails.eval a c290 := h 289 (by decide)
  have h25 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1971 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨31, by decide⟩, false), (⟨34, by decide⟩, false), (⟨42, by decide⟩, false), (⟨15, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1971 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c368, some c162, some c67, some c188, some c127, some c380, some c35, some c172, some c333, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p1971 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1971 : lratChecker f1971 p1971 = .success := by decide +kernel
theorem unsat1971 : Unsatisfiable (PosFin 57) f1971 := by
  apply lratCheckerSound f1971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1971
  · intro a ha; simp [p1971] at ha; subst a; trivial
  · exact checked1971
theorem derived1971 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1971 := by
  apply localUnsat_implies_entails f1971 [c369, c368, c162, c67, c188, c127, c380, c35, c172, c333] c1971 unsat1971 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1972 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1972 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c299, some c376, some c42, some c85, some c291, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p1972 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1972 : lratChecker f1972 p1972 = .success := by decide +kernel
theorem unsat1972 : Unsatisfiable (PosFin 57) f1972 := by
  apply lratCheckerSound f1972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1972
  · intro a ha; simp [p1972] at ha; subst a; trivial
  · exact checked1972
theorem derived1972 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1972 := by
  apply localUnsat_implies_entails f1972 [c1946, c299, c376, c42, c85, c291] c1972 unsat1972 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1973 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨31, by decide⟩, false), (⟨34, by decide⟩, false), (⟨48, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1973 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c841, some c1241, some c1971, some c361, some c1972, some c359, some c86, some c1025, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1973 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1973 : lratChecker f1973 p1973 = .success := by decide +kernel
theorem unsat1973 : Unsatisfiable (PosFin 57) f1973 := by
  apply lratCheckerSound f1973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1973
  · intro a ha; simp [p1973] at ha; subst a; trivial
  · exact checked1973
theorem derived1973 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1973 := by
  apply localUnsat_implies_entails f1973 [c1946, c841, c1241, c1971, c361, c1972, c359, c86, c1025] c1973 unsat1973 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c1241 := derived1241 a h
  have h3 : Entails.eval a c1971 := derived1971 a h
  have h4 : Entails.eval a c361 := h 360 (by decide)
  have h5 : Entails.eval a c1972 := derived1972 a h
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c1025 := derived1025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1974 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1974 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c60, some c318, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1974 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1974 : lratChecker f1974 p1974 = .success := by decide +kernel
theorem unsat1974 : Unsatisfiable (PosFin 57) f1974 := by
  apply lratCheckerSound f1974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1974
  · intro a ha; simp [p1974] at ha; subst a; trivial
  · exact checked1974
theorem derived1974 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1974 := by
  apply localUnsat_implies_entails f1974 [c80, c60, c318] c1974 unsat1974 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1975 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨14, by decide⟩, true), (⟨38, by decide⟩, true), (⟨31, by decide⟩, false), (⟨34, by decide⟩, false), (⟨9, by decide⟩, true), (⟨48, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1975 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c103, some c841, some c976, some c369, some c359, some c162, some c154, some c968, some c380, some c299, some c9, some c88, some c171, some c333, some c291, some c266, some c41, some c295, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p1975 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1975 : lratChecker f1975 p1975 = .success := by decide +kernel
theorem unsat1975 : Unsatisfiable (PosFin 57) f1975 := by
  apply lratCheckerSound f1975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1975
  · intro a ha; simp [p1975] at ha; subst a; trivial
  · exact checked1975
theorem derived1975 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1975 := by
  apply localUnsat_implies_entails f1975 [c1946, c103, c841, c976, c369, c359, c162, c154, c968, c380, c299, c9, c88, c171, c333, c291, c266, c41, c295] c1975 unsat1975 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c976 := derived976 a h
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c162 := h 161 (by decide)
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c968 := derived968 a h
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c333 := h 332 (by decide)
  have h15 : Entails.eval a c291 := h 290 (by decide)
  have h16 : Entails.eval a c266 := h 265 (by decide)
  have h17 : Entails.eval a c41 := h 40 (by decide)
  have h18 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1976 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1976 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1970, some c71, some c841, some c77, some c1955, some c156, some c148, some c183, some c57, some c39, some c350, some c140, some c64, some c1241, some c1973, some c1974, some c103, some c1975, some c361, some c968, some c1118, some c359, some c188, some c127, some c317, some c1961, some c191, some c266, some c597, some c373, some c25, some c309, some c85, some c192, some c334, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1976 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked1976 : lratChecker f1976 p1976 = .success := by decide +kernel
theorem unsat1976 : Unsatisfiable (PosFin 57) f1976 := by
  apply lratCheckerSound f1976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1976
  · intro a ha; simp [p1976] at ha; subst a; trivial
  · exact checked1976
theorem derived1976 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1976 := by
  apply localUnsat_implies_entails f1976 [c1946, c1970, c71, c841, c77, c1955, c156, c148, c183, c57, c39, c350, c140, c64, c1241, c1973, c1974, c103, c1975, c361, c968, c1118, c359, c188, c127, c317, c1961, c191, c266, c597, c373, c25, c309, c85, c192, c334] c1976 unsat1976 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1970 := derived1970 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c1955 := derived1955 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c350 := h 349 (by decide)
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c1241 := derived1241 a h
  have h15 : Entails.eval a c1973 := derived1973 a h
  have h16 : Entails.eval a c1974 := derived1974 a h
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c1975 := derived1975 a h
  have h19 : Entails.eval a c361 := h 360 (by decide)
  have h20 : Entails.eval a c968 := derived968 a h
  have h21 : Entails.eval a c1118 := derived1118 a h
  have h22 : Entails.eval a c359 := h 358 (by decide)
  have h23 : Entails.eval a c188 := h 187 (by decide)
  have h24 : Entails.eval a c127 := h 126 (by decide)
  have h25 : Entails.eval a c317 := h 316 (by decide)
  have h26 : Entails.eval a c1961 := derived1961 a h
  have h27 : Entails.eval a c191 := h 190 (by decide)
  have h28 : Entails.eval a c266 := h 265 (by decide)
  have h29 : Entails.eval a c597 := derived597 a h
  have h30 : Entails.eval a c373 := h 372 (by decide)
  have h31 : Entails.eval a c25 := h 24 (by decide)
  have h32 : Entails.eval a c309 := h 308 (by decide)
  have h33 : Entails.eval a c85 := h 84 (by decide)
  have h34 : Entails.eval a c192 := h 191 (by decide)
  have h35 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1977 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1977 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1976, some c1964, some c102, some c101, some c1645, some c320, some c1956, some c80, some c278, some c190, some c21, some c1967, some c1251, some c1325, some c297, some c1957, some c191, some c709, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1977 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1977 : lratChecker f1977 p1977 = .success := by decide +kernel
theorem unsat1977 : Unsatisfiable (PosFin 57) f1977 := by
  apply lratCheckerSound f1977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1977
  · intro a ha; simp [p1977] at ha; subst a; trivial
  · exact checked1977
theorem derived1977 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1977 := by
  apply localUnsat_implies_entails f1977 [c1976, c1964, c102, c101, c1645, c320, c1956, c80, c278, c190, c21, c1967, c1251, c1325, c297, c1957, c191, c709] c1977 unsat1977 (by rfl) a
  have h0 : Entails.eval a c1976 := derived1976 a h
  have h1 : Entails.eval a c1964 := derived1964 a h
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c1956 := derived1956 a h
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c1967 := derived1967 a h
  have h12 : Entails.eval a c1251 := derived1251 a h
  have h13 : Entails.eval a c1325 := derived1325 a h
  have h14 : Entails.eval a c297 := h 296 (by decide)
  have h15 : Entails.eval a c1957 := derived1957 a h
  have h16 : Entails.eval a c191 := h 190 (by decide)
  have h17 : Entails.eval a c709 := derived709 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1978 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1978 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1946, some c1976, some c1964, some c102, some c1967, some c101, some c1956, some c80, some c1251, some c1645, some c71, some c841, some c370, some c368, some c956, some c1977, some c1118, some c358, some c1951, some c1277, some c1697, some c55, some c316, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1978 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1978 : lratChecker f1978 p1978 = .success := by decide +kernel
theorem unsat1978 : Unsatisfiable (PosFin 57) f1978 := by
  apply lratCheckerSound f1978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1978
  · intro a ha; simp [p1978] at ha; subst a; trivial
  · exact checked1978
theorem derived1978 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1978 := by
  apply localUnsat_implies_entails f1978 [c1946, c1976, c1964, c102, c1967, c101, c1956, c80, c1251, c1645, c71, c841, c370, c368, c956, c1977, c1118, c358, c1951, c1277, c1697, c55, c316] c1978 unsat1978 (by rfl) a
  have h0 : Entails.eval a c1946 := derived1946 a h
  have h1 : Entails.eval a c1976 := derived1976 a h
  have h2 : Entails.eval a c1964 := derived1964 a h
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c1956 := derived1956 a h
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c1251 := derived1251 a h
  have h9 : Entails.eval a c1645 := derived1645 a h
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c370 := h 369 (by decide)
  have h13 : Entails.eval a c368 := h 367 (by decide)
  have h14 : Entails.eval a c956 := derived956 a h
  have h15 : Entails.eval a c1977 := derived1977 a h
  have h16 : Entails.eval a c1118 := derived1118 a h
  have h17 : Entails.eval a c358 := h 357 (by decide)
  have h18 : Entails.eval a c1951 := derived1951 a h
  have h19 : Entails.eval a c1277 := derived1277 a h
  have h20 : Entails.eval a c1697 := derived1697 a h
  have h21 : Entails.eval a c55 := h 54 (by decide)
  have h22 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1979 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨42, by decide⟩, true), (⟨5, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨48, by decide⟩, false), (⟨2, by decide⟩, false), (⟨40, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1979 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c102, some c101, some c1956, some c1251, some c1325, some c376, some c297, some c1951, some c1287, some c356, some c150, some c284, some c7, some c162, some c327, some c285, some c270, some c266, some c709, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1979 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1979 : lratChecker f1979 p1979 = .success := by decide +kernel
theorem unsat1979 : Unsatisfiable (PosFin 57) f1979 := by
  apply lratCheckerSound f1979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1979
  · intro a ha; simp [p1979] at ha; subst a; trivial
  · exact checked1979
theorem derived1979 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1979 := by
  apply localUnsat_implies_entails f1979 [c102, c101, c1956, c1251, c1325, c376, c297, c1951, c1287, c356, c150, c284, c7, c162, c327, c285, c270, c266, c709] c1979 unsat1979 (by rfl) a
  have h0 : Entails.eval a c102 := h 101 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c1956 := derived1956 a h
  have h3 : Entails.eval a c1251 := derived1251 a h
  have h4 : Entails.eval a c1325 := derived1325 a h
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c1951 := derived1951 a h
  have h8 : Entails.eval a c1287 := derived1287 a h
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c150 := h 149 (by decide)
  have h11 : Entails.eval a c284 := h 283 (by decide)
  have h12 : Entails.eval a c7 := h 6 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c285 := h 284 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c266 := h 265 (by decide)
  have h18 : Entails.eval a c709 := derived709 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1980 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1980 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1976, some c71, some c841, some c1964, some c101, some c102, some c1645, some c1251, some c80, some c1967, some c1978, some c1979, some c1118, some c5, some c10, some c1282, some c150, some c1245, some c1345, some c1248, some c1697, some c358, some c366, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1980 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1980 : lratChecker f1980 p1980 = .success := by decide +kernel
theorem unsat1980 : Unsatisfiable (PosFin 57) f1980 := by
  apply lratCheckerSound f1980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1980
  · intro a ha; simp [p1980] at ha; subst a; trivial
  · exact checked1980
theorem derived1980 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1980 := by
  apply localUnsat_implies_entails f1980 [c1976, c71, c841, c1964, c101, c102, c1645, c1251, c80, c1967, c1978, c1979, c1118, c5, c10, c1282, c150, c1245, c1345, c1248, c1697, c358, c366] c1980 unsat1980 (by rfl) a
  have h0 : Entails.eval a c1976 := derived1976 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c1964 := derived1964 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c1645 := derived1645 a h
  have h7 : Entails.eval a c1251 := derived1251 a h
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c1967 := derived1967 a h
  have h10 : Entails.eval a c1978 := derived1978 a h
  have h11 : Entails.eval a c1979 := derived1979 a h
  have h12 : Entails.eval a c1118 := derived1118 a h
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c10 := h 9 (by decide)
  have h15 : Entails.eval a c1282 := derived1282 a h
  have h16 : Entails.eval a c150 := h 149 (by decide)
  have h17 : Entails.eval a c1245 := derived1245 a h
  have h18 : Entails.eval a c1345 := derived1345 a h
  have h19 : Entails.eval a c1248 := derived1248 a h
  have h20 : Entails.eval a c1697 := derived1697 a h
  have h21 : Entails.eval a c358 := h 357 (by decide)
  have h22 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1980

end CochromaticTwenty.Certificates.B16_8_2
