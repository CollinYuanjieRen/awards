import MerLeanExperiment.Certificates.B16_4_2.Steps1400_1499

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1884 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1845, some c1874, some c1878, some c120, some c148, some c1881, some c1882, some c17, some c353, some c21, some c41, some c1763, some c171, some c127, some c323, some c1883, some c1077, some c357, some c1865, some c167, some c413, some c331, some c300, some c1861, some c238, some c270, some c268, some c216, some c1154, some c153, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1884 : lratChecker f1884 p1884 = .success := by decide +kernel
theorem unsat1884 : Unsatisfiable (PosFin 57) f1884 := by
  apply lratCheckerSound f1884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1884
  · intro a ha; simp [p1884] at ha; subst a; trivial
  · exact checked1884
theorem derived1884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1884 := by
  apply localUnsat_implies_entails f1884 [c1569, c1845, c1874, c1878, c120, c148, c1881, c1882, c17, c353, c21, c41, c1763, c171, c127, c323, c1883, c1077, c357, c1865, c167, c413, c331, c300, c1861, c238, c270, c268, c216, c1154, c153] c1884 unsat1884 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1874 := derived1874 a h
  have h3 : Entails.eval a c1878 := derived1878 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c148 := h 147 (by decide)
  have h6 : Entails.eval a c1881 := derived1881 a h
  have h7 : Entails.eval a c1882 := derived1882 a h
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c1763 := derived1763 a h
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c323 := h 322 (by decide)
  have h16 : Entails.eval a c1883 := derived1883 a h
  have h17 : Entails.eval a c1077 := derived1077 a h
  have h18 : Entails.eval a c357 := h 356 (by decide)
  have h19 : Entails.eval a c1865 := derived1865 a h
  have h20 : Entails.eval a c167 := h 166 (by decide)
  have h21 : Entails.eval a c413 := derived413 a h
  have h22 : Entails.eval a c331 := h 330 (by decide)
  have h23 : Entails.eval a c300 := h 299 (by decide)
  have h24 : Entails.eval a c1861 := derived1861 a h
  have h25 : Entails.eval a c238 := h 237 (by decide)
  have h26 : Entails.eval a c270 := h 269 (by decide)
  have h27 : Entails.eval a c268 := h 267 (by decide)
  have h28 : Entails.eval a c216 := h 215 (by decide)
  have h29 : Entails.eval a c1154 := derived1154 a h
  have h30 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1885 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1884, some c1874, some c1791, some c236, some c120, some c899, some c270, some c266, some c42, some c25, some c1282, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1885 : lratChecker f1885 p1885 = .success := by decide +kernel
theorem unsat1885 : Unsatisfiable (PosFin 57) f1885 := by
  apply lratCheckerSound f1885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1885
  · intro a ha; simp [p1885] at ha; subst a; trivial
  · exact checked1885
theorem derived1885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1885 := by
  apply localUnsat_implies_entails f1885 [c1569, c1884, c1874, c1791, c236, c120, c899, c270, c266, c42, c25, c1282] c1885 unsat1885 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1884 := derived1884 a h
  have h2 : Entails.eval a c1874 := derived1874 a h
  have h3 : Entails.eval a c1791 := derived1791 a h
  have h4 : Entails.eval a c236 := h 235 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c899 := derived899 a h
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c1282 := derived1282 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1886 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1845, some c1885, some c1884, some c202, some c203, some c118, some c146, some c1436, some c210, some c1875, some c37, some c45, some c1077, some c353, some c188, some c235, some c74, some c249, some c1282, some c53, some c96, some c318, some c317, some c309, some c281, some c342, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1886 : lratChecker f1886 p1886 = .success := by decide +kernel
theorem unsat1886 : Unsatisfiable (PosFin 57) f1886 := by
  apply lratCheckerSound f1886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1886
  · intro a ha; simp [p1886] at ha; subst a; trivial
  · exact checked1886
theorem derived1886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1886 := by
  apply localUnsat_implies_entails f1886 [c1733, c1569, c1845, c1885, c1884, c202, c203, c118, c146, c1436, c210, c1875, c37, c45, c1077, c353, c188, c235, c74, c249, c1282, c53, c96, c318, c317, c309, c281, c342] c1886 unsat1886 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1885 := derived1885 a h
  have h4 : Entails.eval a c1884 := derived1884 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c1436 := derived1436 a h
  have h10 : Entails.eval a c210 := h 209 (by decide)
  have h11 : Entails.eval a c1875 := derived1875 a h
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c1077 := derived1077 a h
  have h15 : Entails.eval a c353 := h 352 (by decide)
  have h16 : Entails.eval a c188 := h 187 (by decide)
  have h17 : Entails.eval a c235 := h 234 (by decide)
  have h18 : Entails.eval a c74 := h 73 (by decide)
  have h19 : Entails.eval a c249 := h 248 (by decide)
  have h20 : Entails.eval a c1282 := derived1282 a h
  have h21 : Entails.eval a c53 := h 52 (by decide)
  have h22 : Entails.eval a c96 := h 95 (by decide)
  have h23 : Entails.eval a c318 := h 317 (by decide)
  have h24 : Entails.eval a c317 := h 316 (by decide)
  have h25 : Entails.eval a c309 := h 308 (by decide)
  have h26 : Entails.eval a c281 := h 280 (by decide)
  have h27 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1887 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1845, some c1885, some c1884, some c1874, some c1886, some c120, some c148, some c266, some c212, some c1236, some c22, some c37, some c45, some c1282, some c353, some c252, some c339, some c186, some c53, some c21, some c41, some c75, some c1763, some c318, some c249, some c127, some c1754, some c312, some c92, some c298, some c369, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1887 : lratChecker f1887 p1887 = .success := by decide +kernel
theorem unsat1887 : Unsatisfiable (PosFin 57) f1887 := by
  apply lratCheckerSound f1887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1887
  · intro a ha; simp [p1887] at ha; subst a; trivial
  · exact checked1887
theorem derived1887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1887 := by
  apply localUnsat_implies_entails f1887 [c1733, c1569, c1845, c1885, c1884, c1874, c1886, c120, c148, c266, c212, c1236, c22, c37, c45, c1282, c353, c252, c339, c186, c53, c21, c41, c75, c1763, c318, c249, c127, c1754, c312, c92, c298, c369] c1887 unsat1887 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1885 := derived1885 a h
  have h4 : Entails.eval a c1884 := derived1884 a h
  have h5 : Entails.eval a c1874 := derived1874 a h
  have h6 : Entails.eval a c1886 := derived1886 a h
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c1236 := derived1236 a h
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c1282 := derived1282 a h
  have h16 : Entails.eval a c353 := h 352 (by decide)
  have h17 : Entails.eval a c252 := h 251 (by decide)
  have h18 : Entails.eval a c339 := h 338 (by decide)
  have h19 : Entails.eval a c186 := h 185 (by decide)
  have h20 : Entails.eval a c53 := h 52 (by decide)
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c41 := h 40 (by decide)
  have h23 : Entails.eval a c75 := h 74 (by decide)
  have h24 : Entails.eval a c1763 := derived1763 a h
  have h25 : Entails.eval a c318 := h 317 (by decide)
  have h26 : Entails.eval a c249 := h 248 (by decide)
  have h27 : Entails.eval a c127 := h 126 (by decide)
  have h28 : Entails.eval a c1754 := derived1754 a h
  have h29 : Entails.eval a c312 := h 311 (by decide)
  have h30 : Entails.eval a c92 := h 91 (by decide)
  have h31 : Entails.eval a c298 := h 297 (by decide)
  have h32 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1888 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1569, some c1733, some c1887, some c1884, some c1885, some c17, some c353, some c74, some c1282, some c25, some c1763, some c1874, some c202, some c1872, some c118, some c170, some c1739, some c269, some c166, some c136, some c207, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1888 : lratChecker f1888 p1888 = .success := by decide +kernel
theorem unsat1888 : Unsatisfiable (PosFin 57) f1888 := by
  apply lratCheckerSound f1888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1888
  · intro a ha; simp [p1888] at ha; subst a; trivial
  · exact checked1888
theorem derived1888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1888 := by
  apply localUnsat_implies_entails f1888 [c1845, c1569, c1733, c1887, c1884, c1885, c17, c353, c74, c1282, c25, c1763, c1874, c202, c1872, c118, c170, c1739, c269, c166, c136, c207] c1888 unsat1888 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1733 := derived1733 a h
  have h3 : Entails.eval a c1887 := derived1887 a h
  have h4 : Entails.eval a c1884 := derived1884 a h
  have h5 : Entails.eval a c1885 := derived1885 a h
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c1282 := derived1282 a h
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c1763 := derived1763 a h
  have h12 : Entails.eval a c1874 := derived1874 a h
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c1872 := derived1872 a h
  have h15 : Entails.eval a c118 := h 117 (by decide)
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c1739 := derived1739 a h
  have h18 : Entails.eval a c269 := h 268 (by decide)
  have h19 : Entails.eval a c166 := h 165 (by decide)
  have h20 : Entails.eval a c136 := h 135 (by decide)
  have h21 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1889 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1569, some c1874, some c1884, some c1885, some c1887, some c17, some c353, some c74, some c21, some c41, some c1763, some c1282, some c25, some c1888, some c120, some c148, some c270, some c1236, some c216, some c53, some c313, some c153, some c205, some c1154, some c169, some c156, some c590, some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1889 : lratChecker f1889 p1889 = .success := by decide +kernel
theorem unsat1889 : Unsatisfiable (PosFin 57) f1889 := by
  apply lratCheckerSound f1889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1889
  · intro a ha; simp [p1889] at ha; subst a; trivial
  · exact checked1889
theorem derived1889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1889 := by
  apply localUnsat_implies_entails f1889 [c1845, c1569, c1874, c1884, c1885, c1887, c17, c353, c74, c21, c41, c1763, c1282, c25, c1888, c120, c148, c270, c1236, c216, c53, c313, c153, c205, c1154, c169, c156, c590] c1889 unsat1889 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1874 := derived1874 a h
  have h3 : Entails.eval a c1884 := derived1884 a h
  have h4 : Entails.eval a c1885 := derived1885 a h
  have h5 : Entails.eval a c1887 := derived1887 a h
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c1763 := derived1763 a h
  have h12 : Entails.eval a c1282 := derived1282 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c1888 := derived1888 a h
  have h15 : Entails.eval a c120 := h 119 (by decide)
  have h16 : Entails.eval a c148 := h 147 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c1236 := derived1236 a h
  have h19 : Entails.eval a c216 := h 215 (by decide)
  have h20 : Entails.eval a c53 := h 52 (by decide)
  have h21 : Entails.eval a c313 := h 312 (by decide)
  have h22 : Entails.eval a c153 := h 152 (by decide)
  have h23 : Entails.eval a c205 := h 204 (by decide)
  have h24 : Entails.eval a c1154 := derived1154 a h
  have h25 : Entails.eval a c169 := h 168 (by decide)
  have h26 : Entails.eval a c156 := h 155 (by decide)
  have h27 : Entails.eval a c590 := derived590 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1890 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1889, some c203, some c1812, some c119, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1890 : lratChecker f1890 p1890 = .success := by decide +kernel
theorem unsat1890 : Unsatisfiable (PosFin 57) f1890 := by
  apply lratCheckerSound f1890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1890
  · intro a ha; simp [p1890] at ha; subst a; trivial
  · exact checked1890
theorem derived1890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1890 := by
  apply localUnsat_implies_entails f1890 [c1733, c1889, c203, c1812, c119] c1890 unsat1890 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1889 := derived1889 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c1812 := derived1812 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1891 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1889, some c1569, some c1733, some c354, some c17, some c1890, some c37, some c358, some c1073, some c1738, some c211, some c139, some c147, some c201, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1891 : lratChecker f1891 p1891 = .success := by decide +kernel
theorem unsat1891 : Unsatisfiable (PosFin 57) f1891 := by
  apply lratCheckerSound f1891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1891
  · intro a ha; simp [p1891] at ha; subst a; trivial
  · exact checked1891
theorem derived1891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1891 := by
  apply localUnsat_implies_entails f1891 [c1889, c1569, c1733, c354, c17, c1890, c37, c358, c1073, c1738, c211, c139, c147, c201] c1891 unsat1891 (by rfl) a
  have h0 : Entails.eval a c1889 := derived1889 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1733 := derived1733 a h
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c1890 := derived1890 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c1073 := derived1073 a h
  have h9 : Entails.eval a c1738 := derived1738 a h
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1892 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1889, some c1845, some c1569, some c354, some c1049, some c358, some c1073, some c66, some c359, some c1590, some c1282, some c229, some c232, some c268, some c269, some c30, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1892 : lratChecker f1892 p1892 = .success := by decide +kernel
theorem unsat1892 : Unsatisfiable (PosFin 57) f1892 := by
  apply lratCheckerSound f1892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1892
  · intro a ha; simp [p1892] at ha; subst a; trivial
  · exact checked1892
theorem derived1892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1892 := by
  apply localUnsat_implies_entails f1892 [c1889, c1845, c1569, c354, c1049, c358, c1073, c66, c359, c1590, c1282, c229, c232, c268, c269, c30] c1892 unsat1892 (by rfl) a
  have h0 : Entails.eval a c1889 := derived1889 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c1049 := derived1049 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c1073 := derived1073 a h
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c1590 := derived1590 a h
  have h10 : Entails.eval a c1282 := derived1282 a h
  have h11 : Entails.eval a c229 := h 228 (by decide)
  have h12 : Entails.eval a c232 := h 231 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c269 := h 268 (by decide)
  have h15 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1893 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1889, some c1569, some c354, some c17, some c1892, some c267, some c1891, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1893 : lratChecker f1893 p1893 = .success := by decide +kernel
theorem unsat1893 : Unsatisfiable (PosFin 57) f1893 := by
  apply lratCheckerSound f1893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1893
  · intro a ha; simp [p1893] at ha; subst a; trivial
  · exact checked1893
theorem derived1893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1893 := by
  apply localUnsat_implies_entails f1893 [c1889, c1569, c354, c17, c1892, c267, c1891] c1893 unsat1893 (by rfl) a
  have h0 : Entails.eval a c1889 := derived1889 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c1892 := derived1892 a h
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c1891 := derived1891 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1894 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨17, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1845, some c1893, some c1791, some c128, some c265, some c21, some c35, some c139, some c201, some c147, some c172, some c211, some c37, some c45, some c251, some c337, some c186, some c49, some c1584, some c91, some c368, some c370, some c298, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1894 : lratChecker f1894 p1894 = .success := by decide +kernel
theorem unsat1894 : Unsatisfiable (PosFin 57) f1894 := by
  apply lratCheckerSound f1894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1894
  · intro a ha; simp [p1894] at ha; subst a; trivial
  · exact checked1894
theorem derived1894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1894 := by
  apply localUnsat_implies_entails f1894 [c1569, c1733, c1845, c1893, c1791, c128, c265, c21, c35, c139, c201, c147, c172, c211, c37, c45, c251, c337, c186, c49, c1584, c91, c368, c370, c298] c1894 unsat1894 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1893 := derived1893 a h
  have h4 : Entails.eval a c1791 := derived1791 a h
  have h5 : Entails.eval a c128 := h 127 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c139 := h 138 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c172 := h 171 (by decide)
  have h13 : Entails.eval a c211 := h 210 (by decide)
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c251 := h 250 (by decide)
  have h17 : Entails.eval a c337 := h 336 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c49 := h 48 (by decide)
  have h20 : Entails.eval a c1584 := derived1584 a h
  have h21 : Entails.eval a c91 := h 90 (by decide)
  have h22 : Entails.eval a c368 := h 367 (by decide)
  have h23 : Entails.eval a c370 := h 369 (by decide)
  have h24 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1895 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨24, by decide⟩, true), (⟨17, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1845, some c1569, some c1893, some c1791, some c1894, some c119, some c201, some c139, some c49, some c159, some c249, some c1278, some c45, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1895 : lratChecker f1895 p1895 = .success := by decide +kernel
theorem unsat1895 : Unsatisfiable (PosFin 57) f1895 := by
  apply lratCheckerSound f1895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1895
  · intro a ha; simp [p1895] at ha; subst a; trivial
  · exact checked1895
theorem derived1895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1895 := by
  apply localUnsat_implies_entails f1895 [c1733, c1845, c1569, c1893, c1791, c1894, c119, c201, c139, c49, c159, c249, c1278, c45] c1895 unsat1895 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1893 := derived1893 a h
  have h4 : Entails.eval a c1791 := derived1791 a h
  have h5 : Entails.eval a c1894 := derived1894 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c249 := h 248 (by decide)
  have h12 : Entails.eval a c1278 := derived1278 a h
  have h13 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1896 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1889, some c1733, some c1845, some c1893, some c1791, some c128, some c1894, some c23, some c119, some c236, some c201, some c139, some c1895, some c1034, some c209, some c45, some c340, some c187, some c249, some c250, some c103, some c1584, some c92, some c91, some c370, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1896 : lratChecker f1896 p1896 = .success := by decide +kernel
theorem unsat1896 : Unsatisfiable (PosFin 57) f1896 := by
  apply lratCheckerSound f1896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1896
  · intro a ha; simp [p1896] at ha; subst a; trivial
  · exact checked1896
theorem derived1896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1896 := by
  apply localUnsat_implies_entails f1896 [c1569, c1889, c1733, c1845, c1893, c1791, c128, c1894, c23, c119, c236, c201, c139, c1895, c1034, c209, c45, c340, c187, c249, c250, c103, c1584, c92, c91, c370] c1896 unsat1896 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1889 := derived1889 a h
  have h2 : Entails.eval a c1733 := derived1733 a h
  have h3 : Entails.eval a c1845 := derived1845 a h
  have h4 : Entails.eval a c1893 := derived1893 a h
  have h5 : Entails.eval a c1791 := derived1791 a h
  have h6 : Entails.eval a c128 := h 127 (by decide)
  have h7 : Entails.eval a c1894 := derived1894 a h
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c236 := h 235 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c139 := h 138 (by decide)
  have h13 : Entails.eval a c1895 := derived1895 a h
  have h14 : Entails.eval a c1034 := derived1034 a h
  have h15 : Entails.eval a c209 := h 208 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c340 := h 339 (by decide)
  have h18 : Entails.eval a c187 := h 186 (by decide)
  have h19 : Entails.eval a c249 := h 248 (by decide)
  have h20 : Entails.eval a c250 := h 249 (by decide)
  have h21 : Entails.eval a c103 := h 102 (by decide)
  have h22 : Entails.eval a c1584 := derived1584 a h
  have h23 : Entails.eval a c92 := h 91 (by decide)
  have h24 : Entails.eval a c91 := h 90 (by decide)
  have h25 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1897 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1893, some c1896, some c267, some c266, some c236, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1897 : lratChecker f1897 p1897 = .success := by decide +kernel
theorem unsat1897 : Unsatisfiable (PosFin 57) f1897 := by
  apply lratCheckerSound f1897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1897
  · intro a ha; simp [p1897] at ha; subst a; trivial
  · exact checked1897
theorem derived1897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1897 := by
  apply localUnsat_implies_entails f1897 [c1893, c1896, c267, c266, c236] c1897 unsat1897 (by rfl) a
  have h0 : Entails.eval a c1893 := derived1893 a h
  have h1 : Entails.eval a c1896 := derived1896 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1898 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨37, by decide⟩, false), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1845, some c147, some c1897, some c26, some c1673, some c54, some c39, some c47, some c313, some c346, some c49, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1898 : lratChecker f1898 p1898 = .success := by decide +kernel
theorem unsat1898 : Unsatisfiable (PosFin 57) f1898 := by
  apply lratCheckerSound f1898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1898
  · intro a ha; simp [p1898] at ha; subst a; trivial
  · exact checked1898
theorem derived1898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1898 := by
  apply localUnsat_implies_entails f1898 [c1569, c1845, c147, c1897, c26, c1673, c54, c39, c47, c313, c346, c49] c1898 unsat1898 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c1897 := derived1897 a h
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c1673 := derived1673 a h
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1899 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1889, some c1569, some c1897, some c17, some c1893, some c1791, some c128, some c324, some c1077, some c328, some c237, some c172, some c135, some c706, some c207, some c698, some c168, some c612, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1899 : lratChecker f1899 p1899 = .success := by decide +kernel
theorem unsat1899 : Unsatisfiable (PosFin 57) f1899 := by
  apply lratCheckerSound f1899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1899
  · intro a ha; simp [p1899] at ha; subst a; trivial
  · exact checked1899
theorem derived1899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1899 := by
  apply localUnsat_implies_entails f1899 [c1889, c1569, c1897, c17, c1893, c1791, c128, c324, c1077, c328, c237, c172, c135, c706, c207, c698, c168, c612] c1899 unsat1899 (by rfl) a
  have h0 : Entails.eval a c1889 := derived1889 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1897 := derived1897 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c1893 := derived1893 a h
  have h5 : Entails.eval a c1791 := derived1791 a h
  have h6 : Entails.eval a c128 := h 127 (by decide)
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c1077 := derived1077 a h
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c237 := h 236 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c135 := h 134 (by decide)
  have h13 : Entails.eval a c706 := derived706 a h
  have h14 : Entails.eval a c207 := h 206 (by decide)
  have h15 : Entails.eval a c698 := derived698 a h
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c612 := derived612 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1900 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1845, some c1889, some c1897, some c17, some c1893, some c1791, some c128, some c324, some c147, some c172, some c797, some c1898, some c1077, some c328, some c237, some c1899, some c272, some c1673, some c268, some c137, some c1001, some c205, some c155, some c177, some c300, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1900 : lratChecker f1900 p1900 = .success := by decide +kernel
theorem unsat1900 : Unsatisfiable (PosFin 57) f1900 := by
  apply lratCheckerSound f1900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1900
  · intro a ha; simp [p1900] at ha; subst a; trivial
  · exact checked1900
theorem derived1900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1900 := by
  apply localUnsat_implies_entails f1900 [c1569, c1845, c1889, c1897, c17, c1893, c1791, c128, c324, c147, c172, c797, c1898, c1077, c328, c237, c1899, c272, c1673, c268, c137, c1001, c205, c155, c177, c300] c1900 unsat1900 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1889 := derived1889 a h
  have h3 : Entails.eval a c1897 := derived1897 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c1893 := derived1893 a h
  have h6 : Entails.eval a c1791 := derived1791 a h
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  have h11 : Entails.eval a c797 := derived797 a h
  have h12 : Entails.eval a c1898 := derived1898 a h
  have h13 : Entails.eval a c1077 := derived1077 a h
  have h14 : Entails.eval a c328 := h 327 (by decide)
  have h15 : Entails.eval a c237 := h 236 (by decide)
  have h16 : Entails.eval a c1899 := derived1899 a h
  have h17 : Entails.eval a c272 := h 271 (by decide)
  have h18 : Entails.eval a c1673 := derived1673 a h
  have h19 : Entails.eval a c268 := h 267 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c1001 := derived1001 a h
  have h22 : Entails.eval a c205 := h 204 (by decide)
  have h23 : Entails.eval a c155 := h 154 (by decide)
  have h24 : Entails.eval a c177 := h 176 (by decide)
  have h25 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1901 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1889, some c1569, some c1897, some c17, some c1893, some c1791, some c128, some c324, some c1900, some c201, some c139, some c1738, some c272, some c1077, some c238, some c135, some c328, some c746, some c706, some c237, some c269, some c118, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1901 : lratChecker f1901 p1901 = .success := by decide +kernel
theorem unsat1901 : Unsatisfiable (PosFin 57) f1901 := by
  apply lratCheckerSound f1901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1901
  · intro a ha; simp [p1901] at ha; subst a; trivial
  · exact checked1901
theorem derived1901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1901 := by
  apply localUnsat_implies_entails f1901 [c1733, c1889, c1569, c1897, c17, c1893, c1791, c128, c324, c1900, c201, c139, c1738, c272, c1077, c238, c135, c328, c746, c706, c237, c269, c118] c1901 unsat1901 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1889 := derived1889 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1897 := derived1897 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c1893 := derived1893 a h
  have h6 : Entails.eval a c1791 := derived1791 a h
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c1900 := derived1900 a h
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c1738 := derived1738 a h
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c1077 := derived1077 a h
  have h15 : Entails.eval a c238 := h 237 (by decide)
  have h16 : Entails.eval a c135 := h 134 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c746 := derived746 a h
  have h19 : Entails.eval a c706 := derived706 a h
  have h20 : Entails.eval a c237 := h 236 (by decide)
  have h21 : Entails.eval a c269 := h 268 (by decide)
  have h22 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1902 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c166, some c13, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p1902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1902 : lratChecker f1902 p1902 = .success := by decide +kernel
theorem unsat1902 : Unsatisfiable (PosFin 57) f1902 := by
  apply lratCheckerSound f1902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1902
  · intro a ha; simp [p1902] at ha; subst a; trivial
  · exact checked1902
theorem derived1902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1902 := by
  apply localUnsat_implies_entails f1902 [c70, c166, c13] c1902 unsat1902 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c166 := h 165 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1903 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1845, some c1893, some c1791, some c1901, some c119, some c201, some c139, some c1897, some c17, some c26, some c271, some c525, some c734, some c27, some c137, some c1902, some c359, some c74, some c564, some c1282, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1903 : lratChecker f1903 p1903 = .success := by decide +kernel
theorem unsat1903 : Unsatisfiable (PosFin 57) f1903 := by
  apply lratCheckerSound f1903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1903
  · intro a ha; simp [p1903] at ha; subst a; trivial
  · exact checked1903
theorem derived1903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1903 := by
  apply localUnsat_implies_entails f1903 [c1733, c1569, c1845, c1893, c1791, c1901, c119, c201, c139, c1897, c17, c26, c271, c525, c734, c27, c137, c1902, c359, c74, c564, c1282] c1903 unsat1903 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1893 := derived1893 a h
  have h4 : Entails.eval a c1791 := derived1791 a h
  have h5 : Entails.eval a c1901 := derived1901 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c1897 := derived1897 a h
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c271 := h 270 (by decide)
  have h13 : Entails.eval a c525 := derived525 a h
  have h14 : Entails.eval a c734 := derived734 a h
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c137 := h 136 (by decide)
  have h17 : Entails.eval a c1902 := derived1902 a h
  have h18 : Entails.eval a c359 := h 358 (by decide)
  have h19 : Entails.eval a c74 := h 73 (by decide)
  have h20 : Entails.eval a c564 := derived564 a h
  have h21 : Entails.eval a c1282 := derived1282 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1904 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1889, some c1569, some c1845, some c1897, some c17, some c1893, some c1791, some c128, some c324, some c1901, some c119, some c201, some c139, some c1903, some c1077, some c703, some c328, some c135, some c237, some c271, some c525, some c27, some c356, some c108, some c143, some c980, some c218, some c56, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1904 : lratChecker f1904 p1904 = .success := by decide +kernel
theorem unsat1904 : Unsatisfiable (PosFin 57) f1904 := by
  apply lratCheckerSound f1904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1904
  · intro a ha; simp [p1904] at ha; subst a; trivial
  · exact checked1904
theorem derived1904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1904 := by
  apply localUnsat_implies_entails f1904 [c1733, c1889, c1569, c1845, c1897, c17, c1893, c1791, c128, c324, c1901, c119, c201, c139, c1903, c1077, c703, c328, c135, c237, c271, c525, c27, c356, c108, c143, c980, c218, c56] c1904 unsat1904 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1889 := derived1889 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1845 := derived1845 a h
  have h4 : Entails.eval a c1897 := derived1897 a h
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c1893 := derived1893 a h
  have h7 : Entails.eval a c1791 := derived1791 a h
  have h8 : Entails.eval a c128 := h 127 (by decide)
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c1901 := derived1901 a h
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c1903 := derived1903 a h
  have h15 : Entails.eval a c1077 := derived1077 a h
  have h16 : Entails.eval a c703 := derived703 a h
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c135 := h 134 (by decide)
  have h19 : Entails.eval a c237 := h 236 (by decide)
  have h20 : Entails.eval a c271 := h 270 (by decide)
  have h21 : Entails.eval a c525 := derived525 a h
  have h22 : Entails.eval a c27 := h 26 (by decide)
  have h23 : Entails.eval a c356 := h 355 (by decide)
  have h24 : Entails.eval a c108 := h 107 (by decide)
  have h25 : Entails.eval a c143 := h 142 (by decide)
  have h26 : Entails.eval a c980 := derived980 a h
  have h27 : Entails.eval a c218 := h 217 (by decide)
  have h28 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1905 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1845, some c1889, some c1897, some c17, some c1738, some c21, some c1898, some c201, some c532, some c26, some c1681, some c268, some c638, some c237, some c1124, some c328, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1905 : lratChecker f1905 p1905 = .success := by decide +kernel
theorem unsat1905 : Unsatisfiable (PosFin 57) f1905 := by
  apply lratCheckerSound f1905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1905
  · intro a ha; simp [p1905] at ha; subst a; trivial
  · exact checked1905
theorem derived1905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1905 := by
  apply localUnsat_implies_entails f1905 [c1733, c1569, c1845, c1889, c1897, c17, c1738, c21, c1898, c201, c532, c26, c1681, c268, c638, c237, c1124, c328] c1905 unsat1905 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1889 := derived1889 a h
  have h4 : Entails.eval a c1897 := derived1897 a h
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c1738 := derived1738 a h
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c1898 := derived1898 a h
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c532 := derived532 a h
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c1681 := derived1681 a h
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c638 := derived638 a h
  have h15 : Entails.eval a c237 := h 236 (by decide)
  have h16 : Entails.eval a c1124 := derived1124 a h
  have h17 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1906 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1569, some c125, some c21, some c767, some c27, some c25, some c132, some c6, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1906 : lratChecker f1906 p1906 = .success := by decide +kernel
theorem unsat1906 : Unsatisfiable (PosFin 57) f1906 := by
  apply lratCheckerSound f1906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1906
  · intro a ha; simp [p1906] at ha; subst a; trivial
  · exact checked1906
theorem derived1906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1906 := by
  apply localUnsat_implies_entails f1906 [c1845, c1569, c125, c21, c767, c27, c25, c132, c6] c1906 unsat1906 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c767 := derived767 a h
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1907 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1569, some c125, some c21, some c1904, some c1897, some c1893, some c27, some c767, some c1906, some c270, some c118, some c22, some c13, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1907 : lratChecker f1907 p1907 = .success := by decide +kernel
theorem unsat1907 : Unsatisfiable (PosFin 57) f1907 := by
  apply lratCheckerSound f1907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1907
  · intro a ha; simp [p1907] at ha; subst a; trivial
  · exact checked1907
theorem derived1907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1907 := by
  apply localUnsat_implies_entails f1907 [c1845, c1569, c125, c21, c1904, c1897, c1893, c27, c767, c1906, c270, c118, c22, c13] c1907 unsat1907 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c1904 := derived1904 a h
  have h5 : Entails.eval a c1897 := derived1897 a h
  have h6 : Entails.eval a c1893 := derived1893 a h
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c767 := derived767 a h
  have h9 : Entails.eval a c1906 := derived1906 a h
  have h10 : Entails.eval a c270 := h 269 (by decide)
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1908 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1845, some c1897, some c17, some c1893, some c1791, some c26, some c1738, some c21, some c1898, some c201, some c532, some c734, some c1907, some c1681, some c268, some c638, some c1905, some c1282, some c237, some c1124, some c179, some c70, some c325, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1908 : lratChecker f1908 p1908 = .success := by decide +kernel
theorem unsat1908 : Unsatisfiable (PosFin 57) f1908 := by
  apply lratCheckerSound f1908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1908
  · intro a ha; simp [p1908] at ha; subst a; trivial
  · exact checked1908
theorem derived1908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1908 := by
  apply localUnsat_implies_entails f1908 [c1569, c1733, c1845, c1897, c17, c1893, c1791, c26, c1738, c21, c1898, c201, c532, c734, c1907, c1681, c268, c638, c1905, c1282, c237, c1124, c179, c70, c325] c1908 unsat1908 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1897 := derived1897 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c1893 := derived1893 a h
  have h6 : Entails.eval a c1791 := derived1791 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c1738 := derived1738 a h
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c1898 := derived1898 a h
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c532 := derived532 a h
  have h13 : Entails.eval a c734 := derived734 a h
  have h14 : Entails.eval a c1907 := derived1907 a h
  have h15 : Entails.eval a c1681 := derived1681 a h
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c638 := derived638 a h
  have h18 : Entails.eval a c1905 := derived1905 a h
  have h19 : Entails.eval a c1282 := derived1282 a h
  have h20 : Entails.eval a c237 := h 236 (by decide)
  have h21 : Entails.eval a c1124 := derived1124 a h
  have h22 : Entails.eval a c179 := h 178 (by decide)
  have h23 : Entails.eval a c70 := h 69 (by decide)
  have h24 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1909 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨21, by decide⟩, true), (⟨32, by decide⟩, true), (⟨3, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1904, some c1897, some c1893, some c1791, some c207, some c1225, some c157, some c230, some c1857, some c270, some c42, some c25, some c1282, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1909 : lratChecker f1909 p1909 = .success := by decide +kernel
theorem unsat1909 : Unsatisfiable (PosFin 57) f1909 := by
  apply lratCheckerSound f1909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1909
  · intro a ha; simp [p1909] at ha; subst a; trivial
  · exact checked1909
theorem derived1909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1909 := by
  apply localUnsat_implies_entails f1909 [c1569, c1904, c1897, c1893, c1791, c207, c1225, c157, c230, c1857, c270, c42, c25, c1282] c1909 unsat1909 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1904 := derived1904 a h
  have h2 : Entails.eval a c1897 := derived1897 a h
  have h3 : Entails.eval a c1893 := derived1893 a h
  have h4 : Entails.eval a c1791 := derived1791 a h
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c1225 := derived1225 a h
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c230 := h 229 (by decide)
  have h9 : Entails.eval a c1857 := derived1857 a h
  have h10 : Entails.eval a c270 := h 269 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c1282 := derived1282 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1910 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨19, by decide⟩, true), (⟨32, by decide⟩, true), (⟨14, by decide⟩, false), (⟨31, by decide⟩, false), (⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨34, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c123, some c155, some c792, some c325, some c295, some c205, some c177, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1910 : lratChecker f1910 p1910 = .success := by decide +kernel
theorem unsat1910 : Unsatisfiable (PosFin 57) f1910 := by
  apply lratCheckerSound f1910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1910
  · intro a ha; simp [p1910] at ha; subst a; trivial
  · exact checked1910
theorem derived1910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1910 := by
  apply localUnsat_implies_entails f1910 [c115, c123, c155, c792, c325, c295, c205, c177] c1910 unsat1910 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c155 := h 154 (by decide)
  have h3 : Entails.eval a c792 := derived792 a h
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1911 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, true), (⟨32, by decide⟩, true), (⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨3, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1893, some c172, some c147, some c1077, some c1897, some c1791, some c1910, some c706, some c1909, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1911 : lratChecker f1911 p1911 = .success := by decide +kernel
theorem unsat1911 : Unsatisfiable (PosFin 57) f1911 := by
  apply lratCheckerSound f1911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1911
  · intro a ha; simp [p1911] at ha; subst a; trivial
  · exact checked1911
theorem derived1911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1911 := by
  apply localUnsat_implies_entails f1911 [c1893, c172, c147, c1077, c1897, c1791, c1910, c706, c1909] c1911 unsat1911 (by rfl) a
  have h0 : Entails.eval a c1893 := derived1893 a h
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c1897 := derived1897 a h
  have h5 : Entails.eval a c1791 := derived1791 a h
  have h6 : Entails.eval a c1910 := derived1910 a h
  have h7 : Entails.eval a c706 := derived706 a h
  have h8 : Entails.eval a c1909 := derived1909 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1912 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨32, by decide⟩, true), (⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨3, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1569, some c147, some c1904, some c1897, some c1893, some c1791, some c1911, some c1673, some c155, some c734, some c207, some c1225, some c157, some c278, some c317, some c1857, some c22, some c1282, some c56, some c53, some c313, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1912 : lratChecker f1912 p1912 = .success := by decide +kernel
theorem unsat1912 : Unsatisfiable (PosFin 57) f1912 := by
  apply lratCheckerSound f1912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1912
  · intro a ha; simp [p1912] at ha; subst a; trivial
  · exact checked1912
theorem derived1912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1912 := by
  apply localUnsat_implies_entails f1912 [c1845, c1569, c147, c1904, c1897, c1893, c1791, c1911, c1673, c155, c734, c207, c1225, c157, c278, c317, c1857, c22, c1282, c56, c53, c313] c1912 unsat1912 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c1904 := derived1904 a h
  have h4 : Entails.eval a c1897 := derived1897 a h
  have h5 : Entails.eval a c1893 := derived1893 a h
  have h6 : Entails.eval a c1791 := derived1791 a h
  have h7 : Entails.eval a c1911 := derived1911 a h
  have h8 : Entails.eval a c1673 := derived1673 a h
  have h9 : Entails.eval a c155 := h 154 (by decide)
  have h10 : Entails.eval a c734 := derived734 a h
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c1225 := derived1225 a h
  have h13 : Entails.eval a c157 := h 156 (by decide)
  have h14 : Entails.eval a c278 := h 277 (by decide)
  have h15 : Entails.eval a c317 := h 316 (by decide)
  have h16 : Entails.eval a c1857 := derived1857 a h
  have h17 : Entails.eval a c22 := h 21 (by decide)
  have h18 : Entails.eval a c1282 := derived1282 a h
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c53 := h 52 (by decide)
  have h21 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1913 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1733, some c1569, some c1908, some c1077, some c1904, some c1897, some c1893, some c1791, some c147, some c172, some c224, some c1912, some c272, some c222, some c1910, some c49, some c159, some c207, some c185, some c168, some c612, some c348, some c270, some c95, some c25, some c108, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1913 : lratChecker f1913 p1913 = .success := by decide +kernel
theorem unsat1913 : Unsatisfiable (PosFin 57) f1913 := by
  apply lratCheckerSound f1913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1913
  · intro a ha; simp [p1913] at ha; subst a; trivial
  · exact checked1913
theorem derived1913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1913 := by
  apply localUnsat_implies_entails f1913 [c1845, c1733, c1569, c1908, c1077, c1904, c1897, c1893, c1791, c147, c172, c224, c1912, c272, c222, c1910, c49, c159, c207, c185, c168, c612, c348, c270, c95, c25, c108] c1913 unsat1913 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1908 := derived1908 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c1904 := derived1904 a h
  have h6 : Entails.eval a c1897 := derived1897 a h
  have h7 : Entails.eval a c1893 := derived1893 a h
  have h8 : Entails.eval a c1791 := derived1791 a h
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  have h11 : Entails.eval a c224 := h 223 (by decide)
  have h12 : Entails.eval a c1912 := derived1912 a h
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c222 := h 221 (by decide)
  have h15 : Entails.eval a c1910 := derived1910 a h
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c159 := h 158 (by decide)
  have h18 : Entails.eval a c207 := h 206 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c168 := h 167 (by decide)
  have h21 : Entails.eval a c612 := derived612 a h
  have h22 : Entails.eval a c348 := h 347 (by decide)
  have h23 : Entails.eval a c270 := h 269 (by decide)
  have h24 : Entails.eval a c95 := h 94 (by decide)
  have h25 : Entails.eval a c25 := h 24 (by decide)
  have h26 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1914 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, true), (⟨37, by decide⟩, false), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1913, some c201, some c1907, some c1897, some c17, some c532, some c125, some c1908, some c1904, some c1893, some c1791, some c238, some c330, some c115, some c230, some c702, some c270, some c639, some c25, some c5, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1914 : lratChecker f1914 p1914 = .success := by decide +kernel
theorem unsat1914 : Unsatisfiable (PosFin 57) f1914 := by
  apply lratCheckerSound f1914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1914
  · intro a ha; simp [p1914] at ha; subst a; trivial
  · exact checked1914
theorem derived1914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1914 := by
  apply localUnsat_implies_entails f1914 [c1733, c1569, c1913, c201, c1907, c1897, c17, c532, c125, c1908, c1904, c1893, c1791, c238, c330, c115, c230, c702, c270, c639, c25, c5] c1914 unsat1914 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1913 := derived1913 a h
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c1907 := derived1907 a h
  have h5 : Entails.eval a c1897 := derived1897 a h
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c532 := derived532 a h
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c1908 := derived1908 a h
  have h10 : Entails.eval a c1904 := derived1904 a h
  have h11 : Entails.eval a c1893 := derived1893 a h
  have h12 : Entails.eval a c1791 := derived1791 a h
  have h13 : Entails.eval a c238 := h 237 (by decide)
  have h14 : Entails.eval a c330 := h 329 (by decide)
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c230 := h 229 (by decide)
  have h17 : Entails.eval a c702 := derived702 a h
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c639 := derived639 a h
  have h20 : Entails.eval a c25 := h 24 (by decide)
  have h21 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1915 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨37, by decide⟩, false), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1845, some c1913, some c201, some c1908, some c1893, some c1907, some c1914, some c1681, some c1282, some c108, some c1320, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1915 : lratChecker f1915 p1915 = .success := by decide +kernel
theorem unsat1915 : Unsatisfiable (PosFin 57) f1915 := by
  apply lratCheckerSound f1915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1915
  · intro a ha; simp [p1915] at ha; subst a; trivial
  · exact checked1915
theorem derived1915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1915 := by
  apply localUnsat_implies_entails f1915 [c1733, c1845, c1913, c201, c1908, c1893, c1907, c1914, c1681, c1282, c108, c1320] c1915 unsat1915 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1913 := derived1913 a h
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c1908 := derived1908 a h
  have h5 : Entails.eval a c1893 := derived1893 a h
  have h6 : Entails.eval a c1907 := derived1907 a h
  have h7 : Entails.eval a c1914 := derived1914 a h
  have h8 : Entails.eval a c1681 := derived1681 a h
  have h9 : Entails.eval a c1282 := derived1282 a h
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c1320 := derived1320 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1916 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨37, by decide⟩, false), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1915, some c1913, some c201, some c1908, some c1904, some c1893, some c1791, some c702, some c704, some c222, some c159, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1916 : lratChecker f1916 p1916 = .success := by decide +kernel
theorem unsat1916 : Unsatisfiable (PosFin 57) f1916 := by
  apply lratCheckerSound f1916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1916
  · intro a ha; simp [p1916] at ha; subst a; trivial
  · exact checked1916
theorem derived1916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1916 := by
  apply localUnsat_implies_entails f1916 [c1733, c1915, c1913, c201, c1908, c1904, c1893, c1791, c702, c704, c222, c159] c1916 unsat1916 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1915 := derived1915 a h
  have h2 : Entails.eval a c1913 := derived1913 a h
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c1908 := derived1908 a h
  have h5 : Entails.eval a c1904 := derived1904 a h
  have h6 : Entails.eval a c1893 := derived1893 a h
  have h7 : Entails.eval a c1791 := derived1791 a h
  have h8 : Entails.eval a c702 := derived702 a h
  have h9 : Entails.eval a c704 := derived704 a h
  have h10 : Entails.eval a c222 := h 221 (by decide)
  have h11 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1917 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1889, some c1569, some c1845, some c1908, some c1077, some c1897, some c17, some c1893, some c1791, some c1913, some c201, some c1915, some c272, some c1916, some c115, some c123, some c359, some c325, some c330, some c183, some c176, some c324, some c746, some c237, some c269, some c118, some c906, some c205, some c144, some c220, some c214, some c56, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1917 : lratChecker f1917 p1917 = .success := by decide +kernel
theorem unsat1917 : Unsatisfiable (PosFin 57) f1917 := by
  apply lratCheckerSound f1917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1917
  · intro a ha; simp [p1917] at ha; subst a; trivial
  · exact checked1917
theorem derived1917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1917 := by
  apply localUnsat_implies_entails f1917 [c1733, c1889, c1569, c1845, c1908, c1077, c1897, c17, c1893, c1791, c1913, c201, c1915, c272, c1916, c115, c123, c359, c325, c330, c183, c176, c324, c746, c237, c269, c118, c906, c205, c144, c220, c214, c56] c1917 unsat1917 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1889 := derived1889 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1845 := derived1845 a h
  have h4 : Entails.eval a c1908 := derived1908 a h
  have h5 : Entails.eval a c1077 := derived1077 a h
  have h6 : Entails.eval a c1897 := derived1897 a h
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1893 := derived1893 a h
  have h9 : Entails.eval a c1791 := derived1791 a h
  have h10 : Entails.eval a c1913 := derived1913 a h
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c1915 := derived1915 a h
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c1916 := derived1916 a h
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c123 := h 122 (by decide)
  have h17 : Entails.eval a c359 := h 358 (by decide)
  have h18 : Entails.eval a c325 := h 324 (by decide)
  have h19 : Entails.eval a c330 := h 329 (by decide)
  have h20 : Entails.eval a c183 := h 182 (by decide)
  have h21 : Entails.eval a c176 := h 175 (by decide)
  have h22 : Entails.eval a c324 := h 323 (by decide)
  have h23 : Entails.eval a c746 := derived746 a h
  have h24 : Entails.eval a c237 := h 236 (by decide)
  have h25 : Entails.eval a c269 := h 268 (by decide)
  have h26 : Entails.eval a c118 := h 117 (by decide)
  have h27 : Entails.eval a c906 := derived906 a h
  have h28 : Entails.eval a c205 := h 204 (by decide)
  have h29 : Entails.eval a c144 := h 143 (by decide)
  have h30 : Entails.eval a c220 := h 219 (by decide)
  have h31 : Entails.eval a c214 := h 213 (by decide)
  have h32 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1918 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1733, some c1569, some c1897, some c1893, some c1908, some c1077, some c1917, some c797, some c74, some c21, some c41, some c147, some c702, some c272, some c201, some c115, some c170, some c356, some c280, some c220, some c27, some c116, some c13, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1918 : lratChecker f1918 p1918 = .success := by decide +kernel
theorem unsat1918 : Unsatisfiable (PosFin 57) f1918 := by
  apply lratCheckerSound f1918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1918
  · intro a ha; simp [p1918] at ha; subst a; trivial
  · exact checked1918
theorem derived1918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1918 := by
  apply localUnsat_implies_entails f1918 [c1845, c1733, c1569, c1897, c1893, c1908, c1077, c1917, c797, c74, c21, c41, c147, c702, c272, c201, c115, c170, c356, c280, c220, c27, c116, c13] c1918 unsat1918 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1897 := derived1897 a h
  have h4 : Entails.eval a c1893 := derived1893 a h
  have h5 : Entails.eval a c1908 := derived1908 a h
  have h6 : Entails.eval a c1077 := derived1077 a h
  have h7 : Entails.eval a c1917 := derived1917 a h
  have h8 : Entails.eval a c797 := derived797 a h
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c702 := derived702 a h
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c115 := h 114 (by decide)
  have h17 : Entails.eval a c170 := h 169 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c280 := h 279 (by decide)
  have h20 : Entails.eval a c220 := h 219 (by decide)
  have h21 : Entails.eval a c27 := h 26 (by decide)
  have h22 : Entails.eval a c116 := h 115 (by decide)
  have h23 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1919 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1733, some c1569, some c1893, some c1791, some c1918, some c119, some c201, some c1904, some c236, some c1897, some c270, some c25, some c1282, some c42, some c223, some c159, some c74, some c26, some c70, some c734, some c359, some c155, some c712, some c320, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1919 : lratChecker f1919 p1919 = .success := by decide +kernel
theorem unsat1919 : Unsatisfiable (PosFin 57) f1919 := by
  apply lratCheckerSound f1919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1919
  · intro a ha; simp [p1919] at ha; subst a; trivial
  · exact checked1919
theorem derived1919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1919 := by
  apply localUnsat_implies_entails f1919 [c1845, c1733, c1569, c1893, c1791, c1918, c119, c201, c1904, c236, c1897, c270, c25, c1282, c42, c223, c159, c74, c26, c70, c734, c359, c155, c712, c320] c1919 unsat1919 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1893 := derived1893 a h
  have h4 : Entails.eval a c1791 := derived1791 a h
  have h5 : Entails.eval a c1918 := derived1918 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c1904 := derived1904 a h
  have h9 : Entails.eval a c236 := h 235 (by decide)
  have h10 : Entails.eval a c1897 := derived1897 a h
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c1282 := derived1282 a h
  have h14 : Entails.eval a c42 := h 41 (by decide)
  have h15 : Entails.eval a c223 := h 222 (by decide)
  have h16 : Entails.eval a c159 := h 158 (by decide)
  have h17 : Entails.eval a c74 := h 73 (by decide)
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c70 := h 69 (by decide)
  have h20 : Entails.eval a c734 := derived734 a h
  have h21 : Entails.eval a c359 := h 358 (by decide)
  have h22 : Entails.eval a c155 := h 154 (by decide)
  have h23 : Entails.eval a c712 := derived712 a h
  have h24 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1920 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1845, some c1893, some c1897, some c1904, some c1918, some c236, some c270, some c25, some c1282, some c1919, some c108, some c27, some c1320, some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1920 : lratChecker f1920 p1920 = .success := by decide +kernel
theorem unsat1920 : Unsatisfiable (PosFin 57) f1920 := by
  apply lratCheckerSound f1920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1920
  · intro a ha; simp [p1920] at ha; subst a; trivial
  · exact checked1920
theorem derived1920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1920 := by
  apply localUnsat_implies_entails f1920 [c1569, c1845, c1893, c1897, c1904, c1918, c236, c270, c25, c1282, c1919, c108, c27, c1320] c1920 unsat1920 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1893 := derived1893 a h
  have h3 : Entails.eval a c1897 := derived1897 a h
  have h4 : Entails.eval a c1904 := derived1904 a h
  have h5 : Entails.eval a c1918 := derived1918 a h
  have h6 : Entails.eval a c236 := h 235 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c1282 := derived1282 a h
  have h10 : Entails.eval a c1919 := derived1919 a h
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c1320 := derived1320 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1921 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1920, some c1889, some c355, some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1921 : lratChecker f1921 p1921 = .success := by decide +kernel
theorem unsat1921 : Unsatisfiable (PosFin 57) f1921 := by
  apply lratCheckerSound f1921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1921
  · intro a ha; simp [p1921] at ha; subst a; trivial
  · exact checked1921
theorem derived1921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1921 := by
  apply localUnsat_implies_entails f1921 [c1920, c1889, c355] c1921 unsat1921 (by rfl) a
  have h0 : Entails.eval a c1920 := derived1920 a h
  have h1 : Entails.eval a c1889 := derived1889 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1922 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1921, some c1569, some c37, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1922 : lratChecker f1922 p1922 = .success := by decide +kernel
theorem unsat1922 : Unsatisfiable (PosFin 57) f1922 := by
  apply lratCheckerSound f1922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1922
  · intro a ha; simp [p1922] at ha; subst a; trivial
  · exact checked1922
theorem derived1922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1922 := by
  apply localUnsat_implies_entails f1922 [c1921, c1569, c37] c1922 unsat1922 (by rfl) a
  have h0 : Entails.eval a c1921 := derived1921 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1923 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1921, some c1569, some c17, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1923 : lratChecker f1923 p1923 = .success := by decide +kernel
theorem unsat1923 : Unsatisfiable (PosFin 57) f1923 := by
  apply lratCheckerSound f1923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1923
  · intro a ha; simp [p1923] at ha; subst a; trivial
  · exact checked1923
theorem derived1923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1923 := by
  apply localUnsat_implies_entails f1923 [c1921, c1569, c17] c1923 unsat1923 (by rfl) a
  have h0 : Entails.eval a c1921 := derived1921 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1924 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1921, some c1845, some c1569, some c1049, some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1924 : lratChecker f1924 p1924 = .success := by decide +kernel
theorem unsat1924 : Unsatisfiable (PosFin 57) f1924 := by
  apply lratCheckerSound f1924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1924
  · intro a ha; simp [p1924] at ha; subst a; trivial
  · exact checked1924
theorem derived1924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1924 := by
  apply localUnsat_implies_entails f1924 [c1921, c1845, c1569, c1049] c1924 unsat1924 (by rfl) a
  have h0 : Entails.eval a c1921 := derived1921 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1049 := derived1049 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1925 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1924, some c1920, some c1569, some c813, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1925 : lratChecker f1925 p1925 = .success := by decide +kernel
theorem unsat1925 : Unsatisfiable (PosFin 57) f1925 := by
  apply lratCheckerSound f1925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1925
  · intro a ha; simp [p1925] at ha; subst a; trivial
  · exact checked1925
theorem derived1925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1925 := by
  apply localUnsat_implies_entails f1925 [c1924, c1920, c1569, c813] c1925 unsat1925 (by rfl) a
  have h0 : Entails.eval a c1924 := derived1924 a h
  have h1 : Entails.eval a c1920 := derived1920 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c813 := derived813 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1926 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1924, some c1920, some c360, some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p1926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1926 : lratChecker f1926 p1926 = .success := by decide +kernel
theorem unsat1926 : Unsatisfiable (PosFin 57) f1926 := by
  apply lratCheckerSound f1926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1926
  · intro a ha; simp [p1926] at ha; subst a; trivial
  · exact checked1926
theorem derived1926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1926 := by
  apply localUnsat_implies_entails f1926 [c1924, c1920, c360] c1926 unsat1926 (by rfl) a
  have h0 : Entails.eval a c1924 := derived1924 a h
  have h1 : Entails.eval a c1920 := derived1920 a h
  have h2 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1927 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1925, some c1077, some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1927 : lratChecker f1927 p1927 = .success := by decide +kernel
theorem unsat1927 : Unsatisfiable (PosFin 57) f1927 := by
  apply lratCheckerSound f1927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1927
  · intro a ha; simp [p1927] at ha; subst a; trivial
  · exact checked1927
theorem derived1927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1927 := by
  apply localUnsat_implies_entails f1927 [c1925, c1077] c1927 unsat1927 (by rfl) a
  have h0 : Entails.eval a c1925 := derived1925 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1928 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1927, some c1889, some c358, some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p1928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1928 : lratChecker f1928 p1928 = .success := by decide +kernel
theorem unsat1928 : Unsatisfiable (PosFin 57) f1928 := by
  apply lratCheckerSound f1928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1928
  · intro a ha; simp [p1928] at ha; subst a; trivial
  · exact checked1928
theorem derived1928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1928 := by
  apply localUnsat_implies_entails f1928 [c1927, c1889, c358] c1928 unsat1928 (by rfl) a
  have h0 : Entails.eval a c1927 := derived1927 a h
  have h1 : Entails.eval a c1889 := derived1889 a h
  have h2 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1929 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1928, some c1921, some c1820, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1929 : lratChecker f1929 p1929 = .success := by decide +kernel
theorem unsat1929 : Unsatisfiable (PosFin 57) f1929 := by
  apply lratCheckerSound f1929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1929
  · intro a ha; simp [p1929] at ha; subst a; trivial
  · exact checked1929
theorem derived1929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1929 := by
  apply localUnsat_implies_entails f1929 [c1928, c1921, c1820] c1929 unsat1929 (by rfl) a
  have h0 : Entails.eval a c1928 := derived1928 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c1820 := derived1820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1930 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1929, some c1282, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1930 : lratChecker f1930 p1930 = .success := by decide +kernel
theorem unsat1930 : Unsatisfiable (PosFin 57) f1930 := by
  apply lratCheckerSound f1930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1930
  · intro a ha; simp [p1930] at ha; subst a; trivial
  · exact checked1930
theorem derived1930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1930 := by
  apply localUnsat_implies_entails f1930 [c1929, c1282] c1930 unsat1930 (by rfl) a
  have h0 : Entails.eval a c1929 := derived1929 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1931 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1926, some c1925, some c1928, some c118, some c166, some c786, some c269, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1931 : lratChecker f1931 p1931 = .success := by decide +kernel
theorem unsat1931 : Unsatisfiable (PosFin 57) f1931 := by
  apply lratCheckerSound f1931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1931
  · intro a ha; simp [p1931] at ha; subst a; trivial
  · exact checked1931
theorem derived1931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1931 := by
  apply localUnsat_implies_entails f1931 [c1926, c1925, c1928, c118, c166, c786, c269] c1931 unsat1931 (by rfl) a
  have h0 : Entails.eval a c1926 := derived1926 a h
  have h1 : Entails.eval a c1925 := derived1925 a h
  have h2 : Entails.eval a c1928 := derived1928 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c786 := derived786 a h
  have h6 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1932 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1926, some c1928, some c1845, some c1930, some c269, some c1681, some c230, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1932 : lratChecker f1932 p1932 = .success := by decide +kernel
theorem unsat1932 : Unsatisfiable (PosFin 57) f1932 := by
  apply lratCheckerSound f1932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1932
  · intro a ha; simp [p1932] at ha; subst a; trivial
  · exact checked1932
theorem derived1932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1932 := by
  apply localUnsat_implies_entails f1932 [c1926, c1928, c1845, c1930, c269, c1681, c230] c1932 unsat1932 (by rfl) a
  have h0 : Entails.eval a c1926 := derived1926 a h
  have h1 : Entails.eval a c1928 := derived1928 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1930 := derived1930 a h
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c1681 := derived1681 a h
  have h6 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1933 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1923, some c1930, some c1845, some c1920, some c1889, some c1927, some c1733, some c267, some c265, some c28, some c1931, some c202, some c128, some c139, some c336, some c328, some c201, some c177, some c205, some c137, some c1932, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1933 : lratChecker f1933 p1933 = .success := by decide +kernel
theorem unsat1933 : Unsatisfiable (PosFin 57) f1933 := by
  apply lratCheckerSound f1933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1933
  · intro a ha; simp [p1933] at ha; subst a; trivial
  · exact checked1933
theorem derived1933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1933 := by
  apply localUnsat_implies_entails f1933 [c1923, c1930, c1845, c1920, c1889, c1927, c1733, c267, c265, c28, c1931, c202, c128, c139, c336, c328, c201, c177, c205, c137, c1932] c1933 unsat1933 (by rfl) a
  have h0 : Entails.eval a c1923 := derived1923 a h
  have h1 : Entails.eval a c1930 := derived1930 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1920 := derived1920 a h
  have h4 : Entails.eval a c1889 := derived1889 a h
  have h5 : Entails.eval a c1927 := derived1927 a h
  have h6 : Entails.eval a c1733 := derived1733 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c1931 := derived1931 a h
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c128 := h 127 (by decide)
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c336 := h 335 (by decide)
  have h15 : Entails.eval a c328 := h 327 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c177 := h 176 (by decide)
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c137 := h 136 (by decide)
  have h20 : Entails.eval a c1932 := derived1932 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1934 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1928, some c1922, some c1923, some c118, some c146, some c210, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1934 : lratChecker f1934 p1934 = .success := by decide +kernel
theorem unsat1934 : Unsatisfiable (PosFin 57) f1934 := by
  apply lratCheckerSound f1934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1934
  · intro a ha; simp [p1934] at ha; subst a; trivial
  · exact checked1934
theorem derived1934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1934 := by
  apply localUnsat_implies_entails f1934 [c1928, c1922, c1923, c118, c146, c210] c1934 unsat1934 (by rfl) a
  have h0 : Entails.eval a c1928 := derived1928 a h
  have h1 : Entails.eval a c1922 := derived1922 a h
  have h2 : Entails.eval a c1923 := derived1923 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1935 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1934, some c1733, some c202, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1935 : lratChecker f1935 p1935 = .success := by decide +kernel
theorem unsat1935 : Unsatisfiable (PosFin 57) f1935 := by
  apply lratCheckerSound f1935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1935
  · intro a ha; simp [p1935] at ha; subst a; trivial
  · exact checked1935
theorem derived1935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1935 := by
  apply localUnsat_implies_entails f1935 [c1934, c1733, c202] c1935 unsat1935 (by rfl) a
  have h0 : Entails.eval a c1934 := derived1934 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1936 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1928, some c1926, some c1923, some c1920, some c1889, some c1927, some c1933, some c1935, some c1925, some c115, some c230, some c266, some c128, some c336, some c328, some c127, some c241, some c11, some c1932, some c32, some c137, some c9, some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p1936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1936 : lratChecker f1936 p1936 = .success := by decide +kernel
theorem unsat1936 : Unsatisfiable (PosFin 57) f1936 := by
  apply lratCheckerSound f1936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1936
  · intro a ha; simp [p1936] at ha; subst a; trivial
  · exact checked1936
theorem derived1936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1936 := by
  apply localUnsat_implies_entails f1936 [c1928, c1926, c1923, c1920, c1889, c1927, c1933, c1935, c1925, c115, c230, c266, c128, c336, c328, c127, c241, c11, c1932, c32, c137, c9] c1936 unsat1936 (by rfl) a
  have h0 : Entails.eval a c1928 := derived1928 a h
  have h1 : Entails.eval a c1926 := derived1926 a h
  have h2 : Entails.eval a c1923 := derived1923 a h
  have h3 : Entails.eval a c1920 := derived1920 a h
  have h4 : Entails.eval a c1889 := derived1889 a h
  have h5 : Entails.eval a c1927 := derived1927 a h
  have h6 : Entails.eval a c1933 := derived1933 a h
  have h7 : Entails.eval a c1935 := derived1935 a h
  have h8 : Entails.eval a c1925 := derived1925 a h
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c128 := h 127 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c328 := h 327 (by decide)
  have h15 : Entails.eval a c127 := h 126 (by decide)
  have h16 : Entails.eval a c241 := h 240 (by decide)
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c1932 := derived1932 a h
  have h19 : Entails.eval a c32 := h 31 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1937 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1936, some c1845, some c1930, some c1681, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p1937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1937 : lratChecker f1937 p1937 = .success := by decide +kernel
theorem unsat1937 : Unsatisfiable (PosFin 57) f1937 := by
  apply lratCheckerSound f1937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1937
  · intro a ha; simp [p1937] at ha; subst a; trivial
  · exact checked1937
theorem derived1937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1937 := by
  apply localUnsat_implies_entails f1937 [c1936, c1845, c1930, c1681] c1937 unsat1937 (by rfl) a
  have h0 : Entails.eval a c1936 := derived1936 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1930 := derived1930 a h
  have h3 : Entails.eval a c1681 := derived1681 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1938 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1889, some c1920, some c1934, some c1929, some c1935, some c1933, some c1937, some c1925, some c201, some c127, some c136, some c336, some c207, some c13, some c179, some c32, some c87, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1938 : lratChecker f1938 p1938 = .success := by decide +kernel
theorem unsat1938 : Unsatisfiable (PosFin 57) f1938 := by
  apply lratCheckerSound f1938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1938
  · intro a ha; simp [p1938] at ha; subst a; trivial
  · exact checked1938
theorem derived1938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1938 := by
  apply localUnsat_implies_entails f1938 [c1733, c1889, c1920, c1934, c1929, c1935, c1933, c1937, c1925, c201, c127, c136, c336, c207, c13, c179, c32, c87] c1938 unsat1938 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1889 := derived1889 a h
  have h2 : Entails.eval a c1920 := derived1920 a h
  have h3 : Entails.eval a c1934 := derived1934 a h
  have h4 : Entails.eval a c1929 := derived1929 a h
  have h5 : Entails.eval a c1935 := derived1935 a h
  have h6 : Entails.eval a c1933 := derived1933 a h
  have h7 : Entails.eval a c1937 := derived1937 a h
  have h8 : Entails.eval a c1925 := derived1925 a h
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c127 := h 126 (by decide)
  have h11 : Entails.eval a c136 := h 135 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c207 := h 206 (by decide)
  have h14 : Entails.eval a c13 := h 12 (by decide)
  have h15 : Entails.eval a c179 := h 178 (by decide)
  have h16 : Entails.eval a c32 := h 31 (by decide)
  have h17 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1939 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1920, some c1937, some c1933, some c1934, some c1929, some c1924, some c1569, some c1921, some c334, some c767, some c244, some c13, some c332, some c67, some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p1939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1939 : lratChecker f1939 p1939 = .success := by decide +kernel
theorem unsat1939 : Unsatisfiable (PosFin 57) f1939 := by
  apply lratCheckerSound f1939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1939
  · intro a ha; simp [p1939] at ha; subst a; trivial
  · exact checked1939
theorem derived1939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1939 := by
  apply localUnsat_implies_entails f1939 [c1920, c1937, c1933, c1934, c1929, c1924, c1569, c1921, c334, c767, c244, c13, c332, c67] c1939 unsat1939 (by rfl) a
  have h0 : Entails.eval a c1920 := derived1920 a h
  have h1 : Entails.eval a c1937 := derived1937 a h
  have h2 : Entails.eval a c1933 := derived1933 a h
  have h3 : Entails.eval a c1934 := derived1934 a h
  have h4 : Entails.eval a c1929 := derived1929 a h
  have h5 : Entails.eval a c1924 := derived1924 a h
  have h6 : Entails.eval a c1569 := derived1569 a h
  have h7 : Entails.eval a c1921 := derived1921 a h
  have h8 : Entails.eval a c334 := h 333 (by decide)
  have h9 : Entails.eval a c767 := derived767 a h
  have h10 : Entails.eval a c244 := h 243 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c332 := h 331 (by decide)
  have h13 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1940 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1939, some c1938, some c125, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p1940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1940 : lratChecker f1940 p1940 = .success := by decide +kernel
theorem unsat1940 : Unsatisfiable (PosFin 57) f1940 := by
  apply lratCheckerSound f1940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1940
  · intro a ha; simp [p1940] at ha; subst a; trivial
  · exact checked1940
theorem derived1940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1940 := by
  apply localUnsat_implies_entails f1940 [c1939, c1938, c125] c1940 unsat1940 (by rfl) a
  have h0 : Entails.eval a c1939 := derived1939 a h
  have h1 : Entails.eval a c1938 := derived1938 a h
  have h2 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1941 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1940, some c1569, some c1921, some c1034, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1941 : lratChecker f1941 p1941 = .success := by decide +kernel
theorem unsat1941 : Unsatisfiable (PosFin 57) f1941 := by
  apply lratCheckerSound f1941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1941
  · intro a ha; simp [p1941] at ha; subst a; trivial
  · exact checked1941
theorem derived1941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1941 := by
  apply localUnsat_implies_entails f1941 [c1940, c1569, c1921, c1034] c1941 unsat1941 (by rfl) a
  have h0 : Entails.eval a c1940 := derived1940 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c1034 := derived1034 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1942 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1941, some c1938, some c1935, some c159, some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1942 : lratChecker f1942 p1942 = .success := by decide +kernel
theorem unsat1942 : Unsatisfiable (PosFin 57) f1942 := by
  apply lratCheckerSound f1942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1942
  · intro a ha; simp [p1942] at ha; subst a; trivial
  · exact checked1942
theorem derived1942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1942 := by
  apply localUnsat_implies_entails f1942 [c1941, c1938, c1935, c159] c1942 unsat1942 (by rfl) a
  have h0 : Entails.eval a c1941 := derived1941 a h
  have h1 : Entails.eval a c1938 := derived1938 a h
  have h2 : Entails.eval a c1935 := derived1935 a h
  have h3 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1943 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1941, some c1938, some c1935, some c1939, some c641, some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p1943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1943 : lratChecker f1943 p1943 = .success := by decide +kernel
theorem unsat1943 : Unsatisfiable (PosFin 57) f1943 := by
  apply lratCheckerSound f1943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1943
  · intro a ha; simp [p1943] at ha; subst a; trivial
  · exact checked1943
theorem derived1943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1943 := by
  apply localUnsat_implies_entails f1943 [c1941, c1938, c1935, c1939, c641] c1943 unsat1943 (by rfl) a
  have h0 : Entails.eval a c1941 := derived1941 a h
  have h1 : Entails.eval a c1938 := derived1938 a h
  have h2 : Entails.eval a c1935 := derived1935 a h
  have h3 : Entails.eval a c1939 := derived1939 a h
  have h4 : Entails.eval a c641 := derived641 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1944 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1942, some c1922, some c1889, some c1928, some c1569, some c1280, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1944 : lratChecker f1944 p1944 = .success := by decide +kernel
theorem unsat1944 : Unsatisfiable (PosFin 57) f1944 := by
  apply lratCheckerSound f1944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1944
  · intro a ha; simp [p1944] at ha; subst a; trivial
  · exact checked1944
theorem derived1944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1944 := by
  apply localUnsat_implies_entails f1944 [c1942, c1922, c1889, c1928, c1569, c1280] c1944 unsat1944 (by rfl) a
  have h0 : Entails.eval a c1942 := derived1942 a h
  have h1 : Entails.eval a c1922 := derived1922 a h
  have h2 : Entails.eval a c1889 := derived1889 a h
  have h3 : Entails.eval a c1928 := derived1928 a h
  have h4 : Entails.eval a c1569 := derived1569 a h
  have h5 : Entails.eval a c1280 := derived1280 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1945 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1943, some c1934, some c205, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1945 : lratChecker f1945 p1945 = .success := by decide +kernel
theorem unsat1945 : Unsatisfiable (PosFin 57) f1945 := by
  apply lratCheckerSound f1945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1945
  · intro a ha; simp [p1945] at ha; subst a; trivial
  · exact checked1945
theorem derived1945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1945 := by
  apply localUnsat_implies_entails f1945 [c1943, c1934, c205] c1945 unsat1945 (by rfl) a
  have h0 : Entails.eval a c1943 := derived1943 a h
  have h1 : Entails.eval a c1934 := derived1934 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1946 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1945, some c1944, some c1937, some c1935, some c137]
def p1946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1946 : lratChecker f1946 p1946 = .success := by decide +kernel
theorem unsat1946 : Unsatisfiable (PosFin 57) f1946 := by
  apply lratCheckerSound f1946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1946
  · intro a ha; simp [p1946] at ha; subst a; trivial
  · exact checked1946
theorem derived1946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1946 := by
  apply localUnsat_implies_entails f1946 [c1945, c1944, c1937, c1935, c137] c1946 unsat1946 (by rfl) a
  have h0 : Entails.eval a c1945 := derived1945 a h
  have h1 : Entails.eval a c1944 := derived1944 a h
  have h2 : Entails.eval a c1937 := derived1937 a h
  have h3 : Entails.eval a c1935 := derived1935 a h
  have h4 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1946

end CochromaticTwenty.Certificates.B16_4_2
