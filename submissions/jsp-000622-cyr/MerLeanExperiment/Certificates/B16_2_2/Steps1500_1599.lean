import MerLeanExperiment.Certificates.B16_2_2.Steps1400_1499

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1884 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨19, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1231, some c1847, some c1875, some c112, some c189, some c191, some c123, some c1883, some c2, some c1882, some c245, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1884 : lratChecker f1884 p1884 = .success := by decide +kernel
theorem unsat1884 : Unsatisfiable (PosFin 57) f1884 := by
  apply lratCheckerSound f1884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1884
  · intro a ha; simp [p1884] at ha; subst a; trivial
  · exact checked1884
theorem derived1884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1884 := by
  apply localUnsat_implies_entails f1884 [c1817, c1668, c1231, c1847, c1875, c112, c189, c191, c123, c1883, c2, c1882, c245] c1884 unsat1884 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c1847 := derived1847 a h
  have h4 : Entails.eval a c1875 := derived1875 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c1883 := derived1883 a h
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c1882 := derived1882 a h
  have h12 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1885 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨45, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1881, some c1847, some c1875, some c1231, some c1884, some c1861, some c188, some c2, some c190, some c379, some c245, some c184, some c29, some c195, some c1851, some c1882, some c257, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1885 : lratChecker f1885 p1885 = .success := by decide +kernel
theorem unsat1885 : Unsatisfiable (PosFin 57) f1885 := by
  apply lratCheckerSound f1885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1885
  · intro a ha; simp [p1885] at ha; subst a; trivial
  · exact checked1885
theorem derived1885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1885 := by
  apply localUnsat_implies_entails f1885 [c1668, c1881, c1847, c1875, c1231, c1884, c1861, c188, c2, c190, c379, c245, c184, c29, c195, c1851, c1882, c257] c1885 unsat1885 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1881 := derived1881 a h
  have h2 : Entails.eval a c1847 := derived1847 a h
  have h3 : Entails.eval a c1875 := derived1875 a h
  have h4 : Entails.eval a c1231 := derived1231 a h
  have h5 : Entails.eval a c1884 := derived1884 a h
  have h6 : Entails.eval a c1861 := derived1861 a h
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c245 := h 244 (by decide)
  have h12 : Entails.eval a c184 := h 183 (by decide)
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c195 := h 194 (by decide)
  have h15 : Entails.eval a c1851 := derived1851 a h
  have h16 : Entails.eval a c1882 := derived1882 a h
  have h17 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1886 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨56, by decide⟩, true), (⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c189, some c191, some c123, some c8, some c1818, some c203, some c70, some c72, some c159, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1886 : lratChecker f1886 p1886 = .success := by decide +kernel
theorem unsat1886 : Unsatisfiable (PosFin 57) f1886 := by
  apply lratCheckerSound f1886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1886
  · intro a ha; simp [p1886] at ha; subst a; trivial
  · exact checked1886
theorem derived1886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1886 := by
  apply localUnsat_implies_entails f1886 [c1817, c189, c191, c123, c8, c1818, c203, c70, c72, c159] c1886 unsat1886 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c1818 := derived1818 a h
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1887 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c8, some c1818, some c135, some c70, some c72, some c159, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1887 : lratChecker f1887 p1887 = .success := by decide +kernel
theorem unsat1887 : Unsatisfiable (PosFin 57) f1887 := by
  apply lratCheckerSound f1887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1887
  · intro a ha; simp [p1887] at ha; subst a; trivial
  · exact checked1887
theorem derived1887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1887 := by
  apply localUnsat_implies_entails f1887 [c1817, c8, c1818, c135, c70, c72, c159] c1887 unsat1887 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c1818 := derived1818 a h
  have h3 : Entails.eval a c135 := h 134 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1888 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨16, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨19, by decide⟩, false), (⟨45, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1847, some c379, some c245, some c184, some c29, some c192, some c841, some c116, some c250, some c1445, some c1854, some c164, some c73, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1888 : lratChecker f1888 p1888 = .success := by decide +kernel
theorem unsat1888 : Unsatisfiable (PosFin 57) f1888 := by
  apply lratCheckerSound f1888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1888
  · intro a ha; simp [p1888] at ha; subst a; trivial
  · exact checked1888
theorem derived1888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1888 := by
  apply localUnsat_implies_entails f1888 [c1668, c1847, c379, c245, c184, c29, c192, c841, c116, c250, c1445, c1854, c164, c73] c1888 unsat1888 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1847 := derived1847 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c245 := h 244 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c1445 := derived1445 a h
  have h11 : Entails.eval a c1854 := derived1854 a h
  have h12 : Entails.eval a c164 := h 163 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1889 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨45, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1875, some c1881, some c1885, some c1886, some c1887, some c190, some c1888, some c2, some c192, some c972, some c942, some c382, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1889 : lratChecker f1889 p1889 = .success := by decide +kernel
theorem unsat1889 : Unsatisfiable (PosFin 57) f1889 := by
  apply lratCheckerSound f1889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1889
  · intro a ha; simp [p1889] at ha; subst a; trivial
  · exact checked1889
theorem derived1889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1889 := by
  apply localUnsat_implies_entails f1889 [c1875, c1881, c1885, c1886, c1887, c190, c1888, c2, c192, c972, c942, c382] c1889 unsat1889 (by rfl) a
  have h0 : Entails.eval a c1875 := derived1875 a h
  have h1 : Entails.eval a c1881 := derived1881 a h
  have h2 : Entails.eval a c1885 := derived1885 a h
  have h3 : Entails.eval a c1886 := derived1886 a h
  have h4 : Entails.eval a c1887 := derived1887 a h
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c1888 := derived1888 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c192 := h 191 (by decide)
  have h9 : Entails.eval a c972 := derived972 a h
  have h10 : Entails.eval a c942 := derived942 a h
  have h11 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1890 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1875, some c1881, some c1847, some c1885, some c1886, some c1889, some c195, some c122, some c184, some c1113, some c249, some c379, some c31, some c2, some c1859, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1890 : lratChecker f1890 p1890 = .success := by decide +kernel
theorem unsat1890 : Unsatisfiable (PosFin 57) f1890 := by
  apply lratCheckerSound f1890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1890
  · intro a ha; simp [p1890] at ha; subst a; trivial
  · exact checked1890
theorem derived1890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1890 := by
  apply localUnsat_implies_entails f1890 [c1817, c1668, c1875, c1881, c1847, c1885, c1886, c1889, c195, c122, c184, c1113, c249, c379, c31, c2, c1859] c1890 unsat1890 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1875 := derived1875 a h
  have h3 : Entails.eval a c1881 := derived1881 a h
  have h4 : Entails.eval a c1847 := derived1847 a h
  have h5 : Entails.eval a c1885 := derived1885 a h
  have h6 : Entails.eval a c1886 := derived1886 a h
  have h7 : Entails.eval a c1889 := derived1889 a h
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c1113 := derived1113 a h
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c1859 := derived1859 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1891 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨45, by decide⟩, false), (⟨51, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1877, some c1827, some c379, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1891 : lratChecker f1891 p1891 = .success := by decide +kernel
theorem unsat1891 : Unsatisfiable (PosFin 57) f1891 := by
  apply lratCheckerSound f1891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1891
  · intro a ha; simp [p1891] at ha; subst a; trivial
  · exact checked1891
theorem derived1891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1891 := by
  apply localUnsat_implies_entails f1891 [c1877, c1827, c379] c1891 unsat1891 (by rfl) a
  have h0 : Entails.eval a c1877 := derived1877 a h
  have h1 : Entails.eval a c1827 := derived1827 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1892 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1890, some c112, some c1875, some c1891, some c82, some c368, some c23, some c1231, some c1884, some c188, some c367, some c162, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1892 : lratChecker f1892 p1892 = .success := by decide +kernel
theorem unsat1892 : Unsatisfiable (PosFin 57) f1892 := by
  apply lratCheckerSound f1892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1892
  · intro a ha; simp [p1892] at ha; subst a; trivial
  · exact checked1892
theorem derived1892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1892 := by
  apply localUnsat_implies_entails f1892 [c1817, c1668, c1890, c112, c1875, c1891, c82, c368, c23, c1231, c1884, c188, c367, c162] c1892 unsat1892 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1875 := derived1875 a h
  have h5 : Entails.eval a c1891 := derived1891 a h
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c1231 := derived1231 a h
  have h10 : Entails.eval a c1884 := derived1884 a h
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c367 := h 366 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1893 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c158, some c160, some c70, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1893 : lratChecker f1893 p1893 = .success := by decide +kernel
theorem unsat1893 : Unsatisfiable (PosFin 57) f1893 := by
  apply lratCheckerSound f1893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1893
  · intro a ha; simp [p1893] at ha; subst a; trivial
  · exact checked1893
theorem derived1893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1893 := by
  apply localUnsat_implies_entails f1893 [c1817, c158, c160, c70] c1893 unsat1893 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1894 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨38, by decide⟩, false), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨13, by decide⟩, true), (⟨41, by decide⟩, false), (⟨51, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c379, some c338, some c1862, some c808, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1894 : lratChecker f1894 p1894 = .success := by decide +kernel
theorem unsat1894 : Unsatisfiable (PosFin 57) f1894 := by
  apply lratCheckerSound f1894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1894
  · intro a ha; simp [p1894] at ha; subst a; trivial
  · exact checked1894
theorem derived1894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1894 := by
  apply localUnsat_implies_entails f1894 [c1817, c379, c338, c1862, c808] c1894 unsat1894 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c338 := h 337 (by decide)
  have h3 : Entails.eval a c1862 := derived1862 a h
  have h4 : Entails.eval a c808 := derived808 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1895 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1875, some c112, some c1890, some c1891, some c82, some c23, some c161, some c1847, some c1892, some c1886, some c1887, some c190, some c164, some c188, some c1893, some c1894, some c2, some c117, some c1849, some c29, some c116, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1895 : lratChecker f1895 p1895 = .success := by decide +kernel
theorem unsat1895 : Unsatisfiable (PosFin 57) f1895 := by
  apply lratCheckerSound f1895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1895
  · intro a ha; simp [p1895] at ha; subst a; trivial
  · exact checked1895
theorem derived1895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1895 := by
  apply localUnsat_implies_entails f1895 [c1817, c1668, c1875, c112, c1890, c1891, c82, c23, c161, c1847, c1892, c1886, c1887, c190, c164, c188, c1893, c1894, c2, c117, c1849, c29, c116] c1895 unsat1895 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1875 := derived1875 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1890 := derived1890 a h
  have h5 : Entails.eval a c1891 := derived1891 a h
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c161 := h 160 (by decide)
  have h9 : Entails.eval a c1847 := derived1847 a h
  have h10 : Entails.eval a c1892 := derived1892 a h
  have h11 : Entails.eval a c1886 := derived1886 a h
  have h12 : Entails.eval a c1887 := derived1887 a h
  have h13 : Entails.eval a c190 := h 189 (by decide)
  have h14 : Entails.eval a c164 := h 163 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c1893 := derived1893 a h
  have h17 : Entails.eval a c1894 := derived1894 a h
  have h18 : Entails.eval a c2 := h 1 (by decide)
  have h19 : Entails.eval a c117 := h 116 (by decide)
  have h20 : Entails.eval a c1849 := derived1849 a h
  have h21 : Entails.eval a c29 := h 28 (by decide)
  have h22 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1896 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨8, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c189, some c191, some c115, some c1818, some c203, some c70, some c72, some c159, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1896 : lratChecker f1896 p1896 = .success := by decide +kernel
theorem unsat1896 : Unsatisfiable (PosFin 57) f1896 := by
  apply lratCheckerSound f1896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1896
  · intro a ha; simp [p1896] at ha; subst a; trivial
  · exact checked1896
theorem derived1896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1896 := by
  apply localUnsat_implies_entails f1896 [c1817, c189, c191, c115, c1818, c203, c70, c72, c159] c1896 unsat1896 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c1818 := derived1818 a h
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1897 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1818, some c135, some c70, some c72, some c159, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1897 : lratChecker f1897 p1897 = .success := by decide +kernel
theorem unsat1897 : Unsatisfiable (PosFin 57) f1897 := by
  apply lratCheckerSound f1897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1897
  · intro a ha; simp [p1897] at ha; subst a; trivial
  · exact checked1897
theorem derived1897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1897 := by
  apply localUnsat_implies_entails f1897 [c1817, c1818, c135, c70, c72, c159] c1897 unsat1897 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1818 := derived1818 a h
  have h2 : Entails.eval a c135 := h 134 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1898 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c112, some c30, some c1895, some c75, some c94, some c1875, some c1231, some c244, some c35, some c1896, some c188, some c190, some c1897, some c170, some c113, some c1851, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1898 : lratChecker f1898 p1898 = .success := by decide +kernel
theorem unsat1898 : Unsatisfiable (PosFin 57) f1898 := by
  apply lratCheckerSound f1898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1898
  · intro a ha; simp [p1898] at ha; subst a; trivial
  · exact checked1898
theorem derived1898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1898 := by
  apply localUnsat_implies_entails f1898 [c1817, c1668, c112, c30, c1895, c75, c94, c1875, c1231, c244, c35, c1896, c188, c190, c1897, c170, c113, c1851] c1898 unsat1898 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c1895 := derived1895 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c1875 := derived1875 a h
  have h8 : Entails.eval a c1231 := derived1231 a h
  have h9 : Entails.eval a c244 := h 243 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c1896 := derived1896 a h
  have h12 : Entails.eval a c188 := h 187 (by decide)
  have h13 : Entails.eval a c190 := h 189 (by decide)
  have h14 : Entails.eval a c1897 := derived1897 a h
  have h15 : Entails.eval a c170 := h 169 (by decide)
  have h16 : Entails.eval a c113 := h 112 (by decide)
  have h17 : Entails.eval a c1851 := derived1851 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1899 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1897, some c190, some c188, some c1893, some c380, some c338, some c184, some c808, some c192, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1899 : lratChecker f1899 p1899 = .success := by decide +kernel
theorem unsat1899 : Unsatisfiable (PosFin 57) f1899 := by
  apply lratCheckerSound f1899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1899
  · intro a ha; simp [p1899] at ha; subst a; trivial
  · exact checked1899
theorem derived1899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1899 := by
  apply localUnsat_implies_entails f1899 [c1817, c1897, c190, c188, c1893, c380, c338, c184, c808, c192] c1899 unsat1899 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1897 := derived1897 a h
  have h2 : Entails.eval a c190 := h 189 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  have h4 : Entails.eval a c1893 := derived1893 a h
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c338 := h 337 (by decide)
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c808 := derived808 a h
  have h9 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1900 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1875, some c112, some c1895, some c75, some c1877, some c94, some c30, some c1898, some c99, some c1896, some c1832, some c1899, some c195, some c170, some c113, some c184, some c1113, some c238, some c380, some c1733, some c188, some c162, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1900 : lratChecker f1900 p1900 = .success := by decide +kernel
theorem unsat1900 : Unsatisfiable (PosFin 57) f1900 := by
  apply lratCheckerSound f1900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1900
  · intro a ha; simp [p1900] at ha; subst a; trivial
  · exact checked1900
theorem derived1900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1900 := by
  apply localUnsat_implies_entails f1900 [c1668, c1817, c1875, c112, c1895, c75, c1877, c94, c30, c1898, c99, c1896, c1832, c1899, c195, c170, c113, c184, c1113, c238, c380, c1733, c188, c162] c1900 unsat1900 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1875 := derived1875 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1895 := derived1895 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c1877 := derived1877 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c1898 := derived1898 a h
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c1896 := derived1896 a h
  have h12 : Entails.eval a c1832 := derived1832 a h
  have h13 : Entails.eval a c1899 := derived1899 a h
  have h14 : Entails.eval a c195 := h 194 (by decide)
  have h15 : Entails.eval a c170 := h 169 (by decide)
  have h16 : Entails.eval a c113 := h 112 (by decide)
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c1113 := derived1113 a h
  have h19 : Entails.eval a c238 := h 237 (by decide)
  have h20 : Entails.eval a c380 := h 379 (by decide)
  have h21 : Entails.eval a c1733 := derived1733 a h
  have h22 : Entails.eval a c188 := h 187 (by decide)
  have h23 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1901 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨48, by decide⟩, true), (⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c244, some c1896, some c28, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1901 : lratChecker f1901 p1901 = .success := by decide +kernel
theorem unsat1901 : Unsatisfiable (PosFin 57) f1901 := by
  apply lratCheckerSound f1901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1901
  · intro a ha; simp [p1901] at ha; subst a; trivial
  · exact checked1901
theorem derived1901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1901 := by
  apply localUnsat_implies_entails f1901 [c244, c1896, c28] c1901 unsat1901 (by rfl) a
  have h0 : Entails.eval a c244 := h 243 (by decide)
  have h1 : Entails.eval a c1896 := derived1896 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1902 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1231, some c1900, some c1875, some c112, some c1895, some c75, some c1877, some c94, some c189, some c191, some c123, some c171, some c367, some c1711, some c1901, some c29, some c117, some c260, some c31, some c236, some c862, some c169, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1902 : lratChecker f1902 p1902 = .success := by decide +kernel
theorem unsat1902 : Unsatisfiable (PosFin 57) f1902 := by
  apply lratCheckerSound f1902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1902
  · intro a ha; simp [p1902] at ha; subst a; trivial
  · exact checked1902
theorem derived1902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1902 := by
  apply localUnsat_implies_entails f1902 [c1817, c1668, c1231, c1900, c1875, c112, c1895, c75, c1877, c94, c189, c191, c123, c171, c367, c1711, c1901, c29, c117, c260, c31, c236, c862, c169] c1902 unsat1902 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c1900 := derived1900 a h
  have h4 : Entails.eval a c1875 := derived1875 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1895 := derived1895 a h
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c1877 := derived1877 a h
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c189 := h 188 (by decide)
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c123 := h 122 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c367 := h 366 (by decide)
  have h15 : Entails.eval a c1711 := derived1711 a h
  have h16 : Entails.eval a c1901 := derived1901 a h
  have h17 : Entails.eval a c29 := h 28 (by decide)
  have h18 : Entails.eval a c117 := h 116 (by decide)
  have h19 : Entails.eval a c260 := h 259 (by decide)
  have h20 : Entails.eval a c31 := h 30 (by decide)
  have h21 : Entails.eval a c236 := h 235 (by decide)
  have h22 : Entails.eval a c862 := derived862 a h
  have h23 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1903 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨45, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨56, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1231, some c244, some c1851, some c28, some c241, some c1711, some c365, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1903 : lratChecker f1903 p1903 = .success := by decide +kernel
theorem unsat1903 : Unsatisfiable (PosFin 57) f1903 := by
  apply lratCheckerSound f1903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1903
  · intro a ha; simp [p1903] at ha; subst a; trivial
  · exact checked1903
theorem derived1903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1903 := by
  apply localUnsat_implies_entails f1903 [c1668, c1231, c244, c1851, c28, c241, c1711, c365] c1903 unsat1903 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c1851 := derived1851 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c241 := h 240 (by decide)
  have h6 : Entails.eval a c1711 := derived1711 a h
  have h7 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1904 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1231, some c21, some c29, some c162, some c248, some c367, some c28, some c370, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1904 : lratChecker f1904 p1904 = .success := by decide +kernel
theorem unsat1904 : Unsatisfiable (PosFin 57) f1904 := by
  apply lratCheckerSound f1904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1904
  · intro a ha; simp [p1904] at ha; subst a; trivial
  · exact checked1904
theorem derived1904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1904 := by
  apply localUnsat_implies_entails f1904 [c1668, c1231, c21, c29, c162, c248, c367, c28, c370] c1904 unsat1904 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c162 := h 161 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1905 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1231, some c188, some c1904, some c244, some c1903, some c28, some c375, some c1711, some c367, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1905 : lratChecker f1905 p1905 = .success := by decide +kernel
theorem unsat1905 : Unsatisfiable (PosFin 57) f1905 := by
  apply lratCheckerSound f1905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1905
  · intro a ha; simp [p1905] at ha; subst a; trivial
  · exact checked1905
theorem derived1905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1905 := by
  apply localUnsat_implies_entails f1905 [c1668, c1231, c188, c1904, c244, c1903, c28, c375, c1711, c367] c1905 unsat1905 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c1904 := derived1904 a h
  have h4 : Entails.eval a c244 := h 243 (by decide)
  have h5 : Entails.eval a c1903 := derived1903 a h
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c1711 := derived1711 a h
  have h9 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1906 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1900, some c1875, some c112, some c1895, some c75, some c1877, some c94, some c1902, some c1905, some c1899, some c195, some c122, some c170, some c1113, some c1851, some c31, some c29, some c260, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1906 : lratChecker f1906 p1906 = .success := by decide +kernel
theorem unsat1906 : Unsatisfiable (PosFin 57) f1906 := by
  apply lratCheckerSound f1906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1906
  · intro a ha; simp [p1906] at ha; subst a; trivial
  · exact checked1906
theorem derived1906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1906 := by
  apply localUnsat_implies_entails f1906 [c1817, c1668, c1900, c1875, c112, c1895, c75, c1877, c94, c1902, c1905, c1899, c195, c122, c170, c1113, c1851, c31, c29, c260] c1906 unsat1906 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1900 := derived1900 a h
  have h3 : Entails.eval a c1875 := derived1875 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1895 := derived1895 a h
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c1877 := derived1877 a h
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c1902 := derived1902 a h
  have h10 : Entails.eval a c1905 := derived1905 a h
  have h11 : Entails.eval a c1899 := derived1899 a h
  have h12 : Entails.eval a c195 := h 194 (by decide)
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c170 := h 169 (by decide)
  have h15 : Entails.eval a c1113 := derived1113 a h
  have h16 : Entails.eval a c1851 := derived1851 a h
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c29 := h 28 (by decide)
  have h19 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1907 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1875, some c112, some c1895, some c75, some c1877, some c1900, some c1906, some c99, some c1886, some c1899, some c195, some c122, some c170, some c184, some c1113, some c380, some c1733, some c188, some c162, some c367, some c238, some c370, some c114, some c239, some c29, some c262, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1907 : lratChecker f1907 p1907 = .success := by decide +kernel
theorem unsat1907 : Unsatisfiable (PosFin 57) f1907 := by
  apply lratCheckerSound f1907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1907
  · intro a ha; simp [p1907] at ha; subst a; trivial
  · exact checked1907
theorem derived1907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1907 := by
  apply localUnsat_implies_entails f1907 [c1817, c1668, c1875, c112, c1895, c75, c1877, c1900, c1906, c99, c1886, c1899, c195, c122, c170, c184, c1113, c380, c1733, c188, c162, c367, c238, c370, c114, c239, c29, c262] c1907 unsat1907 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1875 := derived1875 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1895 := derived1895 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c1877 := derived1877 a h
  have h7 : Entails.eval a c1900 := derived1900 a h
  have h8 : Entails.eval a c1906 := derived1906 a h
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c1886 := derived1886 a h
  have h11 : Entails.eval a c1899 := derived1899 a h
  have h12 : Entails.eval a c195 := h 194 (by decide)
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c170 := h 169 (by decide)
  have h15 : Entails.eval a c184 := h 183 (by decide)
  have h16 : Entails.eval a c1113 := derived1113 a h
  have h17 : Entails.eval a c380 := h 379 (by decide)
  have h18 : Entails.eval a c1733 := derived1733 a h
  have h19 : Entails.eval a c188 := h 187 (by decide)
  have h20 : Entails.eval a c162 := h 161 (by decide)
  have h21 : Entails.eval a c367 := h 366 (by decide)
  have h22 : Entails.eval a c238 := h 237 (by decide)
  have h23 : Entails.eval a c370 := h 369 (by decide)
  have h24 : Entails.eval a c114 := h 113 (by decide)
  have h25 : Entails.eval a c239 := h 238 (by decide)
  have h26 : Entails.eval a c29 := h 28 (by decide)
  have h27 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1908 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨8, by decide⟩, false), (⟨18, by decide⟩, false), (⟨17, by decide⟩, false), (⟨13, by decide⟩, true), (⟨54, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨49, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c257, some c241, some c186, some c194, some c119, some c1102, some c1818, some c55, some c216, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1908 : lratChecker f1908 p1908 = .success := by decide +kernel
theorem unsat1908 : Unsatisfiable (PosFin 57) f1908 := by
  apply lratCheckerSound f1908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1908
  · intro a ha; simp [p1908] at ha; subst a; trivial
  · exact checked1908
theorem derived1908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1908 := by
  apply localUnsat_implies_entails f1908 [c1254, c257, c241, c186, c194, c119, c1102, c1818, c55, c216] c1908 unsat1908 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c241 := h 240 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c1102 := derived1102 a h
  have h7 : Entails.eval a c1818 := derived1818 a h
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1909 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1875, some c196, some c1231, some c1907, some c9, some c192, some c11, some c1, some c112, some c23, some c30, some c1877, some c165, some c171, some c244, some c22, some c367, some c35, some c1711, some c1908, some c779, some c374, some c1827, some c237, some c246, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1909 : lratChecker f1909 p1909 = .success := by decide +kernel
theorem unsat1909 : Unsatisfiable (PosFin 57) f1909 := by
  apply lratCheckerSound f1909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1909
  · intro a ha; simp [p1909] at ha; subst a; trivial
  · exact checked1909
theorem derived1909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1909 := by
  apply localUnsat_implies_entails f1909 [c1817, c1668, c1875, c196, c1231, c1907, c9, c192, c11, c1, c112, c23, c30, c1877, c165, c171, c244, c22, c367, c35, c1711, c1908, c779, c374, c1827, c237, c246] c1909 unsat1909 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1875 := derived1875 a h
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c1231 := derived1231 a h
  have h5 : Entails.eval a c1907 := derived1907 a h
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c1877 := derived1877 a h
  have h14 : Entails.eval a c165 := h 164 (by decide)
  have h15 : Entails.eval a c171 := h 170 (by decide)
  have h16 : Entails.eval a c244 := h 243 (by decide)
  have h17 : Entails.eval a c22 := h 21 (by decide)
  have h18 : Entails.eval a c367 := h 366 (by decide)
  have h19 : Entails.eval a c35 := h 34 (by decide)
  have h20 : Entails.eval a c1711 := derived1711 a h
  have h21 : Entails.eval a c1908 := derived1908 a h
  have h22 : Entails.eval a c779 := derived779 a h
  have h23 : Entails.eval a c374 := h 373 (by decide)
  have h24 : Entails.eval a c1827 := derived1827 a h
  have h25 : Entails.eval a c237 := h 236 (by decide)
  have h26 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1910 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1231, some c1907, some c9, some c1, some c1875, some c112, some c196, some c1909, some c117, some c22, some c29, some c165, some c244, some c82, some c75, some c1844, some c368, some c370, some c239, some c872, some c250, some c237, some c365, some c372, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1910 : lratChecker f1910 p1910 = .success := by decide +kernel
theorem unsat1910 : Unsatisfiable (PosFin 57) f1910 := by
  apply lratCheckerSound f1910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1910
  · intro a ha; simp [p1910] at ha; subst a; trivial
  · exact checked1910
theorem derived1910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1910 := by
  apply localUnsat_implies_entails f1910 [c1817, c1668, c1231, c1907, c9, c1, c1875, c112, c196, c1909, c117, c22, c29, c165, c244, c82, c75, c1844, c368, c370, c239, c872, c250, c237, c365, c372] c1910 unsat1910 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c1907 := derived1907 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1875 := derived1875 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c1909 := derived1909 a h
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c29 := h 28 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c244 := h 243 (by decide)
  have h15 : Entails.eval a c82 := h 81 (by decide)
  have h16 : Entails.eval a c75 := h 74 (by decide)
  have h17 : Entails.eval a c1844 := derived1844 a h
  have h18 : Entails.eval a c368 := h 367 (by decide)
  have h19 : Entails.eval a c370 := h 369 (by decide)
  have h20 : Entails.eval a c239 := h 238 (by decide)
  have h21 : Entails.eval a c872 := derived872 a h
  have h22 : Entails.eval a c250 := h 249 (by decide)
  have h23 : Entails.eval a c237 := h 236 (by decide)
  have h24 : Entails.eval a c365 := h 364 (by decide)
  have h25 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1911 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1907, some c1875, some c9, some c192, some c11, some c1254, some c1, some c112, some c1231, some c1910, some c1097, some c184, some c1113, some c188, some c122, some c194, some c23, some c30, some c1877, some c165, some c244, some c257, some c379, some c22, some c35, some c246, some c119, some c629, some c72, some c157, some c223, some c439, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1911 : lratChecker f1911 p1911 = .success := by decide +kernel
theorem unsat1911 : Unsatisfiable (PosFin 57) f1911 := by
  apply lratCheckerSound f1911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1911
  · intro a ha; simp [p1911] at ha; subst a; trivial
  · exact checked1911
theorem derived1911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1911 := by
  apply localUnsat_implies_entails f1911 [c1668, c1817, c1907, c1875, c9, c192, c11, c1254, c1, c112, c1231, c1910, c1097, c184, c1113, c188, c122, c194, c23, c30, c1877, c165, c244, c257, c379, c22, c35, c246, c119, c629, c72, c157, c223, c439] c1911 unsat1911 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1907 := derived1907 a h
  have h3 : Entails.eval a c1875 := derived1875 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c1254 := derived1254 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c1231 := derived1231 a h
  have h11 : Entails.eval a c1910 := derived1910 a h
  have h12 : Entails.eval a c1097 := derived1097 a h
  have h13 : Entails.eval a c184 := h 183 (by decide)
  have h14 : Entails.eval a c1113 := derived1113 a h
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c23 := h 22 (by decide)
  have h19 : Entails.eval a c30 := h 29 (by decide)
  have h20 : Entails.eval a c1877 := derived1877 a h
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c244 := h 243 (by decide)
  have h23 : Entails.eval a c257 := h 256 (by decide)
  have h24 : Entails.eval a c379 := h 378 (by decide)
  have h25 : Entails.eval a c22 := h 21 (by decide)
  have h26 : Entails.eval a c35 := h 34 (by decide)
  have h27 : Entails.eval a c246 := h 245 (by decide)
  have h28 : Entails.eval a c119 := h 118 (by decide)
  have h29 : Entails.eval a c629 := derived629 a h
  have h30 : Entails.eval a c72 := h 71 (by decide)
  have h31 : Entails.eval a c157 := h 156 (by decide)
  have h32 : Entails.eval a c223 := h 222 (by decide)
  have h33 : Entails.eval a c439 := derived439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1912 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨18, by decide⟩, false), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c969, some c158, some c134, some c885, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1912 : lratChecker f1912 p1912 = .success := by decide +kernel
theorem unsat1912 : Unsatisfiable (PosFin 57) f1912 := by
  apply lratCheckerSound f1912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1912
  · intro a ha; simp [p1912] at ha; subst a; trivial
  · exact checked1912
theorem derived1912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1912 := by
  apply localUnsat_implies_entails f1912 [c1254, c969, c158, c134, c885] c1912 unsat1912 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c969 := derived969 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c885 := derived885 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1913 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1875, some c196, some c1911, some c1907, some c9, some c192, some c11, some c1254, some c1, some c112, some c23, some c30, some c1877, some c165, some c171, some c22, some c1912, some c194, some c119, some c8, some c1237, some c1102, some c1908, some c1818, some c367, some c55, some c1711, some c210, some c216, some c214, some c259, some c286, some c239, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1913 : lratChecker f1913 p1913 = .success := by decide +kernel
theorem unsat1913 : Unsatisfiable (PosFin 57) f1913 := by
  apply lratCheckerSound f1913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1913
  · intro a ha; simp [p1913] at ha; subst a; trivial
  · exact checked1913
theorem derived1913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1913 := by
  apply localUnsat_implies_entails f1913 [c1817, c1668, c1875, c196, c1911, c1907, c9, c192, c11, c1254, c1, c112, c23, c30, c1877, c165, c171, c22, c1912, c194, c119, c8, c1237, c1102, c1908, c1818, c367, c55, c1711, c210, c216, c214, c259, c286, c239] c1913 unsat1913 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1875 := derived1875 a h
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c1911 := derived1911 a h
  have h5 : Entails.eval a c1907 := derived1907 a h
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c1254 := derived1254 a h
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c1877 := derived1877 a h
  have h15 : Entails.eval a c165 := h 164 (by decide)
  have h16 : Entails.eval a c171 := h 170 (by decide)
  have h17 : Entails.eval a c22 := h 21 (by decide)
  have h18 : Entails.eval a c1912 := derived1912 a h
  have h19 : Entails.eval a c194 := h 193 (by decide)
  have h20 : Entails.eval a c119 := h 118 (by decide)
  have h21 : Entails.eval a c8 := h 7 (by decide)
  have h22 : Entails.eval a c1237 := derived1237 a h
  have h23 : Entails.eval a c1102 := derived1102 a h
  have h24 : Entails.eval a c1908 := derived1908 a h
  have h25 : Entails.eval a c1818 := derived1818 a h
  have h26 : Entails.eval a c367 := h 366 (by decide)
  have h27 : Entails.eval a c55 := h 54 (by decide)
  have h28 : Entails.eval a c1711 := derived1711 a h
  have h29 : Entails.eval a c210 := h 209 (by decide)
  have h30 : Entails.eval a c216 := h 215 (by decide)
  have h31 : Entails.eval a c214 := h 213 (by decide)
  have h32 : Entails.eval a c259 := h 258 (by decide)
  have h33 : Entails.eval a c286 := h 285 (by decide)
  have h34 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1914 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨56, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c187, some c185, some c382, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1914 : lratChecker f1914 p1914 = .success := by decide +kernel
theorem unsat1914 : Unsatisfiable (PosFin 57) f1914 := by
  apply lratCheckerSound f1914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1914
  · intro a ha; simp [p1914] at ha; subst a; trivial
  · exact checked1914
theorem derived1914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1914 := by
  apply localUnsat_implies_entails f1914 [c187, c185, c382] c1914 unsat1914 (by rfl) a
  have h0 : Entails.eval a c187 := h 186 (by decide)
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1915 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c969, some c158, some c134, some c68, some c53, some c132, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1915 : lratChecker f1915 p1915 = .success := by decide +kernel
theorem unsat1915 : Unsatisfiable (PosFin 57) f1915 := by
  apply lratCheckerSound f1915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1915
  · intro a ha; simp [p1915] at ha; subst a; trivial
  · exact checked1915
theorem derived1915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1915 := by
  apply localUnsat_implies_entails f1915 [c969, c158, c134, c68, c53, c132] c1915 unsat1915 (by rfl) a
  have h0 : Entails.eval a c969 := derived969 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1916 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1911, some c1907, some c1875, some c9, some c192, some c11, some c1254, some c112, some c196, some c1913, some c117, some c22, some c165, some c75, some c1914, some c194, some c1915, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1916 : lratChecker f1916 p1916 = .success := by decide +kernel
theorem unsat1916 : Unsatisfiable (PosFin 57) f1916 := by
  apply lratCheckerSound f1916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1916
  · intro a ha; simp [p1916] at ha; subst a; trivial
  · exact checked1916
theorem derived1916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1916 := by
  apply localUnsat_implies_entails f1916 [c1817, c1668, c1911, c1907, c1875, c9, c192, c11, c1254, c112, c196, c1913, c117, c22, c165, c75, c1914, c194, c1915] c1916 unsat1916 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1911 := derived1911 a h
  have h3 : Entails.eval a c1907 := derived1907 a h
  have h4 : Entails.eval a c1875 := derived1875 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c1254 := derived1254 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c1913 := derived1913 a h
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c165 := h 164 (by decide)
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c1914 := derived1914 a h
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c1915 := derived1915 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1917 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1875, some c112, some c1907, some c1, some c9, some c192, some c11, some c1911, some c1916, some c1097, some c184, some c1113, some c122, some c23, some c30, some c1877, some c170, some c241, some c380, some c366, some c365, some c1711, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1917 : lratChecker f1917 p1917 = .success := by decide +kernel
theorem unsat1917 : Unsatisfiable (PosFin 57) f1917 := by
  apply lratCheckerSound f1917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1917
  · intro a ha; simp [p1917] at ha; subst a; trivial
  · exact checked1917
theorem derived1917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1917 := by
  apply localUnsat_implies_entails f1917 [c1817, c1668, c1875, c112, c1907, c1, c9, c192, c11, c1911, c1916, c1097, c184, c1113, c122, c23, c30, c1877, c170, c241, c380, c366, c365, c1711] c1917 unsat1917 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1875 := derived1875 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1907 := derived1907 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c1911 := derived1911 a h
  have h10 : Entails.eval a c1916 := derived1916 a h
  have h11 : Entails.eval a c1097 := derived1097 a h
  have h12 : Entails.eval a c184 := h 183 (by decide)
  have h13 : Entails.eval a c1113 := derived1113 a h
  have h14 : Entails.eval a c122 := h 121 (by decide)
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c30 := h 29 (by decide)
  have h17 : Entails.eval a c1877 := derived1877 a h
  have h18 : Entails.eval a c170 := h 169 (by decide)
  have h19 : Entails.eval a c241 := h 240 (by decide)
  have h20 : Entails.eval a c380 := h 379 (by decide)
  have h21 : Entails.eval a c366 := h 365 (by decide)
  have h22 : Entails.eval a c365 := h 364 (by decide)
  have h23 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1918 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1875, some c1917, some c1003, some c195, some c196, some c112, some c1, some c93, some c94, some c379, some c4, some c1113, some c122, some c113, some c30, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1918 : lratChecker f1918 p1918 = .success := by decide +kernel
theorem unsat1918 : Unsatisfiable (PosFin 57) f1918 := by
  apply lratCheckerSound f1918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1918
  · intro a ha; simp [p1918] at ha; subst a; trivial
  · exact checked1918
theorem derived1918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1918 := by
  apply localUnsat_implies_entails f1918 [c1817, c1668, c1875, c1917, c1003, c195, c196, c112, c1, c93, c94, c379, c4, c1113, c122, c113, c30] c1918 unsat1918 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1875 := derived1875 a h
  have h3 : Entails.eval a c1917 := derived1917 a h
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c195 := h 194 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c1113 := derived1113 a h
  have h14 : Entails.eval a c122 := h 121 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1919 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1917, some c1918, some c376, some c1003, some c1875, some c112, some c23, some c30, some c170, some c243, some c1829, some c1714, some c113, some c1711, some c9, some c365, some c165, some c242, some c81, some c240, some c370, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1919 : lratChecker f1919 p1919 = .success := by decide +kernel
theorem unsat1919 : Unsatisfiable (PosFin 57) f1919 := by
  apply lratCheckerSound f1919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1919
  · intro a ha; simp [p1919] at ha; subst a; trivial
  · exact checked1919
theorem derived1919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1919 := by
  apply localUnsat_implies_entails f1919 [c1817, c1668, c1917, c1918, c376, c1003, c1875, c112, c23, c30, c170, c243, c1829, c1714, c113, c1711, c9, c365, c165, c242, c81, c240, c370] c1919 unsat1919 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1917 := derived1917 a h
  have h3 : Entails.eval a c1918 := derived1918 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c1003 := derived1003 a h
  have h6 : Entails.eval a c1875 := derived1875 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c1829 := derived1829 a h
  have h13 : Entails.eval a c1714 := derived1714 a h
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c1711 := derived1711 a h
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c365 := h 364 (by decide)
  have h18 : Entails.eval a c165 := h 164 (by decide)
  have h19 : Entails.eval a c242 := h 241 (by decide)
  have h20 : Entails.eval a c81 := h 80 (by decide)
  have h21 : Entails.eval a c240 := h 239 (by decide)
  have h22 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1920 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c170, some c161, some c82, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1920 : lratChecker f1920 p1920 = .success := by decide +kernel
theorem unsat1920 : Unsatisfiable (PosFin 57) f1920 := by
  apply lratCheckerSound f1920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1920
  · intro a ha; simp [p1920] at ha; subst a; trivial
  · exact checked1920
theorem derived1920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1920 := by
  apply localUnsat_implies_entails f1920 [c1668, c170, c161, c82] c1920 unsat1920 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c161 := h 160 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1921 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c112, some c1875, some c1917, some c1003, some c196, some c195, some c1918, some c376, some c1919, some c122, some c1113, some c11, some c1920, some c1829, some c29, some c31, some c260, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1921 : lratChecker f1921 p1921 = .success := by decide +kernel
theorem unsat1921 : Unsatisfiable (PosFin 57) f1921 := by
  apply lratCheckerSound f1921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1921
  · intro a ha; simp [p1921] at ha; subst a; trivial
  · exact checked1921
theorem derived1921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1921 := by
  apply localUnsat_implies_entails f1921 [c1817, c1668, c112, c1875, c1917, c1003, c196, c195, c1918, c376, c1919, c122, c1113, c11, c1920, c1829, c29, c31, c260] c1921 unsat1921 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1875 := derived1875 a h
  have h4 : Entails.eval a c1917 := derived1917 a h
  have h5 : Entails.eval a c1003 := derived1003 a h
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c1918 := derived1918 a h
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c1919 := derived1919 a h
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c1113 := derived1113 a h
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c1920 := derived1920 a h
  have h15 : Entails.eval a c1829 := derived1829 a h
  have h16 : Entails.eval a c29 := h 28 (by decide)
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1922 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c3, some c23, some c30, some c1531, some c1569, some c1827, some c363, some c25, some c1727, some c241, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1922 : lratChecker f1922 p1922 = .success := by decide +kernel
theorem unsat1922 : Unsatisfiable (PosFin 57) f1922 := by
  apply lratCheckerSound f1922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1922
  · intro a ha; simp [p1922] at ha; subst a; trivial
  · exact checked1922
theorem derived1922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1922 := by
  apply localUnsat_implies_entails f1922 [c1668, c1921, c3, c23, c30, c1531, c1569, c1827, c363, c25, c1727, c241] c1922 unsat1922 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c1531 := derived1531 a h
  have h6 : Entails.eval a c1569 := derived1569 a h
  have h7 : Entails.eval a c1827 := derived1827 a h
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c1727 := derived1727 a h
  have h11 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1923 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c51, some c56, some c143, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1923 : lratChecker f1923 p1923 = .success := by decide +kernel
theorem unsat1923 : Unsatisfiable (PosFin 57) f1923 := by
  apply lratCheckerSound f1923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1923
  · intro a ha; simp [p1923] at ha; subst a; trivial
  · exact checked1923
theorem derived1923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1923 := by
  apply localUnsat_implies_entails f1923 [c1817, c51, c56, c143] c1923 unsat1923 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1924 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨47, by decide⟩, true), (⟨41, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c162, some c1760, some c182, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1924 : lratChecker f1924 p1924 = .success := by decide +kernel
theorem unsat1924 : Unsatisfiable (PosFin 57) f1924 := by
  apply lratCheckerSound f1924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1924
  · intro a ha; simp [p1924] at ha; subst a; trivial
  · exact checked1924
theorem derived1924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1924 := by
  apply localUnsat_implies_entails f1924 [c367, c162, c1760, c182] c1924 unsat1924 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c1760 := derived1760 a h
  have h3 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1925 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1921, some c12, some c1254, some c191, some c1314, some c662, some c1923, some c203, some c115, some c21, some c163, some c1924, some c1231, some c183, some c1914, some c1760, some c193, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1925 : lratChecker f1925 p1925 = .success := by decide +kernel
theorem unsat1925 : Unsatisfiable (PosFin 57) f1925 := by
  apply lratCheckerSound f1925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1925
  · intro a ha; simp [p1925] at ha; subst a; trivial
  · exact checked1925
theorem derived1925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1925 := by
  apply localUnsat_implies_entails f1925 [c1817, c1668, c1921, c12, c1254, c191, c1314, c662, c1923, c203, c115, c21, c163, c1924, c1231, c183, c1914, c1760, c193] c1925 unsat1925 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c1314 := derived1314 a h
  have h7 : Entails.eval a c662 := derived662 a h
  have h8 : Entails.eval a c1923 := derived1923 a h
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c115 := h 114 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c1924 := derived1924 a h
  have h14 : Entails.eval a c1231 := derived1231 a h
  have h15 : Entails.eval a c183 := h 182 (by decide)
  have h16 : Entails.eval a c1914 := derived1914 a h
  have h17 : Entails.eval a c1760 := derived1760 a h
  have h18 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1926 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1, some c341, some c133, some c293, some c302, some c138, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1926 : lratChecker f1926 p1926 = .success := by decide +kernel
theorem unsat1926 : Unsatisfiable (PosFin 57) f1926 := by
  apply lratCheckerSound f1926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1926
  · intro a ha; simp [p1926] at ha; subst a; trivial
  · exact checked1926
theorem derived1926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1926 := by
  apply localUnsat_implies_entails f1926 [c1668, c1, c341, c133, c293, c302, c138] c1926 unsat1926 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c341 := h 340 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1927 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1, some c1921, some c12, some c5, some c1231, some c244, some c1763, some c1926, some c182, some c194, some c193, some c11, some c594, some c65, some c335, some c151, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1927 : lratChecker f1927 p1927 = .success := by decide +kernel
theorem unsat1927 : Unsatisfiable (PosFin 57) f1927 := by
  apply lratCheckerSound f1927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1927
  · intro a ha; simp [p1927] at ha; subst a; trivial
  · exact checked1927
theorem derived1927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1927 := by
  apply localUnsat_implies_entails f1927 [c1668, c1, c1921, c12, c5, c1231, c244, c1763, c1926, c182, c194, c193, c11, c594, c65, c335, c151] c1927 unsat1927 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c244 := h 243 (by decide)
  have h7 : Entails.eval a c1763 := derived1763 a h
  have h8 : Entails.eval a c1926 := derived1926 a h
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c194 := h 193 (by decide)
  have h11 : Entails.eval a c193 := h 192 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c594 := derived594 a h
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c335 := h 334 (by decide)
  have h16 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1928 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1, some c1926, some c131, some c150, some c302, some c332, some c133, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1928 : lratChecker f1928 p1928 = .success := by decide +kernel
theorem unsat1928 : Unsatisfiable (PosFin 57) f1928 := by
  apply lratCheckerSound f1928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1928
  · intro a ha; simp [p1928] at ha; subst a; trivial
  · exact checked1928
theorem derived1928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1928 := by
  apply localUnsat_implies_entails f1928 [c1668, c1, c1926, c131, c150, c302, c332, c133] c1928 unsat1928 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1926 := derived1926 a h
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c150 := h 149 (by decide)
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1929 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨22, by decide⟩, true), (⟨54, by decide⟩, false), (⟨16, by decide⟩, false), (⟨45, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1711, some c168, some c234, some c74, some c1827, some c380, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1929 : lratChecker f1929 p1929 = .success := by decide +kernel
theorem unsat1929 : Unsatisfiable (PosFin 57) f1929 := by
  apply lratCheckerSound f1929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1929
  · intro a ha; simp [p1929] at ha; subst a; trivial
  · exact checked1929
theorem derived1929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1929 := by
  apply localUnsat_implies_entails f1929 [c1711, c168, c234, c74, c1827, c380] c1929 unsat1929 (by rfl) a
  have h0 : Entails.eval a c1711 := derived1711 a h
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c234 := h 233 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c1827 := derived1827 a h
  have h5 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1930 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c5, some c1928, some c1, some c1762, some c12, some c1254, some c241, some c25, some c1927, some c183, some c194, some c182, some c242, some c1123, some c1929, some c1761, some c11, some c1773, some c65, some c132, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1930 : lratChecker f1930 p1930 = .success := by decide +kernel
theorem unsat1930 : Unsatisfiable (PosFin 57) f1930 := by
  apply lratCheckerSound f1930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1930
  · intro a ha; simp [p1930] at ha; subst a; trivial
  · exact checked1930
theorem derived1930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1930 := by
  apply localUnsat_implies_entails f1930 [c1668, c1921, c5, c1928, c1, c1762, c12, c1254, c241, c25, c1927, c183, c194, c182, c242, c1123, c1929, c1761, c11, c1773, c65, c132] c1930 unsat1930 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c1928 := derived1928 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1762 := derived1762 a h
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c1254 := derived1254 a h
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c1927 := derived1927 a h
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c194 := h 193 (by decide)
  have h13 : Entails.eval a c182 := h 181 (by decide)
  have h14 : Entails.eval a c242 := h 241 (by decide)
  have h15 : Entails.eval a c1123 := derived1123 a h
  have h16 : Entails.eval a c1929 := derived1929 a h
  have h17 : Entails.eval a c1761 := derived1761 a h
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c1773 := derived1773 a h
  have h20 : Entails.eval a c65 := h 64 (by decide)
  have h21 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1931 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1, some c150, some c155, some c335, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1931 : lratChecker f1931 p1931 = .success := by decide +kernel
theorem unsat1931 : Unsatisfiable (PosFin 57) f1931 := by
  apply lratCheckerSound f1931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1931
  · intro a ha; simp [p1931] at ha; subst a; trivial
  · exact checked1931
theorem derived1931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1931 := by
  apply localUnsat_implies_entails f1931 [c1668, c1, c150, c155, c335] c1931 unsat1931 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c150 := h 149 (by decide)
  have h3 : Entails.eval a c155 := h 154 (by decide)
  have h4 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1932 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1, some c1231, some c182, some c194, some c193, some c11, some c1931, some c65, some c157, some c151, some c335, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1932 : lratChecker f1932 p1932 = .success := by decide +kernel
theorem unsat1932 : Unsatisfiable (PosFin 57) f1932 := by
  apply lratCheckerSound f1932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1932
  · intro a ha; simp [p1932] at ha; subst a; trivial
  · exact checked1932
theorem derived1932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1932 := by
  apply localUnsat_implies_entails f1932 [c1668, c1, c1231, c182, c194, c193, c11, c1931, c65, c157, c151, c335] c1932 unsat1932 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c1931 := derived1931 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c151 := h 150 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1933 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨35, by decide⟩, false), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c31, some c1773, some c65, some c200, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1933 : lratChecker f1933 p1933 = .success := by decide +kernel
theorem unsat1933 : Unsatisfiable (PosFin 57) f1933 := by
  apply lratCheckerSound f1933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1933
  · intro a ha; simp [p1933] at ha; subst a; trivial
  · exact checked1933
theorem derived1933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1933 := by
  apply localUnsat_implies_entails f1933 [c1668, c31, c1773, c65, c200] c1933 unsat1933 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c1773 := derived1773 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1934 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c12, some c1254, some c5, some c1922, some c1925, some c1, some c1762, some c1928, some c1930, some c1932, some c183, some c194, some c182, some c1123, some c1933, some c118, some c11, some c1773, some c65, some c132, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1934 : lratChecker f1934 p1934 = .success := by decide +kernel
theorem unsat1934 : Unsatisfiable (PosFin 57) f1934 := by
  apply lratCheckerSound f1934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1934
  · intro a ha; simp [p1934] at ha; subst a; trivial
  · exact checked1934
theorem derived1934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1934 := by
  apply localUnsat_implies_entails f1934 [c1668, c1921, c12, c1254, c5, c1922, c1925, c1, c1762, c1928, c1930, c1932, c183, c194, c182, c1123, c1933, c118, c11, c1773, c65, c132] c1934 unsat1934 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1922 := derived1922 a h
  have h6 : Entails.eval a c1925 := derived1925 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c1762 := derived1762 a h
  have h9 : Entails.eval a c1928 := derived1928 a h
  have h10 : Entails.eval a c1930 := derived1930 a h
  have h11 : Entails.eval a c1932 := derived1932 a h
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c194 := h 193 (by decide)
  have h14 : Entails.eval a c182 := h 181 (by decide)
  have h15 : Entails.eval a c1123 := derived1123 a h
  have h16 : Entails.eval a c1933 := derived1933 a h
  have h17 : Entails.eval a c118 := h 117 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c1773 := derived1773 a h
  have h20 : Entails.eval a c65 := h 64 (by decide)
  have h21 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1935 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1934, some c1921, some c12, some c1254, some c5, some c191, some c1925, some c3, some c1531, some c250, some c1760, some c25, some c193, some c1827, some c1914, some c82, some c1231, some c163, some c1924, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1935 : lratChecker f1935 p1935 = .success := by decide +kernel
theorem unsat1935 : Unsatisfiable (PosFin 57) f1935 := by
  apply lratCheckerSound f1935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1935
  · intro a ha; simp [p1935] at ha; subst a; trivial
  · exact checked1935
theorem derived1935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1935 := by
  apply localUnsat_implies_entails f1935 [c1668, c1934, c1921, c12, c1254, c5, c191, c1925, c3, c1531, c250, c1760, c25, c193, c1827, c1914, c82, c1231, c163, c1924] c1935 unsat1935 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1934 := derived1934 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c1925 := derived1925 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c1531 := derived1531 a h
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c1760 := derived1760 a h
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c1827 := derived1827 a h
  have h15 : Entails.eval a c1914 := derived1914 a h
  have h16 : Entails.eval a c82 := h 81 (by decide)
  have h17 : Entails.eval a c1231 := derived1231 a h
  have h18 : Entails.eval a c163 := h 162 (by decide)
  have h19 : Entails.eval a c1924 := derived1924 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1936 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨35, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1773, some c65, some c200, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1936 : lratChecker f1936 p1936 = .success := by decide +kernel
theorem unsat1936 : Unsatisfiable (PosFin 57) f1936 := by
  apply lratCheckerSound f1936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1936
  · intro a ha; simp [p1936] at ha; subst a; trivial
  · exact checked1936
theorem derived1936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1936 := by
  apply localUnsat_implies_entails f1936 [c1773, c65, c200] c1936 unsat1936 (by rfl) a
  have h0 : Entails.eval a c1773 := derived1773 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1937 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c215, some c146, some c55, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1937 : lratChecker f1937 p1937 = .success := by decide +kernel
theorem unsat1937 : Unsatisfiable (PosFin 57) f1937 := by
  apply lratCheckerSound f1937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1937
  · intro a ha; simp [p1937] at ha; subst a; trivial
  · exact checked1937
theorem derived1937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1937 := by
  apply localUnsat_implies_entails f1937 [c215, c146, c55] c1937 unsat1937 (by rfl) a
  have h0 : Entails.eval a c215 := h 214 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1938 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c12, some c1254, some c5, some c1934, some c1935, some c1, some c10, some c1928, some c1762, some c1932, some c260, some c183, some c194, some c120, some c182, some c1123, some c1933, some c241, some c242, some c39, some c1937, some c293, some c129, some c332, some c333, some c226, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1938 : lratChecker f1938 p1938 = .success := by decide +kernel
theorem unsat1938 : Unsatisfiable (PosFin 57) f1938 := by
  apply lratCheckerSound f1938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1938
  · intro a ha; simp [p1938] at ha; subst a; trivial
  · exact checked1938
theorem derived1938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1938 := by
  apply localUnsat_implies_entails f1938 [c1668, c1921, c12, c1254, c5, c1934, c1935, c1, c10, c1928, c1762, c1932, c260, c183, c194, c120, c182, c1123, c1933, c241, c242, c39, c1937, c293, c129, c332, c333, c226] c1938 unsat1938 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1934 := derived1934 a h
  have h6 : Entails.eval a c1935 := derived1935 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c1928 := derived1928 a h
  have h10 : Entails.eval a c1762 := derived1762 a h
  have h11 : Entails.eval a c1932 := derived1932 a h
  have h12 : Entails.eval a c260 := h 259 (by decide)
  have h13 : Entails.eval a c183 := h 182 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c120 := h 119 (by decide)
  have h16 : Entails.eval a c182 := h 181 (by decide)
  have h17 : Entails.eval a c1123 := derived1123 a h
  have h18 : Entails.eval a c1933 := derived1933 a h
  have h19 : Entails.eval a c241 := h 240 (by decide)
  have h20 : Entails.eval a c242 := h 241 (by decide)
  have h21 : Entails.eval a c39 := h 38 (by decide)
  have h22 : Entails.eval a c1937 := derived1937 a h
  have h23 : Entails.eval a c293 := h 292 (by decide)
  have h24 : Entails.eval a c129 := h 128 (by decide)
  have h25 : Entails.eval a c332 := h 331 (by decide)
  have h26 : Entails.eval a c333 := h 332 (by decide)
  have h27 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1939 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1938, some c1921, some c12, some c1254, some c3, some c1531, some c184, some c193, some c188, some c1760, some c1231, some c1692, some c364, some c1569, some c166, some c23, some c1847, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1939 : lratChecker f1939 p1939 = .success := by decide +kernel
theorem unsat1939 : Unsatisfiable (PosFin 57) f1939 := by
  apply lratCheckerSound f1939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1939
  · intro a ha; simp [p1939] at ha; subst a; trivial
  · exact checked1939
theorem derived1939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1939 := by
  apply localUnsat_implies_entails f1939 [c1668, c1938, c1921, c12, c1254, c3, c1531, c184, c193, c188, c1760, c1231, c1692, c364, c1569, c166, c23, c1847] c1939 unsat1939 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1938 := derived1938 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1531 := derived1531 a h
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c1760 := derived1760 a h
  have h11 : Entails.eval a c1231 := derived1231 a h
  have h12 : Entails.eval a c1692 := derived1692 a h
  have h13 : Entails.eval a c364 := h 363 (by decide)
  have h14 : Entails.eval a c1569 := derived1569 a h
  have h15 : Entails.eval a c166 := h 165 (by decide)
  have h16 : Entails.eval a c23 := h 22 (by decide)
  have h17 : Entails.eval a c1847 := derived1847 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1940 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c19, some c1224, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1940 : lratChecker f1940 p1940 = .success := by decide +kernel
theorem unsat1940 : Unsatisfiable (PosFin 57) f1940 := by
  apply lratCheckerSound f1940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1940
  · intro a ha; simp [p1940] at ha; subst a; trivial
  · exact checked1940
theorem derived1940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1940 := by
  apply localUnsat_implies_entails f1940 [c1817, c19, c1224] c1940 unsat1940 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c1224 := derived1224 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1941 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true), (⟨48, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1921, some c184, some c364, some c1761, some c166, some c22, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1941 : lratChecker f1941 p1941 = .success := by decide +kernel
theorem unsat1941 : Unsatisfiable (PosFin 57) f1941 := by
  apply lratCheckerSound f1941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1941
  · intro a ha; simp [p1941] at ha; subst a; trivial
  · exact checked1941
theorem derived1941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1941 := by
  apply localUnsat_implies_entails f1941 [c1921, c184, c364, c1761, c166, c22] c1941 unsat1941 (by rfl) a
  have h0 : Entails.eval a c1921 := derived1921 a h
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c364 := h 363 (by decide)
  have h3 : Entails.eval a c1761 := derived1761 a h
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1942 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c12, some c1938, some c1939, some c1940, some c1692, some c190, some c188, some c1231, some c80, some c1254, some c5, some c1941, some c1531, some c1776, some c948, some c362, some c93, some c1569, some c1762, some c120, some c1761, some c237, some c132, some c252, some c304, some c1937, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1942 : lratChecker f1942 p1942 = .success := by decide +kernel
theorem unsat1942 : Unsatisfiable (PosFin 57) f1942 := by
  apply lratCheckerSound f1942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1942
  · intro a ha; simp [p1942] at ha; subst a; trivial
  · exact checked1942
theorem derived1942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1942 := by
  apply localUnsat_implies_entails f1942 [c1668, c1921, c12, c1938, c1939, c1940, c1692, c190, c188, c1231, c80, c1254, c5, c1941, c1531, c1776, c948, c362, c93, c1569, c1762, c120, c1761, c237, c132, c252, c304, c1937] c1942 unsat1942 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c1938 := derived1938 a h
  have h4 : Entails.eval a c1939 := derived1939 a h
  have h5 : Entails.eval a c1940 := derived1940 a h
  have h6 : Entails.eval a c1692 := derived1692 a h
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c1231 := derived1231 a h
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c1254 := derived1254 a h
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c1941 := derived1941 a h
  have h14 : Entails.eval a c1531 := derived1531 a h
  have h15 : Entails.eval a c1776 := derived1776 a h
  have h16 : Entails.eval a c948 := derived948 a h
  have h17 : Entails.eval a c362 := h 361 (by decide)
  have h18 : Entails.eval a c93 := h 92 (by decide)
  have h19 : Entails.eval a c1569 := derived1569 a h
  have h20 : Entails.eval a c1762 := derived1762 a h
  have h21 : Entails.eval a c120 := h 119 (by decide)
  have h22 : Entails.eval a c1761 := derived1761 a h
  have h23 : Entails.eval a c237 := h 236 (by decide)
  have h24 : Entails.eval a c132 := h 131 (by decide)
  have h25 : Entails.eval a c252 := h 251 (by decide)
  have h26 : Entails.eval a c304 := h 303 (by decide)
  have h27 : Entails.eval a c1937 := derived1937 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1943 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨19, by decide⟩, false), (⟨56, by decide⟩, true), (⟨48, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1921, some c1531, some c1847, some c184, some c364, some c166, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1943 : lratChecker f1943 p1943 = .success := by decide +kernel
theorem unsat1943 : Unsatisfiable (PosFin 57) f1943 := by
  apply lratCheckerSound f1943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1943
  · intro a ha; simp [p1943] at ha; subst a; trivial
  · exact checked1943
theorem derived1943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1943 := by
  apply localUnsat_implies_entails f1943 [c1921, c1531, c1847, c184, c364, c166] c1943 unsat1943 (by rfl) a
  have h0 : Entails.eval a c1921 := derived1921 a h
  have h1 : Entails.eval a c1531 := derived1531 a h
  have h2 : Entails.eval a c1847 := derived1847 a h
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c364 := h 363 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1944 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1938, some c1921, some c12, some c5, some c1939, some c1940, some c190, some c1692, some c188, some c1231, some c1942, some c1943, some c362, some c1569, some c364, some c1776, some c74, some c93, some c1762, some c260, some c120, some c1768, some c1122, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1944 : lratChecker f1944 p1944 = .success := by decide +kernel
theorem unsat1944 : Unsatisfiable (PosFin 57) f1944 := by
  apply lratCheckerSound f1944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1944
  · intro a ha; simp [p1944] at ha; subst a; trivial
  · exact checked1944
theorem derived1944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1944 := by
  apply localUnsat_implies_entails f1944 [c1668, c1938, c1921, c12, c5, c1939, c1940, c190, c1692, c188, c1231, c1942, c1943, c362, c1569, c364, c1776, c74, c93, c1762, c260, c120, c1768, c1122] c1944 unsat1944 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1938 := derived1938 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1939 := derived1939 a h
  have h6 : Entails.eval a c1940 := derived1940 a h
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c1692 := derived1692 a h
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c1231 := derived1231 a h
  have h11 : Entails.eval a c1942 := derived1942 a h
  have h12 : Entails.eval a c1943 := derived1943 a h
  have h13 : Entails.eval a c362 := h 361 (by decide)
  have h14 : Entails.eval a c1569 := derived1569 a h
  have h15 : Entails.eval a c364 := h 363 (by decide)
  have h16 : Entails.eval a c1776 := derived1776 a h
  have h17 : Entails.eval a c74 := h 73 (by decide)
  have h18 : Entails.eval a c93 := h 92 (by decide)
  have h19 : Entails.eval a c1762 := derived1762 a h
  have h20 : Entails.eval a c260 := h 259 (by decide)
  have h21 : Entails.eval a c120 := h 119 (by decide)
  have h22 : Entails.eval a c1768 := derived1768 a h
  have h23 : Entails.eval a c1122 := derived1122 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1945 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1921, some c12, some c1938, some c1944, some c1, some c10, some c1940, some c194, some c188, some c1123, some c67, some c135, some c160, some c51, some c966, some c142, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1945 : lratChecker f1945 p1945 = .success := by decide +kernel
theorem unsat1945 : Unsatisfiable (PosFin 57) f1945 := by
  apply lratCheckerSound f1945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1945
  · intro a ha; simp [p1945] at ha; subst a; trivial
  · exact checked1945
theorem derived1945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1945 := by
  apply localUnsat_implies_entails f1945 [c1668, c1817, c1921, c12, c1938, c1944, c1, c10, c1940, c194, c188, c1123, c67, c135, c160, c51, c966, c142] c1945 unsat1945 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c1938 := derived1938 a h
  have h5 : Entails.eval a c1944 := derived1944 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c1940 := derived1940 a h
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c1123 := derived1123 a h
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c135 := h 134 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c966 := derived966 a h
  have h17 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1946 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1945, some c1921, some c12, some c23, some c30, some c1569, some c1877, some c171, some c165, some c115, some c363, some c22, some c236, some c246, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1946 : lratChecker f1946 p1946 = .success := by decide +kernel
theorem unsat1946 : Unsatisfiable (PosFin 57) f1946 := by
  apply lratCheckerSound f1946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1946
  · intro a ha; simp [p1946] at ha; subst a; trivial
  · exact checked1946
theorem derived1946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1946 := by
  apply localUnsat_implies_entails f1946 [c1668, c1945, c1921, c12, c23, c30, c1569, c1877, c171, c165, c115, c363, c22, c236, c246] c1946 unsat1946 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1945 := derived1945 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c1569 := derived1569 a h
  have h7 : Entails.eval a c1877 := derived1877 a h
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c115 := h 114 (by decide)
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c236 := h 235 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1947 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1945, some c1921, some c12, some c5, some c1946, some c117, some c32, some c1762, some c250, some c94, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1947 : lratChecker f1947 p1947 = .success := by decide +kernel
theorem unsat1947 : Unsatisfiable (PosFin 57) f1947 := by
  apply lratCheckerSound f1947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1947
  · intro a ha; simp [p1947] at ha; subst a; trivial
  · exact checked1947
theorem derived1947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1947 := by
  apply localUnsat_implies_entails f1947 [c1668, c1945, c1921, c12, c5, c1946, c117, c32, c1762, c250, c94] c1947 unsat1947 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1945 := derived1945 a h
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1946 := derived1946 a h
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c1762 := derived1762 a h
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1948 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c191, some c115, some c244, some c1156, some c594, some c71, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1948 : lratChecker f1948 p1948 = .success := by decide +kernel
theorem unsat1948 : Unsatisfiable (PosFin 57) f1948 := by
  apply lratCheckerSound f1948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1948
  · intro a ha; simp [p1948] at ha; subst a; trivial
  · exact checked1948
theorem derived1948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1948 := by
  apply localUnsat_implies_entails f1948 [c1817, c191, c115, c244, c1156, c594, c71] c1948 unsat1948 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c244 := h 243 (by decide)
  have h4 : Entails.eval a c1156 := derived1156 a h
  have h5 : Entails.eval a c594 := derived594 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1949 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c162, some c367, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1949 : lratChecker f1949 p1949 = .success := by decide +kernel
theorem unsat1949 : Unsatisfiable (PosFin 57) f1949 := by
  apply lratCheckerSound f1949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1949
  · intro a ha; simp [p1949] at ha; subst a; trivial
  · exact checked1949
theorem derived1949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1949 := by
  apply localUnsat_implies_entails f1949 [c163, c162, c367] c1949 unsat1949 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1950 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨51, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c191, some c1921, some c1945, some c1516, some c1914, some c1231, some c1531, some c4, some c1947, some c1314, some c12, some c1254, some c1005, some c1949, some c73, some c21, some c1948, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1950 : lratChecker f1950 p1950 = .success := by decide +kernel
theorem unsat1950 : Unsatisfiable (PosFin 57) f1950 := by
  apply lratCheckerSound f1950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1950
  · intro a ha; simp [p1950] at ha; subst a; trivial
  · exact checked1950
theorem derived1950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1950 := by
  apply localUnsat_implies_entails f1950 [c1668, c191, c1921, c1945, c1516, c1914, c1231, c1531, c4, c1947, c1314, c12, c1254, c1005, c1949, c73, c21, c1948] c1950 unsat1950 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c1945 := derived1945 a h
  have h4 : Entails.eval a c1516 := derived1516 a h
  have h5 : Entails.eval a c1914 := derived1914 a h
  have h6 : Entails.eval a c1231 := derived1231 a h
  have h7 : Entails.eval a c1531 := derived1531 a h
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c1947 := derived1947 a h
  have h10 : Entails.eval a c1314 := derived1314 a h
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c1254 := derived1254 a h
  have h13 : Entails.eval a c1005 := derived1005 a h
  have h14 : Entails.eval a c1949 := derived1949 a h
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c1948 := derived1948 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1951 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c191, some c1921, some c1945, some c1516, some c12, some c1254, some c1531, some c1914, some c1231, some c1950, some c1779, some c367, some c1844, some c363, some c1711, some c22, some c74, some c1569, some c248, some c235, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1951 : lratChecker f1951 p1951 = .success := by decide +kernel
theorem unsat1951 : Unsatisfiable (PosFin 57) f1951 := by
  apply lratCheckerSound f1951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1951
  · intro a ha; simp [p1951] at ha; subst a; trivial
  · exact checked1951
theorem derived1951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1951 := by
  apply localUnsat_implies_entails f1951 [c1668, c191, c1921, c1945, c1516, c12, c1254, c1531, c1914, c1231, c1950, c1779, c367, c1844, c363, c1711, c22, c74, c1569, c248, c235] c1951 unsat1951 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c1921 := derived1921 a h
  have h3 : Entails.eval a c1945 := derived1945 a h
  have h4 : Entails.eval a c1516 := derived1516 a h
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c1254 := derived1254 a h
  have h7 : Entails.eval a c1531 := derived1531 a h
  have h8 : Entails.eval a c1914 := derived1914 a h
  have h9 : Entails.eval a c1231 := derived1231 a h
  have h10 : Entails.eval a c1950 := derived1950 a h
  have h11 : Entails.eval a c1779 := derived1779 a h
  have h12 : Entails.eval a c367 := h 366 (by decide)
  have h13 : Entails.eval a c1844 := derived1844 a h
  have h14 : Entails.eval a c363 := h 362 (by decide)
  have h15 : Entails.eval a c1711 := derived1711 a h
  have h16 : Entails.eval a c22 := h 21 (by decide)
  have h17 : Entails.eval a c74 := h 73 (by decide)
  have h18 : Entails.eval a c1569 := derived1569 a h
  have h19 : Entails.eval a c248 := h 247 (by decide)
  have h20 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1952 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1231, some c1951, some c1947, some c1921, some c1314, some c1945, some c1516, some c12, some c1254, some c1005, some c1949, some c73, some c21, some c1733, some c1948, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1952 : lratChecker f1952 p1952 = .success := by decide +kernel
theorem unsat1952 : Unsatisfiable (PosFin 57) f1952 := by
  apply lratCheckerSound f1952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1952
  · intro a ha; simp [p1952] at ha; subst a; trivial
  · exact checked1952
theorem derived1952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1952 := by
  apply localUnsat_implies_entails f1952 [c1668, c1231, c1951, c1947, c1921, c1314, c1945, c1516, c12, c1254, c1005, c1949, c73, c21, c1733, c1948] c1952 unsat1952 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c1951 := derived1951 a h
  have h3 : Entails.eval a c1947 := derived1947 a h
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c1314 := derived1314 a h
  have h6 : Entails.eval a c1945 := derived1945 a h
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c1254 := derived1254 a h
  have h10 : Entails.eval a c1005 := derived1005 a h
  have h11 : Entails.eval a c1949 := derived1949 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c1733 := derived1733 a h
  have h15 : Entails.eval a c1948 := derived1948 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1953 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c5, some c1762, some c1231, some c12, some c1254, some c1952, some c1779, some c367, some c1711, some c1945, some c115, some c244, some c241, some c235, some c25, some c1877, some c1827, some c1158, some c246, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1953 : lratChecker f1953 p1953 = .success := by decide +kernel
theorem unsat1953 : Unsatisfiable (PosFin 57) f1953 := by
  apply lratCheckerSound f1953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1953
  · intro a ha; simp [p1953] at ha; subst a; trivial
  · exact checked1953
theorem derived1953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1953 := by
  apply localUnsat_implies_entails f1953 [c1668, c1921, c5, c1762, c1231, c12, c1254, c1952, c1779, c367, c1711, c1945, c115, c244, c241, c235, c25, c1877, c1827, c1158, c246] c1953 unsat1953 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c1762 := derived1762 a h
  have h4 : Entails.eval a c1231 := derived1231 a h
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c1254 := derived1254 a h
  have h7 : Entails.eval a c1952 := derived1952 a h
  have h8 : Entails.eval a c1779 := derived1779 a h
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c1711 := derived1711 a h
  have h11 : Entails.eval a c1945 := derived1945 a h
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c244 := h 243 (by decide)
  have h14 : Entails.eval a c241 := h 240 (by decide)
  have h15 : Entails.eval a c235 := h 234 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c1877 := derived1877 a h
  have h18 : Entails.eval a c1827 := derived1827 a h
  have h19 : Entails.eval a c1158 := derived1158 a h
  have h20 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1954 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1921, some c1314, some c191, some c12, some c1254, some c1952, some c1756, some c5, some c332, some c1953, some c197, some c296, some c293, some c147, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1954 : lratChecker f1954 p1954 = .success := by decide +kernel
theorem unsat1954 : Unsatisfiable (PosFin 57) f1954 := by
  apply lratCheckerSound f1954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1954
  · intro a ha; simp [p1954] at ha; subst a; trivial
  · exact checked1954
theorem derived1954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1954 := by
  apply localUnsat_implies_entails f1954 [c1921, c1314, c191, c12, c1254, c1952, c1756, c5, c332, c1953, c197, c296, c293, c147] c1954 unsat1954 (by rfl) a
  have h0 : Entails.eval a c1921 := derived1921 a h
  have h1 : Entails.eval a c1314 := derived1314 a h
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c1952 := derived1952 a h
  have h6 : Entails.eval a c1756 := derived1756 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c332 := h 331 (by decide)
  have h9 : Entails.eval a c1953 := derived1953 a h
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c296 := h 295 (by decide)
  have h12 : Entails.eval a c293 := h 292 (by decide)
  have h13 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1955 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨47, by decide⟩, true), (⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1231, some c367, some c1711, some c1921, some c248, some c235, some c1569, some c363, some c237, some c246, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1955 : lratChecker f1955 p1955 = .success := by decide +kernel
theorem unsat1955 : Unsatisfiable (PosFin 57) f1955 := by
  apply lratCheckerSound f1955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1955
  · intro a ha; simp [p1955] at ha; subst a; trivial
  · exact checked1955
theorem derived1955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1955 := by
  apply localUnsat_implies_entails f1955 [c1668, c1231, c367, c1711, c1921, c248, c235, c1569, c363, c237, c246] c1955 unsat1955 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c1711 := derived1711 a h
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c235 := h 234 (by decide)
  have h7 : Entails.eval a c1569 := derived1569 a h
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c237 := h 236 (by decide)
  have h10 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1956 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c12, some c1254, some c5, some c1231, some c1952, some c1779, some c367, some c1954, some c93, some c1955, some c22, some c32, some c372, some c363, some c252, some c29, some c257, some c236, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1956 : lratChecker f1956 p1956 = .success := by decide +kernel
theorem unsat1956 : Unsatisfiable (PosFin 57) f1956 := by
  apply lratCheckerSound f1956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1956
  · intro a ha; simp [p1956] at ha; subst a; trivial
  · exact checked1956
theorem derived1956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1956 := by
  apply localUnsat_implies_entails f1956 [c1668, c1921, c12, c1254, c5, c1231, c1952, c1779, c367, c1954, c93, c1955, c22, c32, c372, c363, c252, c29, c257, c236] c1956 unsat1956 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c1952 := derived1952 a h
  have h7 : Entails.eval a c1779 := derived1779 a h
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c1954 := derived1954 a h
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c1955 := derived1955 a h
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c32 := h 31 (by decide)
  have h14 : Entails.eval a c372 := h 371 (by decide)
  have h15 : Entails.eval a c363 := h 362 (by decide)
  have h16 : Entails.eval a c252 := h 251 (by decide)
  have h17 : Entails.eval a c29 := h 28 (by decide)
  have h18 : Entails.eval a c257 := h 256 (by decide)
  have h19 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1957 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨52, by decide⟩, false), (⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c159, some c157, some c343, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1957 : lratChecker f1957 p1957 = .success := by decide +kernel
theorem unsat1957 : Unsatisfiable (PosFin 57) f1957 := by
  apply lratCheckerSound f1957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1957
  · intro a ha; simp [p1957] at ha; subst a; trivial
  · exact checked1957
theorem derived1957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1957 := by
  apply localUnsat_implies_entails f1957 [c159, c157, c343] c1957 unsat1957 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c157 := h 156 (by decide)
  have h2 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1958 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c981, some c55, some c56, some c1957, some c72, some c71, some c276, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1958 : lratChecker f1958 p1958 = .success := by decide +kernel
theorem unsat1958 : Unsatisfiable (PosFin 57) f1958 := by
  apply lratCheckerSound f1958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1958
  · intro a ha; simp [p1958] at ha; subst a; trivial
  · exact checked1958
theorem derived1958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1958 := by
  apply localUnsat_implies_entails f1958 [c1817, c981, c55, c56, c1957, c72, c71, c276] c1958 unsat1958 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c981 := derived981 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c1957 := derived1957 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1959 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c1945, some c1516, some c12, some c1254, some c5, some c191, some c1314, some c1958, some c185, some c1231, some c1956, some c123, some c117, some c22, some c32, some c1762, some c165, some c250, some c263, some c1727, some c361, some c236, some c372, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1959 : lratChecker f1959 p1959 = .success := by decide +kernel
theorem unsat1959 : Unsatisfiable (PosFin 57) f1959 := by
  apply lratCheckerSound f1959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1959
  · intro a ha; simp [p1959] at ha; subst a; trivial
  · exact checked1959
theorem derived1959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1959 := by
  apply localUnsat_implies_entails f1959 [c1668, c1921, c1945, c1516, c12, c1254, c5, c191, c1314, c1958, c185, c1231, c1956, c123, c117, c22, c32, c1762, c165, c250, c263, c1727, c361, c236, c372] c1959 unsat1959 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c1945 := derived1945 a h
  have h3 : Entails.eval a c1516 := derived1516 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c1254 := derived1254 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c1314 := derived1314 a h
  have h9 : Entails.eval a c1958 := derived1958 a h
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c1231 := derived1231 a h
  have h12 : Entails.eval a c1956 := derived1956 a h
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c117 := h 116 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c32 := h 31 (by decide)
  have h17 : Entails.eval a c1762 := derived1762 a h
  have h18 : Entails.eval a c165 := h 164 (by decide)
  have h19 : Entails.eval a c250 := h 249 (by decide)
  have h20 : Entails.eval a c263 := h 262 (by decide)
  have h21 : Entails.eval a c1727 := derived1727 a h
  have h22 : Entails.eval a c361 := h 360 (by decide)
  have h23 : Entails.eval a c236 := h 235 (by decide)
  have h24 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1960 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c19, some c1958, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1960 : lratChecker f1960 p1960 = .success := by decide +kernel
theorem unsat1960 : Unsatisfiable (PosFin 57) f1960 := by
  apply lratCheckerSound f1960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1960
  · intro a ha; simp [p1960] at ha; subst a; trivial
  · exact checked1960
theorem derived1960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1960 := by
  apply localUnsat_implies_entails f1960 [c5, c19, c1958] c1960 unsat1960 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c1958 := derived1958 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1961 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c1945, some c1516, some c12, some c1254, some c1959, some c184, some c1531, some c1960, some c190, some c188, some c1231, some c380, some c943, some c74, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1961 : lratChecker f1961 p1961 = .success := by decide +kernel
theorem unsat1961 : Unsatisfiable (PosFin 57) f1961 := by
  apply lratCheckerSound f1961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1961
  · intro a ha; simp [p1961] at ha; subst a; trivial
  · exact checked1961
theorem derived1961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1961 := by
  apply localUnsat_implies_entails f1961 [c1668, c1921, c1945, c1516, c12, c1254, c1959, c184, c1531, c1960, c190, c188, c1231, c380, c943, c74] c1961 unsat1961 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c1945 := derived1945 a h
  have h3 : Entails.eval a c1516 := derived1516 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c1254 := derived1254 a h
  have h6 : Entails.eval a c1959 := derived1959 a h
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c1531 := derived1531 a h
  have h9 : Entails.eval a c1960 := derived1960 a h
  have h10 : Entails.eval a c190 := h 189 (by decide)
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c1231 := derived1231 a h
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c943 := derived943 a h
  have h15 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1962 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨56, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c12, some c1945, some c5, some c1961, some c1, some c1762, some c117, some c74, some c1769, some c1955, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1962 : lratChecker f1962 p1962 = .success := by decide +kernel
theorem unsat1962 : Unsatisfiable (PosFin 57) f1962 := by
  apply lratCheckerSound f1962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1962
  · intro a ha; simp [p1962] at ha; subst a; trivial
  · exact checked1962
theorem derived1962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1962 := by
  apply localUnsat_implies_entails f1962 [c1668, c1921, c12, c1945, c5, c1961, c1, c1762, c117, c74, c1769, c1955] c1962 unsat1962 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c1945 := derived1945 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1961 := derived1961 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c1762 := derived1762 a h
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c1769 := derived1769 a h
  have h11 : Entails.eval a c1955 := derived1955 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1963 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1963 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1, some c1960, some c1780, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1963 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1963 : lratChecker f1963 p1963 = .success := by decide +kernel
theorem unsat1963 : Unsatisfiable (PosFin 57) f1963 := by
  apply lratCheckerSound f1963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1963
  · intro a ha; simp [p1963] at ha; subst a; trivial
  · exact checked1963
theorem derived1963 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1963 := by
  apply localUnsat_implies_entails f1963 [c1668, c1, c1960, c1780] c1963 unsat1963 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1960 := derived1960 a h
  have h3 : Entails.eval a c1780 := derived1780 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1964 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨18, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1964 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c1254, some c165, some c1755, some c1963, some c120, some c168, some c235, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1964 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1964 : lratChecker f1964 p1964 = .success := by decide +kernel
theorem unsat1964 : Unsatisfiable (PosFin 57) f1964 := by
  apply lratCheckerSound f1964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1964
  · intro a ha; simp [p1964] at ha; subst a; trivial
  · exact checked1964
theorem derived1964 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1964 := by
  apply localUnsat_implies_entails f1964 [c117, c1254, c165, c1755, c1963, c120, c168, c235] c1964 unsat1964 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c165 := h 164 (by decide)
  have h3 : Entails.eval a c1755 := derived1755 a h
  have h4 : Entails.eval a c1963 := derived1963 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c168 := h 167 (by decide)
  have h7 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1965 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨56, by decide⟩, true), (⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1965 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1960, some c185, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1965 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1965 : lratChecker f1965 p1965 = .success := by decide +kernel
theorem unsat1965 : Unsatisfiable (PosFin 57) f1965 := by
  apply lratCheckerSound f1965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1965
  · intro a ha; simp [p1965] at ha; subst a; trivial
  · exact checked1965
theorem derived1965 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1965 := by
  apply localUnsat_implies_entails f1965 [c1960, c185] c1965 unsat1965 (by rfl) a
  have h0 : Entails.eval a c1960 := derived1960 a h
  have h1 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1966 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1966 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c5, some c1961, some c1, some c1762, some c12, some c1254, some c1945, some c1516, some c1964, some c1962, some c1965, some c120, some c1769, some c74, some c117, some c235, some c1711, some c234, some c367, some c247, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1966 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1966 : lratChecker f1966 p1966 = .success := by decide +kernel
theorem unsat1966 : Unsatisfiable (PosFin 57) f1966 := by
  apply lratCheckerSound f1966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1966
  · intro a ha; simp [p1966] at ha; subst a; trivial
  · exact checked1966
theorem derived1966 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1966 := by
  apply localUnsat_implies_entails f1966 [c1668, c1921, c5, c1961, c1, c1762, c12, c1254, c1945, c1516, c1964, c1962, c1965, c120, c1769, c74, c117, c235, c1711, c234, c367, c247] c1966 unsat1966 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c1961 := derived1961 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1762 := derived1762 a h
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c1254 := derived1254 a h
  have h8 : Entails.eval a c1945 := derived1945 a h
  have h9 : Entails.eval a c1516 := derived1516 a h
  have h10 : Entails.eval a c1964 := derived1964 a h
  have h11 : Entails.eval a c1962 := derived1962 a h
  have h12 : Entails.eval a c1965 := derived1965 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c1769 := derived1769 a h
  have h15 : Entails.eval a c74 := h 73 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c235 := h 234 (by decide)
  have h18 : Entails.eval a c1711 := derived1711 a h
  have h19 : Entails.eval a c234 := h 233 (by decide)
  have h20 : Entails.eval a c367 := h 366 (by decide)
  have h21 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1967 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1967 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c5, some c12, some c1254, some c1945, some c1516, some c1961, some c1, some c1762, some c1964, some c74, some c84, some c1769, some c1962, some c1965, some c120, some c1966, some c1569, some c1827, some c380, some c246, some c367, some c237, some c1711, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1967 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1967 : lratChecker f1967 p1967 = .success := by decide +kernel
theorem unsat1967 : Unsatisfiable (PosFin 57) f1967 := by
  apply lratCheckerSound f1967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1967
  · intro a ha; simp [p1967] at ha; subst a; trivial
  · exact checked1967
theorem derived1967 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1967 := by
  apply localUnsat_implies_entails f1967 [c1668, c1921, c5, c12, c1254, c1945, c1516, c1961, c1, c1762, c1964, c74, c84, c1769, c1962, c1965, c120, c1966, c1569, c1827, c380, c246, c367, c237, c1711] c1967 unsat1967 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c1945 := derived1945 a h
  have h6 : Entails.eval a c1516 := derived1516 a h
  have h7 : Entails.eval a c1961 := derived1961 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c1762 := derived1762 a h
  have h10 : Entails.eval a c1964 := derived1964 a h
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c1769 := derived1769 a h
  have h14 : Entails.eval a c1962 := derived1962 a h
  have h15 : Entails.eval a c1965 := derived1965 a h
  have h16 : Entails.eval a c120 := h 119 (by decide)
  have h17 : Entails.eval a c1966 := derived1966 a h
  have h18 : Entails.eval a c1569 := derived1569 a h
  have h19 : Entails.eval a c1827 := derived1827 a h
  have h20 : Entails.eval a c380 := h 379 (by decide)
  have h21 : Entails.eval a c246 := h 245 (by decide)
  have h22 : Entails.eval a c367 := h 366 (by decide)
  have h23 : Entails.eval a c237 := h 236 (by decide)
  have h24 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1968 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1968 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1967, some c189, some c1231, some c188, some c1921, some c39, some c1904, some c113, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1968 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1968 : lratChecker f1968 p1968 = .success := by decide +kernel
theorem unsat1968 : Unsatisfiable (PosFin 57) f1968 := by
  apply lratCheckerSound f1968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1968
  · intro a ha; simp [p1968] at ha; subst a; trivial
  · exact checked1968
theorem derived1968 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1968 := by
  apply localUnsat_implies_entails f1968 [c1668, c1967, c189, c1231, c188, c1921, c39, c1904, c113] c1968 unsat1968 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1967 := derived1967 a h
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c1231 := derived1231 a h
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c1921 := derived1921 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c1904 := derived1904 a h
  have h8 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1969 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1969 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1967, some c30, some c1857, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1969 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1969 : lratChecker f1969 p1969 = .success := by decide +kernel
theorem unsat1969 : Unsatisfiable (PosFin 57) f1969 := by
  apply lratCheckerSound f1969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1969
  · intro a ha; simp [p1969] at ha; subst a; trivial
  · exact checked1969
theorem derived1969 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1969 := by
  apply localUnsat_implies_entails f1969 [c1668, c1967, c30, c1857] c1969 unsat1969 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1967 := derived1967 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c1857 := derived1857 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1970 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨50, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1970 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1967, some c189, some c1921, some c1231, some c188, some c190, some c1969, some c1224, some c1904, some c1968, some c113, some c248, some c32, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1970 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1970 : lratChecker f1970 p1970 = .success := by decide +kernel
theorem unsat1970 : Unsatisfiable (PosFin 57) f1970 := by
  apply lratCheckerSound f1970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1970
  · intro a ha; simp [p1970] at ha; subst a; trivial
  · exact checked1970
theorem derived1970 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1970 := by
  apply localUnsat_implies_entails f1970 [c1668, c1817, c1967, c189, c1921, c1231, c188, c190, c1969, c1224, c1904, c1968, c113, c248, c32] c1970 unsat1970 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c1969 := derived1969 a h
  have h9 : Entails.eval a c1224 := derived1224 a h
  have h10 : Entails.eval a c1904 := derived1904 a h
  have h11 : Entails.eval a c1968 := derived1968 a h
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c248 := h 247 (by decide)
  have h14 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1971 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨56, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1971 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1967, some c189, some c1921, some c8, some c183, some c1224, some c1531, some c30, some c1852, some c113, some c25, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1971 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1971 : lratChecker f1971 p1971 = .success := by decide +kernel
theorem unsat1971 : Unsatisfiable (PosFin 57) f1971 := by
  apply lratCheckerSound f1971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1971
  · intro a ha; simp [p1971] at ha; subst a; trivial
  · exact checked1971
theorem derived1971 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1971 := by
  apply localUnsat_implies_entails f1971 [c1817, c1668, c1967, c189, c1921, c8, c183, c1224, c1531, c30, c1852, c113, c25] c1971 unsat1971 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  have h7 : Entails.eval a c1224 := derived1224 a h
  have h8 : Entails.eval a c1531 := derived1531 a h
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c1852 := derived1852 a h
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1972 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1972 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c30, some c1852, some c113, some c25, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1972 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1972 : lratChecker f1972 p1972 = .success := by decide +kernel
theorem unsat1972 : Unsatisfiable (PosFin 57) f1972 := by
  apply lratCheckerSound f1972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1972
  · intro a ha; simp [p1972] at ha; subst a; trivial
  · exact checked1972
theorem derived1972 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1972 := by
  apply localUnsat_implies_entails f1972 [c1668, c30, c1852, c113, c25] c1972 unsat1972 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c1852 := derived1852 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1973 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1973 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1967, some c172, some c1827, some c364, some c234, some c1711, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1973 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1973 : lratChecker f1973 p1973 = .success := by decide +kernel
theorem unsat1973 : Unsatisfiable (PosFin 57) f1973 := by
  apply lratCheckerSound f1973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1973
  · intro a ha; simp [p1973] at ha; subst a; trivial
  · exact checked1973
theorem derived1973 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1973 := by
  apply localUnsat_implies_entails f1973 [c1967, c172, c1827, c364, c234, c1711] c1973 unsat1973 (by rfl) a
  have h0 : Entails.eval a c1967 := derived1967 a h
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c1827 := derived1827 a h
  have h3 : Entails.eval a c364 := h 363 (by decide)
  have h4 : Entails.eval a c234 := h 233 (by decide)
  have h5 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1974 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1974 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1967, some c189, some c184, some c1921, some c1973, some c84, some c25, some c1612, some c113, some c363, some c364, some c21, some c370, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1974 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1974 : lratChecker f1974 p1974 = .success := by decide +kernel
theorem unsat1974 : Unsatisfiable (PosFin 57) f1974 := by
  apply lratCheckerSound f1974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1974
  · intro a ha; simp [p1974] at ha; subst a; trivial
  · exact checked1974
theorem derived1974 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1974 := by
  apply localUnsat_implies_entails f1974 [c1668, c1967, c189, c184, c1921, c1973, c84, c25, c1612, c113, c363, c364, c21, c370] c1974 unsat1974 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1967 := derived1967 a h
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c1973 := derived1973 a h
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c1612 := derived1612 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c363 := h 362 (by decide)
  have h11 : Entails.eval a c364 := h 363 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1975 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1975 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1921, some c29, some c32, some c113, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1975 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1975 : lratChecker f1975 p1975 = .success := by decide +kernel
theorem unsat1975 : Unsatisfiable (PosFin 57) f1975 := by
  apply lratCheckerSound f1975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1975
  · intro a ha; simp [p1975] at ha; subst a; trivial
  · exact checked1975
theorem derived1975 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1975 := by
  apply localUnsat_implies_entails f1975 [c1668, c1921, c29, c32, c113] c1975 unsat1975 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1921 := derived1921 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1976 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨50, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1976 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1967, some c1975, some c189, some c1970, some c1971, some c190, some c188, some c380, some c247, some c1974, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1976 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1976 : lratChecker f1976 p1976 = .success := by decide +kernel
theorem unsat1976 : Unsatisfiable (PosFin 57) f1976 := by
  apply lratCheckerSound f1976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1976
  · intro a ha; simp [p1976] at ha; subst a; trivial
  · exact checked1976
theorem derived1976 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1976 := by
  apply localUnsat_implies_entails f1976 [c1967, c1975, c189, c1970, c1971, c190, c188, c380, c247, c1974] c1976 unsat1976 (by rfl) a
  have h0 : Entails.eval a c1967 := derived1967 a h
  have h1 : Entails.eval a c1975 := derived1975 a h
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c1970 := derived1970 a h
  have h4 : Entails.eval a c1971 := derived1971 a h
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c1974 := derived1974 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1977 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1977 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1967, some c2, some c1976, some c1856, some c1975, some c189, some c1231, some c248, some c188, some c1968, some c190, some c1224, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1977 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1977 : lratChecker f1977 p1977 = .success := by decide +kernel
theorem unsat1977 : Unsatisfiable (PosFin 57) f1977 := by
  apply lratCheckerSound f1977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1977
  · intro a ha; simp [p1977] at ha; subst a; trivial
  · exact checked1977
theorem derived1977 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1977 := by
  apply localUnsat_implies_entails f1977 [c1668, c1817, c1967, c2, c1976, c1856, c1975, c189, c1231, c248, c188, c1968, c190, c1224] c1977 unsat1977 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c1976 := derived1976 a h
  have h5 : Entails.eval a c1856 := derived1856 a h
  have h6 : Entails.eval a c1975 := derived1975 a h
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c1231 := derived1231 a h
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c1968 := derived1968 a h
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c1224 := derived1224 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1978 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1978 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1936, some c1773, some c154, some c200, some c69, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1978 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1978 : lratChecker f1978 p1978 = .success := by decide +kernel
theorem unsat1978 : Unsatisfiable (PosFin 57) f1978 := by
  apply lratCheckerSound f1978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1978
  · intro a ha; simp [p1978] at ha; subst a; trivial
  · exact checked1978
theorem derived1978 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1978 := by
  apply localUnsat_implies_entails f1978 [c1936, c1773, c154, c200, c69] c1978 unsat1978 (by rfl) a
  have h0 : Entails.eval a c1936 := derived1936 a h
  have h1 : Entails.eval a c1773 := derived1773 a h
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1979 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨52, by decide⟩, true), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1979 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c38, some c652, some c1978, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1979 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1979 : lratChecker f1979 p1979 = .success := by decide +kernel
theorem unsat1979 : Unsatisfiable (PosFin 57) f1979 := by
  apply lratCheckerSound f1979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1979
  · intro a ha; simp [p1979] at ha; subst a; trivial
  · exact checked1979
theorem derived1979 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1979 := by
  apply localUnsat_implies_entails f1979 [c25, c38, c652, c1978] c1979 unsat1979 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c652 := derived652 a h
  have h3 : Entails.eval a c1978 := derived1978 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1980 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1980 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1967, some c1975, some c189, some c1921, some c2, some c1976, some c1856, some c260, some c245, some c1977, some c183, some c190, some c188, some c380, some c247, some c1979, some c113, some c1245, some c31, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1980 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1980 : lratChecker f1980 p1980 = .success := by decide +kernel
theorem unsat1980 : Unsatisfiable (PosFin 57) f1980 := by
  apply lratCheckerSound f1980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1980
  · intro a ha; simp [p1980] at ha; subst a; trivial
  · exact checked1980
theorem derived1980 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1980 := by
  apply localUnsat_implies_entails f1980 [c1817, c1668, c1967, c1975, c189, c1921, c2, c1976, c1856, c260, c245, c1977, c183, c190, c188, c380, c247, c1979, c113, c1245, c31] c1980 unsat1980 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c1975 := derived1975 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c1921 := derived1921 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c1976 := derived1976 a h
  have h8 : Entails.eval a c1856 := derived1856 a h
  have h9 : Entails.eval a c260 := h 259 (by decide)
  have h10 : Entails.eval a c245 := h 244 (by decide)
  have h11 : Entails.eval a c1977 := derived1977 a h
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c190 := h 189 (by decide)
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c247 := h 246 (by decide)
  have h17 : Entails.eval a c1979 := derived1979 a h
  have h18 : Entails.eval a c113 := h 112 (by decide)
  have h19 : Entails.eval a c1245 := derived1245 a h
  have h20 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1981 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1981 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1980, some c1967, some c189, some c1231, some c1969, some c188, some c190, some c193, some c1224, some c1546, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1981 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1981 : lratChecker f1981 p1981 = .success := by decide +kernel
theorem unsat1981 : Unsatisfiable (PosFin 57) f1981 := by
  apply lratCheckerSound f1981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1981
  · intro a ha; simp [p1981] at ha; subst a; trivial
  · exact checked1981
theorem derived1981 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1981 := by
  apply localUnsat_implies_entails f1981 [c1668, c1817, c1980, c1967, c189, c1231, c1969, c188, c190, c193, c1224, c1546] c1981 unsat1981 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1980 := derived1980 a h
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c1969 := derived1969 a h
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c1224 := derived1224 a h
  have h11 : Entails.eval a c1546 := derived1546 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1982 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1982 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1980, some c1967, some c1975, some c189, some c1921, some c1976, some c96, some c1981, some c1971, some c1692, some c120, some c235, some c1941, some c1761, some c1569, some c1531, some c237, some c3, some c252, some c1527, some c25, some c83, some c161, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1982 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1982 : lratChecker f1982 p1982 = .success := by decide +kernel
theorem unsat1982 : Unsatisfiable (PosFin 57) f1982 := by
  apply lratCheckerSound f1982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1982
  · intro a ha; simp [p1982] at ha; subst a; trivial
  · exact checked1982
theorem derived1982 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1982 := by
  apply localUnsat_implies_entails f1982 [c1817, c1668, c1980, c1967, c1975, c189, c1921, c1976, c96, c1981, c1971, c1692, c120, c235, c1941, c1761, c1569, c1531, c237, c3, c252, c1527, c25, c83, c161] c1982 unsat1982 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1980 := derived1980 a h
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c1975 := derived1975 a h
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c1921 := derived1921 a h
  have h7 : Entails.eval a c1976 := derived1976 a h
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c1981 := derived1981 a h
  have h10 : Entails.eval a c1971 := derived1971 a h
  have h11 : Entails.eval a c1692 := derived1692 a h
  have h12 : Entails.eval a c120 := h 119 (by decide)
  have h13 : Entails.eval a c235 := h 234 (by decide)
  have h14 : Entails.eval a c1941 := derived1941 a h
  have h15 : Entails.eval a c1761 := derived1761 a h
  have h16 : Entails.eval a c1569 := derived1569 a h
  have h17 : Entails.eval a c1531 := derived1531 a h
  have h18 : Entails.eval a c237 := h 236 (by decide)
  have h19 : Entails.eval a c3 := h 2 (by decide)
  have h20 : Entails.eval a c252 := h 251 (by decide)
  have h21 : Entails.eval a c1527 := derived1527 a h
  have h22 : Entails.eval a c25 := h 24 (by decide)
  have h23 : Entails.eval a c83 := h 82 (by decide)
  have h24 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1983 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1983 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1980, some c1967, some c189, some c1921, some c190, some c193, some c184, some c1531, some c3, some c1224, some c1575, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1983 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1983 : lratChecker f1983 p1983 = .success := by decide +kernel
theorem unsat1983 : Unsatisfiable (PosFin 57) f1983 := by
  apply lratCheckerSound f1983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1983
  · intro a ha; simp [p1983] at ha; subst a; trivial
  · exact checked1983
theorem derived1983 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1983 := by
  apply localUnsat_implies_entails f1983 [c1817, c1980, c1967, c189, c1921, c190, c193, c184, c1531, c3, c1224, c1575] c1983 unsat1983 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1980 := derived1980 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c1921 := derived1921 a h
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c1531 := derived1531 a h
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1224 := derived1224 a h
  have h11 : Entails.eval a c1575 := derived1575 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1983

end CochromaticTwenty.Certificates.B16_2_2
