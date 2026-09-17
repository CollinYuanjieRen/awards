import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps1400_1499

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1914 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c31, some c1, some c1913, some c110, some c14, some c963, some c62, some c562, some c182, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1914 : lratChecker f1914 p1914 = .success := by decide +kernel
theorem unsat1914 : Unsatisfiable (PosFin 57) f1914 := by
  apply lratCheckerSound f1914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1914
  · intro a ha; simp [p1914] at ha; subst a; trivial
  · exact checked1914
theorem derived1914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1914 := by
  apply localUnsat_implies_entails f1914 [c1829, c31, c1, c1913, c110, c14, c963, c62, c562, c182] c1914 unsat1914 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1913 := derived1913 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c963 := derived963 a h
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c562 := derived562 a h
  have h9 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1915 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c200, some c1, some c17, some c1533, some c71, some c73, some c157, some c352, some c220, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1915 : lratChecker f1915 p1915 = .success := by decide +kernel
theorem unsat1915 : Unsatisfiable (PosFin 57) f1915 := by
  apply lratCheckerSound f1915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1915
  · intro a ha; simp [p1915] at ha; subst a; trivial
  · exact checked1915
theorem derived1915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1915 := by
  apply localUnsat_implies_entails f1915 [c1829, c200, c1, c17, c1533, c71, c73, c157, c352, c220] c1915 unsat1915 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c1533 := derived1533 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1916 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨6, by decide⟩, true), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c157, some c59, some c70, some c253, some c350, some c60, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1916 : lratChecker f1916 p1916 = .success := by decide +kernel
theorem unsat1916 : Unsatisfiable (PosFin 57) f1916 := by
  apply lratCheckerSound f1916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1916
  · intro a ha; simp [p1916] at ha; subst a; trivial
  · exact checked1916
theorem derived1916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1916 := by
  apply localUnsat_implies_entails f1916 [c157, c59, c70, c253, c350, c60] c1916 unsat1916 (by rfl) a
  have h0 : Entails.eval a c157 := h 156 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c253 := h 252 (by decide)
  have h4 : Entails.eval a c350 := h 349 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1917 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c268, some c21, some c1, some c1911, some c1890, some c31, some c1914, some c200, some c1915, some c110, some c1916, some c220, some c153, some c835, some c117, some c139, some c715, some c269, some c707, some c205, some c48, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1917 : lratChecker f1917 p1917 = .success := by decide +kernel
theorem unsat1917 : Unsatisfiable (PosFin 57) f1917 := by
  apply lratCheckerSound f1917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1917
  · intro a ha; simp [p1917] at ha; subst a; trivial
  · exact checked1917
theorem derived1917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1917 := by
  apply localUnsat_implies_entails f1917 [c1829, c268, c21, c1, c1911, c1890, c31, c1914, c200, c1915, c110, c1916, c220, c153, c835, c117, c139, c715, c269, c707, c205, c48] c1917 unsat1917 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1911 := derived1911 a h
  have h5 : Entails.eval a c1890 := derived1890 a h
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c1914 := derived1914 a h
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c1915 := derived1915 a h
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c1916 := derived1916 a h
  have h12 : Entails.eval a c220 := h 219 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c835 := derived835 a h
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c139 := h 138 (by decide)
  have h17 : Entails.eval a c715 := derived715 a h
  have h18 : Entails.eval a c269 := h 268 (by decide)
  have h19 : Entails.eval a c707 := derived707 a h
  have h20 : Entails.eval a c205 := h 204 (by decide)
  have h21 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1918 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c52, some c208, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1918 : lratChecker f1918 p1918 = .success := by decide +kernel
theorem unsat1918 : Unsatisfiable (PosFin 57) f1918 := by
  apply lratCheckerSound f1918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1918
  · intro a ha; simp [p1918] at ha; subst a; trivial
  · exact checked1918
theorem derived1918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1918 := by
  apply localUnsat_implies_entails f1918 [c46, c52, c208] c1918 unsat1918 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1919 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1558, some c14, some c202, some c201, some c149, some c148, some c56, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1919 : lratChecker f1919 p1919 = .success := by decide +kernel
theorem unsat1919 : Unsatisfiable (PosFin 57) f1919 := by
  apply lratCheckerSound f1919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1919
  · intro a ha; simp [p1919] at ha; subst a; trivial
  · exact checked1919
theorem derived1919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1919 := by
  apply localUnsat_implies_entails f1919 [c1558, c14, c202, c201, c149, c148, c56] c1919 unsat1919 (by rfl) a
  have h0 : Entails.eval a c1558 := derived1558 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c148 := h 147 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1920 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1911, some c1890, some c268, some c1896, some c1917, some c109, some c1918, some c1919, some c200, some c148, some c136, some c835, some c88, some c82, some c1496, some c59, some c185, some c190, some c357, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1920 : lratChecker f1920 p1920 = .success := by decide +kernel
theorem unsat1920 : Unsatisfiable (PosFin 57) f1920 := by
  apply lratCheckerSound f1920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1920
  · intro a ha; simp [p1920] at ha; subst a; trivial
  · exact checked1920
theorem derived1920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1920 := by
  apply localUnsat_implies_entails f1920 [c1911, c1890, c268, c1896, c1917, c109, c1918, c1919, c200, c148, c136, c835, c88, c82, c1496, c59, c185, c190, c357] c1920 unsat1920 (by rfl) a
  have h0 : Entails.eval a c1911 := derived1911 a h
  have h1 : Entails.eval a c1890 := derived1890 a h
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c1896 := derived1896 a h
  have h4 : Entails.eval a c1917 := derived1917 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c1918 := derived1918 a h
  have h7 : Entails.eval a c1919 := derived1919 a h
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c136 := h 135 (by decide)
  have h11 : Entails.eval a c835 := derived835 a h
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c1496 := derived1496 a h
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c185 := h 184 (by decide)
  have h17 : Entails.eval a c190 := h 189 (by decide)
  have h18 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1921 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c267, some c1744, some c31, some c201, some c200, some c109, some c14, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1921 : lratChecker f1921 p1921 = .success := by decide +kernel
theorem unsat1921 : Unsatisfiable (PosFin 57) f1921 := by
  apply lratCheckerSound f1921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1921
  · intro a ha; simp [p1921] at ha; subst a; trivial
  · exact checked1921
theorem derived1921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1921 := by
  apply localUnsat_implies_entails f1921 [c1829, c267, c1744, c31, c201, c200, c109, c14] c1921 unsat1921 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c1744 := derived1744 a h
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1922 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c31, some c1914, some c1916, some c1915, some c110, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1922 : lratChecker f1922 p1922 = .success := by decide +kernel
theorem unsat1922 : Unsatisfiable (PosFin 57) f1922 := by
  apply lratCheckerSound f1922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1922
  · intro a ha; simp [p1922] at ha; subst a; trivial
  · exact checked1922
theorem derived1922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1922 := by
  apply localUnsat_implies_entails f1922 [c1829, c31, c1914, c1916, c1915, c110] c1922 unsat1922 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c1914 := derived1914 a h
  have h3 : Entails.eval a c1916 := derived1916 a h
  have h4 : Entails.eval a c1915 := derived1915 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1923 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1911, some c1890, some c1, some c21, some c1920, some c119, some c1921, some c1896, some c835, some c54, some c153, some c208, some c220, some c1922, some c109, some c1918, some c1678, some c1919, some c200, some c1496, some c128, some c136, some c70, some c88, some c241, some c275, some c294, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1923 : lratChecker f1923 p1923 = .success := by decide +kernel
theorem unsat1923 : Unsatisfiable (PosFin 57) f1923 := by
  apply lratCheckerSound f1923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1923
  · intro a ha; simp [p1923] at ha; subst a; trivial
  · exact checked1923
theorem derived1923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1923 := by
  apply localUnsat_implies_entails f1923 [c1829, c1911, c1890, c1, c21, c1920, c119, c1921, c1896, c835, c54, c153, c208, c220, c1922, c109, c1918, c1678, c1919, c200, c1496, c128, c136, c70, c88, c241, c275, c294] c1923 unsat1923 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1911 := derived1911 a h
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c1920 := derived1920 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c1921 := derived1921 a h
  have h8 : Entails.eval a c1896 := derived1896 a h
  have h9 : Entails.eval a c835 := derived835 a h
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c208 := h 207 (by decide)
  have h13 : Entails.eval a c220 := h 219 (by decide)
  have h14 : Entails.eval a c1922 := derived1922 a h
  have h15 : Entails.eval a c109 := h 108 (by decide)
  have h16 : Entails.eval a c1918 := derived1918 a h
  have h17 : Entails.eval a c1678 := derived1678 a h
  have h18 : Entails.eval a c1919 := derived1919 a h
  have h19 : Entails.eval a c200 := h 199 (by decide)
  have h20 : Entails.eval a c1496 := derived1496 a h
  have h21 : Entails.eval a c128 := h 127 (by decide)
  have h22 : Entails.eval a c136 := h 135 (by decide)
  have h23 : Entails.eval a c70 := h 69 (by decide)
  have h24 : Entails.eval a c88 := h 87 (by decide)
  have h25 : Entails.eval a c241 := h 240 (by decide)
  have h26 : Entails.eval a c275 := h 274 (by decide)
  have h27 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1924 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨31, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1147, some c201, some c202, some c1275, some c110, some c56, some c1530, some c26, some c149, some c54, some c1257, some c281, some c214, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1924 : lratChecker f1924 p1924 = .success := by decide +kernel
theorem unsat1924 : Unsatisfiable (PosFin 57) f1924 := by
  apply lratCheckerSound f1924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1924
  · intro a ha; simp [p1924] at ha; subst a; trivial
  · exact checked1924
theorem derived1924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1924 := by
  apply localUnsat_implies_entails f1924 [c1829, c1147, c201, c202, c1275, c110, c56, c1530, c26, c149, c54, c1257, c281, c214] c1924 unsat1924 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1275 := derived1275 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c1530 := derived1530 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c149 := h 148 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c1257 := derived1257 a h
  have h12 : Entails.eval a c281 := h 280 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1925 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1911, some c1912, some c1890, some c1923, some c263, some c262, some c119, some c1147, some c202, some c201, some c1744, some c1924, some c109, some c1530, some c54, some c1918, some c208, some c214, some c149, some c317, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1925 : lratChecker f1925 p1925 = .success := by decide +kernel
theorem unsat1925 : Unsatisfiable (PosFin 57) f1925 := by
  apply lratCheckerSound f1925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1925
  · intro a ha; simp [p1925] at ha; subst a; trivial
  · exact checked1925
theorem derived1925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1925 := by
  apply localUnsat_implies_entails f1925 [c1911, c1912, c1890, c1923, c263, c262, c119, c1147, c202, c201, c1744, c1924, c109, c1530, c54, c1918, c208, c214, c149, c317] c1925 unsat1925 (by rfl) a
  have h0 : Entails.eval a c1911 := derived1911 a h
  have h1 : Entails.eval a c1912 := derived1912 a h
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c1923 := derived1923 a h
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c1744 := derived1744 a h
  have h11 : Entails.eval a c1924 := derived1924 a h
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c1530 := derived1530 a h
  have h14 : Entails.eval a c54 := h 53 (by decide)
  have h15 : Entails.eval a c1918 := derived1918 a h
  have h16 : Entails.eval a c208 := h 207 (by decide)
  have h17 : Entails.eval a c214 := h 213 (by decide)
  have h18 : Entails.eval a c149 := h 148 (by decide)
  have h19 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1926 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1911, some c1912, some c1925, some c29, some c22, some c263, some c262, some c1147, some c201, some c159, some c1744, some c226, some c228, some c346, some c353, some c66, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1926 : lratChecker f1926 p1926 = .success := by decide +kernel
theorem unsat1926 : Unsatisfiable (PosFin 57) f1926 := by
  apply lratCheckerSound f1926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1926
  · intro a ha; simp [p1926] at ha; subst a; trivial
  · exact checked1926
theorem derived1926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1926 := by
  apply localUnsat_implies_entails f1926 [c1829, c1911, c1912, c1925, c29, c22, c263, c262, c1147, c201, c159, c1744, c226, c228, c346, c353, c66] c1926 unsat1926 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1911 := derived1911 a h
  have h2 : Entails.eval a c1912 := derived1912 a h
  have h3 : Entails.eval a c1925 := derived1925 a h
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c1744 := derived1744 a h
  have h12 : Entails.eval a c226 := h 225 (by decide)
  have h13 : Entails.eval a c228 := h 227 (by decide)
  have h14 : Entails.eval a c346 := h 345 (by decide)
  have h15 : Entails.eval a c353 := h 352 (by decide)
  have h16 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1927 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1926, some c1911, some c1890, some c3, some c23, some c30, some c35, some c1906, some c200, some c157, some c261, some c22, some c220, some c1496, some c110, some c353, some c352, some c835, some c5, some c117, some c131, some c34, some c139, some c148, some c579, some c90, some c92, some c4, some c60, some c257, some c307, some c98, some c364, some c185, some c698, some c338, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1927 : lratChecker f1927 p1927 = .success := by decide +kernel
theorem unsat1927 : Unsatisfiable (PosFin 57) f1927 := by
  apply lratCheckerSound f1927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1927
  · intro a ha; simp [p1927] at ha; subst a; trivial
  · exact checked1927
theorem derived1927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1927 := by
  apply localUnsat_implies_entails f1927 [c1829, c1926, c1911, c1890, c3, c23, c30, c35, c1906, c200, c157, c261, c22, c220, c1496, c110, c353, c352, c835, c5, c117, c131, c34, c139, c148, c579, c90, c92, c4, c60, c257, c307, c98, c364, c185, c698, c338] c1927 unsat1927 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1926 := derived1926 a h
  have h2 : Entails.eval a c1911 := derived1911 a h
  have h3 : Entails.eval a c1890 := derived1890 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c1906 := derived1906 a h
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c220 := h 219 (by decide)
  have h14 : Entails.eval a c1496 := derived1496 a h
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c353 := h 352 (by decide)
  have h17 : Entails.eval a c352 := h 351 (by decide)
  have h18 : Entails.eval a c835 := derived835 a h
  have h19 : Entails.eval a c5 := h 4 (by decide)
  have h20 : Entails.eval a c117 := h 116 (by decide)
  have h21 : Entails.eval a c131 := h 130 (by decide)
  have h22 : Entails.eval a c34 := h 33 (by decide)
  have h23 : Entails.eval a c139 := h 138 (by decide)
  have h24 : Entails.eval a c148 := h 147 (by decide)
  have h25 : Entails.eval a c579 := derived579 a h
  have h26 : Entails.eval a c90 := h 89 (by decide)
  have h27 : Entails.eval a c92 := h 91 (by decide)
  have h28 : Entails.eval a c4 := h 3 (by decide)
  have h29 : Entails.eval a c60 := h 59 (by decide)
  have h30 : Entails.eval a c257 := h 256 (by decide)
  have h31 : Entails.eval a c307 := h 306 (by decide)
  have h32 : Entails.eval a c98 := h 97 (by decide)
  have h33 : Entails.eval a c364 := h 363 (by decide)
  have h34 : Entails.eval a c185 := h 184 (by decide)
  have h35 : Entails.eval a c698 := derived698 a h
  have h36 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1928 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1927, some c29, some c1923, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1928 : lratChecker f1928 p1928 = .success := by decide +kernel
theorem unsat1928 : Unsatisfiable (PosFin 57) f1928 := by
  apply lratCheckerSound f1928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1928
  · intro a ha; simp [p1928] at ha; subst a; trivial
  · exact checked1928
theorem derived1928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1928 := by
  apply localUnsat_implies_entails f1928 [c1829, c1927, c29, c1923] c1928 unsat1928 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1927 := derived1927 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c1923 := derived1923 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1929 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c1744, some c1211, some c896, some c200, some c14, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1929 : lratChecker f1929 p1929 = .success := by decide +kernel
theorem unsat1929 : Unsatisfiable (PosFin 57) f1929 := by
  apply lratCheckerSound f1929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1929
  · intro a ha; simp [p1929] at ha; subst a; trivial
  · exact checked1929
theorem derived1929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1929 := by
  apply localUnsat_implies_entails f1929 [c267, c1744, c1211, c896, c200, c14] c1929 unsat1929 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c1744 := derived1744 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c896 := derived896 a h
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1930 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1911, some c1926, some c1927, some c1929, some c1928, some c1890, some c1211, some c110, some c28, some c8, some c1275, some c868, some c1147, some c876, some c873, some c139, some c152, some c239, some c231, some c313, some c47, some c727, some c286, some c208, some c156, some c278, some c66, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1930 : lratChecker f1930 p1930 = .success := by decide +kernel
theorem unsat1930 : Unsatisfiable (PosFin 57) f1930 := by
  apply lratCheckerSound f1930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1930
  · intro a ha; simp [p1930] at ha; subst a; trivial
  · exact checked1930
theorem derived1930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1930 := by
  apply localUnsat_implies_entails f1930 [c1829, c1911, c1926, c1927, c1929, c1928, c1890, c1211, c110, c28, c8, c1275, c868, c1147, c876, c873, c139, c152, c239, c231, c313, c47, c727, c286, c208, c156, c278, c66] c1930 unsat1930 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1911 := derived1911 a h
  have h2 : Entails.eval a c1926 := derived1926 a h
  have h3 : Entails.eval a c1927 := derived1927 a h
  have h4 : Entails.eval a c1929 := derived1929 a h
  have h5 : Entails.eval a c1928 := derived1928 a h
  have h6 : Entails.eval a c1890 := derived1890 a h
  have h7 : Entails.eval a c1211 := derived1211 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c1275 := derived1275 a h
  have h12 : Entails.eval a c868 := derived868 a h
  have h13 : Entails.eval a c1147 := derived1147 a h
  have h14 : Entails.eval a c876 := derived876 a h
  have h15 : Entails.eval a c873 := derived873 a h
  have h16 : Entails.eval a c139 := h 138 (by decide)
  have h17 : Entails.eval a c152 := h 151 (by decide)
  have h18 : Entails.eval a c239 := h 238 (by decide)
  have h19 : Entails.eval a c231 := h 230 (by decide)
  have h20 : Entails.eval a c313 := h 312 (by decide)
  have h21 : Entails.eval a c47 := h 46 (by decide)
  have h22 : Entails.eval a c727 := derived727 a h
  have h23 : Entails.eval a c286 := h 285 (by decide)
  have h24 : Entails.eval a c208 := h 207 (by decide)
  have h25 : Entails.eval a c156 := h 155 (by decide)
  have h26 : Entails.eval a c278 := h 277 (by decide)
  have h27 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1931 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c201, some c200, some c14, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1931 : lratChecker f1931 p1931 = .success := by decide +kernel
theorem unsat1931 : Unsatisfiable (PosFin 57) f1931 := by
  apply lratCheckerSound f1931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1931
  · intro a ha; simp [p1931] at ha; subst a; trivial
  · exact checked1931
theorem derived1931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1931 := by
  apply localUnsat_implies_entails f1931 [c201, c200, c14] c1931 unsat1931 (by rfl) a
  have h0 : Entails.eval a c201 := h 200 (by decide)
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1932 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1931, some c1558, some c14, some c202, some c120, some c56, some c966, some c878, some c139, some c715, some c239, some c135, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1932 : lratChecker f1932 p1932 = .success := by decide +kernel
theorem unsat1932 : Unsatisfiable (PosFin 57) f1932 := by
  apply lratCheckerSound f1932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1932
  · intro a ha; simp [p1932] at ha; subst a; trivial
  · exact checked1932
theorem derived1932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1932 := by
  apply localUnsat_implies_entails f1932 [c1931, c1558, c14, c202, c120, c56, c966, c878, c139, c715, c239, c135] c1932 unsat1932 (by rfl) a
  have h0 : Entails.eval a c1931 := derived1931 a h
  have h1 : Entails.eval a c1558 := derived1558 a h
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c966 := derived966 a h
  have h7 : Entails.eval a c878 := derived878 a h
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c715 := derived715 a h
  have h10 : Entails.eval a c239 := h 238 (by decide)
  have h11 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1933 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨20, by decide⟩, false), (⟨12, by decide⟩, true), (⟨23, by decide⟩, false), (⟨21, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1928, some c1927, some c1890, some c1147, some c876, some c873, some c139, some c152, some c148, some c239, some c231, some c313, some c987, some c286, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1933 : lratChecker f1933 p1933 = .success := by decide +kernel
theorem unsat1933 : Unsatisfiable (PosFin 57) f1933 := by
  apply lratCheckerSound f1933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1933
  · intro a ha; simp [p1933] at ha; subst a; trivial
  · exact checked1933
theorem derived1933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1933 := by
  apply localUnsat_implies_entails f1933 [c1928, c1927, c1890, c1147, c876, c873, c139, c152, c148, c239, c231, c313, c987, c286] c1933 unsat1933 (by rfl) a
  have h0 : Entails.eval a c1928 := derived1928 a h
  have h1 : Entails.eval a c1927 := derived1927 a h
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c876 := derived876 a h
  have h5 : Entails.eval a c873 := derived873 a h
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c239 := h 238 (by decide)
  have h10 : Entails.eval a c231 := h 230 (by decide)
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c987 := derived987 a h
  have h13 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1934 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1911, some c1926, some c1927, some c1929, some c1928, some c1890, some c1930, some c1909, some c1931, some c11, some c4, some c1932, some c1916, some c220, some c1933, some c202, some c131, some c1496, some c153, some c66, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1934 : lratChecker f1934 p1934 = .success := by decide +kernel
theorem unsat1934 : Unsatisfiable (PosFin 57) f1934 := by
  apply lratCheckerSound f1934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1934
  · intro a ha; simp [p1934] at ha; subst a; trivial
  · exact checked1934
theorem derived1934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1934 := by
  apply localUnsat_implies_entails f1934 [c1829, c1911, c1926, c1927, c1929, c1928, c1890, c1930, c1909, c1931, c11, c4, c1932, c1916, c220, c1933, c202, c131, c1496, c153, c66] c1934 unsat1934 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1911 := derived1911 a h
  have h2 : Entails.eval a c1926 := derived1926 a h
  have h3 : Entails.eval a c1927 := derived1927 a h
  have h4 : Entails.eval a c1929 := derived1929 a h
  have h5 : Entails.eval a c1928 := derived1928 a h
  have h6 : Entails.eval a c1890 := derived1890 a h
  have h7 : Entails.eval a c1930 := derived1930 a h
  have h8 : Entails.eval a c1909 := derived1909 a h
  have h9 : Entails.eval a c1931 := derived1931 a h
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c1932 := derived1932 a h
  have h13 : Entails.eval a c1916 := derived1916 a h
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c1933 := derived1933 a h
  have h16 : Entails.eval a c202 := h 201 (by decide)
  have h17 : Entails.eval a c131 := h 130 (by decide)
  have h18 : Entails.eval a c1496 := derived1496 a h
  have h19 : Entails.eval a c153 := h 152 (by decide)
  have h20 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1935 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c109, some c1911, some c1926, some c1927, some c1929, some c1928, some c1890, some c10, some c1919, some c1908, some c1918, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1935 : lratChecker f1935 p1935 = .success := by decide +kernel
theorem unsat1935 : Unsatisfiable (PosFin 57) f1935 := by
  apply lratCheckerSound f1935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1935
  · intro a ha; simp [p1935] at ha; subst a; trivial
  · exact checked1935
theorem derived1935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1935 := by
  apply localUnsat_implies_entails f1935 [c1829, c109, c1911, c1926, c1927, c1929, c1928, c1890, c10, c1919, c1908, c1918] c1935 unsat1935 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c1911 := derived1911 a h
  have h3 : Entails.eval a c1926 := derived1926 a h
  have h4 : Entails.eval a c1927 := derived1927 a h
  have h5 : Entails.eval a c1929 := derived1929 a h
  have h6 : Entails.eval a c1928 := derived1928 a h
  have h7 : Entails.eval a c1890 := derived1890 a h
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c1919 := derived1919 a h
  have h10 : Entails.eval a c1908 := derived1908 a h
  have h11 : Entails.eval a c1918 := derived1918 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1936 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c109, some c1931, some c116, some c129, some c46, some c1918, some c868, some c208, some c5, some c280, some c1496, some c225, some c66, some c70, some c347, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1936 : lratChecker f1936 p1936 = .success := by decide +kernel
theorem unsat1936 : Unsatisfiable (PosFin 57) f1936 := by
  apply lratCheckerSound f1936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1936
  · intro a ha; simp [p1936] at ha; subst a; trivial
  · exact checked1936
theorem derived1936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1936 := by
  apply localUnsat_implies_entails f1936 [c1829, c109, c1931, c116, c129, c46, c1918, c868, c208, c5, c280, c1496, c225, c66, c70, c347] c1936 unsat1936 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c1931 := derived1931 a h
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c1918 := derived1918 a h
  have h7 : Entails.eval a c868 := derived868 a h
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c1496 := derived1496 a h
  have h12 : Entails.eval a c225 := h 224 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1937 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1911, some c1926, some c1927, some c1929, some c1928, some c1890, some c1934, some c109, some c1931, some c1935, some c1936, some c1933, some c202, some c120, some c8, some c131, some c48, some c56, some c699, some c1496, some c208, some c139, some c1918, some c66, some c715, some c239, some c231, some c25, some c269, some c286, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1937 : lratChecker f1937 p1937 = .success := by decide +kernel
theorem unsat1937 : Unsatisfiable (PosFin 57) f1937 := by
  apply lratCheckerSound f1937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1937
  · intro a ha; simp [p1937] at ha; subst a; trivial
  · exact checked1937
theorem derived1937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1937 := by
  apply localUnsat_implies_entails f1937 [c1829, c1911, c1926, c1927, c1929, c1928, c1890, c1934, c109, c1931, c1935, c1936, c1933, c202, c120, c8, c131, c48, c56, c699, c1496, c208, c139, c1918, c66, c715, c239, c231, c25, c269, c286] c1937 unsat1937 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1911 := derived1911 a h
  have h2 : Entails.eval a c1926 := derived1926 a h
  have h3 : Entails.eval a c1927 := derived1927 a h
  have h4 : Entails.eval a c1929 := derived1929 a h
  have h5 : Entails.eval a c1928 := derived1928 a h
  have h6 : Entails.eval a c1890 := derived1890 a h
  have h7 : Entails.eval a c1934 := derived1934 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c1931 := derived1931 a h
  have h10 : Entails.eval a c1935 := derived1935 a h
  have h11 : Entails.eval a c1936 := derived1936 a h
  have h12 : Entails.eval a c1933 := derived1933 a h
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  have h16 : Entails.eval a c131 := h 130 (by decide)
  have h17 : Entails.eval a c48 := h 47 (by decide)
  have h18 : Entails.eval a c56 := h 55 (by decide)
  have h19 : Entails.eval a c699 := derived699 a h
  have h20 : Entails.eval a c1496 := derived1496 a h
  have h21 : Entails.eval a c208 := h 207 (by decide)
  have h22 : Entails.eval a c139 := h 138 (by decide)
  have h23 : Entails.eval a c1918 := derived1918 a h
  have h24 : Entails.eval a c66 := h 65 (by decide)
  have h25 : Entails.eval a c715 := derived715 a h
  have h26 : Entails.eval a c239 := h 238 (by decide)
  have h27 : Entails.eval a c231 := h 230 (by decide)
  have h28 : Entails.eval a c25 := h 24 (by decide)
  have h29 : Entails.eval a c269 := h 268 (by decide)
  have h30 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1938 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1928, some c1927, some c1926, some c1911, some c1890, some c1929, some c1937, some c874, some c119, some c120, some c215, some c703, some c202, some c54, some c110, some c1147, some c14, some c1909, some c876, some c1936, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1938 : lratChecker f1938 p1938 = .success := by decide +kernel
theorem unsat1938 : Unsatisfiable (PosFin 57) f1938 := by
  apply lratCheckerSound f1938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1938
  · intro a ha; simp [p1938] at ha; subst a; trivial
  · exact checked1938
theorem derived1938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1938 := by
  apply localUnsat_implies_entails f1938 [c1928, c1927, c1926, c1911, c1890, c1929, c1937, c874, c119, c120, c215, c703, c202, c54, c110, c1147, c14, c1909, c876, c1936] c1938 unsat1938 (by rfl) a
  have h0 : Entails.eval a c1928 := derived1928 a h
  have h1 : Entails.eval a c1927 := derived1927 a h
  have h2 : Entails.eval a c1926 := derived1926 a h
  have h3 : Entails.eval a c1911 := derived1911 a h
  have h4 : Entails.eval a c1890 := derived1890 a h
  have h5 : Entails.eval a c1929 := derived1929 a h
  have h6 : Entails.eval a c1937 := derived1937 a h
  have h7 : Entails.eval a c874 := derived874 a h
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c215 := h 214 (by decide)
  have h11 : Entails.eval a c703 := derived703 a h
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c54 := h 53 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c1147 := derived1147 a h
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c1909 := derived1909 a h
  have h18 : Entails.eval a c876 := derived876 a h
  have h19 : Entails.eval a c1936 := derived1936 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1939 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1938, some c22, some c1927, some c1926, some c268, some c267, some c1744, some c874, some c158, some c120, some c225, some c160, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1939 : lratChecker f1939 p1939 = .success := by decide +kernel
theorem unsat1939 : Unsatisfiable (PosFin 57) f1939 := by
  apply lratCheckerSound f1939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1939
  · intro a ha; simp [p1939] at ha; subst a; trivial
  · exact checked1939
theorem derived1939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1939 := by
  apply localUnsat_implies_entails f1939 [c1938, c22, c1927, c1926, c268, c267, c1744, c874, c158, c120, c225, c160] c1939 unsat1939 (by rfl) a
  have h0 : Entails.eval a c1938 := derived1938 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c1927 := derived1927 a h
  have h3 : Entails.eval a c1926 := derived1926 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c1744 := derived1744 a h
  have h7 : Entails.eval a c874 := derived874 a h
  have h8 : Entails.eval a c158 := h 157 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c225 := h 224 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1940 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨20, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1939, some c1926, some c1938, some c22, some c982, some c1928, some c1911, some c1890, some c201, some c200, some c1856, some c1147, some c1094, some c876, some c152, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1940 : lratChecker f1940 p1940 = .success := by decide +kernel
theorem unsat1940 : Unsatisfiable (PosFin 57) f1940 := by
  apply lratCheckerSound f1940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1940
  · intro a ha; simp [p1940] at ha; subst a; trivial
  · exact checked1940
theorem derived1940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1940 := by
  apply localUnsat_implies_entails f1940 [c1939, c1926, c1938, c22, c982, c1928, c1911, c1890, c201, c200, c1856, c1147, c1094, c876, c152] c1940 unsat1940 (by rfl) a
  have h0 : Entails.eval a c1939 := derived1939 a h
  have h1 : Entails.eval a c1926 := derived1926 a h
  have h2 : Entails.eval a c1938 := derived1938 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c982 := derived982 a h
  have h5 : Entails.eval a c1928 := derived1928 a h
  have h6 : Entails.eval a c1911 := derived1911 a h
  have h7 : Entails.eval a c1890 := derived1890 a h
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c1856 := derived1856 a h
  have h11 : Entails.eval a c1147 := derived1147 a h
  have h12 : Entails.eval a c1094 := derived1094 a h
  have h13 : Entails.eval a c876 := derived876 a h
  have h14 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1941 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1938, some c22, some c1083, some c1939, some c1926, some c982, some c1927, some c1911, some c1890, some c1940, some c11, some c1933, some c202, some c159, some c1189, some c120, some c131, some c56, some c139, some c239, some c92, some c175, some c1496, some c66, some c59, some c153, some c190, some c343, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1941 : lratChecker f1941 p1941 = .success := by decide +kernel
theorem unsat1941 : Unsatisfiable (PosFin 57) f1941 := by
  apply lratCheckerSound f1941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1941
  · intro a ha; simp [p1941] at ha; subst a; trivial
  · exact checked1941
theorem derived1941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1941 := by
  apply localUnsat_implies_entails f1941 [c1829, c1938, c22, c1083, c1939, c1926, c982, c1927, c1911, c1890, c1940, c11, c1933, c202, c159, c1189, c120, c131, c56, c139, c239, c92, c175, c1496, c66, c59, c153, c190, c343] c1941 unsat1941 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1938 := derived1938 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c1083 := derived1083 a h
  have h4 : Entails.eval a c1939 := derived1939 a h
  have h5 : Entails.eval a c1926 := derived1926 a h
  have h6 : Entails.eval a c982 := derived982 a h
  have h7 : Entails.eval a c1927 := derived1927 a h
  have h8 : Entails.eval a c1911 := derived1911 a h
  have h9 : Entails.eval a c1890 := derived1890 a h
  have h10 : Entails.eval a c1940 := derived1940 a h
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c1933 := derived1933 a h
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c159 := h 158 (by decide)
  have h15 : Entails.eval a c1189 := derived1189 a h
  have h16 : Entails.eval a c120 := h 119 (by decide)
  have h17 : Entails.eval a c131 := h 130 (by decide)
  have h18 : Entails.eval a c56 := h 55 (by decide)
  have h19 : Entails.eval a c139 := h 138 (by decide)
  have h20 : Entails.eval a c239 := h 238 (by decide)
  have h21 : Entails.eval a c92 := h 91 (by decide)
  have h22 : Entails.eval a c175 := h 174 (by decide)
  have h23 : Entails.eval a c1496 := derived1496 a h
  have h24 : Entails.eval a c66 := h 65 (by decide)
  have h25 : Entails.eval a c59 := h 58 (by decide)
  have h26 : Entails.eval a c153 := h 152 (by decide)
  have h27 : Entails.eval a c190 := h 189 (by decide)
  have h28 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1942 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1938, some c1939, some c32, some c22, some c1928, some c1927, some c1926, some c1911, some c1890, some c1083, some c1941, some c1931, some c1916, some c11, some c1932, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1942 : lratChecker f1942 p1942 = .success := by decide +kernel
theorem unsat1942 : Unsatisfiable (PosFin 57) f1942 := by
  apply lratCheckerSound f1942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1942
  · intro a ha; simp [p1942] at ha; subst a; trivial
  · exact checked1942
theorem derived1942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1942 := by
  apply localUnsat_implies_entails f1942 [c1829, c1938, c1939, c32, c22, c1928, c1927, c1926, c1911, c1890, c1083, c1941, c1931, c1916, c11, c1932] c1942 unsat1942 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1938 := derived1938 a h
  have h2 : Entails.eval a c1939 := derived1939 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c1928 := derived1928 a h
  have h6 : Entails.eval a c1927 := derived1927 a h
  have h7 : Entails.eval a c1926 := derived1926 a h
  have h8 : Entails.eval a c1911 := derived1911 a h
  have h9 : Entails.eval a c1890 := derived1890 a h
  have h10 : Entails.eval a c1083 := derived1083 a h
  have h11 : Entails.eval a c1941 := derived1941 a h
  have h12 : Entails.eval a c1931 := derived1931 a h
  have h13 : Entails.eval a c1916 := derived1916 a h
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c1932 := derived1932 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1943 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1942, some c1926, some c1938, some c22, some c982, some c1928, some c1927, some c1911, some c200, some c1857, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1943 : lratChecker f1943 p1943 = .success := by decide +kernel
theorem unsat1943 : Unsatisfiable (PosFin 57) f1943 := by
  apply lratCheckerSound f1943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1943
  · intro a ha; simp [p1943] at ha; subst a; trivial
  · exact checked1943
theorem derived1943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1943 := by
  apply localUnsat_implies_entails f1943 [c1942, c1926, c1938, c22, c982, c1928, c1927, c1911, c200, c1857] c1943 unsat1943 (by rfl) a
  have h0 : Entails.eval a c1942 := derived1942 a h
  have h1 : Entails.eval a c1926 := derived1926 a h
  have h2 : Entails.eval a c1938 := derived1938 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c982 := derived982 a h
  have h5 : Entails.eval a c1928 := derived1928 a h
  have h6 : Entails.eval a c1927 := derived1927 a h
  have h7 : Entails.eval a c1911 := derived1911 a h
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c1857 := derived1857 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1944 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨11, by decide⟩, true), (⟨23, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c56, some c139, some c239, some c92, some c175, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1944 : lratChecker f1944 p1944 = .success := by decide +kernel
theorem unsat1944 : Unsatisfiable (PosFin 57) f1944 := by
  apply lratCheckerSound f1944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1944
  · intro a ha; simp [p1944] at ha; subst a; trivial
  · exact checked1944
theorem derived1944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1944 := by
  apply localUnsat_implies_entails f1944 [c120, c56, c139, c239, c92, c175] c1944 unsat1944 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c239 := h 238 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1945 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1943, some c1942, some c1938, some c1939, some c32, some c22, some c1926, some c202, some c160, some c1933, some c225, some c116, some c274, some c52, some c208, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1945 : lratChecker f1945 p1945 = .success := by decide +kernel
theorem unsat1945 : Unsatisfiable (PosFin 57) f1945 := by
  apply lratCheckerSound f1945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1945
  · intro a ha; simp [p1945] at ha; subst a; trivial
  · exact checked1945
theorem derived1945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1945 := by
  apply localUnsat_implies_entails f1945 [c1943, c1942, c1938, c1939, c32, c22, c1926, c202, c160, c1933, c225, c116, c274, c52, c208] c1945 unsat1945 (by rfl) a
  have h0 : Entails.eval a c1943 := derived1943 a h
  have h1 : Entails.eval a c1942 := derived1942 a h
  have h2 : Entails.eval a c1938 := derived1938 a h
  have h3 : Entails.eval a c1939 := derived1939 a h
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c1926 := derived1926 a h
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c1933 := derived1933 a h
  have h10 : Entails.eval a c225 := h 224 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c274 := h 273 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1946 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨33, by decide⟩, false), (⟨31, by decide⟩, true), (⟨14, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c120, some c1094, some c975, some c981, some c214, some c878, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1946 : lratChecker f1946 p1946 = .success := by decide +kernel
theorem unsat1946 : Unsatisfiable (PosFin 57) f1946 := by
  apply lratCheckerSound f1946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1946
  · intro a ha; simp [p1946] at ha; subst a; trivial
  · exact checked1946
theorem derived1946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1946 := by
  apply localUnsat_implies_entails f1946 [c1829, c120, c1094, c975, c981, c214, c878] c1946 unsat1946 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c1094 := derived1094 a h
  have h3 : Entails.eval a c975 := derived975 a h
  have h4 : Entails.eval a c981 := derived981 a h
  have h5 : Entails.eval a c214 := h 213 (by decide)
  have h6 : Entails.eval a c878 := derived878 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1947 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1938, some c1939, some c32, some c1926, some c22, some c982, some c1928, some c1927, some c1911, some c1890, some c1942, some c1943, some c1945, some c129, some c120, some c131, some c1944, some c1933, some c56, some c1496, some c699, some c66, some c59, some c52, some c1946, some c159, some c70, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1947 : lratChecker f1947 p1947 = .success := by decide +kernel
theorem unsat1947 : Unsatisfiable (PosFin 57) f1947 := by
  apply lratCheckerSound f1947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1947
  · intro a ha; simp [p1947] at ha; subst a; trivial
  · exact checked1947
theorem derived1947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1947 := by
  apply localUnsat_implies_entails f1947 [c1829, c1938, c1939, c32, c1926, c22, c982, c1928, c1927, c1911, c1890, c1942, c1943, c1945, c129, c120, c131, c1944, c1933, c56, c1496, c699, c66, c59, c52, c1946, c159, c70] c1947 unsat1947 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1938 := derived1938 a h
  have h2 : Entails.eval a c1939 := derived1939 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c1926 := derived1926 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c982 := derived982 a h
  have h7 : Entails.eval a c1928 := derived1928 a h
  have h8 : Entails.eval a c1927 := derived1927 a h
  have h9 : Entails.eval a c1911 := derived1911 a h
  have h10 : Entails.eval a c1890 := derived1890 a h
  have h11 : Entails.eval a c1942 := derived1942 a h
  have h12 : Entails.eval a c1943 := derived1943 a h
  have h13 : Entails.eval a c1945 := derived1945 a h
  have h14 : Entails.eval a c129 := h 128 (by decide)
  have h15 : Entails.eval a c120 := h 119 (by decide)
  have h16 : Entails.eval a c131 := h 130 (by decide)
  have h17 : Entails.eval a c1944 := derived1944 a h
  have h18 : Entails.eval a c1933 := derived1933 a h
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c1496 := derived1496 a h
  have h21 : Entails.eval a c699 := derived699 a h
  have h22 : Entails.eval a c66 := h 65 (by decide)
  have h23 : Entails.eval a c59 := h 58 (by decide)
  have h24 : Entails.eval a c52 := h 51 (by decide)
  have h25 : Entails.eval a c1946 := derived1946 a h
  have h26 : Entails.eval a c159 := h 158 (by decide)
  have h27 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1948 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c1926, some c1938, some c1939, some c32, some c1947, some c874, some c119, some c215, some c54, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1948 : lratChecker f1948 p1948 = .success := by decide +kernel
theorem unsat1948 : Unsatisfiable (PosFin 57) f1948 := by
  apply lratCheckerSound f1948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1948
  · intro a ha; simp [p1948] at ha; subst a; trivial
  · exact checked1948
theorem derived1948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1948 := by
  apply localUnsat_implies_entails f1948 [c1890, c1926, c1938, c1939, c32, c1947, c874, c119, c215, c54] c1948 unsat1948 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c1926 := derived1926 a h
  have h2 : Entails.eval a c1938 := derived1938 a h
  have h3 : Entails.eval a c1939 := derived1939 a h
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c1947 := derived1947 a h
  have h6 : Entails.eval a c874 := derived874 a h
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c215 := h 214 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1949 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c819, some c48, some c317, some c30, some c949, some c1436, some c108, some c45, some c1445, some c206, some c198, some c314, some c152, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1949 : lratChecker f1949 p1949 = .success := by decide +kernel
theorem unsat1949 : Unsatisfiable (PosFin 57) f1949 := by
  apply lratCheckerSound f1949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1949
  · intro a ha; simp [p1949] at ha; subst a; trivial
  · exact checked1949
theorem derived1949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1949 := by
  apply localUnsat_implies_entails f1949 [c1829, c819, c48, c317, c30, c949, c1436, c108, c45, c1445, c206, c198, c314, c152] c1949 unsat1949 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c819 := derived819 a h
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c949 := derived949 a h
  have h6 : Entails.eval a c1436 := derived1436 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c1445 := derived1445 a h
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c314 := h 313 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1950 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1948, some c2, some c114, some c819, some c48, some c317, some c125, some c1890, some c753, some c263, some c21, some c1949, some c1901, some c268, some c124, some c1896, some c153, some c220, some c276, some c71, some c349, some c73, some c109, some c46, some c1524, some c699, some c203, some c54, some c136, some c116, some c214, some c88, some c241, some c294, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1950 : lratChecker f1950 p1950 = .success := by decide +kernel
theorem unsat1950 : Unsatisfiable (PosFin 57) f1950 := by
  apply lratCheckerSound f1950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1950
  · intro a ha; simp [p1950] at ha; subst a; trivial
  · exact checked1950
theorem derived1950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1950 := by
  apply localUnsat_implies_entails f1950 [c1829, c1948, c2, c114, c819, c48, c317, c125, c1890, c753, c263, c21, c1949, c1901, c268, c124, c1896, c153, c220, c276, c71, c349, c73, c109, c46, c1524, c699, c203, c54, c136, c116, c214, c88, c241, c294] c1950 unsat1950 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1948 := derived1948 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c819 := derived819 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c1890 := derived1890 a h
  have h9 : Entails.eval a c753 := derived753 a h
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c1949 := derived1949 a h
  have h13 : Entails.eval a c1901 := derived1901 a h
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c1896 := derived1896 a h
  have h17 : Entails.eval a c153 := h 152 (by decide)
  have h18 : Entails.eval a c220 := h 219 (by decide)
  have h19 : Entails.eval a c276 := h 275 (by decide)
  have h20 : Entails.eval a c71 := h 70 (by decide)
  have h21 : Entails.eval a c349 := h 348 (by decide)
  have h22 : Entails.eval a c73 := h 72 (by decide)
  have h23 : Entails.eval a c109 := h 108 (by decide)
  have h24 : Entails.eval a c46 := h 45 (by decide)
  have h25 : Entails.eval a c1524 := derived1524 a h
  have h26 : Entails.eval a c699 := derived699 a h
  have h27 : Entails.eval a c203 := h 202 (by decide)
  have h28 : Entails.eval a c54 := h 53 (by decide)
  have h29 : Entails.eval a c136 := h 135 (by decide)
  have h30 : Entails.eval a c116 := h 115 (by decide)
  have h31 : Entails.eval a c214 := h 213 (by decide)
  have h32 : Entails.eval a c88 := h 87 (by decide)
  have h33 : Entails.eval a c241 := h 240 (by decide)
  have h34 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1951 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1948, some c2, some c114, some c819, some c48, some c125, some c1890, some c949, some c1580, some c1723, some c1949, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1951 : lratChecker f1951 p1951 = .success := by decide +kernel
theorem unsat1951 : Unsatisfiable (PosFin 57) f1951 := by
  apply lratCheckerSound f1951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1951
  · intro a ha; simp [p1951] at ha; subst a; trivial
  · exact checked1951
theorem derived1951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1951 := by
  apply localUnsat_implies_entails f1951 [c1948, c2, c114, c819, c48, c125, c1890, c949, c1580, c1723, c1949] c1951 unsat1951 (by rfl) a
  have h0 : Entails.eval a c1948 := derived1948 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c819 := derived819 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c1890 := derived1890 a h
  have h7 : Entails.eval a c949 := derived949 a h
  have h8 : Entails.eval a c1580 := derived1580 a h
  have h9 : Entails.eval a c1723 := derived1723 a h
  have h10 : Entails.eval a c1949 := derived1949 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1952 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1, some c21, some c156, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1952 : lratChecker f1952 p1952 = .success := by decide +kernel
theorem unsat1952 : Unsatisfiable (PosFin 57) f1952 := by
  apply lratCheckerSound f1952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1952
  · intro a ha; simp [p1952] at ha; subst a; trivial
  · exact checked1952
theorem derived1952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1952 := by
  apply localUnsat_implies_entails f1952 [c1829, c1, c21, c156] c1952 unsat1952 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1953 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨20, by decide⟩, false), (⟨17, by decide⟩, false), (⟨30, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c152, some c876, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1953 : lratChecker f1953 p1953 = .success := by decide +kernel
theorem unsat1953 : Unsatisfiable (PosFin 57) f1953 := by
  apply lratCheckerSound f1953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1953
  · intro a ha; simp [p1953] at ha; subst a; trivial
  · exact checked1953
theorem derived1953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1953 := by
  apply localUnsat_implies_entails f1953 [c1147, c152, c876] c1953 unsat1953 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c876 := derived876 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1954 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨13, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨30, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c28, some c8, some c1952, some c268, some c39, some c37, some c1953, some c198, some c167, some c11, some c1293, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1954 : lratChecker f1954 p1954 = .success := by decide +kernel
theorem unsat1954 : Unsatisfiable (PosFin 57) f1954 := by
  apply lratCheckerSound f1954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1954
  · intro a ha; simp [p1954] at ha; subst a; trivial
  · exact checked1954
theorem derived1954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1954 := by
  apply localUnsat_implies_entails f1954 [c1829, c28, c8, c1952, c268, c39, c37, c1953, c198, c167, c11, c1293] c1954 unsat1954 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c1952 := derived1952 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c1953 := derived1953 a h
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c1293 := derived1293 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1955 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c10, some c1524, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1955 : lratChecker f1955 p1955 = .success := by decide +kernel
theorem unsat1955 : Unsatisfiable (PosFin 57) f1955 := by
  apply lratCheckerSound f1955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1955
  · intro a ha; simp [p1955] at ha; subst a; trivial
  · exact checked1955
theorem derived1955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1955 := by
  apply localUnsat_implies_entails f1955 [c1829, c10, c1524] c1955 unsat1955 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c1524 := derived1524 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1956 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c1948, some c2, some c114, some c819, some c125, some c317, some c48, some c1950, some c28, some c8, some c276, some c1951, some c268, some c124, some c39, some c220, some c112, some c1952, some c1954, some c109, some c46, some c1955, some c699, some c203, some c54, some c116, some c214, some c876, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1956 : lratChecker f1956 p1956 = .success := by decide +kernel
theorem unsat1956 : Unsatisfiable (PosFin 57) f1956 := by
  apply lratCheckerSound f1956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1956
  · intro a ha; simp [p1956] at ha; subst a; trivial
  · exact checked1956
theorem derived1956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1956 := by
  apply localUnsat_implies_entails f1956 [c1890, c1948, c2, c114, c819, c125, c317, c48, c1950, c28, c8, c276, c1951, c268, c124, c39, c220, c112, c1952, c1954, c109, c46, c1955, c699, c203, c54, c116, c214, c876] c1956 unsat1956 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c1948 := derived1948 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c819 := derived819 a h
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c1950 := derived1950 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c276 := h 275 (by decide)
  have h12 : Entails.eval a c1951 := derived1951 a h
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c220 := h 219 (by decide)
  have h17 : Entails.eval a c112 := h 111 (by decide)
  have h18 : Entails.eval a c1952 := derived1952 a h
  have h19 : Entails.eval a c1954 := derived1954 a h
  have h20 : Entails.eval a c109 := h 108 (by decide)
  have h21 : Entails.eval a c46 := h 45 (by decide)
  have h22 : Entails.eval a c1955 := derived1955 a h
  have h23 : Entails.eval a c699 := derived699 a h
  have h24 : Entails.eval a c203 := h 202 (by decide)
  have h25 : Entails.eval a c54 := h 53 (by decide)
  have h26 : Entails.eval a c116 := h 115 (by decide)
  have h27 : Entails.eval a c214 := h 213 (by decide)
  have h28 : Entails.eval a c876 := derived876 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1957 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1956, some c1, some c197, some c29, some c1890, some c1912, some c1037, some c108, some c1137, some c1894, some c110, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1957 : lratChecker f1957 p1957 = .success := by decide +kernel
theorem unsat1957 : Unsatisfiable (PosFin 57) f1957 := by
  apply lratCheckerSound f1957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1957
  · intro a ha; simp [p1957] at ha; subst a; trivial
  · exact checked1957
theorem derived1957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1957 := by
  apply localUnsat_implies_entails f1957 [c1829, c1956, c1, c197, c29, c1890, c1912, c1037, c108, c1137, c1894, c110] c1957 unsat1957 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c197 := h 196 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c1890 := derived1890 a h
  have h6 : Entails.eval a c1912 := derived1912 a h
  have h7 : Entails.eval a c1037 := derived1037 a h
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c1137 := derived1137 a h
  have h10 : Entails.eval a c1894 := derived1894 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1958 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1956, some c263, some c1, some c197, some c1957, some c268, some c117, some c1890, some c835, some c1901, some c1261, some c199, some c21, some c29, some c1922, some c1914, some c220, some c200, some c1915, some c269, some c205, some c48, some c149, some c140, some c1382, some c719, some c316, some c243, some c296, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1958 : lratChecker f1958 p1958 = .success := by decide +kernel
theorem unsat1958 : Unsatisfiable (PosFin 57) f1958 := by
  apply lratCheckerSound f1958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1958
  · intro a ha; simp [p1958] at ha; subst a; trivial
  · exact checked1958
theorem derived1958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1958 := by
  apply localUnsat_implies_entails f1958 [c1829, c1956, c263, c1, c197, c1957, c268, c117, c1890, c835, c1901, c1261, c199, c21, c29, c1922, c1914, c220, c200, c1915, c269, c205, c48, c149, c140, c1382, c719, c316, c243, c296] c1958 unsat1958 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c1957 := derived1957 a h
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c1890 := derived1890 a h
  have h9 : Entails.eval a c835 := derived835 a h
  have h10 : Entails.eval a c1901 := derived1901 a h
  have h11 : Entails.eval a c1261 := derived1261 a h
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c1922 := derived1922 a h
  have h16 : Entails.eval a c1914 := derived1914 a h
  have h17 : Entails.eval a c220 := h 219 (by decide)
  have h18 : Entails.eval a c200 := h 199 (by decide)
  have h19 : Entails.eval a c1915 := derived1915 a h
  have h20 : Entails.eval a c269 := h 268 (by decide)
  have h21 : Entails.eval a c205 := h 204 (by decide)
  have h22 : Entails.eval a c48 := h 47 (by decide)
  have h23 : Entails.eval a c149 := h 148 (by decide)
  have h24 : Entails.eval a c140 := h 139 (by decide)
  have h25 : Entails.eval a c1382 := derived1382 a h
  have h26 : Entails.eval a c719 := derived719 a h
  have h27 : Entails.eval a c316 := h 315 (by decide)
  have h28 : Entails.eval a c243 := h 242 (by decide)
  have h29 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1959 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1956, some c1890, some c263, some c1, some c29, some c197, some c199, some c1261, some c1957, some c268, some c1901, some c5, some c835, some c1958, some c109, some c1918, some c1931, some c149, some c136, some c116, some c88, some c82, some c241, some c179, some c244, some c289, some c296, some c317, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1959 : lratChecker f1959 p1959 = .success := by decide +kernel
theorem unsat1959 : Unsatisfiable (PosFin 57) f1959 := by
  apply lratCheckerSound f1959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1959
  · intro a ha; simp [p1959] at ha; subst a; trivial
  · exact checked1959
theorem derived1959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1959 := by
  apply localUnsat_implies_entails f1959 [c1829, c1956, c1890, c263, c1, c29, c197, c199, c1261, c1957, c268, c1901, c5, c835, c1958, c109, c1918, c1931, c149, c136, c116, c88, c82, c241, c179, c244, c289, c296, c317] c1959 unsat1959 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c1261 := derived1261 a h
  have h9 : Entails.eval a c1957 := derived1957 a h
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c1901 := derived1901 a h
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c835 := derived835 a h
  have h14 : Entails.eval a c1958 := derived1958 a h
  have h15 : Entails.eval a c109 := h 108 (by decide)
  have h16 : Entails.eval a c1918 := derived1918 a h
  have h17 : Entails.eval a c1931 := derived1931 a h
  have h18 : Entails.eval a c149 := h 148 (by decide)
  have h19 : Entails.eval a c136 := h 135 (by decide)
  have h20 : Entails.eval a c116 := h 115 (by decide)
  have h21 : Entails.eval a c88 := h 87 (by decide)
  have h22 : Entails.eval a c82 := h 81 (by decide)
  have h23 : Entails.eval a c241 := h 240 (by decide)
  have h24 : Entails.eval a c179 := h 178 (by decide)
  have h25 : Entails.eval a c244 := h 243 (by decide)
  have h26 : Entails.eval a c289 := h 288 (by decide)
  have h27 : Entails.eval a c296 := h 295 (by decide)
  have h28 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1960 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1147, some c201, some c108, some c1275, some c11, some c110, some c1909, some c26, some c154, some c57, some c245, some c182, some c102, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1960 : lratChecker f1960 p1960 = .success := by decide +kernel
theorem unsat1960 : Unsatisfiable (PosFin 57) f1960 := by
  apply lratCheckerSound f1960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1960
  · intro a ha; simp [p1960] at ha; subst a; trivial
  · exact checked1960
theorem derived1960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1960 := by
  apply localUnsat_implies_entails f1960 [c1829, c1147, c201, c108, c1275, c11, c110, c1909, c26, c154, c57, c245, c182, c102] c1960 unsat1960 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1275 := derived1275 a h
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c1909 := derived1909 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c245 := h 244 (by decide)
  have h12 : Entails.eval a c182 := h 181 (by decide)
  have h13 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1961 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1959, some c1956, some c1890, some c1912, some c1957, some c112, some c262, some c1147, some c1960, some c22, some c159, some c1100, some c222, some c115, some c51, some c273, some c209, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1961 : lratChecker f1961 p1961 = .success := by decide +kernel
theorem unsat1961 : Unsatisfiable (PosFin 57) f1961 := by
  apply lratCheckerSound f1961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1961
  · intro a ha; simp [p1961] at ha; subst a; trivial
  · exact checked1961
theorem derived1961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1961 := by
  apply localUnsat_implies_entails f1961 [c1959, c1956, c1890, c1912, c1957, c112, c262, c1147, c1960, c22, c159, c1100, c222, c115, c51, c273, c209] c1961 unsat1961 (by rfl) a
  have h0 : Entails.eval a c1959 := derived1959 a h
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c1912 := derived1912 a h
  have h4 : Entails.eval a c1957 := derived1957 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c1960 := derived1960 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c1100 := derived1100 a h
  have h12 : Entails.eval a c222 := h 221 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c273 := h 272 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1962 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1901, some c31, some c1922, some c267, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1962 : lratChecker f1962 p1962 = .success := by decide +kernel
theorem unsat1962 : Unsatisfiable (PosFin 57) f1962 := by
  apply lratCheckerSound f1962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1962
  · intro a ha; simp [p1962] at ha; subst a; trivial
  · exact checked1962
theorem derived1962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1962 := by
  apply localUnsat_implies_entails f1962 [c1829, c1901, c31, c1922, c267] c1962 unsat1962 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1901 := derived1901 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c1922 := derived1922 a h
  have h4 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1963 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨6, by decide⟩, true), (⟨34, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1963 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c349, some c350, some c70, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1963 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1963 : lratChecker f1963 p1963 = .success := by decide +kernel
theorem unsat1963 : Unsatisfiable (PosFin 57) f1963 := by
  apply lratCheckerSound f1963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1963
  · intro a ha; simp [p1963] at ha; subst a; trivial
  · exact checked1963
theorem derived1963 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1963 := by
  apply localUnsat_implies_entails f1963 [c349, c350, c70] c1963 unsat1963 (by rfl) a
  have h0 : Entails.eval a c349 := h 348 (by decide)
  have h1 : Entails.eval a c350 := h 349 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1964 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1964 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1961, some c1959, some c1956, some c1890, some c1, some c1848, some c1901, some c197, some c199, some c221, some c1962, some c109, some c1931, some c1678, some c1963, some c224, some c267, some c5, some c835, some c1918, some c209, some c149, some c136, some c317, some c276, some c48, some c237, some c241, some c290, some c71, some c273, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1964 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1964 : lratChecker f1964 p1964 = .success := by decide +kernel
theorem unsat1964 : Unsatisfiable (PosFin 57) f1964 := by
  apply lratCheckerSound f1964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1964
  · intro a ha; simp [p1964] at ha; subst a; trivial
  · exact checked1964
theorem derived1964 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1964 := by
  apply localUnsat_implies_entails f1964 [c1829, c1961, c1959, c1956, c1890, c1, c1848, c1901, c197, c199, c221, c1962, c109, c1931, c1678, c1963, c224, c267, c5, c835, c1918, c209, c149, c136, c317, c276, c48, c237, c241, c290, c71, c273] c1964 unsat1964 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1961 := derived1961 a h
  have h2 : Entails.eval a c1959 := derived1959 a h
  have h3 : Entails.eval a c1956 := derived1956 a h
  have h4 : Entails.eval a c1890 := derived1890 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1848 := derived1848 a h
  have h7 : Entails.eval a c1901 := derived1901 a h
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c1962 := derived1962 a h
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c1931 := derived1931 a h
  have h14 : Entails.eval a c1678 := derived1678 a h
  have h15 : Entails.eval a c1963 := derived1963 a h
  have h16 : Entails.eval a c224 := h 223 (by decide)
  have h17 : Entails.eval a c267 := h 266 (by decide)
  have h18 : Entails.eval a c5 := h 4 (by decide)
  have h19 : Entails.eval a c835 := derived835 a h
  have h20 : Entails.eval a c1918 := derived1918 a h
  have h21 : Entails.eval a c209 := h 208 (by decide)
  have h22 : Entails.eval a c149 := h 148 (by decide)
  have h23 : Entails.eval a c136 := h 135 (by decide)
  have h24 : Entails.eval a c317 := h 316 (by decide)
  have h25 : Entails.eval a c276 := h 275 (by decide)
  have h26 : Entails.eval a c48 := h 47 (by decide)
  have h27 : Entails.eval a c237 := h 236 (by decide)
  have h28 : Entails.eval a c241 := h 240 (by decide)
  have h29 : Entails.eval a c290 := h 289 (by decide)
  have h30 : Entails.eval a c71 := h 70 (by decide)
  have h31 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1965 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨17, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1965 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c1960, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1965 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1965 : lratChecker f1965 p1965 = .success := by decide +kernel
theorem unsat1965 : Unsatisfiable (PosFin 57) f1965 := by
  apply lratCheckerSound f1965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1965
  · intro a ha; simp [p1965] at ha; subst a; trivial
  · exact checked1965
theorem derived1965 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1965 := by
  apply localUnsat_implies_entails f1965 [c112, c1960] c1965 unsat1965 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c1960 := derived1960 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1966 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1966 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1964, some c262, some c1147, some c201, some c202, some c1961, some c1959, some c1956, some c1890, some c11, some c4, some c1275, some c197, some c267, some c110, some c835, some c26, some c209, some c1255, some c48, some c149, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1966 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1966 : lratChecker f1966 p1966 = .success := by decide +kernel
theorem unsat1966 : Unsatisfiable (PosFin 57) f1966 := by
  apply lratCheckerSound f1966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1966
  · intro a ha; simp [p1966] at ha; subst a; trivial
  · exact checked1966
theorem derived1966 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1966 := by
  apply localUnsat_implies_entails f1966 [c1829, c1964, c262, c1147, c201, c202, c1961, c1959, c1956, c1890, c11, c4, c1275, c197, c267, c110, c835, c26, c209, c1255, c48, c149] c1966 unsat1966 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1964 := derived1964 a h
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c1961 := derived1961 a h
  have h7 : Entails.eval a c1959 := derived1959 a h
  have h8 : Entails.eval a c1956 := derived1956 a h
  have h9 : Entails.eval a c1890 := derived1890 a h
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c1275 := derived1275 a h
  have h13 : Entails.eval a c197 := h 196 (by decide)
  have h14 : Entails.eval a c267 := h 266 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c835 := derived835 a h
  have h17 : Entails.eval a c26 := h 25 (by decide)
  have h18 : Entails.eval a c209 := h 208 (by decide)
  have h19 : Entails.eval a c1255 := derived1255 a h
  have h20 : Entails.eval a c48 := h 47 (by decide)
  have h21 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1967 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨3, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1967 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c204, some c197, some c10, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1967 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1967 : lratChecker f1967 p1967 = .success := by decide +kernel
theorem unsat1967 : Unsatisfiable (PosFin 57) f1967 := by
  apply lratCheckerSound f1967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1967
  · intro a ha; simp [p1967] at ha; subst a; trivial
  · exact checked1967
theorem derived1967 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1967 := by
  apply localUnsat_implies_entails f1967 [c1829, c204, c197, c10] c1967 unsat1967 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c197 := h 196 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1968 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1968 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1961, some c1959, some c1956, some c1890, some c1964, some c262, some c1147, some c202, some c201, some c1965, some c1966, some c109, some c26, some c1967, some c1255, some c1254, some c149, some c267, some c835, some c209, some c216, some c317, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1968 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1968 : lratChecker f1968 p1968 = .success := by decide +kernel
theorem unsat1968 : Unsatisfiable (PosFin 57) f1968 := by
  apply lratCheckerSound f1968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1968
  · intro a ha; simp [p1968] at ha; subst a; trivial
  · exact checked1968
theorem derived1968 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1968 := by
  apply localUnsat_implies_entails f1968 [c1961, c1959, c1956, c1890, c1964, c262, c1147, c202, c201, c1965, c1966, c109, c26, c1967, c1255, c1254, c149, c267, c835, c209, c216, c317] c1968 unsat1968 (by rfl) a
  have h0 : Entails.eval a c1961 := derived1961 a h
  have h1 : Entails.eval a c1959 := derived1959 a h
  have h2 : Entails.eval a c1956 := derived1956 a h
  have h3 : Entails.eval a c1890 := derived1890 a h
  have h4 : Entails.eval a c1964 := derived1964 a h
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c1965 := derived1965 a h
  have h10 : Entails.eval a c1966 := derived1966 a h
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c1967 := derived1967 a h
  have h14 : Entails.eval a c1255 := derived1255 a h
  have h15 : Entails.eval a c1254 := derived1254 a h
  have h16 : Entails.eval a c149 := h 148 (by decide)
  have h17 : Entails.eval a c267 := h 266 (by decide)
  have h18 : Entails.eval a c835 := derived835 a h
  have h19 : Entails.eval a c209 := h 208 (by decide)
  have h20 : Entails.eval a c216 := h 215 (by decide)
  have h21 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1969 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1969 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c204, some c911, some c147, some c314, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1969 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1969 : lratChecker f1969 p1969 = .success := by decide +kernel
theorem unsat1969 : Unsatisfiable (PosFin 57) f1969 := by
  apply lratCheckerSound f1969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1969
  · intro a ha; simp [p1969] at ha; subst a; trivial
  · exact checked1969
theorem derived1969 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1969 := by
  apply localUnsat_implies_entails f1969 [c216, c204, c911, c147, c314] c1969 unsat1969 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c911 := derived911 a h
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1970 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨39, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨19, by decide⟩, false), (⟨23, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1970 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1956, some c1890, some c112, some c32, some c267, some c4, some c116, some c1783, some c53, some c216, some c1969, some c1709, some c56, some c140, some c151, some c91, some c92, some c282, some c290, some c61, some c85, some c309, some c307, some c361, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1970 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1970 : lratChecker f1970 p1970 = .success := by decide +kernel
theorem unsat1970 : Unsatisfiable (PosFin 57) f1970 := by
  apply lratCheckerSound f1970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1970
  · intro a ha; simp [p1970] at ha; subst a; trivial
  · exact checked1970
theorem derived1970 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1970 := by
  apply localUnsat_implies_entails f1970 [c1956, c1890, c112, c32, c267, c4, c116, c1783, c53, c216, c1969, c1709, c56, c140, c151, c91, c92, c282, c290, c61, c85, c309, c307, c361] c1970 unsat1970 (by rfl) a
  have h0 : Entails.eval a c1956 := derived1956 a h
  have h1 : Entails.eval a c1890 := derived1890 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c1783 := derived1783 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c1969 := derived1969 a h
  have h11 : Entails.eval a c1709 := derived1709 a h
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c140 := h 139 (by decide)
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c91 := h 90 (by decide)
  have h16 : Entails.eval a c92 := h 91 (by decide)
  have h17 : Entails.eval a c282 := h 281 (by decide)
  have h18 : Entails.eval a c290 := h 289 (by decide)
  have h19 : Entails.eval a c61 := h 60 (by decide)
  have h20 : Entails.eval a c85 := h 84 (by decide)
  have h21 : Entails.eval a c309 := h 308 (by decide)
  have h22 : Entails.eval a c307 := h 306 (by decide)
  have h23 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1971 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨31, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, true), (⟨39, by decide⟩, false), (⟨16, by decide⟩, true), (⟨34, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1971 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c15, some c52, some c157, some c151, some c71, some c284, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1971 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1971 : lratChecker f1971 p1971 = .success := by decide +kernel
theorem unsat1971 : Unsatisfiable (PosFin 57) f1971 := by
  apply lratCheckerSound f1971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1971
  · intro a ha; simp [p1971] at ha; subst a; trivial
  · exact checked1971
theorem derived1971 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1971 := by
  apply localUnsat_implies_entails f1971 [c19, c15, c52, c157, c151, c71, c284] c1971 unsat1971 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1972 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1972 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1956, some c1959, some c1961, some c1968, some c29, some c262, some c22, some c1678, some c1147, some c202, some c201, some c159, some c228, some c1970, some c1967, some c1890, some c267, some c4, some c116, some c53, some c216, some c1971, some c56, some c1236, some c151, some c1232, some c319, some c147, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1972 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1972 : lratChecker f1972 p1972 = .success := by decide +kernel
theorem unsat1972 : Unsatisfiable (PosFin 57) f1972 := by
  apply lratCheckerSound f1972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1972
  · intro a ha; simp [p1972] at ha; subst a; trivial
  · exact checked1972
theorem derived1972 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1972 := by
  apply localUnsat_implies_entails f1972 [c1829, c1956, c1959, c1961, c1968, c29, c262, c22, c1678, c1147, c202, c201, c159, c228, c1970, c1967, c1890, c267, c4, c116, c53, c216, c1971, c56, c1236, c151, c1232, c319, c147] c1972 unsat1972 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c1959 := derived1959 a h
  have h3 : Entails.eval a c1961 := derived1961 a h
  have h4 : Entails.eval a c1968 := derived1968 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1678 := derived1678 a h
  have h9 : Entails.eval a c1147 := derived1147 a h
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c228 := h 227 (by decide)
  have h14 : Entails.eval a c1970 := derived1970 a h
  have h15 : Entails.eval a c1967 := derived1967 a h
  have h16 : Entails.eval a c1890 := derived1890 a h
  have h17 : Entails.eval a c267 := h 266 (by decide)
  have h18 : Entails.eval a c4 := h 3 (by decide)
  have h19 : Entails.eval a c116 := h 115 (by decide)
  have h20 : Entails.eval a c53 := h 52 (by decide)
  have h21 : Entails.eval a c216 := h 215 (by decide)
  have h22 : Entails.eval a c1971 := derived1971 a h
  have h23 : Entails.eval a c56 := h 55 (by decide)
  have h24 : Entails.eval a c1236 := derived1236 a h
  have h25 : Entails.eval a c151 := h 150 (by decide)
  have h26 : Entails.eval a c1232 := derived1232 a h
  have h27 : Entails.eval a c319 := h 318 (by decide)
  have h28 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1973 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1973 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1959, some c1961, some c1968, some c29, some c22, some c262, some c1678, some c1147, some c202, some c201, some c159, some c228, some c1970, some c1972, some c226, some c353, some c346, some c66, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1973 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1973 : lratChecker f1973 p1973 = .success := by decide +kernel
theorem unsat1973 : Unsatisfiable (PosFin 57) f1973 := by
  apply lratCheckerSound f1973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1973
  · intro a ha; simp [p1973] at ha; subst a; trivial
  · exact checked1973
theorem derived1973 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1973 := by
  apply localUnsat_implies_entails f1973 [c1829, c1959, c1961, c1968, c29, c22, c262, c1678, c1147, c202, c201, c159, c228, c1970, c1972, c226, c353, c346, c66] c1973 unsat1973 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1959 := derived1959 a h
  have h2 : Entails.eval a c1961 := derived1961 a h
  have h3 : Entails.eval a c1968 := derived1968 a h
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c1678 := derived1678 a h
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c159 := h 158 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  have h13 : Entails.eval a c1970 := derived1970 a h
  have h14 : Entails.eval a c1972 := derived1972 a h
  have h15 : Entails.eval a c226 := h 225 (by decide)
  have h16 : Entails.eval a c353 := h 352 (by decide)
  have h17 : Entails.eval a c346 := h 345 (by decide)
  have h18 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1974 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1974 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1723, some c261, some c110, some c1909, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1974 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1974 : lratChecker f1974 p1974 = .success := by decide +kernel
theorem unsat1974 : Unsatisfiable (PosFin 57) f1974 := by
  apply lratCheckerSound f1974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1974
  · intro a ha; simp [p1974] at ha; subst a; trivial
  · exact checked1974
theorem derived1974 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1974 := by
  apply localUnsat_implies_entails f1974 [c1723, c261, c110, c1909] c1974 unsat1974 (by rfl) a
  have h0 : Entails.eval a c1723 := derived1723 a h
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c1909 := derived1909 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1975 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1975 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c112, some c8, some c1464, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1975 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1975 : lratChecker f1975 p1975 = .success := by decide +kernel
theorem unsat1975 : Unsatisfiable (PosFin 57) f1975 := by
  apply lratCheckerSound f1975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1975
  · intro a ha; simp [p1975] at ha; subst a; trivial
  · exact checked1975
theorem derived1975 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1975 := by
  apply localUnsat_implies_entails f1975 [c1890, c112, c8, c1464] c1975 unsat1975 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c1464 := derived1464 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1976 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1976 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c51, some c45, some c209, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1976 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1976 : lratChecker f1976 p1976 = .success := by decide +kernel
theorem unsat1976 : Unsatisfiable (PosFin 57) f1976 := by
  apply lratCheckerSound f1976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1976
  · intro a ha; simp [p1976] at ha; subst a; trivial
  · exact checked1976
theorem derived1976 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1976 := by
  apply localUnsat_implies_entails f1976 [c1890, c51, c45, c209] c1976 unsat1976 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1977 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1977 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c112, some c1973, some c1903, some c108, some c1974, some c1976, some c1965, some c1975, some c211, some c854, some c48, some c209, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1977 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1977 : lratChecker f1977 p1977 = .success := by decide +kernel
theorem unsat1977 : Unsatisfiable (PosFin 57) f1977 := by
  apply lratCheckerSound f1977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1977
  · intro a ha; simp [p1977] at ha; subst a; trivial
  · exact checked1977
theorem derived1977 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1977 := by
  apply localUnsat_implies_entails f1977 [c1890, c112, c1973, c1903, c108, c1974, c1976, c1965, c1975, c211, c854, c48, c209] c1977 unsat1977 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c1973 := derived1973 a h
  have h3 : Entails.eval a c1903 := derived1903 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1974 := derived1974 a h
  have h6 : Entails.eval a c1976 := derived1976 a h
  have h7 : Entails.eval a c1965 := derived1965 a h
  have h8 : Entails.eval a c1975 := derived1975 a h
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c854 := derived854 a h
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1978 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1978 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1973, some c1956, some c1890, some c112, some c1903, some c108, some c1974, some c1977, some c1460, some c110, some c1909, some c267, some c4, some c896, some c24, some c18, some c550, some c192, some c245, some c95, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1978 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1978 : lratChecker f1978 p1978 = .success := by decide +kernel
theorem unsat1978 : Unsatisfiable (PosFin 57) f1978 := by
  apply lratCheckerSound f1978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1978
  · intro a ha; simp [p1978] at ha; subst a; trivial
  · exact checked1978
theorem derived1978 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1978 := by
  apply localUnsat_implies_entails f1978 [c1829, c1973, c1956, c1890, c112, c1903, c108, c1974, c1977, c1460, c110, c1909, c267, c4, c896, c24, c18, c550, c192, c245, c95] c1978 unsat1978 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1973 := derived1973 a h
  have h2 : Entails.eval a c1956 := derived1956 a h
  have h3 : Entails.eval a c1890 := derived1890 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1903 := derived1903 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c1974 := derived1974 a h
  have h8 : Entails.eval a c1977 := derived1977 a h
  have h9 : Entails.eval a c1460 := derived1460 a h
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c1909 := derived1909 a h
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c896 := derived896 a h
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c18 := h 17 (by decide)
  have h17 : Entails.eval a c550 := derived550 a h
  have h18 : Entails.eval a c192 := h 191 (by decide)
  have h19 : Entails.eval a c245 := h 244 (by decide)
  have h20 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1979 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1979 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1978, some c1973, some c1956, some c1, some c30, some c199, some c885, some c1393, some c267, some c110, some c129, some c1931, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1979 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1979 : lratChecker f1979 p1979 = .success := by decide +kernel
theorem unsat1979 : Unsatisfiable (PosFin 57) f1979 := by
  apply lratCheckerSound f1979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1979
  · intro a ha; simp [p1979] at ha; subst a; trivial
  · exact checked1979
theorem derived1979 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1979 := by
  apply localUnsat_implies_entails f1979 [c1829, c1978, c1973, c1956, c1, c30, c199, c885, c1393, c267, c110, c129, c1931] c1979 unsat1979 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1978 := derived1978 a h
  have h2 : Entails.eval a c1973 := derived1973 a h
  have h3 : Entails.eval a c1956 := derived1956 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c885 := derived885 a h
  have h8 : Entails.eval a c1393 := derived1393 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c129 := h 128 (by decide)
  have h12 : Entails.eval a c1931 := derived1931 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1980 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1980 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1979, some c1956, some c1978, some c1967, some c1973, some c3, some c23, some c200, some c163, some c157, some c221, some c261, some c885, some c5, some c131, some c11, some c1918, some c202, some c1936, some c136, some c1362, some c88, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1980 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1980 : lratChecker f1980 p1980 = .success := by decide +kernel
theorem unsat1980 : Unsatisfiable (PosFin 57) f1980 := by
  apply lratCheckerSound f1980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1980
  · intro a ha; simp [p1980] at ha; subst a; trivial
  · exact checked1980
theorem derived1980 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1980 := by
  apply localUnsat_implies_entails f1980 [c1829, c1979, c1956, c1978, c1967, c1973, c3, c23, c200, c163, c157, c221, c261, c885, c5, c131, c11, c1918, c202, c1936, c136, c1362, c88] c1980 unsat1980 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1979 := derived1979 a h
  have h2 : Entails.eval a c1956 := derived1956 a h
  have h3 : Entails.eval a c1978 := derived1978 a h
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c1973 := derived1973 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c261 := h 260 (by decide)
  have h13 : Entails.eval a c885 := derived885 a h
  have h14 : Entails.eval a c5 := h 4 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c1918 := derived1918 a h
  have h18 : Entails.eval a c202 := h 201 (by decide)
  have h19 : Entails.eval a c1936 := derived1936 a h
  have h20 : Entails.eval a c136 := h 135 (by decide)
  have h21 : Entails.eval a c1362 := derived1362 a h
  have h22 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1981 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1981 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1979, some c1956, some c1978, some c1967, some c1973, some c885, some c5, some c117, some c131, some c10, some c202, some c200, some c11, some c52, some c1936, some c136, some c1362, some c88, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1981 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1981 : lratChecker f1981 p1981 = .success := by decide +kernel
theorem unsat1981 : Unsatisfiable (PosFin 57) f1981 := by
  apply lratCheckerSound f1981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1981
  · intro a ha; simp [p1981] at ha; subst a; trivial
  · exact checked1981
theorem derived1981 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1981 := by
  apply localUnsat_implies_entails f1981 [c1829, c1979, c1956, c1978, c1967, c1973, c885, c5, c117, c131, c10, c202, c200, c11, c52, c1936, c136, c1362, c88] c1981 unsat1981 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1979 := derived1979 a h
  have h2 : Entails.eval a c1956 := derived1956 a h
  have h3 : Entails.eval a c1978 := derived1978 a h
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c1973 := derived1973 a h
  have h6 : Entails.eval a c885 := derived885 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c200 := h 199 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c52 := h 51 (by decide)
  have h15 : Entails.eval a c1936 := derived1936 a h
  have h16 : Entails.eval a c136 := h 135 (by decide)
  have h17 : Entails.eval a c1362 := derived1362 a h
  have h18 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1982 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1982 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1973, some c1956, some c1978, some c1967, some c1979, some c1980, some c1981, some c267, some c1211, some c896, some c1931, some c18, some c4, some c129, some c116, some c199, some c52, some c137, some c88, some c229, some c171, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1982 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1982 : lratChecker f1982 p1982 = .success := by decide +kernel
theorem unsat1982 : Unsatisfiable (PosFin 57) f1982 := by
  apply lratCheckerSound f1982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1982
  · intro a ha; simp [p1982] at ha; subst a; trivial
  · exact checked1982
theorem derived1982 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1982 := by
  apply localUnsat_implies_entails f1982 [c1973, c1956, c1978, c1967, c1979, c1980, c1981, c267, c1211, c896, c1931, c18, c4, c129, c116, c199, c52, c137, c88, c229, c171] c1982 unsat1982 (by rfl) a
  have h0 : Entails.eval a c1973 := derived1973 a h
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c1978 := derived1978 a h
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c1979 := derived1979 a h
  have h5 : Entails.eval a c1980 := derived1980 a h
  have h6 : Entails.eval a c1981 := derived1981 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c1211 := derived1211 a h
  have h9 : Entails.eval a c896 := derived896 a h
  have h10 : Entails.eval a c1931 := derived1931 a h
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c129 := h 128 (by decide)
  have h14 : Entails.eval a c116 := h 115 (by decide)
  have h15 : Entails.eval a c199 := h 198 (by decide)
  have h16 : Entails.eval a c52 := h 51 (by decide)
  have h17 : Entails.eval a c137 := h 136 (by decide)
  have h18 : Entails.eval a c88 := h 87 (by decide)
  have h19 : Entails.eval a c229 := h 228 (by decide)
  have h20 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1983 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1983 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1982, some c22, some c1973, some c1890, some c120, some c127, some c854, some c157, some c209, some c223, some c276, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1983 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1983 : lratChecker f1983 p1983 = .success := by decide +kernel
theorem unsat1983 : Unsatisfiable (PosFin 57) f1983 := by
  apply lratCheckerSound f1983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1983
  · intro a ha; simp [p1983] at ha; subst a; trivial
  · exact checked1983
theorem derived1983 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1983 := by
  apply localUnsat_implies_entails f1983 [c1982, c22, c1973, c1890, c120, c127, c854, c157, c209, c223, c276] c1983 unsat1983 (by rfl) a
  have h0 : Entails.eval a c1982 := derived1982 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c1973 := derived1973 a h
  have h3 : Entails.eval a c1890 := derived1890 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c854 := derived854 a h
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c223 := h 222 (by decide)
  have h10 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1984 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1984 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1982, some c29, some c1890, some c112, some c32, some c261, some c22, some c1973, some c1983, some c1040, some c160, some c115, some c223, some c51, some c273, some c209, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1984 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1984 : lratChecker f1984 p1984 = .success := by decide +kernel
theorem unsat1984 : Unsatisfiable (PosFin 57) f1984 := by
  apply lratCheckerSound f1984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1984
  · intro a ha; simp [p1984] at ha; subst a; trivial
  · exact checked1984
theorem derived1984 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1984 := by
  apply localUnsat_implies_entails f1984 [c1829, c1982, c29, c1890, c112, c32, c261, c22, c1973, c1983, c1040, c160, c115, c223, c51, c273, c209] c1984 unsat1984 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1982 := derived1982 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c1890 := derived1890 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1973 := derived1973 a h
  have h9 : Entails.eval a c1983 := derived1983 a h
  have h10 : Entails.eval a c1040 := derived1040 a h
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c223 := h 222 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c273 := h 272 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1985 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨27, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨34, by decide⟩, false), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1985 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c896, some c1147, some c200, some c158, some c146, some c224, some c225, some c973, some c160, some c348, some c1094, some c57, some c62, some c246, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1985 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1985 : lratChecker f1985 p1985 = .success := by decide +kernel
theorem unsat1985 : Unsatisfiable (PosFin 57) f1985 := by
  apply lratCheckerSound f1985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1985
  · intro a ha; simp [p1985] at ha; subst a; trivial
  · exact checked1985
theorem derived1985 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1985 := by
  apply localUnsat_implies_entails f1985 [c1829, c896, c1147, c200, c158, c146, c224, c225, c973, c160, c348, c1094, c57, c62, c246] c1985 unsat1985 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c896 := derived896 a h
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c224 := h 223 (by decide)
  have h7 : Entails.eval a c225 := h 224 (by decide)
  have h8 : Entails.eval a c973 := derived973 a h
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c1094 := derived1094 a h
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1986 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1986 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1973, some c1982, some c22, some c982, some c29, some c1956, some c1890, some c112, some c32, some c261, some c1984, some c267, some c896, some c1083, some c1147, some c1783, some c1985, some c129, some c116, some c199, some c160, some c980, some c225, some c18, some c349, some c350, some c274, some c204, some c62, some c74, some c209, some c135, some c146, some c142, some c246, some c308, some c166, some c280, some c854, some c87, some c238, some c85, some c1404, some c57, some c93, some c356, some c361, some c1402, some c371, some c188, some c194, some c340, some c409, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1986 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54]]
theorem checked1986 : lratChecker f1986 p1986 = .success := by decide +kernel
theorem unsat1986 : Unsatisfiable (PosFin 57) f1986 := by
  apply lratCheckerSound f1986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1986
  · intro a ha; simp [p1986] at ha; subst a; trivial
  · exact checked1986
theorem derived1986 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1986 := by
  apply localUnsat_implies_entails f1986 [c1829, c1973, c1982, c22, c982, c29, c1956, c1890, c112, c32, c261, c1984, c267, c896, c1083, c1147, c1783, c1985, c129, c116, c199, c160, c980, c225, c18, c349, c350, c274, c204, c62, c74, c209, c135, c146, c142, c246, c308, c166, c280, c854, c87, c238, c85, c1404, c57, c93, c356, c361, c1402, c371, c188, c194, c340, c409] c1986 unsat1986 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1973 := derived1973 a h
  have h2 : Entails.eval a c1982 := derived1982 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c982 := derived982 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c1956 := derived1956 a h
  have h7 : Entails.eval a c1890 := derived1890 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c1984 := derived1984 a h
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c896 := derived896 a h
  have h14 : Entails.eval a c1083 := derived1083 a h
  have h15 : Entails.eval a c1147 := derived1147 a h
  have h16 : Entails.eval a c1783 := derived1783 a h
  have h17 : Entails.eval a c1985 := derived1985 a h
  have h18 : Entails.eval a c129 := h 128 (by decide)
  have h19 : Entails.eval a c116 := h 115 (by decide)
  have h20 : Entails.eval a c199 := h 198 (by decide)
  have h21 : Entails.eval a c160 := h 159 (by decide)
  have h22 : Entails.eval a c980 := derived980 a h
  have h23 : Entails.eval a c225 := h 224 (by decide)
  have h24 : Entails.eval a c18 := h 17 (by decide)
  have h25 : Entails.eval a c349 := h 348 (by decide)
  have h26 : Entails.eval a c350 := h 349 (by decide)
  have h27 : Entails.eval a c274 := h 273 (by decide)
  have h28 : Entails.eval a c204 := h 203 (by decide)
  have h29 : Entails.eval a c62 := h 61 (by decide)
  have h30 : Entails.eval a c74 := h 73 (by decide)
  have h31 : Entails.eval a c209 := h 208 (by decide)
  have h32 : Entails.eval a c135 := h 134 (by decide)
  have h33 : Entails.eval a c146 := h 145 (by decide)
  have h34 : Entails.eval a c142 := h 141 (by decide)
  have h35 : Entails.eval a c246 := h 245 (by decide)
  have h36 : Entails.eval a c308 := h 307 (by decide)
  have h37 : Entails.eval a c166 := h 165 (by decide)
  have h38 : Entails.eval a c280 := h 279 (by decide)
  have h39 : Entails.eval a c854 := derived854 a h
  have h40 : Entails.eval a c87 := h 86 (by decide)
  have h41 : Entails.eval a c238 := h 237 (by decide)
  have h42 : Entails.eval a c85 := h 84 (by decide)
  have h43 : Entails.eval a c1404 := derived1404 a h
  have h44 : Entails.eval a c57 := h 56 (by decide)
  have h45 : Entails.eval a c93 := h 92 (by decide)
  have h46 : Entails.eval a c356 := h 355 (by decide)
  have h47 : Entails.eval a c361 := h 360 (by decide)
  have h48 : Entails.eval a c1402 := derived1402 a h
  have h49 : Entails.eval a c371 := h 370 (by decide)
  have h50 : Entails.eval a c188 := h 187 (by decide)
  have h51 : Entails.eval a c194 := h 193 (by decide)
  have h52 : Entails.eval a c340 := h 339 (by decide)
  have h53 : Entails.eval a c409 := h 408 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1987 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨34, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1987 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c23, some c157, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1987 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1987 : lratChecker f1987 p1987 = .success := by decide +kernel
theorem unsat1987 : Unsatisfiable (PosFin 57) f1987 := by
  apply lratCheckerSound f1987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1987
  · intro a ha; simp [p1987] at ha; subst a; trivial
  · exact checked1987
theorem derived1987 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1987 := by
  apply localUnsat_implies_entails f1987 [c3, c23, c157] c1987 unsat1987 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1988 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1988 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1956, some c1986, some c1967, some c1982, some c22, some c1973, some c885, some c32, some c117, some c131, some c10, some c868, some c200, some c157, some c11, some c66, some c52, some c269, some c143, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1988 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1988 : lratChecker f1988 p1988 = .success := by decide +kernel
theorem unsat1988 : Unsatisfiable (PosFin 57) f1988 := by
  apply lratCheckerSound f1988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1988
  · intro a ha; simp [p1988] at ha; subst a; trivial
  · exact checked1988
theorem derived1988 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1988 := by
  apply localUnsat_implies_entails f1988 [c1829, c1956, c1986, c1967, c1982, c22, c1973, c885, c32, c117, c131, c10, c868, c200, c157, c11, c66, c52, c269, c143] c1988 unsat1988 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c1986 := derived1986 a h
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c1982 := derived1982 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c1973 := derived1973 a h
  have h7 : Entails.eval a c885 := derived885 a h
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c131 := h 130 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c868 := derived868 a h
  have h13 : Entails.eval a c200 := h 199 (by decide)
  have h14 : Entails.eval a c157 := h 156 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c66 := h 65 (by decide)
  have h17 : Entails.eval a c52 := h 51 (by decide)
  have h18 : Entails.eval a c269 := h 268 (by decide)
  have h19 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1989 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨3, by decide⟩, true), (⟨34, by decide⟩, false), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1989 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c896, some c1147, some c1083, some c129, some c199, some c160, some c980, some c225, some c1963, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1989 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1989 : lratChecker f1989 p1989 = .success := by decide +kernel
theorem unsat1989 : Unsatisfiable (PosFin 57) f1989 := by
  apply lratCheckerSound f1989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1989
  · intro a ha; simp [p1989] at ha; subst a; trivial
  · exact checked1989
theorem derived1989 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1989 := by
  apply localUnsat_implies_entails f1989 [c896, c1147, c1083, c129, c199, c160, c980, c225, c1963] c1989 unsat1989 (by rfl) a
  have h0 : Entails.eval a c896 := derived896 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c1083 := derived1083 a h
  have h3 : Entails.eval a c129 := h 128 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c980 := derived980 a h
  have h7 : Entails.eval a c225 := h 224 (by decide)
  have h8 : Entails.eval a c1963 := derived1963 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1990 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1990 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1956, some c1890, some c1973, some c1982, some c29, some c22, some c1986, some c1987, some c1988, some c261, some c267, some c1989, some c200, some c158, some c10, some c225, some c199, some c120, some c854, some c276, some c209, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1990 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1990 : lratChecker f1990 p1990 = .success := by decide +kernel
theorem unsat1990 : Unsatisfiable (PosFin 57) f1990 := by
  apply lratCheckerSound f1990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1990
  · intro a ha; simp [p1990] at ha; subst a; trivial
  · exact checked1990
theorem derived1990 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1990 := by
  apply localUnsat_implies_entails f1990 [c1829, c1956, c1890, c1973, c1982, c29, c22, c1986, c1987, c1988, c261, c267, c1989, c200, c158, c10, c225, c199, c120, c854, c276, c209] c1990 unsat1990 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c1973 := derived1973 a h
  have h4 : Entails.eval a c1982 := derived1982 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c1986 := derived1986 a h
  have h8 : Entails.eval a c1987 := derived1987 a h
  have h9 : Entails.eval a c1988 := derived1988 a h
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c1989 := derived1989 a h
  have h13 : Entails.eval a c200 := h 199 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c225 := h 224 (by decide)
  have h17 : Entails.eval a c199 := h 198 (by decide)
  have h18 : Entails.eval a c120 := h 119 (by decide)
  have h19 : Entails.eval a c854 := derived854 a h
  have h20 : Entails.eval a c276 := h 275 (by decide)
  have h21 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1991 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1991 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1990, some c2, some c108, some c1890, some c112, some c1956, some c1, some c1894, some c1137, some c110, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1991 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1991 : lratChecker f1991 p1991 = .success := by decide +kernel
theorem unsat1991 : Unsatisfiable (PosFin 57) f1991 := by
  apply lratCheckerSound f1991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1991
  · intro a ha; simp [p1991] at ha; subst a; trivial
  · exact checked1991
theorem derived1991 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1991 := by
  apply localUnsat_implies_entails f1991 [c1829, c1990, c2, c108, c1890, c112, c1956, c1, c1894, c1137, c110] c1991 unsat1991 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1990 := derived1990 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1890 := derived1890 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1956 := derived1956 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c1894 := derived1894 a h
  have h9 : Entails.eval a c1137 := derived1137 a h
  have h10 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1992 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1992 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1990, some c2, some c114, some c45, some c108, some c1956, some c1890, some c115, some c204, some c1991, some c262, some c1147, some c210, some c316, some c47, some c317, some c820, some c149, some c11, some c199, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1992 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1992 : lratChecker f1992 p1992 = .success := by decide +kernel
theorem unsat1992 : Unsatisfiable (PosFin 57) f1992 := by
  apply lratCheckerSound f1992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1992
  · intro a ha; simp [p1992] at ha; subst a; trivial
  · exact checked1992
theorem derived1992 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1992 := by
  apply localUnsat_implies_entails f1992 [c1829, c1990, c2, c114, c45, c108, c1956, c1890, c115, c204, c1991, c262, c1147, c210, c316, c47, c317, c820, c149, c11, c199] c1992 unsat1992 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1990 := derived1990 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1956 := derived1956 a h
  have h7 : Entails.eval a c1890 := derived1890 a h
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c1991 := derived1991 a h
  have h11 : Entails.eval a c262 := h 261 (by decide)
  have h12 : Entails.eval a c1147 := derived1147 a h
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c47 := h 46 (by decide)
  have h16 : Entails.eval a c317 := h 316 (by decide)
  have h17 : Entails.eval a c820 := derived820 a h
  have h18 : Entails.eval a c149 := h 148 (by decide)
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1993 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨42, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, false), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1993 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c135, some c262, some c1990, some c114, some c142, some c169, some c314, some c312, some c232, some c1545, some c295, some c316, some c238, some c214, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1993 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1993 : lratChecker f1993 p1993 = .success := by decide +kernel
theorem unsat1993 : Unsatisfiable (PosFin 57) f1993 := by
  apply lratCheckerSound f1993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1993
  · intro a ha; simp [p1993] at ha; subst a; trivial
  · exact checked1993
theorem derived1993 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1993 := by
  apply localUnsat_implies_entails f1993 [c135, c262, c1990, c114, c142, c169, c314, c312, c232, c1545, c295, c316, c238, c214] c1993 unsat1993 (by rfl) a
  have h0 : Entails.eval a c135 := h 134 (by decide)
  have h1 : Entails.eval a c262 := h 261 (by decide)
  have h2 : Entails.eval a c1990 := derived1990 a h
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c232 := h 231 (by decide)
  have h9 : Entails.eval a c1545 := derived1545 a h
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c316 := h 315 (by decide)
  have h12 : Entails.eval a c238 := h 237 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1994 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1994 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1990, some c114, some c1890, some c112, some c2, some c1992, some c1901, some c1461, some c45, some c1956, some c135, some c81, some c1993, some c199, some c1137, some c1336, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1994 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1994 : lratChecker f1994 p1994 = .success := by decide +kernel
theorem unsat1994 : Unsatisfiable (PosFin 57) f1994 := by
  apply lratCheckerSound f1994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1994
  · intro a ha; simp [p1994] at ha; subst a; trivial
  · exact checked1994
theorem derived1994 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1994 := by
  apply localUnsat_implies_entails f1994 [c1990, c114, c1890, c112, c2, c1992, c1901, c1461, c45, c1956, c135, c81, c1993, c199, c1137, c1336] c1994 unsat1994 (by rfl) a
  have h0 : Entails.eval a c1990 := derived1990 a h
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1992 := derived1992 a h
  have h6 : Entails.eval a c1901 := derived1901 a h
  have h7 : Entails.eval a c1461 := derived1461 a h
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c1956 := derived1956 a h
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c1993 := derived1993 a h
  have h13 : Entails.eval a c199 := h 198 (by decide)
  have h14 : Entails.eval a c1137 := derived1137 a h
  have h15 : Entails.eval a c1336 := derived1336 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1995 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1995 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1990, some c2, some c108, some c1890, some c112, some c114, some c1956, some c1992, some c1901, some c262, some c1461, some c1147, some c1994, some c204, some c850, some c124, some c4, some c267, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1995 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1995 : lratChecker f1995 p1995 = .success := by decide +kernel
theorem unsat1995 : Unsatisfiable (PosFin 57) f1995 := by
  apply lratCheckerSound f1995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1995
  · intro a ha; simp [p1995] at ha; subst a; trivial
  · exact checked1995
theorem derived1995 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1995 := by
  apply localUnsat_implies_entails f1995 [c1990, c2, c108, c1890, c112, c114, c1956, c1992, c1901, c262, c1461, c1147, c1994, c204, c850, c124, c4, c267] c1995 unsat1995 (by rfl) a
  have h0 : Entails.eval a c1990 := derived1990 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1890 := derived1890 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c1956 := derived1956 a h
  have h7 : Entails.eval a c1992 := derived1992 a h
  have h8 : Entails.eval a c1901 := derived1901 a h
  have h9 : Entails.eval a c262 := h 261 (by decide)
  have h10 : Entails.eval a c1461 := derived1461 a h
  have h11 : Entails.eval a c1147 := derived1147 a h
  have h12 : Entails.eval a c1994 := derived1994 a h
  have h13 : Entails.eval a c204 := h 203 (by decide)
  have h14 : Entails.eval a c850 := derived850 a h
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c4 := h 3 (by decide)
  have h17 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1996 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1996 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1995, some c1990, some c2, some c114, some c45, some c1890, some c112, some c1956, some c211, some c115, some c48, some c317, some c204, some c8, some c210, some c1991, some c1464, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1996 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1996 : lratChecker f1996 p1996 = .success := by decide +kernel
theorem unsat1996 : Unsatisfiable (PosFin 57) f1996 := by
  apply lratCheckerSound f1996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1996
  · intro a ha; simp [p1996] at ha; subst a; trivial
  · exact checked1996
theorem derived1996 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1996 := by
  apply localUnsat_implies_entails f1996 [c1995, c1990, c2, c114, c45, c1890, c112, c1956, c211, c115, c48, c317, c204, c8, c210, c1991, c1464] c1996 unsat1996 (by rfl) a
  have h0 : Entails.eval a c1995 := derived1995 a h
  have h1 : Entails.eval a c1990 := derived1990 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c1890 := derived1890 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c1956 := derived1956 a h
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c48 := h 47 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c210 := h 209 (by decide)
  have h15 : Entails.eval a c1991 := derived1991 a h
  have h16 : Entails.eval a c1464 := derived1464 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1997 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1997 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1990, some c114, some c1995, some c2, some c108, some c1890, some c112, some c1996, some c1460, some c48, some c1901, some c110, some c1909, some c267, some c213, some c316, some c4, some c1974, some c45, some c1956, some c135, some c146, some c81, some c238, some c1229, some c172, some c74, some c1021, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1997 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1997 : lratChecker f1997 p1997 = .success := by decide +kernel
theorem unsat1997 : Unsatisfiable (PosFin 57) f1997 := by
  apply lratCheckerSound f1997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1997
  · intro a ha; simp [p1997] at ha; subst a; trivial
  · exact checked1997
theorem derived1997 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1997 := by
  apply localUnsat_implies_entails f1997 [c1990, c114, c1995, c2, c108, c1890, c112, c1996, c1460, c48, c1901, c110, c1909, c267, c213, c316, c4, c1974, c45, c1956, c135, c146, c81, c238, c1229, c172, c74, c1021] c1997 unsat1997 (by rfl) a
  have h0 : Entails.eval a c1990 := derived1990 a h
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c1995 := derived1995 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1890 := derived1890 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c1996 := derived1996 a h
  have h8 : Entails.eval a c1460 := derived1460 a h
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c1901 := derived1901 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c1909 := derived1909 a h
  have h13 : Entails.eval a c267 := h 266 (by decide)
  have h14 : Entails.eval a c213 := h 212 (by decide)
  have h15 : Entails.eval a c316 := h 315 (by decide)
  have h16 : Entails.eval a c4 := h 3 (by decide)
  have h17 : Entails.eval a c1974 := derived1974 a h
  have h18 : Entails.eval a c45 := h 44 (by decide)
  have h19 : Entails.eval a c1956 := derived1956 a h
  have h20 : Entails.eval a c135 := h 134 (by decide)
  have h21 : Entails.eval a c146 := h 145 (by decide)
  have h22 : Entails.eval a c81 := h 80 (by decide)
  have h23 : Entails.eval a c238 := h 237 (by decide)
  have h24 : Entails.eval a c1229 := derived1229 a h
  have h25 : Entails.eval a c172 := h 171 (by decide)
  have h26 : Entails.eval a c74 := h 73 (by decide)
  have h27 : Entails.eval a c1021 := derived1021 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1998 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1998 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1990, some c2, some c1956, some c1890, some c112, some c108, some c1995, some c1996, some c1901, some c1460, some c110, some c1909, some c267, some c4, some c1997, some c204, some c18, some c1229, some c26, some c62, some c193, some c246, some c95, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1998 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1998 : lratChecker f1998 p1998 = .success := by decide +kernel
theorem unsat1998 : Unsatisfiable (PosFin 57) f1998 := by
  apply lratCheckerSound f1998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1998
  · intro a ha; simp [p1998] at ha; subst a; trivial
  · exact checked1998
theorem derived1998 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1998 := by
  apply localUnsat_implies_entails f1998 [c1829, c1990, c2, c1956, c1890, c112, c108, c1995, c1996, c1901, c1460, c110, c1909, c267, c4, c1997, c204, c18, c1229, c26, c62, c193, c246, c95] c1998 unsat1998 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1990 := derived1990 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1956 := derived1956 a h
  have h4 : Entails.eval a c1890 := derived1890 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c1995 := derived1995 a h
  have h8 : Entails.eval a c1996 := derived1996 a h
  have h9 : Entails.eval a c1901 := derived1901 a h
  have h10 : Entails.eval a c1460 := derived1460 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c1909 := derived1909 a h
  have h13 : Entails.eval a c267 := h 266 (by decide)
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c1997 := derived1997 a h
  have h16 : Entails.eval a c204 := h 203 (by decide)
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c1229 := derived1229 a h
  have h19 : Entails.eval a c26 := h 25 (by decide)
  have h20 : Entails.eval a c62 := h 61 (by decide)
  have h21 : Entails.eval a c193 := h 192 (by decide)
  have h22 : Entails.eval a c246 := h 245 (by decide)
  have h23 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1999 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1999 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1998, some c1990, some c114, some c2, some c1956, some c30, some c3, some c23, some c263, some c262, some c163, some c34, some c221, some c47, some c273, some c210, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1999 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1999 : lratChecker f1999 p1999 = .success := by decide +kernel
theorem unsat1999 : Unsatisfiable (PosFin 57) f1999 := by
  apply lratCheckerSound f1999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1999
  · intro a ha; simp [p1999] at ha; subst a; trivial
  · exact checked1999
theorem derived1999 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1999 := by
  apply localUnsat_implies_entails f1999 [c1829, c1998, c1990, c114, c2, c1956, c30, c3, c23, c263, c262, c163, c34, c221, c47, c273, c210] c1999 unsat1999 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1998 := derived1998 a h
  have h2 : Entails.eval a c1990 := derived1990 a h
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1956 := derived1956 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c262 := h 261 (by decide)
  have h11 : Entails.eval a c163 := h 162 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c221 := h 220 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c273 := h 272 (by decide)
  have h16 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2000 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2000 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1990, some c1956, some c1998, some c1967, some c124, some c267, some c268, some c2, some c1848, some c31, some c221, some c224, some c109, some c1963, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p2000 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2000 : lratChecker f2000 p2000 = .success := by decide +kernel
theorem unsat2000 : Unsatisfiable (PosFin 57) f2000 := by
  apply lratCheckerSound f2000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2000
  · intro a ha; simp [p2000] at ha; subst a; trivial
  · exact checked2000
theorem derived2000 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2000 := by
  apply localUnsat_implies_entails f2000 [c1829, c1990, c1956, c1998, c1967, c124, c267, c268, c2, c1848, c31, c221, c224, c109, c1963] c2000 unsat2000 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1990 := derived1990 a h
  have h2 : Entails.eval a c1956 := derived1956 a h
  have h3 : Entails.eval a c1998 := derived1998 a h
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c1848 := derived1848 a h
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c224 := h 223 (by decide)
  have h13 : Entails.eval a c109 := h 108 (by decide)
  have h14 : Entails.eval a c1963 := derived1963 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2001 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2001 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1990, some c1956, some c1998, some c1967, some c124, some c2, some c1999, some c268, some c267, some c2000, some c262, some c1147, some c1254, some c26, some c109, some c110, some c4, some c24, some c844, some c10, some c15, some c199, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p2001 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2001 : lratChecker f2001 p2001 = .success := by decide +kernel
theorem unsat2001 : Unsatisfiable (PosFin 57) f2001 := by
  apply lratCheckerSound f2001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2001
  · intro a ha; simp [p2001] at ha; subst a; trivial
  · exact checked2001
theorem derived2001 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2001 := by
  apply localUnsat_implies_entails f2001 [c1829, c1990, c1956, c1998, c1967, c124, c2, c1999, c268, c267, c2000, c262, c1147, c1254, c26, c109, c110, c4, c24, c844, c10, c15, c199] c2001 unsat2001 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1990 := derived1990 a h
  have h2 : Entails.eval a c1956 := derived1956 a h
  have h3 : Entails.eval a c1998 := derived1998 a h
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c1999 := derived1999 a h
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c2000 := derived2000 a h
  have h11 : Entails.eval a c262 := h 261 (by decide)
  have h12 : Entails.eval a c1147 := derived1147 a h
  have h13 : Entails.eval a c1254 := derived1254 a h
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c109 := h 108 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c844 := derived844 a h
  have h20 : Entails.eval a c10 := h 9 (by decide)
  have h21 : Entails.eval a c15 := h 14 (by decide)
  have h22 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2002 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2002 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2001, some c1990, some c1956, some c1998, some c1967, some c124, some c35, some c30, some c3, some c23, some c261, some c163, some c583, some c221, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p2002 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2002 : lratChecker f2002 p2002 = .success := by decide +kernel
theorem unsat2002 : Unsatisfiable (PosFin 57) f2002 := by
  apply lratCheckerSound f2002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2002
  · intro a ha; simp [p2002] at ha; subst a; trivial
  · exact checked2002
theorem derived2002 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2002 := by
  apply localUnsat_implies_entails f2002 [c1829, c2001, c1990, c1956, c1998, c1967, c124, c35, c30, c3, c23, c261, c163, c583, c221] c2002 unsat2002 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2001 := derived2001 a h
  have h2 : Entails.eval a c1990 := derived1990 a h
  have h3 : Entails.eval a c1956 := derived1956 a h
  have h4 : Entails.eval a c1998 := derived1998 a h
  have h5 : Entails.eval a c1967 := derived1967 a h
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c583 := derived583 a h
  have h14 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2003 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2003 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1990, some c2, some c2001, some c1956, some c1998, some c1967, some c124, some c2002, some c267, some c1211, some c114, some c10, some c1524, some c199, some c48, some c120, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p2003 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2003 : lratChecker f2003 p2003 = .success := by decide +kernel
theorem unsat2003 : Unsatisfiable (PosFin 57) f2003 := by
  apply lratCheckerSound f2003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2003
  · intro a ha; simp [p2003] at ha; subst a; trivial
  · exact checked2003
theorem derived2003 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2003 := by
  apply localUnsat_implies_entails f2003 [c1829, c1990, c2, c2001, c1956, c1998, c1967, c124, c2002, c267, c1211, c114, c10, c1524, c199, c48, c120] c2003 unsat2003 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1990 := derived1990 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c2001 := derived2001 a h
  have h4 : Entails.eval a c1956 := derived1956 a h
  have h5 : Entails.eval a c1998 := derived1998 a h
  have h6 : Entails.eval a c1967 := derived1967 a h
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c2002 := derived2002 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c1211 := derived1211 a h
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c1524 := derived1524 a h
  have h14 : Entails.eval a c199 := h 198 (by decide)
  have h15 : Entails.eval a c48 := h 47 (by decide)
  have h16 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2004 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2004 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2003, some c1990, some c2, some c2001, some c1956, some c1998, some c1967, some c124, some c2002, some c267, some c1211, some c2000, some c268, some c114, some c1890, some c24, some c37, some c1963, some c161, some c48, some c221, some c66, some c59, some c70, some c120, some c213, some c1232, some c155, some c348, some c346, some c191, some c189, some c254, some c1229, some c1254, some c281, some c315, some c95, some c337, some c344, some c851, some c138, some c150, some c246, some c230, some c331, some c169, some c133, some c361, some c84, some c761, some c90, some c410, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p2004 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54]]
theorem checked2004 : lratChecker f2004 p2004 = .success := by decide +kernel
theorem unsat2004 : Unsatisfiable (PosFin 57) f2004 := by
  apply lratCheckerSound f2004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2004
  · intro a ha; simp [p2004] at ha; subst a; trivial
  · exact checked2004
theorem derived2004 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2004 := by
  apply localUnsat_implies_entails f2004 [c1829, c2003, c1990, c2, c2001, c1956, c1998, c1967, c124, c2002, c267, c1211, c2000, c268, c114, c1890, c24, c37, c1963, c161, c48, c221, c66, c59, c70, c120, c213, c1232, c155, c348, c346, c191, c189, c254, c1229, c1254, c281, c315, c95, c337, c344, c851, c138, c150, c246, c230, c331, c169, c133, c361, c84, c761, c90, c410] c2004 unsat2004 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2003 := derived2003 a h
  have h2 : Entails.eval a c1990 := derived1990 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c2001 := derived2001 a h
  have h5 : Entails.eval a c1956 := derived1956 a h
  have h6 : Entails.eval a c1998 := derived1998 a h
  have h7 : Entails.eval a c1967 := derived1967 a h
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c2002 := derived2002 a h
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c1211 := derived1211 a h
  have h12 : Entails.eval a c2000 := derived2000 a h
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c1890 := derived1890 a h
  have h16 : Entails.eval a c24 := h 23 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c1963 := derived1963 a h
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c48 := h 47 (by decide)
  have h21 : Entails.eval a c221 := h 220 (by decide)
  have h22 : Entails.eval a c66 := h 65 (by decide)
  have h23 : Entails.eval a c59 := h 58 (by decide)
  have h24 : Entails.eval a c70 := h 69 (by decide)
  have h25 : Entails.eval a c120 := h 119 (by decide)
  have h26 : Entails.eval a c213 := h 212 (by decide)
  have h27 : Entails.eval a c1232 := derived1232 a h
  have h28 : Entails.eval a c155 := h 154 (by decide)
  have h29 : Entails.eval a c348 := h 347 (by decide)
  have h30 : Entails.eval a c346 := h 345 (by decide)
  have h31 : Entails.eval a c191 := h 190 (by decide)
  have h32 : Entails.eval a c189 := h 188 (by decide)
  have h33 : Entails.eval a c254 := h 253 (by decide)
  have h34 : Entails.eval a c1229 := derived1229 a h
  have h35 : Entails.eval a c1254 := derived1254 a h
  have h36 : Entails.eval a c281 := h 280 (by decide)
  have h37 : Entails.eval a c315 := h 314 (by decide)
  have h38 : Entails.eval a c95 := h 94 (by decide)
  have h39 : Entails.eval a c337 := h 336 (by decide)
  have h40 : Entails.eval a c344 := h 343 (by decide)
  have h41 : Entails.eval a c851 := derived851 a h
  have h42 : Entails.eval a c138 := h 137 (by decide)
  have h43 : Entails.eval a c150 := h 149 (by decide)
  have h44 : Entails.eval a c246 := h 245 (by decide)
  have h45 : Entails.eval a c230 := h 229 (by decide)
  have h46 : Entails.eval a c331 := h 330 (by decide)
  have h47 : Entails.eval a c169 := h 168 (by decide)
  have h48 : Entails.eval a c133 := h 132 (by decide)
  have h49 : Entails.eval a c361 := h 360 (by decide)
  have h50 : Entails.eval a c84 := h 83 (by decide)
  have h51 : Entails.eval a c761 := derived761 a h
  have h52 : Entails.eval a c90 := h 89 (by decide)
  have h53 : Entails.eval a c410 := h 409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2005 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2005 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1990, some c1956, some c1998, some c1967, some c124, some c2002, some c267, some c268, some c2001, some c114, some c1890, some c212, some c213, some c56, some c28, some c276, some c284, some c221, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p2005 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2005 : lratChecker f2005 p2005 = .success := by decide +kernel
theorem unsat2005 : Unsatisfiable (PosFin 57) f2005 := by
  apply lratCheckerSound f2005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2005
  · intro a ha; simp [p2005] at ha; subst a; trivial
  · exact checked2005
theorem derived2005 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2005 := by
  apply localUnsat_implies_entails f2005 [c1990, c1956, c1998, c1967, c124, c2002, c267, c268, c2001, c114, c1890, c212, c213, c56, c28, c276, c284, c221] c2005 unsat2005 (by rfl) a
  have h0 : Entails.eval a c1990 := derived1990 a h
  have h1 : Entails.eval a c1956 := derived1956 a h
  have h2 : Entails.eval a c1998 := derived1998 a h
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c2002 := derived2002 a h
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c2001 := derived2001 a h
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c1890 := derived1890 a h
  have h11 : Entails.eval a c212 := h 211 (by decide)
  have h12 : Entails.eval a c213 := h 212 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c276 := h 275 (by decide)
  have h16 : Entails.eval a c284 := h 283 (by decide)
  have h17 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2006 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2006 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1956, some c1990, some c2, some c114, some c1998, some c1967, some c124, some c2002, some c267, some c2005, some c46, some c4, some c2004, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p2006 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2006 : lratChecker f2006 p2006 = .success := by decide +kernel
theorem unsat2006 : Unsatisfiable (PosFin 57) f2006 := by
  apply lratCheckerSound f2006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2006
  · intro a ha; simp [p2006] at ha; subst a; trivial
  · exact checked2006
theorem derived2006 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2006 := by
  apply localUnsat_implies_entails f2006 [c1956, c1990, c2, c114, c1998, c1967, c124, c2002, c267, c2005, c46, c4, c2004] c2006 unsat2006 (by rfl) a
  have h0 : Entails.eval a c1956 := derived1956 a h
  have h1 : Entails.eval a c1990 := derived1990 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c1998 := derived1998 a h
  have h5 : Entails.eval a c1967 := derived1967 a h
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c2002 := derived2002 a h
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c2005 := derived2005 a h
  have h10 : Entails.eval a c46 := h 45 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c2004 := derived2004 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2007 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨15, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2007 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c110, some c1541, some c1607, some c819, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p2007 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2007 : lratChecker f2007 p2007 = .success := by decide +kernel
theorem unsat2007 : Unsatisfiable (PosFin 57) f2007 := by
  apply lratCheckerSound f2007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2007
  · intro a ha; simp [p2007] at ha; subst a; trivial
  · exact checked2007
theorem derived2007 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2007 := by
  apply localUnsat_implies_entails f2007 [c2006, c110, c1541, c1607, c819] c2007 unsat2007 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c1541 := derived1541 a h
  have h3 : Entails.eval a c1607 := derived1607 a h
  have h4 : Entails.eval a c819 := derived819 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2008 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2008 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c11, some c198, some c17, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p2008 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2008 : lratChecker f2008 p2008 = .success := by decide +kernel
theorem unsat2008 : Unsatisfiable (PosFin 57) f2008 := by
  apply lratCheckerSound f2008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2008
  · intro a ha; simp [p2008] at ha; subst a; trivial
  · exact checked2008
theorem derived2008 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2008 := by
  apply localUnsat_implies_entails f2008 [c1829, c11, c198, c17] c2008 unsat2008 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2009 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2009 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2006, some c108, some c266, some c1147, some c2007, some c26, some c963, some c1229, some c263, some c1335, some c119, some c1965, some c819, some c56, some c2008, some c264, some c820, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2009 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2009 : lratChecker f2009 p2009 = .success := by decide +kernel
theorem unsat2009 : Unsatisfiable (PosFin 57) f2009 := by
  apply lratCheckerSound f2009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2009
  · intro a ha; simp [p2009] at ha; subst a; trivial
  · exact checked2009
theorem derived2009 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2009 := by
  apply localUnsat_implies_entails f2009 [c1829, c2006, c108, c266, c1147, c2007, c26, c963, c1229, c263, c1335, c119, c1965, c819, c56, c2008, c264, c820] c2009 unsat2009 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c2007 := derived2007 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c963 := derived963 a h
  have h8 : Entails.eval a c1229 := derived1229 a h
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c1335 := derived1335 a h
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c1965 := derived1965 a h
  have h13 : Entails.eval a c819 := derived819 a h
  have h14 : Entails.eval a c56 := h 55 (by decide)
  have h15 : Entails.eval a c2008 := derived2008 a h
  have h16 : Entails.eval a c264 := h 263 (by decide)
  have h17 : Entails.eval a c820 := derived820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2010 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2010 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1147, some c1, some c1848, some c963, some c1261, some c228, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p2010 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2010 : lratChecker f2010 p2010 = .success := by decide +kernel
theorem unsat2010 : Unsatisfiable (PosFin 57) f2010 := by
  apply lratCheckerSound f2010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2010
  · intro a ha; simp [p2010] at ha; subst a; trivial
  · exact checked2010
theorem derived2010 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2010 := by
  apply localUnsat_implies_entails f2010 [c1829, c1147, c1, c1848, c963, c1261, c228] c2010 unsat2010 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1848 := derived1848 a h
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c1261 := derived1261 a h
  have h6 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2011 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2011 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c266, some c2009, some c2010, some c1607, some c1965, some c1335, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2011 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2011 : lratChecker f2011 p2011 = .success := by decide +kernel
theorem unsat2011 : Unsatisfiable (PosFin 57) f2011 := by
  apply lratCheckerSound f2011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2011
  · intro a ha; simp [p2011] at ha; subst a; trivial
  · exact checked2011
theorem derived2011 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2011 := by
  apply localUnsat_implies_entails f2011 [c2006, c266, c2009, c2010, c1607, c1965, c1335] c2011 unsat2011 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c2009 := derived2009 a h
  have h3 : Entails.eval a c2010 := derived2010 a h
  have h4 : Entails.eval a c1607 := derived1607 a h
  have h5 : Entails.eval a c1965 := derived1965 a h
  have h6 : Entails.eval a c1335 := derived1335 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2012 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2012 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c2009, some c2010, some c263, some c27, some c108, some c36, some c110, some c1541, some c2011, some c1147, some c115, some c45, some c134, some c81, some c236, some c234, some c175, some c293, some c199, some c168, some c967, some c73, some c222, some c277, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2012 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2012 : lratChecker f2012 p2012 = .success := by decide +kernel
theorem unsat2012 : Unsatisfiable (PosFin 57) f2012 := by
  apply lratCheckerSound f2012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2012
  · intro a ha; simp [p2012] at ha; subst a; trivial
  · exact checked2012
theorem derived2012 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2012 := by
  apply localUnsat_implies_entails f2012 [c2006, c1829, c266, c2009, c2010, c263, c27, c108, c36, c110, c1541, c2011, c1147, c115, c45, c134, c81, c236, c234, c175, c293, c199, c168, c967, c73, c222, c277] c2012 unsat2012 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2009 := derived2009 a h
  have h4 : Entails.eval a c2010 := derived2010 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c1541 := derived1541 a h
  have h11 : Entails.eval a c2011 := derived2011 a h
  have h12 : Entails.eval a c1147 := derived1147 a h
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c134 := h 133 (by decide)
  have h16 : Entails.eval a c81 := h 80 (by decide)
  have h17 : Entails.eval a c236 := h 235 (by decide)
  have h18 : Entails.eval a c234 := h 233 (by decide)
  have h19 : Entails.eval a c175 := h 174 (by decide)
  have h20 : Entails.eval a c293 := h 292 (by decide)
  have h21 : Entails.eval a c199 := h 198 (by decide)
  have h22 : Entails.eval a c168 := h 167 (by decide)
  have h23 : Entails.eval a c967 := derived967 a h
  have h24 : Entails.eval a c73 := h 72 (by decide)
  have h25 : Entails.eval a c222 := h 221 (by decide)
  have h26 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2013 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2013 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1829, some c266, some c1147, some c2008, some c968, some c165, some c154, some c67, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p2013 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2013 : lratChecker f2013 p2013 = .success := by decide +kernel
theorem unsat2013 : Unsatisfiable (PosFin 57) f2013 := by
  apply lratCheckerSound f2013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2013
  · intro a ha; simp [p2013] at ha; subst a; trivial
  · exact checked2013
theorem derived2013 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2013 := by
  apply localUnsat_implies_entails f2013 [c2006, c1829, c266, c1147, c2008, c968, c165, c154, c67] c2013 unsat2013 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1829 := derived1829 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c2008 := derived2008 a h
  have h5 : Entails.eval a c968 := derived968 a h
  have h6 : Entails.eval a c165 := h 164 (by decide)
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2013

end CochromaticTwenty.Certificates.B16_0_2Enumerating
