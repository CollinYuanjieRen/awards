import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps1300_1399

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1814 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1811, some c107, some c15, some c1632, some c1803, some c2, some c266, some c1147, some c198, some c105, some c12, some c1738, some c264, some c268, some c263, some c38, some c25, some c123, some c113, some c164, some c42, some c219, some c214, some c269, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1814 : lratChecker f1814 p1814 = .success := by decide +kernel
theorem unsat1814 : Unsatisfiable (PosFin 57) f1814 := by
  apply lratCheckerSound f1814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1814
  · intro a ha; simp [p1814] at ha; subst a; trivial
  · exact checked1814
theorem derived1814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1814 := by
  apply localUnsat_implies_entails f1814 [c1794, c1811, c107, c15, c1632, c1803, c2, c266, c1147, c198, c105, c12, c1738, c264, c268, c263, c38, c25, c123, c113, c164, c42, c219, c214, c269] c1814 unsat1814 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1811 := derived1811 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c1632 := derived1632 a h
  have h5 : Entails.eval a c1803 := derived1803 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c1738 := derived1738 a h
  have h13 : Entails.eval a c264 := h 263 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c123 := h 122 (by decide)
  have h19 : Entails.eval a c113 := h 112 (by decide)
  have h20 : Entails.eval a c164 := h 163 (by decide)
  have h21 : Entails.eval a c42 := h 41 (by decide)
  have h22 : Entails.eval a c219 := h 218 (by decide)
  have h23 : Entails.eval a c214 := h 213 (by decide)
  have h24 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1815 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨23, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c75, some c351, some c168, some c228, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1815 : lratChecker f1815 p1815 = .success := by decide +kernel
theorem unsat1815 : Unsatisfiable (PosFin 57) f1815 := by
  apply lratCheckerSound f1815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1815
  · intro a ha; simp [p1815] at ha; subst a; trivial
  · exact checked1815
theorem derived1815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1815 := by
  apply localUnsat_implies_entails f1815 [c68, c75, c351, c168, c228] c1815 unsat1815 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c75 := h 74 (by decide)
  have h2 : Entails.eval a c351 := h 350 (by decide)
  have h3 : Entails.eval a c168 := h 167 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1816 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1803, some c1811, some c105, some c12, some c1794, some c107, some c15, some c1738, some c2, some c264, some c266, some c1147, some c1813, some c1814, some c1815, some c166, some c228, some c224, some c167, some c1615, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1816 : lratChecker f1816 p1816 = .success := by decide +kernel
theorem unsat1816 : Unsatisfiable (PosFin 57) f1816 := by
  apply lratCheckerSound f1816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1816
  · intro a ha; simp [p1816] at ha; subst a; trivial
  · exact checked1816
theorem derived1816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1816 := by
  apply localUnsat_implies_entails f1816 [c1632, c1803, c1811, c105, c12, c1794, c107, c15, c1738, c2, c264, c266, c1147, c1813, c1814, c1815, c166, c228, c224, c167, c1615] c1816 unsat1816 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1803 := derived1803 a h
  have h2 : Entails.eval a c1811 := derived1811 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c1794 := derived1794 a h
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c1738 := derived1738 a h
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c1147 := derived1147 a h
  have h13 : Entails.eval a c1813 := derived1813 a h
  have h14 : Entails.eval a c1814 := derived1814 a h
  have h15 : Entails.eval a c1815 := derived1815 a h
  have h16 : Entails.eval a c166 := h 165 (by decide)
  have h17 : Entails.eval a c228 := h 227 (by decide)
  have h18 : Entails.eval a c224 := h 223 (by decide)
  have h19 : Entails.eval a c167 := h 166 (by decide)
  have h20 : Entails.eval a c1615 := derived1615 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1817 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1811, some c105, some c107, some c1816, some c39, some c268, some c28, some c1632, some c1803, some c12, some c2, some c264, some c1794, some c819, some c706, some c119, some c284, some c224, some c164, some c68, some c61, some c349, some c254, some c59, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1817 : lratChecker f1817 p1817 = .success := by decide +kernel
theorem unsat1817 : Unsatisfiable (PosFin 57) f1817 := by
  apply lratCheckerSound f1817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1817
  · intro a ha; simp [p1817] at ha; subst a; trivial
  · exact checked1817
theorem derived1817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1817 := by
  apply localUnsat_implies_entails f1817 [c1738, c1811, c105, c107, c1816, c39, c268, c28, c1632, c1803, c12, c2, c264, c1794, c819, c706, c119, c284, c224, c164, c68, c61, c349, c254, c59] c1817 unsat1817 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1811 := derived1811 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c1816 := derived1816 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c1632 := derived1632 a h
  have h9 : Entails.eval a c1803 := derived1803 a h
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c1794 := derived1794 a h
  have h14 : Entails.eval a c819 := derived819 a h
  have h15 : Entails.eval a c706 := derived706 a h
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c284 := h 283 (by decide)
  have h18 : Entails.eval a c224 := h 223 (by decide)
  have h19 : Entails.eval a c164 := h 163 (by decide)
  have h20 : Entails.eval a c68 := h 67 (by decide)
  have h21 : Entails.eval a c61 := h 60 (by decide)
  have h22 : Entails.eval a c349 := h 348 (by decide)
  have h23 : Entails.eval a c254 := h 253 (by decide)
  have h24 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1818 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1811, some c105, some c107, some c1816, some c39, some c268, some c1632, some c1803, some c2, some c264, some c1794, some c15, some c28, some c1817, some c168, some c224, some c68, some c61, some c349, some c254, some c59, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1818 : lratChecker f1818 p1818 = .success := by decide +kernel
theorem unsat1818 : Unsatisfiable (PosFin 57) f1818 := by
  apply lratCheckerSound f1818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1818
  · intro a ha; simp [p1818] at ha; subst a; trivial
  · exact checked1818
theorem derived1818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1818 := by
  apply localUnsat_implies_entails f1818 [c1738, c1811, c105, c107, c1816, c39, c268, c1632, c1803, c2, c264, c1794, c15, c28, c1817, c168, c224, c68, c61, c349, c254, c59] c1818 unsat1818 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1811 := derived1811 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c1816 := derived1816 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c1632 := derived1632 a h
  have h8 : Entails.eval a c1803 := derived1803 a h
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c1794 := derived1794 a h
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c1817 := derived1817 a h
  have h15 : Entails.eval a c168 := h 167 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  have h17 : Entails.eval a c68 := h 67 (by decide)
  have h18 : Entails.eval a c61 := h 60 (by decide)
  have h19 : Entails.eval a c349 := h 348 (by decide)
  have h20 : Entails.eval a c254 := h 253 (by decide)
  have h21 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1819 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1738, some c1632, some c1803, some c2, some c264, some c1811, some c107, some c105, some c15, some c1816, some c28, some c39, some c268, some c1817, some c168, some c224, some c1818, some c352, some c59, some c249, some c254, some c96, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1819 : lratChecker f1819 p1819 = .success := by decide +kernel
theorem unsat1819 : Unsatisfiable (PosFin 57) f1819 := by
  apply lratCheckerSound f1819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1819
  · intro a ha; simp [p1819] at ha; subst a; trivial
  · exact checked1819
theorem derived1819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1819 := by
  apply localUnsat_implies_entails f1819 [c1794, c1738, c1632, c1803, c2, c264, c1811, c107, c105, c15, c1816, c28, c39, c268, c1817, c168, c224, c1818, c352, c59, c249, c254, c96] c1819 unsat1819 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1803 := derived1803 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c1811 := derived1811 a h
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c1816 := derived1816 a h
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c1817 := derived1817 a h
  have h15 : Entails.eval a c168 := h 167 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  have h17 : Entails.eval a c1818 := derived1818 a h
  have h18 : Entails.eval a c352 := h 351 (by decide)
  have h19 : Entails.eval a c59 := h 58 (by decide)
  have h20 : Entails.eval a c249 := h 248 (by decide)
  have h21 : Entails.eval a c254 := h 253 (by decide)
  have h22 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1820 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1819, some c1632, some c2, some c1794, some c22, some c157, some c59, some c185, some c1738, some c33, some c97, some c255, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1820 : lratChecker f1820 p1820 = .success := by decide +kernel
theorem unsat1820 : Unsatisfiable (PosFin 57) f1820 := by
  apply lratCheckerSound f1820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1820
  · intro a ha; simp [p1820] at ha; subst a; trivial
  · exact checked1820
theorem derived1820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1820 := by
  apply localUnsat_implies_entails f1820 [c1819, c1632, c2, c1794, c22, c157, c59, c185, c1738, c33, c97, c255] c1820 unsat1820 (by rfl) a
  have h0 : Entails.eval a c1819 := derived1819 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1794 := derived1794 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c1738 := derived1738 a h
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  have h11 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1821 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1819, some c1632, some c2, some c1820, some c107, some c105, some c1791, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1821 : lratChecker f1821 p1821 = .success := by decide +kernel
theorem unsat1821 : Unsatisfiable (PosFin 57) f1821 := by
  apply lratCheckerSound f1821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1821
  · intro a ha; simp [p1821] at ha; subst a; trivial
  · exact checked1821
theorem derived1821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1821 := by
  apply localUnsat_implies_entails f1821 [c1819, c1632, c2, c1820, c107, c105, c1791] c1821 unsat1821 (by rfl) a
  have h0 : Entails.eval a c1819 := derived1819 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1820 := derived1820 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1791 := derived1791 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1822 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1821, some c264, some c1819, some c200, some c116, some c4, some c1788, some c52, some c266, some c1744, some c128, some c117, some c214, some c263, some c776, some c123, some c1485, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1822 : lratChecker f1822 p1822 = .success := by decide +kernel
theorem unsat1822 : Unsatisfiable (PosFin 57) f1822 := by
  apply lratCheckerSound f1822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1822
  · intro a ha; simp [p1822] at ha; subst a; trivial
  · exact checked1822
theorem derived1822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1822 := by
  apply localUnsat_implies_entails f1822 [c1738, c1821, c264, c1819, c200, c116, c4, c1788, c52, c266, c1744, c128, c117, c214, c263, c776, c123, c1485] c1822 unsat1822 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1821 := derived1821 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c1819 := derived1819 a h
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c1788 := derived1788 a h
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c1744 := derived1744 a h
  have h11 : Entails.eval a c128 := h 127 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  have h14 : Entails.eval a c263 := h 262 (by decide)
  have h15 : Entails.eval a c776 := derived776 a h
  have h16 : Entails.eval a c123 := h 122 (by decide)
  have h17 : Entails.eval a c1485 := derived1485 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1823 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1821, some c264, some c1819, some c266, some c1788, some c1147, some c202, some c1822, some c204, some c1216, some c1386, some c1219, some c1224, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1823 : lratChecker f1823 p1823 = .success := by decide +kernel
theorem unsat1823 : Unsatisfiable (PosFin 57) f1823 := by
  apply lratCheckerSound f1823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1823
  · intro a ha; simp [p1823] at ha; subst a; trivial
  · exact checked1823
theorem derived1823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1823 := by
  apply localUnsat_implies_entails f1823 [c1738, c1821, c264, c1819, c266, c1788, c1147, c202, c1822, c204, c1216, c1386, c1219, c1224] c1823 unsat1823 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1821 := derived1821 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c1819 := derived1819 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c1788 := derived1788 a h
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c1822 := derived1822 a h
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c1216 := derived1216 a h
  have h11 : Entails.eval a c1386 := derived1386 a h
  have h12 : Entails.eval a c1219 := derived1219 a h
  have h13 : Entails.eval a c1224 := derived1224 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1824 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1821, some c264, some c1823, some c896, some c1819, some c200, some c116, some c4, some c1632, some c1744, some c1789, some c20, some c52, some c106, some c53, some c215, some c982, some c28, some c152, some c69, some c284, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1824 : lratChecker f1824 p1824 = .success := by decide +kernel
theorem unsat1824 : Unsatisfiable (PosFin 57) f1824 := by
  apply lratCheckerSound f1824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1824
  · intro a ha; simp [p1824] at ha; subst a; trivial
  · exact checked1824
theorem derived1824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1824 := by
  apply localUnsat_implies_entails f1824 [c1738, c1821, c264, c1823, c896, c1819, c200, c116, c4, c1632, c1744, c1789, c20, c52, c106, c53, c215, c982, c28, c152, c69, c284] c1824 unsat1824 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1821 := derived1821 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c1823 := derived1823 a h
  have h4 : Entails.eval a c896 := derived896 a h
  have h5 : Entails.eval a c1819 := derived1819 a h
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c1632 := derived1632 a h
  have h10 : Entails.eval a c1744 := derived1744 a h
  have h11 : Entails.eval a c1789 := derived1789 a h
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c53 := h 52 (by decide)
  have h16 : Entails.eval a c215 := h 214 (by decide)
  have h17 : Entails.eval a c982 := derived982 a h
  have h18 : Entails.eval a c28 := h 27 (by decide)
  have h19 : Entails.eval a c152 := h 151 (by decide)
  have h20 : Entails.eval a c69 := h 68 (by decide)
  have h21 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1825 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1819, some c200, some c1738, some c1821, some c264, some c1632, some c1823, some c896, some c129, some c1147, some c1824, some c1755, some c106, some c1769, some c1808, some c168, some c225, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1825 : lratChecker f1825 p1825 = .success := by decide +kernel
theorem unsat1825 : Unsatisfiable (PosFin 57) f1825 := by
  apply lratCheckerSound f1825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1825
  · intro a ha; simp [p1825] at ha; subst a; trivial
  · exact checked1825
theorem derived1825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1825 := by
  apply localUnsat_implies_entails f1825 [c1819, c200, c1738, c1821, c264, c1632, c1823, c896, c129, c1147, c1824, c1755, c106, c1769, c1808, c168, c225] c1825 unsat1825 (by rfl) a
  have h0 : Entails.eval a c1819 := derived1819 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c1738 := derived1738 a h
  have h3 : Entails.eval a c1821 := derived1821 a h
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c1632 := derived1632 a h
  have h6 : Entails.eval a c1823 := derived1823 a h
  have h7 : Entails.eval a c896 := derived896 a h
  have h8 : Entails.eval a c129 := h 128 (by decide)
  have h9 : Entails.eval a c1147 := derived1147 a h
  have h10 : Entails.eval a c1824 := derived1824 a h
  have h11 : Entails.eval a c1755 := derived1755 a h
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c1769 := derived1769 a h
  have h14 : Entails.eval a c1808 := derived1808 a h
  have h15 : Entails.eval a c168 := h 167 (by decide)
  have h16 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1826 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1821, some c264, some c1819, some c1632, some c200, some c4, some c1825, some c107, some c105, some c1788, some c39, some c896, some c129, some c982, some c1744, some c1147, some c58, some c199, some c1807, some c985, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1826 : lratChecker f1826 p1826 = .success := by decide +kernel
theorem unsat1826 : Unsatisfiable (PosFin 57) f1826 := by
  apply lratCheckerSound f1826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1826
  · intro a ha; simp [p1826] at ha; subst a; trivial
  · exact checked1826
theorem derived1826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1826 := by
  apply localUnsat_implies_entails f1826 [c1738, c1821, c264, c1819, c1632, c200, c4, c1825, c107, c105, c1788, c39, c896, c129, c982, c1744, c1147, c58, c199, c1807, c985] c1826 unsat1826 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1821 := derived1821 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c1819 := derived1819 a h
  have h4 : Entails.eval a c1632 := derived1632 a h
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c1825 := derived1825 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c1788 := derived1788 a h
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c896 := derived896 a h
  have h13 : Entails.eval a c129 := h 128 (by decide)
  have h14 : Entails.eval a c982 := derived982 a h
  have h15 : Entails.eval a c1744 := derived1744 a h
  have h16 : Entails.eval a c1147 := derived1147 a h
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c199 := h 198 (by decide)
  have h19 : Entails.eval a c1807 := derived1807 a h
  have h20 : Entails.eval a c985 := derived985 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1827 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1826, some c1819, some c13, some c204, some c12, some c1738, some c1821, some c264, some c1794, some c266, some c1216, some c1386, some c1219, some c1224, some c1564, some c1513, some c71, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1827 : lratChecker f1827 p1827 = .success := by decide +kernel
theorem unsat1827 : Unsatisfiable (PosFin 57) f1827 := by
  apply lratCheckerSound f1827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1827
  · intro a ha; simp [p1827] at ha; subst a; trivial
  · exact checked1827
theorem derived1827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1827 := by
  apply localUnsat_implies_entails f1827 [c1632, c1826, c1819, c13, c204, c12, c1738, c1821, c264, c1794, c266, c1216, c1386, c1219, c1224, c1564, c1513, c71] c1827 unsat1827 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1826 := derived1826 a h
  have h2 : Entails.eval a c1819 := derived1819 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c1738 := derived1738 a h
  have h7 : Entails.eval a c1821 := derived1821 a h
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c1794 := derived1794 a h
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c1216 := derived1216 a h
  have h12 : Entails.eval a c1386 := derived1386 a h
  have h13 : Entails.eval a c1219 := derived1219 a h
  have h14 : Entails.eval a c1224 := derived1224 a h
  have h15 : Entails.eval a c1564 := derived1564 a h
  have h16 : Entails.eval a c1513 := derived1513 a h
  have h17 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1828 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1826, some c1738, some c1821, some c264, some c1819, some c1794, some c1632, some c13, some c204, some c1827, some c1565, some c106, some c1769, some c1386, some c163, some c1807, some c59, some c97, some c191, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1828 : lratChecker f1828 p1828 = .success := by decide +kernel
theorem unsat1828 : Unsatisfiable (PosFin 57) f1828 := by
  apply lratCheckerSound f1828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1828
  · intro a ha; simp [p1828] at ha; subst a; trivial
  · exact checked1828
theorem derived1828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1828 := by
  apply localUnsat_implies_entails f1828 [c1826, c1738, c1821, c264, c1819, c1794, c1632, c13, c204, c1827, c1565, c106, c1769, c1386, c163, c1807, c59, c97, c191] c1828 unsat1828 (by rfl) a
  have h0 : Entails.eval a c1826 := derived1826 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1821 := derived1821 a h
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c1819 := derived1819 a h
  have h5 : Entails.eval a c1794 := derived1794 a h
  have h6 : Entails.eval a c1632 := derived1632 a h
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c1827 := derived1827 a h
  have h10 : Entails.eval a c1565 := derived1565 a h
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c1769 := derived1769 a h
  have h13 : Entails.eval a c1386 := derived1386 a h
  have h14 : Entails.eval a c163 := h 162 (by decide)
  have h15 : Entails.eval a c1807 := derived1807 a h
  have h16 : Entails.eval a c59 := h 58 (by decide)
  have h17 : Entails.eval a c97 := h 96 (by decide)
  have h18 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1829 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1738, some c1819, some c1821, some c264, some c1826, some c1828, some c107, some c105, some c12, some c204, some c203, some c1744, some c39, some c266, some c1787, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1829 : lratChecker f1829 p1829 = .success := by decide +kernel
theorem unsat1829 : Unsatisfiable (PosFin 57) f1829 := by
  apply lratCheckerSound f1829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1829
  · intro a ha; simp [p1829] at ha; subst a; trivial
  · exact checked1829
theorem derived1829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1829 := by
  apply localUnsat_implies_entails f1829 [c1632, c1738, c1819, c1821, c264, c1826, c1828, c107, c105, c12, c204, c203, c1744, c39, c266, c1787] c1829 unsat1829 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1819 := derived1819 a h
  have h3 : Entails.eval a c1821 := derived1821 a h
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c1826 := derived1826 a h
  have h6 : Entails.eval a c1828 := derived1828 a h
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c1744 := derived1744 a h
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c1787 := derived1787 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1830 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨21, by decide⟩, false), (⟨29, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c139, some c152, some c244, some c242, some c313, some c295, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1830 : lratChecker f1830 p1830 = .success := by decide +kernel
theorem unsat1830 : Unsatisfiable (PosFin 57) f1830 := by
  apply lratCheckerSound f1830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1830
  · intro a ha; simp [p1830] at ha; subst a; trivial
  · exact checked1830
theorem derived1830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1830 := by
  apply localUnsat_implies_entails f1830 [c139, c152, c244, c242, c313, c295] c1830 unsat1830 (by rfl) a
  have h0 : Entails.eval a c139 := h 138 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c242 := h 241 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1831 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c243, some c244, some c180, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1831 : lratChecker f1831 p1831 = .success := by decide +kernel
theorem unsat1831 : Unsatisfiable (PosFin 57) f1831 := by
  apply lratCheckerSound f1831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1831
  · intro a ha; simp [p1831] at ha; subst a; trivial
  · exact checked1831
theorem derived1831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1831 := by
  apply localUnsat_implies_entails f1831 [c1147, c243, c244, c180] c1831 unsat1831 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1832 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨33, by decide⟩, false), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1302, some c314, some c140, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1832 : lratChecker f1832 p1832 = .success := by decide +kernel
theorem unsat1832 : Unsatisfiable (PosFin 57) f1832 := by
  apply lratCheckerSound f1832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1832
  · intro a ha; simp [p1832] at ha; subst a; trivial
  · exact checked1832
theorem derived1832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1832 := by
  apply localUnsat_implies_entails f1832 [c1302, c314, c140] c1832 unsat1832 (by rfl) a
  have h0 : Entails.eval a c1302 := derived1302 a h
  have h1 : Entails.eval a c314 := h 313 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1833 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c7, some c263, some c1, some c29, some c21, some c108, some c45, some c16, some c1332, some c31, some c205, some c201, some c110, some c1147, some c1831, some c1832, some c152, some c313, some c270, some c140, some c1533, some c64, some c73, some c259, some c260, some c158, some c345, some c100, some c346, some c220, some c343, some c256, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1833 : lratChecker f1833 p1833 = .success := by decide +kernel
theorem unsat1833 : Unsatisfiable (PosFin 57) f1833 := by
  apply lratCheckerSound f1833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1833
  · intro a ha; simp [p1833] at ha; subst a; trivial
  · exact checked1833
theorem derived1833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1833 := by
  apply localUnsat_implies_entails f1833 [c1829, c7, c263, c1, c29, c21, c108, c45, c16, c1332, c31, c205, c201, c110, c1147, c1831, c1832, c152, c313, c270, c140, c1533, c64, c73, c259, c260, c158, c345, c100, c346, c220, c343, c256] c1833 unsat1833 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c1332 := derived1332 a h
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c205 := h 204 (by decide)
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c1147 := derived1147 a h
  have h15 : Entails.eval a c1831 := derived1831 a h
  have h16 : Entails.eval a c1832 := derived1832 a h
  have h17 : Entails.eval a c152 := h 151 (by decide)
  have h18 : Entails.eval a c313 := h 312 (by decide)
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c140 := h 139 (by decide)
  have h21 : Entails.eval a c1533 := derived1533 a h
  have h22 : Entails.eval a c64 := h 63 (by decide)
  have h23 : Entails.eval a c73 := h 72 (by decide)
  have h24 : Entails.eval a c259 := h 258 (by decide)
  have h25 : Entails.eval a c260 := h 259 (by decide)
  have h26 : Entails.eval a c158 := h 157 (by decide)
  have h27 : Entails.eval a c345 := h 344 (by decide)
  have h28 : Entails.eval a c100 := h 99 (by decide)
  have h29 : Entails.eval a c346 := h 345 (by decide)
  have h30 : Entails.eval a c220 := h 219 (by decide)
  have h31 : Entails.eval a c343 := h 342 (by decide)
  have h32 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1834 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c108, some c45, some c1275, some c1147, some c262, some c1, some c205, some c1137, some c197, some c50, some c150, some c1004, some c313, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1834 : lratChecker f1834 p1834 = .success := by decide +kernel
theorem unsat1834 : Unsatisfiable (PosFin 57) f1834 := by
  apply lratCheckerSound f1834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1834
  · intro a ha; simp [p1834] at ha; subst a; trivial
  · exact checked1834
theorem derived1834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1834 := by
  apply localUnsat_implies_entails f1834 [c1829, c108, c45, c1275, c1147, c262, c1, c205, c1137, c197, c50, c150, c1004, c313] c1834 unsat1834 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c1137 := derived1137 a h
  have h9 : Entails.eval a c197 := h 196 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c150 := h 149 (by decide)
  have h12 : Entails.eval a c1004 := derived1004 a h
  have h13 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1835 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c29, some c33, some c263, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1835 : lratChecker f1835 p1835 = .success := by decide +kernel
theorem unsat1835 : Unsatisfiable (PosFin 57) f1835 := by
  apply lratCheckerSound f1835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1835
  · intro a ha; simp [p1835] at ha; subst a; trivial
  · exact checked1835
theorem derived1835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1835 := by
  apply localUnsat_implies_entails f1835 [c1829, c29, c33, c263] c1835 unsat1835 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1836 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1833, some c1835, some c45, some c1834, some c110, some c1335, some c1, some c21, some c205, some c197, some c155, some c1192, some c63, some c27, some c76, some c260, some c258, some c963, some c347, some c270, some c344, some c150, some c269, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1836 : lratChecker f1836 p1836 = .success := by decide +kernel
theorem unsat1836 : Unsatisfiable (PosFin 57) f1836 := by
  apply lratCheckerSound f1836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1836
  · intro a ha; simp [p1836] at ha; subst a; trivial
  · exact checked1836
theorem derived1836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1836 := by
  apply localUnsat_implies_entails f1836 [c1829, c1833, c1835, c45, c1834, c110, c1335, c1, c21, c205, c197, c155, c1192, c63, c27, c76, c260, c258, c963, c347, c270, c344, c150, c269] c1836 unsat1836 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1833 := derived1833 a h
  have h2 : Entails.eval a c1835 := derived1835 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c1834 := derived1834 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c1335 := derived1335 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c1192 := derived1192 a h
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c27 := h 26 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c260 := h 259 (by decide)
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c963 := derived963 a h
  have h19 : Entails.eval a c347 := h 346 (by decide)
  have h20 : Entails.eval a c270 := h 269 (by decide)
  have h21 : Entails.eval a c344 := h 343 (by decide)
  have h22 : Entails.eval a c150 := h 149 (by decide)
  have h23 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1837 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨12, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c982, some c22, some c45, some c50, some c208, some c1315, some c261, some c1393, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1837 : lratChecker f1837 p1837 = .success := by decide +kernel
theorem unsat1837 : Unsatisfiable (PosFin 57) f1837 := by
  apply lratCheckerSound f1837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1837
  · intro a ha; simp [p1837] at ha; subst a; trivial
  · exact checked1837
theorem derived1837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1837 := by
  apply localUnsat_implies_entails f1837 [c982, c22, c45, c50, c208, c1315, c261, c1393] c1837 unsat1837 (by rfl) a
  have h0 : Entails.eval a c982 := derived982 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c1315 := derived1315 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c1393 := derived1393 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1838 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1837, some c1723, some c1, some c1393, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1838 : lratChecker f1838 p1838 = .success := by decide +kernel
theorem unsat1838 : Unsatisfiable (PosFin 57) f1838 := by
  apply lratCheckerSound f1838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1838
  · intro a ha; simp [p1838] at ha; subst a; trivial
  · exact checked1838
theorem derived1838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1838 := by
  apply localUnsat_implies_entails f1838 [c1829, c1837, c1723, c1, c1393] c1838 unsat1838 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1837 := derived1837 a h
  have h2 : Entails.eval a c1723 := derived1723 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1393 := derived1393 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1839 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c1836, some c982, some c22, some c108, some c16, some c1838, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1839 : lratChecker f1839 p1839 = .success := by decide +kernel
theorem unsat1839 : Unsatisfiable (PosFin 57) f1839 := by
  apply lratCheckerSound f1839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1839
  · intro a ha; simp [p1839] at ha; subst a; trivial
  · exact checked1839
theorem derived1839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1839 := by
  apply localUnsat_implies_entails f1839 [c7, c1836, c982, c22, c108, c16, c1838] c1839 unsat1839 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c1836 := derived1836 a h
  have h2 : Entails.eval a c982 := derived982 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c1838 := derived1838 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1840 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c202, some c1836, some c7, some c20, some c1839, some c110, some c29, some c22, some c261, some c160, some c32, some c223, some c50, some c273, some c208, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1840 : lratChecker f1840 p1840 = .success := by decide +kernel
theorem unsat1840 : Unsatisfiable (PosFin 57) f1840 := by
  apply lratCheckerSound f1840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1840
  · intro a ha; simp [p1840] at ha; subst a; trivial
  · exact checked1840
theorem derived1840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1840 := by
  apply localUnsat_implies_entails f1840 [c1829, c202, c1836, c7, c20, c1839, c110, c29, c22, c261, c160, c32, c223, c50, c273, c208] c1840 unsat1840 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c1836 := derived1836 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c1839 := derived1839 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c223 := h 222 (by decide)
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c273 := h 272 (by decide)
  have h15 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1841 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨4, by decide⟩, true), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c199, some c11, some c1836, some c1192, some c868, some c166, some c164, some c72, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1841 : lratChecker f1841 p1841 = .success := by decide +kernel
theorem unsat1841 : Unsatisfiable (PosFin 57) f1841 := by
  apply lratCheckerSound f1841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1841
  · intro a ha; simp [p1841] at ha; subst a; trivial
  · exact checked1841
theorem derived1841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1841 := by
  apply localUnsat_implies_entails f1841 [c1829, c199, c11, c1836, c1192, c868, c166, c164, c72] c1841 unsat1841 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c1836 := derived1836 a h
  have h4 : Entails.eval a c1192 := derived1192 a h
  have h5 : Entails.eval a c868 := derived868 a h
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1842 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1840, some c1836, some c108, some c45, some c1841, some c261, some c27, some c209, some c889, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1842 : lratChecker f1842 p1842 = .success := by decide +kernel
theorem unsat1842 : Unsatisfiable (PosFin 57) f1842 := by
  apply lratCheckerSound f1842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1842
  · intro a ha; simp [p1842] at ha; subst a; trivial
  · exact checked1842
theorem derived1842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1842 := by
  apply localUnsat_implies_entails f1842 [c1840, c1836, c108, c45, c1841, c261, c27, c209, c889] c1842 unsat1842 (by rfl) a
  have h0 : Entails.eval a c1840 := derived1840 a h
  have h1 : Entails.eval a c1836 := derived1836 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c1841 := derived1841 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c889 := derived889 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1843 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c115, some c1836, some c127, some c1840, some c199, some c122, some c1842, some c33, some c261, some c32, some c1841, some c111, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1843 : lratChecker f1843 p1843 = .success := by decide +kernel
theorem unsat1843 : Unsatisfiable (PosFin 57) f1843 := by
  apply lratCheckerSound f1843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1843
  · intro a ha; simp [p1843] at ha; subst a; trivial
  · exact checked1843
theorem derived1843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1843 := by
  apply localUnsat_implies_entails f1843 [c3, c115, c1836, c127, c1840, c199, c122, c1842, c33, c261, c32, c1841, c111] c1843 unsat1843 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c115 := h 114 (by decide)
  have h2 : Entails.eval a c1836 := derived1836 a h
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c1840 := derived1840 a h
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c1842 := derived1842 a h
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c1841 := derived1841 a h
  have h12 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1844 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c263, some c1835, some c1843, some c1836, some c108, some c135, some c16, some c1332, some c81, some c201, some c1301, some c205, some c1404, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1844 : lratChecker f1844 p1844 = .success := by decide +kernel
theorem unsat1844 : Unsatisfiable (PosFin 57) f1844 := by
  apply lratCheckerSound f1844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1844
  · intro a ha; simp [p1844] at ha; subst a; trivial
  · exact checked1844
theorem derived1844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1844 := by
  apply localUnsat_implies_entails f1844 [c7, c263, c1835, c1843, c1836, c108, c135, c16, c1332, c81, c201, c1301, c205, c1404] c1844 unsat1844 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c1835 := derived1835 a h
  have h3 : Entails.eval a c1843 := derived1843 a h
  have h4 : Entails.eval a c1836 := derived1836 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c1332 := derived1332 a h
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c1301 := derived1301 a h
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c1404 := derived1404 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1845 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c21, some c1, some c1843, some c268, some c15, some c1558, some c1019, some c1533, some c109, some c63, some c71, some c73, some c346, some c349, some c220, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1845 : lratChecker f1845 p1845 = .success := by decide +kernel
theorem unsat1845 : Unsatisfiable (PosFin 57) f1845 := by
  apply lratCheckerSound f1845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1845
  · intro a ha; simp [p1845] at ha; subst a; trivial
  · exact checked1845
theorem derived1845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1845 := by
  apply localUnsat_implies_entails f1845 [c1829, c21, c1, c1843, c268, c15, c1558, c1019, c1533, c109, c63, c71, c73, c346, c349, c220] c1845 unsat1845 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1843 := derived1843 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c1558 := derived1558 a h
  have h7 : Entails.eval a c1019 := derived1019 a h
  have h8 : Entails.eval a c1533 := derived1533 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c346 := h 345 (by decide)
  have h14 : Entails.eval a c349 := h 348 (by decide)
  have h15 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1846 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1835, some c1843, some c7, some c268, some c263, some c1, some c21, some c1844, some c1845, some c110, some c14, some c963, some c26, some c70, some c62, some c76, some c353, some c259, some c182, some c348, some c220, some c344, some c94, some c349, some c380, some c342, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1846 : lratChecker f1846 p1846 = .success := by decide +kernel
theorem unsat1846 : Unsatisfiable (PosFin 57) f1846 := by
  apply lratCheckerSound f1846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1846
  · intro a ha; simp [p1846] at ha; subst a; trivial
  · exact checked1846
theorem derived1846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1846 := by
  apply localUnsat_implies_entails f1846 [c1829, c1835, c1843, c7, c268, c263, c1, c21, c1844, c1845, c110, c14, c963, c26, c70, c62, c76, c353, c259, c182, c348, c220, c344, c94, c349, c380, c342] c1846 unsat1846 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1835 := derived1835 a h
  have h2 : Entails.eval a c1843 := derived1843 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c1844 := derived1844 a h
  have h9 : Entails.eval a c1845 := derived1845 a h
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c963 := derived963 a h
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c76 := h 75 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c259 := h 258 (by decide)
  have h19 : Entails.eval a c182 := h 181 (by decide)
  have h20 : Entails.eval a c348 := h 347 (by decide)
  have h21 : Entails.eval a c220 := h 219 (by decide)
  have h22 : Entails.eval a c344 := h 343 (by decide)
  have h23 : Entails.eval a c94 := h 93 (by decide)
  have h24 : Entails.eval a c349 := h 348 (by decide)
  have h25 : Entails.eval a c380 := h 379 (by decide)
  have h26 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1847 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨15, by decide⟩, false), (⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1406, some c263, some c1, some c21, some c31, some c197, some c199, some c1261, some c155, some c237, some c5, some c117, some c63, some c86, some c183, some c179, some c95, some c243, some c257, some c178, some c363, some c201, some c307, some c136, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1847 : lratChecker f1847 p1847 = .success := by decide +kernel
theorem unsat1847 : Unsatisfiable (PosFin 57) f1847 := by
  apply lratCheckerSound f1847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1847
  · intro a ha; simp [p1847] at ha; subst a; trivial
  · exact checked1847
theorem derived1847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1847 := by
  apply localUnsat_implies_entails f1847 [c1829, c1406, c263, c1, c21, c31, c197, c199, c1261, c155, c237, c5, c117, c63, c86, c183, c179, c95, c243, c257, c178, c363, c201, c307, c136] c1847 unsat1847 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1406 := derived1406 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c1261 := derived1261 a h
  have h9 : Entails.eval a c155 := h 154 (by decide)
  have h10 : Entails.eval a c237 := h 236 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c86 := h 85 (by decide)
  have h15 : Entails.eval a c183 := h 182 (by decide)
  have h16 : Entails.eval a c179 := h 178 (by decide)
  have h17 : Entails.eval a c95 := h 94 (by decide)
  have h18 : Entails.eval a c243 := h 242 (by decide)
  have h19 : Entails.eval a c257 := h 256 (by decide)
  have h20 : Entails.eval a c178 := h 177 (by decide)
  have h21 : Entails.eval a c363 := h 362 (by decide)
  have h22 : Entails.eval a c201 := h 200 (by decide)
  have h23 : Entails.eval a c307 := h 306 (by decide)
  have h24 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1848 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨39, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1, some c21, some c155, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1848 : lratChecker f1848 p1848 = .success := by decide +kernel
theorem unsat1848 : Unsatisfiable (PosFin 57) f1848 := by
  apply lratCheckerSound f1848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1848
  · intro a ha; simp [p1848] at ha; subst a; trivial
  · exact checked1848
theorem derived1848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1848 := by
  apply localUnsat_implies_entails f1848 [c1829, c1, c21, c155] c1848 unsat1848 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1849 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1846, some c1835, some c1843, some c1836, some c108, some c135, some c1847, some c27, some c1848, some c262, some c1335, some c1147, some c110, some c1275, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1849 : lratChecker f1849 p1849 = .success := by decide +kernel
theorem unsat1849 : Unsatisfiable (PosFin 57) f1849 := by
  apply lratCheckerSound f1849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1849
  · intro a ha; simp [p1849] at ha; subst a; trivial
  · exact checked1849
theorem derived1849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1849 := by
  apply localUnsat_implies_entails f1849 [c1846, c1835, c1843, c1836, c108, c135, c1847, c27, c1848, c262, c1335, c1147, c110, c1275] c1849 unsat1849 (by rfl) a
  have h0 : Entails.eval a c1846 := derived1846 a h
  have h1 : Entails.eval a c1835 := derived1835 a h
  have h2 : Entails.eval a c1843 := derived1843 a h
  have h3 : Entails.eval a c1836 := derived1836 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c1847 := derived1847 a h
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c1848 := derived1848 a h
  have h9 : Entails.eval a c262 := h 261 (by decide)
  have h10 : Entails.eval a c1335 := derived1335 a h
  have h11 : Entails.eval a c1147 := derived1147 a h
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c1275 := derived1275 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1850 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1835, some c1846, some c1849, some c10, some c199, some c15, some c110, some c1335, some c14, some c1848, some c963, some c76, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1850 : lratChecker f1850 p1850 = .success := by decide +kernel
theorem unsat1850 : Unsatisfiable (PosFin 57) f1850 := by
  apply lratCheckerSound f1850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1850
  · intro a ha; simp [p1850] at ha; subst a; trivial
  · exact checked1850
theorem derived1850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1850 := by
  apply localUnsat_implies_entails f1850 [c1829, c1835, c1846, c1849, c10, c199, c15, c110, c1335, c14, c1848, c963, c76] c1850 unsat1850 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1835 := derived1835 a h
  have h2 : Entails.eval a c1846 := derived1846 a h
  have h3 : Entails.eval a c1849 := derived1849 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c1335 := derived1335 a h
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c1848 := derived1848 a h
  have h11 : Entails.eval a c963 := derived963 a h
  have h12 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1851 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c1843, some c108, some c16, some c1332, some c201, some c110, some c1301, some c1147, some c1469, some c1839, some c83, some c135, some c1404, some c205, some c285, some c230, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1851 : lratChecker f1851 p1851 = .success := by decide +kernel
theorem unsat1851 : Unsatisfiable (PosFin 57) f1851 := by
  apply lratCheckerSound f1851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1851
  · intro a ha; simp [p1851] at ha; subst a; trivial
  · exact checked1851
theorem derived1851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1851 := by
  apply localUnsat_implies_entails f1851 [c7, c1843, c108, c16, c1332, c201, c110, c1301, c1147, c1469, c1839, c83, c135, c1404, c205, c285, c230] c1851 unsat1851 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c1843 := derived1843 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c1301 := derived1301 a h
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c1469 := derived1469 a h
  have h10 : Entails.eval a c1839 := derived1839 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c135 := h 134 (by decide)
  have h13 : Entails.eval a c1404 := derived1404 a h
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c285 := h 284 (by decide)
  have h16 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1852 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1843, some c7, some c268, some c1850, some c1851, some c22, some c32, some c111, some c16, some c158, some c72, some c67, some c348, some c346, some c227, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1852 : lratChecker f1852 p1852 = .success := by decide +kernel
theorem unsat1852 : Unsatisfiable (PosFin 57) f1852 := by
  apply lratCheckerSound f1852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1852
  · intro a ha; simp [p1852] at ha; subst a; trivial
  · exact checked1852
theorem derived1852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1852 := by
  apply localUnsat_implies_entails f1852 [c1829, c1843, c7, c268, c1850, c1851, c22, c32, c111, c16, c158, c72, c67, c348, c346, c227] c1852 unsat1852 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1843 := derived1843 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c1850 := derived1850 a h
  have h5 : Entails.eval a c1851 := derived1851 a h
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c348 := h 347 (by decide)
  have h14 : Entails.eval a c346 := h 345 (by decide)
  have h15 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1853 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1852, some c10, some c1843, some c7, some c268, some c1850, some c15, some c28, some c1019, some c868, some c156, some c63, some c353, some c66, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1853 : lratChecker f1853 p1853 = .success := by decide +kernel
theorem unsat1853 : Unsatisfiable (PosFin 57) f1853 := by
  apply lratCheckerSound f1853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1853
  · intro a ha; simp [p1853] at ha; subst a; trivial
  · exact checked1853
theorem derived1853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1853 := by
  apply localUnsat_implies_entails f1853 [c1829, c1852, c10, c1843, c7, c268, c1850, c15, c28, c1019, c868, c156, c63, c353, c66] c1853 unsat1853 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1852 := derived1852 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c1843 := derived1843 a h
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c1850 := derived1850 a h
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c1019 := derived1019 a h
  have h10 : Entails.eval a c868 := derived868 a h
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c353 := h 352 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1854 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1853, some c1852, some c10, some c1843, some c7, some c268, some c1850, some c110, some c14, some c1489, some c201, some c896, some c120, some c48, some c208, some c715, some c135, some c239, some c237, some c176, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1854 : lratChecker f1854 p1854 = .success := by decide +kernel
theorem unsat1854 : Unsatisfiable (PosFin 57) f1854 := by
  apply lratCheckerSound f1854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1854
  · intro a ha; simp [p1854] at ha; subst a; trivial
  · exact checked1854
theorem derived1854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1854 := by
  apply localUnsat_implies_entails f1854 [c1829, c1853, c1852, c10, c1843, c7, c268, c1850, c110, c14, c1489, c201, c896, c120, c48, c208, c715, c135, c239, c237, c176] c1854 unsat1854 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1853 := derived1853 a h
  have h2 : Entails.eval a c1852 := derived1852 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c1843 := derived1843 a h
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c1850 := derived1850 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c1489 := derived1489 a h
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c896 := derived896 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c48 := h 47 (by decide)
  have h15 : Entails.eval a c208 := h 207 (by decide)
  have h16 : Entails.eval a c715 := derived715 a h
  have h17 : Entails.eval a c135 := h 134 (by decide)
  have h18 : Entails.eval a c239 := h 238 (by decide)
  have h19 : Entails.eval a c237 := h 236 (by decide)
  have h20 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1855 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c7, some c16, some c1083, some c158, some c1597, some c60, some c94, some c186, some c247, some c97, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1855 : lratChecker f1855 p1855 = .success := by decide +kernel
theorem unsat1855 : Unsatisfiable (PosFin 57) f1855 := by
  apply lratCheckerSound f1855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1855
  · intro a ha; simp [p1855] at ha; subst a; trivial
  · exact checked1855
theorem derived1855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1855 := by
  apply localUnsat_implies_entails f1855 [c1829, c7, c16, c1083, c158, c1597, c60, c94, c186, c247, c97] c1855 unsat1855 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c1083 := derived1083 a h
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c1597 := derived1597 a h
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1856 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨34, by decide⟩, false), (⟨17, by decide⟩, false), (⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c201, some c14, some c1147, some c158, some c868, some c160, some c225, some c873, some c55, some c152, some c146, some c319, some c314, some c208, some c117, some c875, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1856 : lratChecker f1856 p1856 = .success := by decide +kernel
theorem unsat1856 : Unsatisfiable (PosFin 57) f1856 := by
  apply lratCheckerSound f1856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1856
  · intro a ha; simp [p1856] at ha; subst a; trivial
  · exact checked1856
theorem derived1856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1856 := by
  apply localUnsat_implies_entails f1856 [c1829, c201, c14, c1147, c158, c868, c160, c225, c873, c55, c152, c146, c319, c314, c208, c117, c875] c1856 unsat1856 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c868 := derived868 a h
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c225 := h 224 (by decide)
  have h8 : Entails.eval a c873 := derived873 a h
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c314 := h 313 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c875 := derived875 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1857 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨34, by decide⟩, false), (⟨17, by decide⟩, false), (⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c201, some c1147, some c14, some c1469, some c89, some c230, some c1856, some c120, some c1094, some c152, some c146, some c319, some c314, some c208, some c287, some c315, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1857 : lratChecker f1857 p1857 = .success := by decide +kernel
theorem unsat1857 : Unsatisfiable (PosFin 57) f1857 := by
  apply lratCheckerSound f1857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1857
  · intro a ha; simp [p1857] at ha; subst a; trivial
  · exact checked1857
theorem derived1857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1857 := by
  apply localUnsat_implies_entails f1857 [c268, c201, c1147, c14, c1469, c89, c230, c1856, c120, c1094, c152, c146, c319, c314, c208, c287, c315] c1857 unsat1857 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c1469 := derived1469 a h
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c230 := h 229 (by decide)
  have h7 : Entails.eval a c1856 := derived1856 a h
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c1094 := derived1094 a h
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c314 := h 313 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c287 := h 286 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1858 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, false), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c14, some c1046, some c315, some c53, some c146, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1858 : lratChecker f1858 p1858 = .success := by decide +kernel
theorem unsat1858 : Unsatisfiable (PosFin 57) f1858 := by
  apply lratCheckerSound f1858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1858
  · intro a ha; simp [p1858] at ha; subst a; trivial
  · exact checked1858
theorem derived1858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1858 := by
  apply localUnsat_implies_entails f1858 [c14, c1046, c315, c53, c146] c1858 unsat1858 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c1046 := derived1046 a h
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1859 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1850, some c1843, some c7, some c268, some c1852, some c10, some c1853, some c1854, some c29, some c22, some c32, some c1855, some c1857, some c1473, some c1858, some c202, some c120, some c131, some c276, some c227, some c153, some c66, some c57, some c353, some c247, some c63, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1859 : lratChecker f1859 p1859 = .success := by decide +kernel
theorem unsat1859 : Unsatisfiable (PosFin 57) f1859 := by
  apply lratCheckerSound f1859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1859
  · intro a ha; simp [p1859] at ha; subst a; trivial
  · exact checked1859
theorem derived1859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1859 := by
  apply localUnsat_implies_entails f1859 [c1829, c1850, c1843, c7, c268, c1852, c10, c1853, c1854, c29, c22, c32, c1855, c1857, c1473, c1858, c202, c120, c131, c276, c227, c153, c66, c57, c353, c247, c63] c1859 unsat1859 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1850 := derived1850 a h
  have h2 : Entails.eval a c1843 := derived1843 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c1852 := derived1852 a h
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c1853 := derived1853 a h
  have h8 : Entails.eval a c1854 := derived1854 a h
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c1855 := derived1855 a h
  have h13 : Entails.eval a c1857 := derived1857 a h
  have h14 : Entails.eval a c1473 := derived1473 a h
  have h15 : Entails.eval a c1858 := derived1858 a h
  have h16 : Entails.eval a c202 := h 201 (by decide)
  have h17 : Entails.eval a c120 := h 119 (by decide)
  have h18 : Entails.eval a c131 := h 130 (by decide)
  have h19 : Entails.eval a c276 := h 275 (by decide)
  have h20 : Entails.eval a c227 := h 226 (by decide)
  have h21 : Entails.eval a c153 := h 152 (by decide)
  have h22 : Entails.eval a c66 := h 65 (by decide)
  have h23 : Entails.eval a c57 := h 56 (by decide)
  have h24 : Entails.eval a c353 := h 352 (by decide)
  have h25 : Entails.eval a c247 := h 246 (by decide)
  have h26 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1860 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨9, by decide⟩, true), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨11, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c135, some c146, some c142, some c81, some c239, some c313, some c1404, some c215, some c316, some c312, some c213, some c292, some c237, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1860 : lratChecker f1860 p1860 = .success := by decide +kernel
theorem unsat1860 : Unsatisfiable (PosFin 57) f1860 := by
  apply lratCheckerSound f1860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1860
  · intro a ha; simp [p1860] at ha; subst a; trivial
  · exact checked1860
theorem derived1860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1860 := by
  apply localUnsat_implies_entails f1860 [c135, c146, c142, c81, c239, c313, c1404, c215, c316, c312, c213, c292, c237] c1860 unsat1860 (by rfl) a
  have h0 : Entails.eval a c135 := h 134 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c239 := h 238 (by decide)
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c1404 := derived1404 a h
  have h7 : Entails.eval a c215 := h 214 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c312 := h 311 (by decide)
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1861 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c45, some c1192, some c208, some c50, some c25, some c166, some c164, some c72, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1861 : lratChecker f1861 p1861 = .success := by decide +kernel
theorem unsat1861 : Unsatisfiable (PosFin 57) f1861 := by
  apply lratCheckerSound f1861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1861
  · intro a ha; simp [p1861] at ha; subst a; trivial
  · exact checked1861
theorem derived1861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1861 := by
  apply localUnsat_implies_entails f1861 [c108, c45, c1192, c208, c50, c25, c166, c164, c72] c1861 unsat1861 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c1192 := derived1192 a h
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1862 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1859, some c1850, some c1843, some c108, some c1406, some c885, some c1, some c11, some c201, some c1147, some c1861, some c135, some c146, some c142, some c1860, some c81, some c313, some c27, some c36, some c1404, some c120, some c215, some c168, some c237, some c1301, some c316, some c868, some c1601, some c312, some c269, some c28, some c293, some c292, some c353, some c5, some c67, some c57, some c368, some c332, some c158, some c298, some c297, some c178, some c104, some c62, some c357, some c624, some c186, some c340, some c406, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]]
theorem checked1862 : lratChecker f1862 p1862 = .success := by decide +kernel
theorem unsat1862 : Unsatisfiable (PosFin 57) f1862 := by
  apply lratCheckerSound f1862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1862
  · intro a ha; simp [p1862] at ha; subst a; trivial
  · exact checked1862
theorem derived1862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1862 := by
  apply localUnsat_implies_entails f1862 [c1829, c1859, c1850, c1843, c108, c1406, c885, c1, c11, c201, c1147, c1861, c135, c146, c142, c1860, c81, c313, c27, c36, c1404, c120, c215, c168, c237, c1301, c316, c868, c1601, c312, c269, c28, c293, c292, c353, c5, c67, c57, c368, c332, c158, c298, c297, c178, c104, c62, c357, c624, c186, c340, c406] c1862 unsat1862 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1859 := derived1859 a h
  have h2 : Entails.eval a c1850 := derived1850 a h
  have h3 : Entails.eval a c1843 := derived1843 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1406 := derived1406 a h
  have h6 : Entails.eval a c885 := derived885 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c1147 := derived1147 a h
  have h11 : Entails.eval a c1861 := derived1861 a h
  have h12 : Entails.eval a c135 := h 134 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c142 := h 141 (by decide)
  have h15 : Entails.eval a c1860 := derived1860 a h
  have h16 : Entails.eval a c81 := h 80 (by decide)
  have h17 : Entails.eval a c313 := h 312 (by decide)
  have h18 : Entails.eval a c27 := h 26 (by decide)
  have h19 : Entails.eval a c36 := h 35 (by decide)
  have h20 : Entails.eval a c1404 := derived1404 a h
  have h21 : Entails.eval a c120 := h 119 (by decide)
  have h22 : Entails.eval a c215 := h 214 (by decide)
  have h23 : Entails.eval a c168 := h 167 (by decide)
  have h24 : Entails.eval a c237 := h 236 (by decide)
  have h25 : Entails.eval a c1301 := derived1301 a h
  have h26 : Entails.eval a c316 := h 315 (by decide)
  have h27 : Entails.eval a c868 := derived868 a h
  have h28 : Entails.eval a c1601 := derived1601 a h
  have h29 : Entails.eval a c312 := h 311 (by decide)
  have h30 : Entails.eval a c269 := h 268 (by decide)
  have h31 : Entails.eval a c28 := h 27 (by decide)
  have h32 : Entails.eval a c293 := h 292 (by decide)
  have h33 : Entails.eval a c292 := h 291 (by decide)
  have h34 : Entails.eval a c353 := h 352 (by decide)
  have h35 : Entails.eval a c5 := h 4 (by decide)
  have h36 : Entails.eval a c67 := h 66 (by decide)
  have h37 : Entails.eval a c57 := h 56 (by decide)
  have h38 : Entails.eval a c368 := h 367 (by decide)
  have h39 : Entails.eval a c332 := h 331 (by decide)
  have h40 : Entails.eval a c158 := h 157 (by decide)
  have h41 : Entails.eval a c298 := h 297 (by decide)
  have h42 : Entails.eval a c297 := h 296 (by decide)
  have h43 : Entails.eval a c178 := h 177 (by decide)
  have h44 : Entails.eval a c104 := h 103 (by decide)
  have h45 : Entails.eval a c62 := h 61 (by decide)
  have h46 : Entails.eval a c357 := h 356 (by decide)
  have h47 : Entails.eval a c624 := derived624 a h
  have h48 : Entails.eval a c186 := h 185 (by decide)
  have h49 : Entails.eval a c340 := h 339 (by decide)
  have h50 : Entails.eval a c406 := h 405 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1863 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1859, some c1850, some c1843, some c1862, some c22, some c33, some c268, some c885, some c32, some c111, some c11, some c158, some c72, some c67, some c348, some c346, some c227, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1863 : lratChecker f1863 p1863 = .success := by decide +kernel
theorem unsat1863 : Unsatisfiable (PosFin 57) f1863 := by
  apply lratCheckerSound f1863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1863
  · intro a ha; simp [p1863] at ha; subst a; trivial
  · exact checked1863
theorem derived1863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1863 := by
  apply localUnsat_implies_entails f1863 [c1829, c1859, c1850, c1843, c1862, c22, c33, c268, c885, c32, c111, c11, c158, c72, c67, c348, c346, c227] c1863 unsat1863 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1859 := derived1859 a h
  have h2 : Entails.eval a c1850 := derived1850 a h
  have h3 : Entails.eval a c1843 := derived1843 a h
  have h4 : Entails.eval a c1862 := derived1862 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c885 := derived885 a h
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c348 := h 347 (by decide)
  have h16 : Entails.eval a c346 := h 345 (by decide)
  have h17 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1864 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1843, some c1850, some c1859, some c1863, some c10, some c885, some c1474, some c268, some c267, some c14, some c33, some c1211, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1864 : lratChecker f1864 p1864 = .success := by decide +kernel
theorem unsat1864 : Unsatisfiable (PosFin 57) f1864 := by
  apply lratCheckerSound f1864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1864
  · intro a ha; simp [p1864] at ha; subst a; trivial
  · exact checked1864
theorem derived1864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1864 := by
  apply localUnsat_implies_entails f1864 [c1829, c1843, c1850, c1859, c1863, c10, c885, c1474, c268, c267, c14, c33, c1211] c1864 unsat1864 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1843 := derived1843 a h
  have h2 : Entails.eval a c1850 := derived1850 a h
  have h3 : Entails.eval a c1859 := derived1859 a h
  have h4 : Entails.eval a c1863 := derived1863 a h
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c885 := derived885 a h
  have h7 : Entails.eval a c1474 := derived1474 a h
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c1211 := derived1211 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1865 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c108, some c111, some c29, some c32, some c261, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1865 : lratChecker f1865 p1865 = .success := by decide +kernel
theorem unsat1865 : Unsatisfiable (PosFin 57) f1865 := by
  apply lratCheckerSound f1865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1865
  · intro a ha; simp [p1865] at ha; subst a; trivial
  · exact checked1865
theorem derived1865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1865 := by
  apply localUnsat_implies_entails f1865 [c1829, c108, c111, c29, c32, c261] c1865 unsat1865 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1866 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c20, some c7, some c1864, some c200, some c16, some c1865, some c30, some c21, some c963, some c1744, some c76, some c70, some c346, some c157, some c220, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1866 : lratChecker f1866 p1866 = .success := by decide +kernel
theorem unsat1866 : Unsatisfiable (PosFin 57) f1866 := by
  apply lratCheckerSound f1866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1866
  · intro a ha; simp [p1866] at ha; subst a; trivial
  · exact checked1866
theorem derived1866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1866 := by
  apply localUnsat_implies_entails f1866 [c1829, c20, c7, c1864, c200, c16, c1865, c30, c21, c963, c1744, c76, c70, c346, c157, c220] c1866 unsat1866 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c1864 := derived1864 a h
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c1865 := derived1865 a h
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c963 := derived963 a h
  have h10 : Entails.eval a c1744 := derived1744 a h
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c346 := h 345 (by decide)
  have h14 : Entails.eval a c157 := h 156 (by decide)
  have h15 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1867 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c7, some c1864, some c200, some c16, some c1865, some c20, some c202, some c1866, some c263, some c261, some c131, some c1496, some c23, some c66, some c59, some c70, some c185, some c255, some c190, some c159, some c63, some c337, some c346, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1867 : lratChecker f1867 p1867 = .success := by decide +kernel
theorem unsat1867 : Unsatisfiable (PosFin 57) f1867 := by
  apply lratCheckerSound f1867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1867
  · intro a ha; simp [p1867] at ha; subst a; trivial
  · exact checked1867
theorem derived1867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1867 := by
  apply localUnsat_implies_entails f1867 [c1829, c7, c1864, c200, c16, c1865, c20, c202, c1866, c263, c261, c131, c1496, c23, c66, c59, c70, c185, c255, c190, c159, c63, c337, c346] c1867 unsat1867 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c1864 := derived1864 a h
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c1865 := derived1865 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c1866 := derived1866 a h
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c1496 := derived1496 a h
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c185 := h 184 (by decide)
  have h18 : Entails.eval a c255 := h 254 (by decide)
  have h19 : Entails.eval a c190 := h 189 (by decide)
  have h20 : Entails.eval a c159 := h 158 (by decide)
  have h21 : Entails.eval a c63 := h 62 (by decide)
  have h22 : Entails.eval a c337 := h 336 (by decide)
  have h23 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1868 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1864, some c200, some c7, some c16, some c1865, some c1867, some c109, some c22, some c157, some c23, some c59, some c185, some c255, some c97, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1868 : lratChecker f1868 p1868 = .success := by decide +kernel
theorem unsat1868 : Unsatisfiable (PosFin 57) f1868 := by
  apply lratCheckerSound f1868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1868
  · intro a ha; simp [p1868] at ha; subst a; trivial
  · exact checked1868
theorem derived1868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1868 := by
  apply localUnsat_implies_entails f1868 [c1864, c200, c7, c16, c1865, c1867, c109, c22, c157, c23, c59, c185, c255, c97] c1868 unsat1868 (by rfl) a
  have h0 : Entails.eval a c1864 := derived1864 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c1865 := derived1865 a h
  have h5 : Entails.eval a c1867 := derived1867 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c157 := h 156 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c185 := h 184 (by decide)
  have h12 : Entails.eval a c255 := h 254 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1869 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1868, some c1864, some c204, some c200, some c108, some c11, some c1294, some c110, some c1386, some c199, some c263, some c1836, some c21, some c1848, some c206, some c72, some c76, some c270, some c963, some c138, some c243, some c331, some c177, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1869 : lratChecker f1869 p1869 = .success := by decide +kernel
theorem unsat1869 : Unsatisfiable (PosFin 57) f1869 := by
  apply lratCheckerSound f1869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1869
  · intro a ha; simp [p1869] at ha; subst a; trivial
  · exact checked1869
theorem derived1869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1869 := by
  apply localUnsat_implies_entails f1869 [c1829, c1868, c1864, c204, c200, c108, c11, c1294, c110, c1386, c199, c263, c1836, c21, c1848, c206, c72, c76, c270, c963, c138, c243, c331, c177] c1869 unsat1869 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1868 := derived1868 a h
  have h2 : Entails.eval a c1864 := derived1864 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c1386 := derived1386 a h
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c1836 := derived1836 a h
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c1848 := derived1848 a h
  have h15 : Entails.eval a c206 := h 205 (by decide)
  have h16 : Entails.eval a c72 := h 71 (by decide)
  have h17 : Entails.eval a c76 := h 75 (by decide)
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c963 := derived963 a h
  have h20 : Entails.eval a c138 := h 137 (by decide)
  have h21 : Entails.eval a c243 := h 242 (by decide)
  have h22 : Entails.eval a c331 := h 330 (by decide)
  have h23 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1870 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1868, some c1864, some c204, some c200, some c108, some c11, some c1294, some c110, some c1386, some c199, some c4, some c1869, some c885, some c120, some c261, some c48, some c21, some c1848, some c205, some c63, some c72, some c76, some c270, some c272, some c314, some c191, some c183, some c258, some c963, some c350, some c138, some c150, some c223, some c95, some c562, some c474, some c18, some c331, some c321, some c50, some c269, some c177, some c136, some c355, some c344, some c371, some c86, some c289, some c407, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]]
theorem checked1870 : lratChecker f1870 p1870 = .success := by decide +kernel
theorem unsat1870 : Unsatisfiable (PosFin 57) f1870 := by
  apply lratCheckerSound f1870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1870
  · intro a ha; simp [p1870] at ha; subst a; trivial
  · exact checked1870
theorem derived1870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1870 := by
  apply localUnsat_implies_entails f1870 [c1829, c1868, c1864, c204, c200, c108, c11, c1294, c110, c1386, c199, c4, c1869, c885, c120, c261, c48, c21, c1848, c205, c63, c72, c76, c270, c272, c314, c191, c183, c258, c963, c350, c138, c150, c223, c95, c562, c474, c18, c331, c321, c50, c269, c177, c136, c355, c344, c371, c86, c289, c407] c1870 unsat1870 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1868 := derived1868 a h
  have h2 : Entails.eval a c1864 := derived1864 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c1386 := derived1386 a h
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c1869 := derived1869 a h
  have h13 : Entails.eval a c885 := derived885 a h
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  have h16 : Entails.eval a c48 := h 47 (by decide)
  have h17 : Entails.eval a c21 := h 20 (by decide)
  have h18 : Entails.eval a c1848 := derived1848 a h
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c63 := h 62 (by decide)
  have h21 : Entails.eval a c72 := h 71 (by decide)
  have h22 : Entails.eval a c76 := h 75 (by decide)
  have h23 : Entails.eval a c270 := h 269 (by decide)
  have h24 : Entails.eval a c272 := h 271 (by decide)
  have h25 : Entails.eval a c314 := h 313 (by decide)
  have h26 : Entails.eval a c191 := h 190 (by decide)
  have h27 : Entails.eval a c183 := h 182 (by decide)
  have h28 : Entails.eval a c258 := h 257 (by decide)
  have h29 : Entails.eval a c963 := derived963 a h
  have h30 : Entails.eval a c350 := h 349 (by decide)
  have h31 : Entails.eval a c138 := h 137 (by decide)
  have h32 : Entails.eval a c150 := h 149 (by decide)
  have h33 : Entails.eval a c223 := h 222 (by decide)
  have h34 : Entails.eval a c95 := h 94 (by decide)
  have h35 : Entails.eval a c562 := derived562 a h
  have h36 : Entails.eval a c474 := derived474 a h
  have h37 : Entails.eval a c18 := h 17 (by decide)
  have h38 : Entails.eval a c331 := h 330 (by decide)
  have h39 : Entails.eval a c321 := h 320 (by decide)
  have h40 : Entails.eval a c50 := h 49 (by decide)
  have h41 : Entails.eval a c269 := h 268 (by decide)
  have h42 : Entails.eval a c177 := h 176 (by decide)
  have h43 : Entails.eval a c136 := h 135 (by decide)
  have h44 : Entails.eval a c355 := h 354 (by decide)
  have h45 : Entails.eval a c344 := h 343 (by decide)
  have h46 : Entails.eval a c371 := h 370 (by decide)
  have h47 : Entails.eval a c86 := h 85 (by decide)
  have h48 : Entails.eval a c289 := h 288 (by decide)
  have h49 : Entails.eval a c407 := h 406 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1871 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1864, some c200, some c108, some c11, some c1294, some c110, some c4, some c1868, some c1870, some c268, some c1597, some c885, some c263, some c21, some c1848, some c63, some c72, some c76, some c260, some c347, some c350, some c340, some c220, some c352, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1871 : lratChecker f1871 p1871 = .success := by decide +kernel
theorem unsat1871 : Unsatisfiable (PosFin 57) f1871 := by
  apply lratCheckerSound f1871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1871
  · intro a ha; simp [p1871] at ha; subst a; trivial
  · exact checked1871
theorem derived1871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1871 := by
  apply localUnsat_implies_entails f1871 [c1829, c1864, c200, c108, c11, c1294, c110, c4, c1868, c1870, c268, c1597, c885, c263, c21, c1848, c63, c72, c76, c260, c347, c350, c340, c220, c352] c1871 unsat1871 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1864 := derived1864 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c1294 := derived1294 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c1868 := derived1868 a h
  have h9 : Entails.eval a c1870 := derived1870 a h
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c1597 := derived1597 a h
  have h12 : Entails.eval a c885 := derived885 a h
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c21 := h 20 (by decide)
  have h15 : Entails.eval a c1848 := derived1848 a h
  have h16 : Entails.eval a c63 := h 62 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c76 := h 75 (by decide)
  have h19 : Entails.eval a c260 := h 259 (by decide)
  have h20 : Entails.eval a c347 := h 346 (by decide)
  have h21 : Entails.eval a c350 := h 349 (by decide)
  have h22 : Entails.eval a c340 := h 339 (by decide)
  have h23 : Entails.eval a c220 := h 219 (by decide)
  have h24 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1872 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1864, some c1868, some c204, some c200, some c108, some c11, some c1294, some c110, some c1386, some c1871, some c27, some c1848, some c155, some c57, some c183, some c246, some c104, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1872 : lratChecker f1872 p1872 = .success := by decide +kernel
theorem unsat1872 : Unsatisfiable (PosFin 57) f1872 := by
  apply lratCheckerSound f1872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1872
  · intro a ha; simp [p1872] at ha; subst a; trivial
  · exact checked1872
theorem derived1872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1872 := by
  apply localUnsat_implies_entails f1872 [c1829, c1864, c1868, c204, c200, c108, c11, c1294, c110, c1386, c1871, c27, c1848, c155, c57, c183, c246, c104] c1872 unsat1872 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1864 := derived1864 a h
  have h2 : Entails.eval a c1868 := derived1868 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c1386 := derived1386 a h
  have h10 : Entails.eval a c1871 := derived1871 a h
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c1848 := derived1848 a h
  have h13 : Entails.eval a c155 := h 154 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c183 := h 182 (by decide)
  have h16 : Entails.eval a c246 := h 245 (by decide)
  have h17 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1873 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1868, some c1864, some c200, some c1872, some c29, some c33, some c1835, some c261, some c1865, some c885, some c11, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1873 : lratChecker f1873 p1873 = .success := by decide +kernel
theorem unsat1873 : Unsatisfiable (PosFin 57) f1873 := by
  apply lratCheckerSound f1873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1873
  · intro a ha; simp [p1873] at ha; subst a; trivial
  · exact checked1873
theorem derived1873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1873 := by
  apply localUnsat_implies_entails f1873 [c1829, c1868, c1864, c200, c1872, c29, c33, c1835, c261, c1865, c885, c11] c1873 unsat1873 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1868 := derived1868 a h
  have h2 : Entails.eval a c1864 := derived1864 a h
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c1872 := derived1872 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c1835 := derived1835 a h
  have h8 : Entails.eval a c261 := h 260 (by decide)
  have h9 : Entails.eval a c1865 := derived1865 a h
  have h10 : Entails.eval a c885 := derived885 a h
  have h11 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1874 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1, some c30, some c1848, some c63, some c255, some c183, some c94, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1874 : lratChecker f1874 p1874 = .success := by decide +kernel
theorem unsat1874 : Unsatisfiable (PosFin 57) f1874 := by
  apply lratCheckerSound f1874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1874
  · intro a ha; simp [p1874] at ha; subst a; trivial
  · exact checked1874
theorem derived1874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1874 := by
  apply localUnsat_implies_entails f1874 [c1829, c1, c30, c1848, c63, c255, c183, c94] c1874 unsat1874 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c1848 := derived1848 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c255 := h 254 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  have h7 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1875 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1874, some c263, some c261, some c885, some c131, some c5, some c117, some c11, some c202, some c52, some c116, some c136, some c1362, some c88, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1875 : lratChecker f1875 p1875 = .success := by decide +kernel
theorem unsat1875 : Unsatisfiable (PosFin 57) f1875 := by
  apply lratCheckerSound f1875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1875
  · intro a ha; simp [p1875] at ha; subst a; trivial
  · exact checked1875
theorem derived1875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1875 := by
  apply localUnsat_implies_entails f1875 [c1829, c1874, c263, c261, c885, c131, c5, c117, c11, c202, c52, c116, c136, c1362, c88] c1875 unsat1875 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1874 := derived1874 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c885 := derived885 a h
  have h5 : Entails.eval a c131 := h 130 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  have h13 : Entails.eval a c1362 := derived1362 a h
  have h14 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1876 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c200, some c204, some c1875, some c27, some c163, some c66, some c348, some c346, some c23, some c1848, some c1335, some c1593, some c227, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1876 : lratChecker f1876 p1876 = .success := by decide +kernel
theorem unsat1876 : Unsatisfiable (PosFin 57) f1876 := by
  apply lratCheckerSound f1876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1876
  · intro a ha; simp [p1876] at ha; subst a; trivial
  · exact checked1876
theorem derived1876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1876 := by
  apply localUnsat_implies_entails f1876 [c1829, c200, c204, c1875, c27, c163, c66, c348, c346, c23, c1848, c1335, c1593, c227] c1876 unsat1876 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c1875 := derived1875 a h
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c163 := h 162 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c348 := h 347 (by decide)
  have h8 : Entails.eval a c346 := h 345 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c1848 := derived1848 a h
  have h11 : Entails.eval a c1335 := derived1335 a h
  have h12 : Entails.eval a c1593 := derived1593 a h
  have h13 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1877 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1864, some c200, some c1868, some c204, some c1873, some c1875, some c27, some c163, some c66, some c155, some c11, some c1876, some c33, some c109, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1877 : lratChecker f1877 p1877 = .success := by decide +kernel
theorem unsat1877 : Unsatisfiable (PosFin 57) f1877 := by
  apply lratCheckerSound f1877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1877
  · intro a ha; simp [p1877] at ha; subst a; trivial
  · exact checked1877
theorem derived1877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1877 := by
  apply localUnsat_implies_entails f1877 [c1829, c1864, c200, c1868, c204, c1873, c1875, c27, c163, c66, c155, c11, c1876, c33, c109] c1877 unsat1877 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1864 := derived1864 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c1868 := derived1868 a h
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c1873 := derived1873 a h
  have h6 : Entails.eval a c1875 := derived1875 a h
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c1876 := derived1876 a h
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1878 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1877, some c114, some c819, some c317, some c2, some c48, some c7, some c108, some c45, some c1320, some c1373, some c124, some c1406, some c261, some c1312, some c206, some c1, some c272, some c314, some c28, some c139, some c152, some c244, some c242, some c198, some c179, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1878 : lratChecker f1878 p1878 = .success := by decide +kernel
theorem unsat1878 : Unsatisfiable (PosFin 57) f1878 := by
  apply lratCheckerSound f1878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1878
  · intro a ha; simp [p1878] at ha; subst a; trivial
  · exact checked1878
theorem derived1878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1878 := by
  apply localUnsat_implies_entails f1878 [c1829, c1877, c114, c819, c317, c2, c48, c7, c108, c45, c1320, c1373, c124, c1406, c261, c1312, c206, c1, c272, c314, c28, c139, c152, c244, c242, c198, c179] c1878 unsat1878 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1877 := derived1877 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c819 := derived819 a h
  have h4 : Entails.eval a c317 := h 316 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c1320 := derived1320 a h
  have h11 : Entails.eval a c1373 := derived1373 a h
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c1406 := derived1406 a h
  have h14 : Entails.eval a c261 := h 260 (by decide)
  have h15 : Entails.eval a c1312 := derived1312 a h
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c1 := h 0 (by decide)
  have h18 : Entails.eval a c272 := h 271 (by decide)
  have h19 : Entails.eval a c314 := h 313 (by decide)
  have h20 : Entails.eval a c28 := h 27 (by decide)
  have h21 : Entails.eval a c139 := h 138 (by decide)
  have h22 : Entails.eval a c152 := h 151 (by decide)
  have h23 : Entails.eval a c244 := h 243 (by decide)
  have h24 : Entails.eval a c242 := h 241 (by decide)
  have h25 : Entails.eval a c198 := h 197 (by decide)
  have h26 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1879 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1878, some c1877, some c2, some c114, some c819, some c48, some c7, some c753, some c263, some c30, some c21, some c268, some c124, some c153, some c220, some c276, some c71, some c349, some c73, some c109, some c20, some c1490, some c1480, some c963, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1879 : lratChecker f1879 p1879 = .success := by decide +kernel
theorem unsat1879 : Unsatisfiable (PosFin 57) f1879 := by
  apply lratCheckerSound f1879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1879
  · intro a ha; simp [p1879] at ha; subst a; trivial
  · exact checked1879
theorem derived1879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1879 := by
  apply localUnsat_implies_entails f1879 [c1829, c1878, c1877, c2, c114, c819, c48, c7, c753, c263, c30, c21, c268, c124, c153, c220, c276, c71, c349, c73, c109, c20, c1490, c1480, c963] c1879 unsat1879 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1878 := derived1878 a h
  have h2 : Entails.eval a c1877 := derived1877 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c819 := derived819 a h
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c753 := derived753 a h
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c30 := h 29 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c153 := h 152 (by decide)
  have h15 : Entails.eval a c220 := h 219 (by decide)
  have h16 : Entails.eval a c276 := h 275 (by decide)
  have h17 : Entails.eval a c71 := h 70 (by decide)
  have h18 : Entails.eval a c349 := h 348 (by decide)
  have h19 : Entails.eval a c73 := h 72 (by decide)
  have h20 : Entails.eval a c109 := h 108 (by decide)
  have h21 : Entails.eval a c20 := h 19 (by decide)
  have h22 : Entails.eval a c1490 := derived1490 a h
  have h23 : Entails.eval a c1480 := derived1480 a h
  have h24 : Entails.eval a c963 := derived963 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1880 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1877, some c114, some c2, some c819, some c7, some c48, some c1878, some c1879, some c28, some c8, some c35, some c276, some c1019, some c268, some c220, some c63, some c353, some c346, some c66, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1880 : lratChecker f1880 p1880 = .success := by decide +kernel
theorem unsat1880 : Unsatisfiable (PosFin 57) f1880 := by
  apply lratCheckerSound f1880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1880
  · intro a ha; simp [p1880] at ha; subst a; trivial
  · exact checked1880
theorem derived1880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1880 := by
  apply localUnsat_implies_entails f1880 [c1829, c1877, c114, c2, c819, c7, c48, c1878, c1879, c28, c8, c35, c276, c1019, c268, c220, c63, c353, c346, c66] c1880 unsat1880 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1877 := derived1877 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c819 := derived819 a h
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c1878 := derived1878 a h
  have h8 : Entails.eval a c1879 := derived1879 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c1019 := derived1019 a h
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c220 := h 219 (by decide)
  have h16 : Entails.eval a c63 := h 62 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c346 := h 345 (by decide)
  have h19 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1881 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c340, some c339, some c347, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1881 : lratChecker f1881 p1881 = .success := by decide +kernel
theorem unsat1881 : Unsatisfiable (PosFin 57) f1881 := by
  apply lratCheckerSound f1881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1881
  · intro a ha; simp [p1881] at ha; subst a; trivial
  · exact checked1881
theorem derived1881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1881 := by
  apply localUnsat_implies_entails f1881 [c340, c339, c347] c1881 unsat1881 (by rfl) a
  have h0 : Entails.eval a c340 := h 339 (by decide)
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1882 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1877, some c2, some c114, some c45, some c108, some c1880, some c263, some c1, some c21, some c1848, some c31, some c197, some c1261, some c63, some c72, some c124, some c260, some c183, some c258, some c1406, some c95, some c115, some c257, some c191, some c1881, some c352, some c344, some c343, some c347, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1882 : lratChecker f1882 p1882 = .success := by decide +kernel
theorem unsat1882 : Unsatisfiable (PosFin 57) f1882 := by
  apply lratCheckerSound f1882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1882
  · intro a ha; simp [p1882] at ha; subst a; trivial
  · exact checked1882
theorem derived1882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1882 := by
  apply localUnsat_implies_entails f1882 [c1829, c1877, c2, c114, c45, c108, c1880, c263, c1, c21, c1848, c31, c197, c1261, c63, c72, c124, c260, c183, c258, c1406, c95, c115, c257, c191, c1881, c352, c344, c343, c347] c1882 unsat1882 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1877 := derived1877 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1880 := derived1880 a h
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c1848 := derived1848 a h
  have h11 : Entails.eval a c31 := h 30 (by decide)
  have h12 : Entails.eval a c197 := h 196 (by decide)
  have h13 : Entails.eval a c1261 := derived1261 a h
  have h14 : Entails.eval a c63 := h 62 (by decide)
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c124 := h 123 (by decide)
  have h17 : Entails.eval a c260 := h 259 (by decide)
  have h18 : Entails.eval a c183 := h 182 (by decide)
  have h19 : Entails.eval a c258 := h 257 (by decide)
  have h20 : Entails.eval a c1406 := derived1406 a h
  have h21 : Entails.eval a c95 := h 94 (by decide)
  have h22 : Entails.eval a c115 := h 114 (by decide)
  have h23 : Entails.eval a c257 := h 256 (by decide)
  have h24 : Entails.eval a c191 := h 190 (by decide)
  have h25 : Entails.eval a c1881 := derived1881 a h
  have h26 : Entails.eval a c352 := h 351 (by decide)
  have h27 : Entails.eval a c344 := h 343 (by decide)
  have h28 : Entails.eval a c343 := h 342 (by decide)
  have h29 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1883 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1877, some c2, some c114, some c45, some c108, some c1880, some c115, some c211, some c48, some c8, some c1327, some c199, some c1, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1883 : lratChecker f1883 p1883 = .success := by decide +kernel
theorem unsat1883 : Unsatisfiable (PosFin 57) f1883 := by
  apply lratCheckerSound f1883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1883
  · intro a ha; simp [p1883] at ha; subst a; trivial
  · exact checked1883
theorem derived1883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1883 := by
  apply localUnsat_implies_entails f1883 [c1829, c1877, c2, c114, c45, c108, c1880, c115, c211, c48, c8, c1327, c199, c1] c1883 unsat1883 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1877 := derived1877 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1880 := derived1880 a h
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c1327 := derived1327 a h
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1884 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨14, by decide⟩, false), (⟨12, by decide⟩, false), (⟨17, by decide⟩, false), (⟨13, by decide⟩, false), (⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c63, some c72, some c247, some c194, some c164, some c165, some c95, some c343, some c193, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1884 : lratChecker f1884 p1884 = .success := by decide +kernel
theorem unsat1884 : Unsatisfiable (PosFin 57) f1884 := by
  apply lratCheckerSound f1884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1884
  · intro a ha; simp [p1884] at ha; subst a; trivial
  · exact checked1884
theorem derived1884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1884 := by
  apply localUnsat_implies_entails f1884 [c1829, c63, c72, c247, c194, c164, c165, c95, c343, c193] c1884 unsat1884 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c247 := h 246 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c165 := h 164 (by decide)
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c343 := h 342 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1885 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1877, some c2, some c114, some c45, some c108, some c1880, some c1882, some c1883, some c268, some c885, some c124, some c1, some c11, some c204, some c1860, some c1884, some c166, some c220, some c227, some c276, some c168, some c120, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1885 : lratChecker f1885 p1885 = .success := by decide +kernel
theorem unsat1885 : Unsatisfiable (PosFin 57) f1885 := by
  apply lratCheckerSound f1885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1885
  · intro a ha; simp [p1885] at ha; subst a; trivial
  · exact checked1885
theorem derived1885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1885 := by
  apply localUnsat_implies_entails f1885 [c1829, c1877, c2, c114, c45, c108, c1880, c1882, c1883, c268, c885, c124, c1, c11, c204, c1860, c1884, c166, c220, c227, c276, c168, c120] c1885 unsat1885 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1877 := derived1877 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1880 := derived1880 a h
  have h7 : Entails.eval a c1882 := derived1882 a h
  have h8 : Entails.eval a c1883 := derived1883 a h
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c885 := derived885 a h
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c204 := h 203 (by decide)
  have h15 : Entails.eval a c1860 := derived1860 a h
  have h16 : Entails.eval a c1884 := derived1884 a h
  have h17 : Entails.eval a c166 := h 165 (by decide)
  have h18 : Entails.eval a c220 := h 219 (by decide)
  have h19 : Entails.eval a c227 := h 226 (by decide)
  have h20 : Entails.eval a c276 := h 275 (by decide)
  have h21 : Entails.eval a c168 := h 167 (by decide)
  have h22 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1886 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1880, some c1885, some c27, some c1848, some c1877, some c2, some c114, some c45, some c108, some c1335, some c262, some c47, some c216, some c210, some c1406, some c124, some c214, some c204, some c197, some c312, some c142, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1886 : lratChecker f1886 p1886 = .success := by decide +kernel
theorem unsat1886 : Unsatisfiable (PosFin 57) f1886 := by
  apply lratCheckerSound f1886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1886
  · intro a ha; simp [p1886] at ha; subst a; trivial
  · exact checked1886
theorem derived1886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1886 := by
  apply localUnsat_implies_entails f1886 [c1880, c1885, c27, c1848, c1877, c2, c114, c45, c108, c1335, c262, c47, c216, c210, c1406, c124, c214, c204, c197, c312, c142] c1886 unsat1886 (by rfl) a
  have h0 : Entails.eval a c1880 := derived1880 a h
  have h1 : Entails.eval a c1885 := derived1885 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c1848 := derived1848 a h
  have h4 : Entails.eval a c1877 := derived1877 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c1335 := derived1335 a h
  have h10 : Entails.eval a c262 := h 261 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c216 := h 215 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c1406 := derived1406 a h
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c214 := h 213 (by decide)
  have h17 : Entails.eval a c204 := h 203 (by decide)
  have h18 : Entails.eval a c197 := h 196 (by decide)
  have h19 : Entails.eval a c312 := h 311 (by decide)
  have h20 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1887 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1880, some c1877, some c114, some c2, some c108, some c1885, some c1886, some c1883, some c1406, some c124, some c204, some c1601, some c8, some c1336, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1887 : lratChecker f1887 p1887 = .success := by decide +kernel
theorem unsat1887 : Unsatisfiable (PosFin 57) f1887 := by
  apply lratCheckerSound f1887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1887
  · intro a ha; simp [p1887] at ha; subst a; trivial
  · exact checked1887
theorem derived1887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1887 := by
  apply localUnsat_implies_entails f1887 [c1880, c1877, c114, c2, c108, c1885, c1886, c1883, c1406, c124, c204, c1601, c8, c1336] c1887 unsat1887 (by rfl) a
  have h0 : Entails.eval a c1880 := derived1880 a h
  have h1 : Entails.eval a c1877 := derived1877 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1885 := derived1885 a h
  have h6 : Entails.eval a c1886 := derived1886 a h
  have h7 : Entails.eval a c1883 := derived1883 a h
  have h8 : Entails.eval a c1406 := derived1406 a h
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c1601 := derived1601 a h
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c1336 := derived1336 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1888 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1887, some c1880, some c1877, some c1874, some c263, some c261, some c885, some c124, some c10, some c204, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1888 : lratChecker f1888 p1888 = .success := by decide +kernel
theorem unsat1888 : Unsatisfiable (PosFin 57) f1888 := by
  apply lratCheckerSound f1888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1888
  · intro a ha; simp [p1888] at ha; subst a; trivial
  · exact checked1888
theorem derived1888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1888 := by
  apply localUnsat_implies_entails f1888 [c1829, c1887, c1880, c1877, c1874, c263, c261, c885, c124, c10, c204] c1888 unsat1888 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1887 := derived1887 a h
  have h2 : Entails.eval a c1880 := derived1880 a h
  have h3 : Entails.eval a c1877 := derived1877 a h
  have h4 : Entails.eval a c1874 := derived1874 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c885 := derived885 a h
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1889 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1887, some c1880, some c1877, some c1888, some c27, some c1848, some c1595, some c2, some c109, some c110, some c1574, some c1406, some c197, some c124, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1889 : lratChecker f1889 p1889 = .success := by decide +kernel
theorem unsat1889 : Unsatisfiable (PosFin 57) f1889 := by
  apply lratCheckerSound f1889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1889
  · intro a ha; simp [p1889] at ha; subst a; trivial
  · exact checked1889
theorem derived1889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1889 := by
  apply localUnsat_implies_entails f1889 [c1887, c1880, c1877, c1888, c27, c1848, c1595, c2, c109, c110, c1574, c1406, c197, c124] c1889 unsat1889 (by rfl) a
  have h0 : Entails.eval a c1887 := derived1887 a h
  have h1 : Entails.eval a c1880 := derived1880 a h
  have h2 : Entails.eval a c1877 := derived1877 a h
  have h3 : Entails.eval a c1888 := derived1888 a h
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c1848 := derived1848 a h
  have h6 : Entails.eval a c1595 := derived1595 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c1574 := derived1574 a h
  have h11 : Entails.eval a c1406 := derived1406 a h
  have h12 : Entails.eval a c197 := h 196 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1890 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1877, some c2, some c114, some c1880, some c1887, some c1888, some c27, some c1848, some c1595, some c1889, some c1335, some c1609, some c48, some c1596, some c120, some c124, some c1601, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1890 : lratChecker f1890 p1890 = .success := by decide +kernel
theorem unsat1890 : Unsatisfiable (PosFin 57) f1890 := by
  apply lratCheckerSound f1890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1890
  · intro a ha; simp [p1890] at ha; subst a; trivial
  · exact checked1890
theorem derived1890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1890 := by
  apply localUnsat_implies_entails f1890 [c1877, c2, c114, c1880, c1887, c1888, c27, c1848, c1595, c1889, c1335, c1609, c48, c1596, c120, c124, c1601] c1890 unsat1890 (by rfl) a
  have h0 : Entails.eval a c1877 := derived1877 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c1880 := derived1880 a h
  have h4 : Entails.eval a c1887 := derived1887 a h
  have h5 : Entails.eval a c1888 := derived1888 a h
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c1848 := derived1848 a h
  have h8 : Entails.eval a c1595 := derived1595 a h
  have h9 : Entails.eval a c1889 := derived1889 a h
  have h10 : Entails.eval a c1335 := derived1335 a h
  have h11 : Entails.eval a c1609 := derived1609 a h
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c1596 := derived1596 a h
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c1601 := derived1601 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1891 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1865, some c263, some c31, some c29, some c1890, some c115, some c51, some c45, some c139, some c205, some c87, some c244, some c175, some c202, some c684, some c1389, some c152, some c1830, some c241, some c313, some c318, some c293, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1891 : lratChecker f1891 p1891 = .success := by decide +kernel
theorem unsat1891 : Unsatisfiable (PosFin 57) f1891 := by
  apply lratCheckerSound f1891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1891
  · intro a ha; simp [p1891] at ha; subst a; trivial
  · exact checked1891
theorem derived1891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1891 := by
  apply localUnsat_implies_entails f1891 [c1829, c1865, c263, c31, c29, c1890, c115, c51, c45, c139, c205, c87, c244, c175, c202, c684, c1389, c152, c1830, c241, c313, c318, c293] c1891 unsat1891 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1865 := derived1865 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c1890 := derived1890 a h
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c139 := h 138 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c244 := h 243 (by decide)
  have h13 : Entails.eval a c175 := h 174 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c684 := derived684 a h
  have h16 : Entails.eval a c1389 := derived1389 a h
  have h17 : Entails.eval a c152 := h 151 (by decide)
  have h18 : Entails.eval a c1830 := derived1830 a h
  have h19 : Entails.eval a c241 := h 240 (by decide)
  have h20 : Entails.eval a c313 := h 312 (by decide)
  have h21 : Entails.eval a c318 := h 317 (by decide)
  have h22 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1892 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨21, by decide⟩, false), (⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c31, some c1, some c1036, some c61, some c256, some c181, some c95, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1892 : lratChecker f1892 p1892 = .success := by decide +kernel
theorem unsat1892 : Unsatisfiable (PosFin 57) f1892 := by
  apply lratCheckerSound f1892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1892
  · intro a ha; simp [p1892] at ha; subst a; trivial
  · exact checked1892
theorem derived1892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1892 := by
  apply localUnsat_implies_entails f1892 [c1829, c31, c1, c1036, c61, c256, c181, c95] c1892 unsat1892 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1036 := derived1036 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c181 := h 180 (by decide)
  have h7 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1893 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨39, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c263, some c29, some c1, some c202, some c1533, some c1147, some c18, some c110, some c1636, some c64, some c73, some c188, some c259, some c338, some c345, some c350, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1893 : lratChecker f1893 p1893 = .success := by decide +kernel
theorem unsat1893 : Unsatisfiable (PosFin 57) f1893 := by
  apply lratCheckerSound f1893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1893
  · intro a ha; simp [p1893] at ha; subst a; trivial
  · exact checked1893
theorem derived1893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1893 := by
  apply localUnsat_implies_entails f1893 [c1829, c263, c29, c1, c202, c1533, c1147, c18, c110, c1636, c64, c73, c188, c259, c338, c345, c350] c1893 unsat1893 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c1533 := derived1533 a h
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c1636 := derived1636 a h
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c188 := h 187 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c338 := h 337 (by decide)
  have h15 : Entails.eval a c345 := h 344 (by decide)
  have h16 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1894 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨17, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c31, some c1, some c18, some c963, some c62, some c562, some c182, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1894 : lratChecker f1894 p1894 = .success := by decide +kernel
theorem unsat1894 : Unsatisfiable (PosFin 57) f1894 := by
  apply lratCheckerSound f1894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1894
  · intro a ha; simp [p1894] at ha; subst a; trivial
  · exact checked1894
theorem derived1894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1894 := by
  apply localUnsat_implies_entails f1894 [c1829, c31, c1, c18, c963, c62, c562, c182] c1894 unsat1894 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c562 := derived562 a h
  have h7 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1895 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c263, some c21, some c29, some c1, some c1865, some c1890, some c112, some c1891, some c1892, some c1894, some c110, some c19, some c1533, some c1893, some c75, some c346, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1895 : lratChecker f1895 p1895 = .success := by decide +kernel
theorem unsat1895 : Unsatisfiable (PosFin 57) f1895 := by
  apply lratCheckerSound f1895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1895
  · intro a ha; simp [p1895] at ha; subst a; trivial
  · exact checked1895
theorem derived1895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1895 := by
  apply localUnsat_implies_entails f1895 [c1829, c263, c21, c29, c1, c1865, c1890, c112, c1891, c1892, c1894, c110, c19, c1533, c1893, c75, c346] c1895 unsat1895 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1865 := derived1865 a h
  have h6 : Entails.eval a c1890 := derived1890 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c1891 := derived1891 a h
  have h9 : Entails.eval a c1892 := derived1892 a h
  have h10 : Entails.eval a c1894 := derived1894 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c1533 := derived1533 a h
  have h14 : Entails.eval a c1893 := derived1893 a h
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1896 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c21, some c1, some c5, some c25, some c153, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1896 : lratChecker f1896 p1896 = .success := by decide +kernel
theorem unsat1896 : Unsatisfiable (PosFin 57) f1896 := by
  apply lratCheckerSound f1896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1896
  · intro a ha; simp [p1896] at ha; subst a; trivial
  · exact checked1896
theorem derived1896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1896 := by
  apply localUnsat_implies_entails f1896 [c1829, c21, c1, c5, c25, c153] c1896 unsat1896 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1897 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c112, some c263, some c1896, some c268, some c1895, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1897 : lratChecker f1897 p1897 = .success := by decide +kernel
theorem unsat1897 : Unsatisfiable (PosFin 57) f1897 := by
  apply lratCheckerSound f1897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1897
  · intro a ha; simp [p1897] at ha; subst a; trivial
  · exact checked1897
theorem derived1897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1897 := by
  apply localUnsat_implies_entails f1897 [c1890, c112, c263, c1896, c268, c1895] c1897 unsat1897 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c1896 := derived1896 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c1895 := derived1895 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1898 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1897, some c1890, some c119, some c51, some c115, some c200, some c128, some c112, some c1, some c29, some c21, some c1896, some c206, some c108, some c1892, some c271, some c314, some c312, some c1894, some c221, some c151, some c137, some c110, some c160, some c157, some c202, some c240, some c64, some c75, some c73, some c1161, some c150, some c176, some c136, some c188, some c184, some c259, some c320, some c350, some c47, some c87, some c795, some c95, some c669, some c354, some c345, some c243, some c380, some c408, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]]
theorem checked1898 : lratChecker f1898 p1898 = .success := by decide +kernel
theorem unsat1898 : Unsatisfiable (PosFin 57) f1898 := by
  apply lratCheckerSound f1898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1898
  · intro a ha; simp [p1898] at ha; subst a; trivial
  · exact checked1898
theorem derived1898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1898 := by
  apply localUnsat_implies_entails f1898 [c1829, c1897, c1890, c119, c51, c115, c200, c128, c112, c1, c29, c21, c1896, c206, c108, c1892, c271, c314, c312, c1894, c221, c151, c137, c110, c160, c157, c202, c240, c64, c75, c73, c1161, c150, c176, c136, c188, c184, c259, c320, c350, c47, c87, c795, c95, c669, c354, c345, c243, c380, c408] c1898 unsat1898 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1897 := derived1897 a h
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c1896 := derived1896 a h
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c1892 := derived1892 a h
  have h16 : Entails.eval a c271 := h 270 (by decide)
  have h17 : Entails.eval a c314 := h 313 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c1894 := derived1894 a h
  have h20 : Entails.eval a c221 := h 220 (by decide)
  have h21 : Entails.eval a c151 := h 150 (by decide)
  have h22 : Entails.eval a c137 := h 136 (by decide)
  have h23 : Entails.eval a c110 := h 109 (by decide)
  have h24 : Entails.eval a c160 := h 159 (by decide)
  have h25 : Entails.eval a c157 := h 156 (by decide)
  have h26 : Entails.eval a c202 := h 201 (by decide)
  have h27 : Entails.eval a c240 := h 239 (by decide)
  have h28 : Entails.eval a c64 := h 63 (by decide)
  have h29 : Entails.eval a c75 := h 74 (by decide)
  have h30 : Entails.eval a c73 := h 72 (by decide)
  have h31 : Entails.eval a c1161 := derived1161 a h
  have h32 : Entails.eval a c150 := h 149 (by decide)
  have h33 : Entails.eval a c176 := h 175 (by decide)
  have h34 : Entails.eval a c136 := h 135 (by decide)
  have h35 : Entails.eval a c188 := h 187 (by decide)
  have h36 : Entails.eval a c184 := h 183 (by decide)
  have h37 : Entails.eval a c259 := h 258 (by decide)
  have h38 : Entails.eval a c320 := h 319 (by decide)
  have h39 : Entails.eval a c350 := h 349 (by decide)
  have h40 : Entails.eval a c47 := h 46 (by decide)
  have h41 : Entails.eval a c87 := h 86 (by decide)
  have h42 : Entails.eval a c795 := derived795 a h
  have h43 : Entails.eval a c95 := h 94 (by decide)
  have h44 : Entails.eval a c669 := derived669 a h
  have h45 : Entails.eval a c354 := h 353 (by decide)
  have h46 : Entails.eval a c345 := h 344 (by decide)
  have h47 : Entails.eval a c243 := h 242 (by decide)
  have h48 : Entails.eval a c380 := h 379 (by decide)
  have h49 : Entails.eval a c408 := h 407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1899 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨30, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨31, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c202, some c108, some c1275, some c110, some c56, some c26, some c149, some c1256, some c281, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1899 : lratChecker f1899 p1899 = .success := by decide +kernel
theorem unsat1899 : Unsatisfiable (PosFin 57) f1899 := by
  apply lratCheckerSound f1899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1899
  · intro a ha; simp [p1899] at ha; subst a; trivial
  · exact checked1899
theorem derived1899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1899 := by
  apply localUnsat_implies_entails f1899 [c1147, c202, c108, c1275, c110, c56, c26, c149, c1256, c281] c1899 unsat1899 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c149 := h 148 (by decide)
  have h8 : Entails.eval a c1256 := derived1256 a h
  have h9 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1900 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c1897, some c119, some c51, some c115, some c200, some c128, some c1898, some c876, some c1147, some c210, some c1899, some c22, some c157, some c159, some c222, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1900 : lratChecker f1900 p1900 = .success := by decide +kernel
theorem unsat1900 : Unsatisfiable (PosFin 57) f1900 := by
  apply lratCheckerSound f1900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1900
  · intro a ha; simp [p1900] at ha; subst a; trivial
  · exact checked1900
theorem derived1900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1900 := by
  apply localUnsat_implies_entails f1900 [c1890, c1897, c119, c51, c115, c200, c128, c1898, c876, c1147, c210, c1899, c22, c157, c159, c222] c1900 unsat1900 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c1897 := derived1897 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c128 := h 127 (by decide)
  have h7 : Entails.eval a c1898 := derived1898 a h
  have h8 : Entails.eval a c876 := derived876 a h
  have h9 : Entails.eval a c1147 := derived1147 a h
  have h10 : Entails.eval a c210 := h 209 (by decide)
  have h11 : Entails.eval a c1899 := derived1899 a h
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c157 := h 156 (by decide)
  have h14 : Entails.eval a c159 := h 158 (by decide)
  have h15 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1901 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1890, some c112, some c29, some c1896, some c108, some c267, some c31, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1901 : lratChecker f1901 p1901 = .success := by decide +kernel
theorem unsat1901 : Unsatisfiable (PosFin 57) f1901 := by
  apply lratCheckerSound f1901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1901
  · intro a ha; simp [p1901] at ha; subst a; trivial
  · exact checked1901
theorem derived1901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1901 := by
  apply localUnsat_implies_entails f1901 [c1829, c1890, c112, c29, c1896, c108, c267, c31] c1901 unsat1901 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1890 := derived1890 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c1896 := derived1896 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1902 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c112, some c1900, some c1901, some c262, some c1147, some c201, some c1744, some c32, some c38, some c108, some c110, some c1275, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1902 : lratChecker f1902 p1902 = .success := by decide +kernel
theorem unsat1902 : Unsatisfiable (PosFin 57) f1902 := by
  apply lratCheckerSound f1902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1902
  · intro a ha; simp [p1902] at ha; subst a; trivial
  · exact checked1902
theorem derived1902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1902 := by
  apply localUnsat_implies_entails f1902 [c1890, c112, c1900, c1901, c262, c1147, c201, c1744, c32, c38, c108, c110, c1275] c1902 unsat1902 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c1900 := derived1900 a h
  have h3 : Entails.eval a c1901 := derived1901 a h
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c1147 := derived1147 a h
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c1744 := derived1744 a h
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c1275 := derived1275 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1903 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1890, some c112, some c1, some c29, some c1393, some c21, some c1896, some c108, some c110, some c31, some c1894, some c153, some c61, some c256, some c181, some c95, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1903 : lratChecker f1903 p1903 = .success := by decide +kernel
theorem unsat1903 : Unsatisfiable (PosFin 57) f1903 := by
  apply lratCheckerSound f1903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1903
  · intro a ha; simp [p1903] at ha; subst a; trivial
  · exact checked1903
theorem derived1903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1903 := by
  apply localUnsat_implies_entails f1903 [c1829, c1890, c112, c1, c29, c1393, c21, c1896, c108, c110, c31, c1894, c153, c61, c256, c181, c95] c1903 unsat1903 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1890 := derived1890 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c1393 := derived1393 a h
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c1896 := derived1896 a h
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c1894 := derived1894 a h
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c61 := h 60 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c181 := h 180 (by decide)
  have h16 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1904 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1902, some c1903, some c261, some c1890, some c112, some c1723, some c110, some c38, some c25, some c5, some c108, some c127, some c115, some c202, some c51, some c45, some c1389, some c139, some c208, some c230, some c87, some c715, some c170, some c164, some c153, some c67, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1904 : lratChecker f1904 p1904 = .success := by decide +kernel
theorem unsat1904 : Unsatisfiable (PosFin 57) f1904 := by
  apply lratCheckerSound f1904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1904
  · intro a ha; simp [p1904] at ha; subst a; trivial
  · exact checked1904
theorem derived1904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1904 := by
  apply localUnsat_implies_entails f1904 [c1829, c1902, c1903, c261, c1890, c112, c1723, c110, c38, c25, c5, c108, c127, c115, c202, c51, c45, c1389, c139, c208, c230, c87, c715, c170, c164, c153, c67] c1904 unsat1904 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1902 := derived1902 a h
  have h2 : Entails.eval a c1903 := derived1903 a h
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c1890 := derived1890 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1723 := derived1723 a h
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c127 := h 126 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c1389 := derived1389 a h
  have h18 : Entails.eval a c139 := h 138 (by decide)
  have h19 : Entails.eval a c208 := h 207 (by decide)
  have h20 : Entails.eval a c230 := h 229 (by decide)
  have h21 : Entails.eval a c87 := h 86 (by decide)
  have h22 : Entails.eval a c715 := derived715 a h
  have h23 : Entails.eval a c170 := h 169 (by decide)
  have h24 : Entails.eval a c164 := h 163 (by decide)
  have h25 : Entails.eval a c153 := h 152 (by decide)
  have h26 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1905 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c108, some c1902, some c1903, some c1890, some c112, some c261, some c1723, some c5, some c25, some c110, some c38, some c1904, some c200, some c4, some c11, some c876, some c873, some c153, some c699, some c48, some c67, some c280, some c208, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1905 : lratChecker f1905 p1905 = .success := by decide +kernel
theorem unsat1905 : Unsatisfiable (PosFin 57) f1905 := by
  apply lratCheckerSound f1905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1905
  · intro a ha; simp [p1905] at ha; subst a; trivial
  · exact checked1905
theorem derived1905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1905 := by
  apply localUnsat_implies_entails f1905 [c1829, c108, c1902, c1903, c1890, c112, c261, c1723, c5, c25, c110, c38, c1904, c200, c4, c11, c876, c873, c153, c699, c48, c67, c280, c208] c1905 unsat1905 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1902 := derived1902 a h
  have h3 : Entails.eval a c1903 := derived1903 a h
  have h4 : Entails.eval a c1890 := derived1890 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c1723 := derived1723 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c1904 := derived1904 a h
  have h13 : Entails.eval a c200 := h 199 (by decide)
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c876 := derived876 a h
  have h17 : Entails.eval a c873 := derived873 a h
  have h18 : Entails.eval a c153 := h 152 (by decide)
  have h19 : Entails.eval a c699 := derived699 a h
  have h20 : Entails.eval a c48 := h 47 (by decide)
  have h21 : Entails.eval a c67 := h 66 (by decide)
  have h22 : Entails.eval a c280 := h 279 (by decide)
  have h23 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1906 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c874, some c119, some c857, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1906 : lratChecker f1906 p1906 = .success := by decide +kernel
theorem unsat1906 : Unsatisfiable (PosFin 57) f1906 := by
  apply lratCheckerSound f1906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1906
  · intro a ha; simp [p1906] at ha; subst a; trivial
  · exact checked1906
theorem derived1906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1906 := by
  apply localUnsat_implies_entails f1906 [c1890, c874, c119, c857] c1906 unsat1906 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c874 := derived874 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c857 := derived857 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1907 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1902, some c1903, some c1890, some c112, some c1906, some c261, some c1905, some c32, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1907 : lratChecker f1907 p1907 = .success := by decide +kernel
theorem unsat1907 : Unsatisfiable (PosFin 57) f1907 := by
  apply lratCheckerSound f1907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1907
  · intro a ha; simp [p1907] at ha; subst a; trivial
  · exact checked1907
theorem derived1907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1907 := by
  apply localUnsat_implies_entails f1907 [c1902, c1903, c1890, c112, c1906, c261, c1905, c32] c1907 unsat1907 (by rfl) a
  have h0 : Entails.eval a c1902 := derived1902 a h
  have h1 : Entails.eval a c1903 := derived1903 a h
  have h2 : Entails.eval a c1890 := derived1890 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1906 := derived1906 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c1905 := derived1905 a h
  have h7 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1908 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c38, some c25, some c5, some c153, some c57, some c181, some c246, some c102, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1908 : lratChecker f1908 p1908 = .success := by decide +kernel
theorem unsat1908 : Unsatisfiable (PosFin 57) f1908 := by
  apply lratCheckerSound f1908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1908
  · intro a ha; simp [p1908] at ha; subst a; trivial
  · exact checked1908
theorem derived1908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1908 := by
  apply localUnsat_implies_entails f1908 [c1829, c38, c25, c5, c153, c57, c181, c246, c102] c1908 unsat1908 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c181 := h 180 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1909 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c5, some c25, some c38, some c1908, some c11, some c164, some c24, some c60, some c192, some c257, some c102, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1909 : lratChecker f1909 p1909 = .success := by decide +kernel
theorem unsat1909 : Unsatisfiable (PosFin 57) f1909 := by
  apply lratCheckerSound f1909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1909
  · intro a ha; simp [p1909] at ha; subst a; trivial
  · exact checked1909
theorem derived1909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1909 := by
  apply localUnsat_implies_entails f1909 [c1829, c5, c25, c38, c1908, c11, c164, c24, c60, c192, c257, c102] c1909 unsat1909 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c1908 := derived1908 a h
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c257 := h 256 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1910 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1907, some c1902, some c1903, some c1890, some c112, some c108, some c1460, some c110, some c1909, some c268, some c267, some c1744, some c874, some c119, some c24, some c896, some c200, some c213, some c51, some c18, some c146, some c164, some c281, some c74, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1910 : lratChecker f1910 p1910 = .success := by decide +kernel
theorem unsat1910 : Unsatisfiable (PosFin 57) f1910 := by
  apply lratCheckerSound f1910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1910
  · intro a ha; simp [p1910] at ha; subst a; trivial
  · exact checked1910
theorem derived1910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1910 := by
  apply localUnsat_implies_entails f1910 [c1907, c1902, c1903, c1890, c112, c108, c1460, c110, c1909, c268, c267, c1744, c874, c119, c24, c896, c200, c213, c51, c18, c146, c164, c281, c74] c1910 unsat1910 (by rfl) a
  have h0 : Entails.eval a c1907 := derived1907 a h
  have h1 : Entails.eval a c1902 := derived1902 a h
  have h2 : Entails.eval a c1903 := derived1903 a h
  have h3 : Entails.eval a c1890 := derived1890 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1460 := derived1460 a h
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c1909 := derived1909 a h
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c1744 := derived1744 a h
  have h12 : Entails.eval a c874 := derived874 a h
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c896 := derived896 a h
  have h16 : Entails.eval a c200 := h 199 (by decide)
  have h17 : Entails.eval a c213 := h 212 (by decide)
  have h18 : Entails.eval a c51 := h 50 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  have h20 : Entails.eval a c146 := h 145 (by decide)
  have h21 : Entails.eval a c164 := h 163 (by decide)
  have h22 : Entails.eval a c281 := h 280 (by decide)
  have h23 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1911 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1890, some c112, some c1902, some c1907, some c1910, some c22, some c32, some c268, some c267, some c1744, some c874, some c158, some c120, some c225, some c160, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1911 : lratChecker f1911 p1911 = .success := by decide +kernel
theorem unsat1911 : Unsatisfiable (PosFin 57) f1911 := by
  apply lratCheckerSound f1911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1911
  · intro a ha; simp [p1911] at ha; subst a; trivial
  · exact checked1911
theorem derived1911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1911 := by
  apply localUnsat_implies_entails f1911 [c1890, c112, c1902, c1907, c1910, c22, c32, c268, c267, c1744, c874, c158, c120, c225, c160] c1911 unsat1911 (by rfl) a
  have h0 : Entails.eval a c1890 := derived1890 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c1902 := derived1902 a h
  have h3 : Entails.eval a c1907 := derived1907 a h
  have h4 : Entails.eval a c1910 := derived1910 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c1744 := derived1744 a h
  have h10 : Entails.eval a c874 := derived874 a h
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c120 := h 119 (by decide)
  have h13 : Entails.eval a c225 := h 224 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1912 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c3, some c23, some c30, some c200, some c157, some c262, some c22, some c1147, some c34, some c202, some c109, some c110, some c17, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1912 : lratChecker f1912 p1912 = .success := by decide +kernel
theorem unsat1912 : Unsatisfiable (PosFin 57) f1912 := by
  apply lratCheckerSound f1912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1912
  · intro a ha; simp [p1912] at ha; subst a; trivial
  · exact checked1912
theorem derived1912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1912 := by
  apply localUnsat_implies_entails f1912 [c1829, c3, c23, c30, c200, c157, c262, c22, c1147, c34, c202, c109, c110, c17] c1912 unsat1912 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1913 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1, some c15, some c1533, some c71, some c73, some c349, some c352, some c220, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1913 : lratChecker f1913 p1913 = .success := by decide +kernel
theorem unsat1913 : Unsatisfiable (PosFin 57) f1913 := by
  apply lratCheckerSound f1913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1913
  · intro a ha; simp [p1913] at ha; subst a; trivial
  · exact checked1913
theorem derived1913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1913 := by
  apply localUnsat_implies_entails f1913 [c1829, c1, c15, c1533, c71, c73, c349, c352, c220] c1913 unsat1913 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c1533 := derived1533 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c352 := h 351 (by decide)
  have h8 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1913

end CochromaticTwenty.Certificates.B16_0_2Enumerating
