import MerLeanExperiment.Certificates.B16_0_1.Steps0500_0599

/-! Generated from the actual pinned b16_0_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c927 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨39, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c243, some c924, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked927 : lratChecker f927 p927 = .success := by decide +kernel
theorem unsat927 : Unsatisfiable (PosFin 57) f927 := by
  apply lratCheckerSound f927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p927
  · intro a ha; simp [p927] at ha; subst a; trivial
  · exact checked927
theorem derived927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c927 := by
  apply localUnsat_implies_entails f927 [c239, c243, c924] c927 unsat927 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c924 := derived924 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c928 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨39, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c912, some c825, some c923, some c927, some c299, some c296, some c917, some c100, some c925, some c10, some c926, some c9, some c24, some c924, some c98, some c240, some c32, some c902, some c672, some c293, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked928 : lratChecker f928 p928 = .success := by decide +kernel
theorem unsat928 : Unsatisfiable (PosFin 57) f928 := by
  apply lratCheckerSound f928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p928
  · intro a ha; simp [p928] at ha; subst a; trivial
  · exact checked928
theorem derived928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c928 := by
  apply localUnsat_implies_entails f928 [c731, c912, c825, c923, c927, c299, c296, c917, c100, c925, c10, c926, c9, c24, c924, c98, c240, c32, c902, c672, c293] c928 unsat928 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c923 := derived923 a h
  have h4 : Entails.eval a c927 := derived927 a h
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c917 := derived917 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c925 := derived925 a h
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c926 := derived926 a h
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c924 := derived924 a h
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c240 := h 239 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  have h18 : Entails.eval a c902 := derived902 a h
  have h19 : Entails.eval a c672 := derived672 a h
  have h20 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c929 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c912, some c731, some c917, some c100, some c923, some c925, some c10, some c926, some c9, some c296, some c299, some c927, some c34, some c928, some c241, some c32, some c98, some c68, some c297, some c817, some c913, some c918, some c103, some c195, some c258, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked929 : lratChecker f929 p929 = .success := by decide +kernel
theorem unsat929 : Unsatisfiable (PosFin 57) f929 := by
  apply lratCheckerSound f929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p929
  · intro a ha; simp [p929] at ha; subst a; trivial
  · exact checked929
theorem derived929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c929 := by
  apply localUnsat_implies_entails f929 [c912, c731, c917, c100, c923, c925, c10, c926, c9, c296, c299, c927, c34, c928, c241, c32, c98, c68, c297, c817, c913, c918, c103, c195, c258] c929 unsat929 (by rfl) a
  have h0 : Entails.eval a c912 := derived912 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c917 := derived917 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c923 := derived923 a h
  have h5 : Entails.eval a c925 := derived925 a h
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c926 := derived926 a h
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c927 := derived927 a h
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c928 := derived928 a h
  have h14 : Entails.eval a c241 := h 240 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c98 := h 97 (by decide)
  have h17 : Entails.eval a c68 := h 67 (by decide)
  have h18 : Entails.eval a c297 := h 296 (by decide)
  have h19 : Entails.eval a c817 := derived817 a h
  have h20 : Entails.eval a c913 := derived913 a h
  have h21 : Entails.eval a c918 := derived918 a h
  have h22 : Entails.eval a c103 := h 102 (by decide)
  have h23 : Entails.eval a c195 := h 194 (by decide)
  have h24 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c930 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c912, some c825, some c917, some c100, some c923, some c925, some c10, some c926, some c9, some c929, some c69, some c60, some c25, some c297, some c295, some c668, some c224, some c239, some c243, some c98, some c81, some c202, some c33, some c234, some c246, some c497, some c103, some c170, some c42, some c104, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked930 : lratChecker f930 p930 = .success := by decide +kernel
theorem unsat930 : Unsatisfiable (PosFin 57) f930 := by
  apply lratCheckerSound f930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p930
  · intro a ha; simp [p930] at ha; subst a; trivial
  · exact checked930
theorem derived930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c930 := by
  apply localUnsat_implies_entails f930 [c731, c912, c825, c917, c100, c923, c925, c10, c926, c9, c929, c69, c60, c25, c297, c295, c668, c224, c239, c243, c98, c81, c202, c33, c234, c246, c497, c103, c170, c42, c104] c930 unsat930 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c917 := derived917 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c923 := derived923 a h
  have h6 : Entails.eval a c925 := derived925 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c926 := derived926 a h
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c929 := derived929 a h
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c297 := h 296 (by decide)
  have h15 : Entails.eval a c295 := h 294 (by decide)
  have h16 : Entails.eval a c668 := derived668 a h
  have h17 : Entails.eval a c224 := h 223 (by decide)
  have h18 : Entails.eval a c239 := h 238 (by decide)
  have h19 : Entails.eval a c243 := h 242 (by decide)
  have h20 : Entails.eval a c98 := h 97 (by decide)
  have h21 : Entails.eval a c81 := h 80 (by decide)
  have h22 : Entails.eval a c202 := h 201 (by decide)
  have h23 : Entails.eval a c33 := h 32 (by decide)
  have h24 : Entails.eval a c234 := h 233 (by decide)
  have h25 : Entails.eval a c246 := h 245 (by decide)
  have h26 : Entails.eval a c497 := derived497 a h
  have h27 : Entails.eval a c103 := h 102 (by decide)
  have h28 : Entails.eval a c170 := h 169 (by decide)
  have h29 : Entails.eval a c42 := h 41 (by decide)
  have h30 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c931 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c912, some c825, some c731, some c930, some c21, some c3, some c643, some c650, some c139, some c9, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked931 : lratChecker f931 p931 = .success := by decide +kernel
theorem unsat931 : Unsatisfiable (PosFin 57) f931 := by
  apply lratCheckerSound f931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p931
  · intro a ha; simp [p931] at ha; subst a; trivial
  · exact checked931
theorem derived931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c931 := by
  apply localUnsat_implies_entails f931 [c912, c825, c731, c930, c21, c3, c643, c650, c139, c9] c931 unsat931 (by rfl) a
  have h0 : Entails.eval a c912 := derived912 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c731 := derived731 a h
  have h3 : Entails.eval a c930 := derived930 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c643 := derived643 a h
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c932 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c825, some c912, some c930, some c931, some c240, some c239, some c25, some c7, some c656, some c296, some c299, some c143, some c66, some c9, some c98, some c591, some c32, some c207, some c241, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked932 : lratChecker f932 p932 = .success := by decide +kernel
theorem unsat932 : Unsatisfiable (PosFin 57) f932 := by
  apply lratCheckerSound f932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p932
  · intro a ha; simp [p932] at ha; subst a; trivial
  · exact checked932
theorem derived932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c932 := by
  apply localUnsat_implies_entails f932 [c731, c825, c912, c930, c931, c240, c239, c25, c7, c656, c296, c299, c143, c66, c9, c98, c591, c32, c207, c241] c932 unsat932 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c930 := derived930 a h
  have h4 : Entails.eval a c931 := derived931 a h
  have h5 : Entails.eval a c240 := h 239 (by decide)
  have h6 : Entails.eval a c239 := h 238 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c656 := derived656 a h
  have h10 : Entails.eval a c296 := h 295 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c9 := h 8 (by decide)
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c591 := derived591 a h
  have h17 : Entails.eval a c32 := h 31 (by decide)
  have h18 : Entails.eval a c207 := h 206 (by decide)
  have h19 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c933 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c912, some c825, some c932, some c930, some c1, some c643, some c656, some c245, some c27, some c56, some c232, some c60, some c299, some c657, some c66, some c98, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked933 : lratChecker f933 p933 = .success := by decide +kernel
theorem unsat933 : Unsatisfiable (PosFin 57) f933 := by
  apply lratCheckerSound f933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p933
  · intro a ha; simp [p933] at ha; subst a; trivial
  · exact checked933
theorem derived933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c933 := by
  apply localUnsat_implies_entails f933 [c731, c912, c825, c932, c930, c1, c643, c656, c245, c27, c56, c232, c60, c299, c657, c66, c98] c933 unsat933 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c932 := derived932 a h
  have h4 : Entails.eval a c930 := derived930 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c643 := derived643 a h
  have h7 : Entails.eval a c656 := derived656 a h
  have h8 : Entails.eval a c245 := h 244 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c232 := h 231 (by decide)
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c657 := derived657 a h
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c934 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c912, some c825, some c930, some c932, some c1, some c933, some c382, some c296, some c295, some c134, some c69, some c101, some c67, some c12, some c135, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked934 : lratChecker f934 p934 = .success := by decide +kernel
theorem unsat934 : Unsatisfiable (PosFin 57) f934 := by
  apply lratCheckerSound f934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p934
  · intro a ha; simp [p934] at ha; subst a; trivial
  · exact checked934
theorem derived934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c934 := by
  apply localUnsat_implies_entails f934 [c731, c912, c825, c930, c932, c1, c933, c382, c296, c295, c134, c69, c101, c67, c12, c135] c934 unsat934 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c930 := derived930 a h
  have h4 : Entails.eval a c932 := derived932 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c933 := derived933 a h
  have h7 : Entails.eval a c382 := derived382 a h
  have h8 : Entails.eval a c296 := h 295 (by decide)
  have h9 : Entails.eval a c295 := h 294 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c935 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c934, some c912, some c825, some c731, some c21, some c56, some c239, some c245, some c232, some c60, some c299, some c66, some c92, some c65, some c657, some c102, some c110, some c252, some c254, some c143, some c140, some c131, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked935 : lratChecker f935 p935 = .success := by decide +kernel
theorem unsat935 : Unsatisfiable (PosFin 57) f935 := by
  apply lratCheckerSound f935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p935
  · intro a ha; simp [p935] at ha; subst a; trivial
  · exact checked935
theorem derived935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c935 := by
  apply localUnsat_implies_entails f935 [c934, c912, c825, c731, c21, c56, c239, c245, c232, c60, c299, c66, c92, c65, c657, c102, c110, c252, c254, c143, c140, c131] c935 unsat935 (by rfl) a
  have h0 : Entails.eval a c934 := derived934 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c731 := derived731 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c239 := h 238 (by decide)
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c232 := h 231 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c657 := derived657 a h
  have h15 : Entails.eval a c102 := h 101 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c252 := h 251 (by decide)
  have h18 : Entails.eval a c254 := h 253 (by decide)
  have h19 : Entails.eval a c143 := h 142 (by decide)
  have h20 : Entails.eval a c140 := h 139 (by decide)
  have h21 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c936 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c825, some c731, some c912, some c934, some c935, some c382, some c296, some c295, some c291, some c93, some c60, some c67, some c739, some c298, some c426, some c479, some c459, some c288, some c238, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked936 : lratChecker f936 p936 = .success := by decide +kernel
theorem unsat936 : Unsatisfiable (PosFin 57) f936 := by
  apply lratCheckerSound f936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p936
  · intro a ha; simp [p936] at ha; subst a; trivial
  · exact checked936
theorem derived936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c936 := by
  apply localUnsat_implies_entails f936 [c825, c731, c912, c934, c935, c382, c296, c295, c291, c93, c60, c67, c739, c298, c426, c479, c459, c288, c238] c936 unsat936 (by rfl) a
  have h0 : Entails.eval a c825 := derived825 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c934 := derived934 a h
  have h4 : Entails.eval a c935 := derived935 a h
  have h5 : Entails.eval a c382 := derived382 a h
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c295 := h 294 (by decide)
  have h8 : Entails.eval a c291 := h 290 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c60 := h 59 (by decide)
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c739 := derived739 a h
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c426 := derived426 a h
  have h15 : Entails.eval a c479 := derived479 a h
  have h16 : Entails.eval a c459 := derived459 a h
  have h17 : Entails.eval a c288 := h 287 (by decide)
  have h18 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c937 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨39, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c825, some c912, some c934, some c936, some c91, some c71, some c293, some c67, some c92, some c60, some c24, some c59, some c238, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked937 : lratChecker f937 p937 = .success := by decide +kernel
theorem unsat937 : Unsatisfiable (PosFin 57) f937 := by
  apply lratCheckerSound f937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p937
  · intro a ha; simp [p937] at ha; subst a; trivial
  · exact checked937
theorem derived937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c937 := by
  apply localUnsat_implies_entails f937 [c825, c912, c934, c936, c91, c71, c293, c67, c92, c60, c24, c59, c238] c937 unsat937 (by rfl) a
  have h0 : Entails.eval a c825 := derived825 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c934 := derived934 a h
  have h3 : Entails.eval a c936 := derived936 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c938 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨39, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c912, some c934, some c825, some c936, some c91, some c71, some c293, some c67, some c92, some c60, some c248, some c238, some c88, some c470, some c479, some c499, some c29, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked938 : lratChecker f938 p938 = .success := by decide +kernel
theorem unsat938 : Unsatisfiable (PosFin 57) f938 := by
  apply lratCheckerSound f938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p938
  · intro a ha; simp [p938] at ha; subst a; trivial
  · exact checked938
theorem derived938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c938 := by
  apply localUnsat_implies_entails f938 [c912, c934, c825, c936, c91, c71, c293, c67, c92, c60, c248, c238, c88, c470, c479, c499, c29] c938 unsat938 (by rfl) a
  have h0 : Entails.eval a c912 := derived912 a h
  have h1 : Entails.eval a c934 := derived934 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c936 := derived936 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c238 := h 237 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c470 := derived470 a h
  have h14 : Entails.eval a c479 := derived479 a h
  have h15 : Entails.eval a c499 := derived499 a h
  have h16 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c939 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c912, some c825, some c934, some c936, some c91, some c382, some c71, some c293, some c67, some c92, some c937, some c938, some c663, some c35, some c913, some c833, some c102, some c245, some c253, some c37, some c194, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked939 : lratChecker f939 p939 = .success := by decide +kernel
theorem unsat939 : Unsatisfiable (PosFin 57) f939 := by
  apply lratCheckerSound f939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p939
  · intro a ha; simp [p939] at ha; subst a; trivial
  · exact checked939
theorem derived939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c939 := by
  apply localUnsat_implies_entails f939 [c912, c825, c934, c936, c91, c382, c71, c293, c67, c92, c937, c938, c663, c35, c913, c833, c102, c245, c253, c37, c194] c939 unsat939 (by rfl) a
  have h0 : Entails.eval a c912 := derived912 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c934 := derived934 a h
  have h3 : Entails.eval a c936 := derived936 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c382 := derived382 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c937 := derived937 a h
  have h11 : Entails.eval a c938 := derived938 a h
  have h12 : Entails.eval a c663 := derived663 a h
  have h13 : Entails.eval a c35 := h 34 (by decide)
  have h14 : Entails.eval a c913 := derived913 a h
  have h15 : Entails.eval a c833 := derived833 a h
  have h16 : Entails.eval a c102 := h 101 (by decide)
  have h17 : Entails.eval a c245 := h 244 (by decide)
  have h18 : Entails.eval a c253 := h 252 (by decide)
  have h19 : Entails.eval a c37 := h 36 (by decide)
  have h20 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c940 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c934, some c825, some c731, some c912, some c939, some c299, some c24, some c92, some c924, some c245, some c927, some c936, some c91, some c382, some c613, some c421, some c2, some c765, some c143, some c18, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked940 : lratChecker f940 p940 = .success := by decide +kernel
theorem unsat940 : Unsatisfiable (PosFin 57) f940 := by
  apply lratCheckerSound f940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p940
  · intro a ha; simp [p940] at ha; subst a; trivial
  · exact checked940
theorem derived940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c940 := by
  apply localUnsat_implies_entails f940 [c934, c825, c731, c912, c939, c299, c24, c92, c924, c245, c927, c936, c91, c382, c613, c421, c2, c765, c143, c18] c940 unsat940 (by rfl) a
  have h0 : Entails.eval a c934 := derived934 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c731 := derived731 a h
  have h3 : Entails.eval a c912 := derived912 a h
  have h4 : Entails.eval a c939 := derived939 a h
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c924 := derived924 a h
  have h9 : Entails.eval a c245 := h 244 (by decide)
  have h10 : Entails.eval a c927 := derived927 a h
  have h11 : Entails.eval a c936 := derived936 a h
  have h12 : Entails.eval a c91 := h 90 (by decide)
  have h13 : Entails.eval a c382 := derived382 a h
  have h14 : Entails.eval a c613 := derived613 a h
  have h15 : Entails.eval a c421 := derived421 a h
  have h16 : Entails.eval a c2 := h 1 (by decide)
  have h17 : Entails.eval a c765 := derived765 a h
  have h18 : Entails.eval a c143 := h 142 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c941 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c934, some c912, some c825, some c939, some c927, some c299, some c936, some c91, some c924, some c24, some c245, some c92, some c940, some c29, some c207, some c8, some c95, some c765, some c603, some c758, some c293, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked941 : lratChecker f941 p941 = .success := by decide +kernel
theorem unsat941 : Unsatisfiable (PosFin 57) f941 := by
  apply lratCheckerSound f941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p941
  · intro a ha; simp [p941] at ha; subst a; trivial
  · exact checked941
theorem derived941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c941 := by
  apply localUnsat_implies_entails f941 [c731, c934, c912, c825, c939, c927, c299, c936, c91, c924, c24, c245, c92, c940, c29, c207, c8, c95, c765, c603, c758, c293] c941 unsat941 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c934 := derived934 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c825 := derived825 a h
  have h4 : Entails.eval a c939 := derived939 a h
  have h5 : Entails.eval a c927 := derived927 a h
  have h6 : Entails.eval a c299 := h 298 (by decide)
  have h7 : Entails.eval a c936 := derived936 a h
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c924 := derived924 a h
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c245 := h 244 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c940 := derived940 a h
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c207 := h 206 (by decide)
  have h16 : Entails.eval a c8 := h 7 (by decide)
  have h17 : Entails.eval a c95 := h 94 (by decide)
  have h18 : Entails.eval a c765 := derived765 a h
  have h19 : Entails.eval a c603 := derived603 a h
  have h20 : Entails.eval a c758 := derived758 a h
  have h21 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c942 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨4, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c934, some c825, some c912, some c941, some c248, some c939, some c927, some c936, some c91, some c29, some c26, some c8, some c95, some c293, some c765, some c603, some c758, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked942 : lratChecker f942 p942 = .success := by decide +kernel
theorem unsat942 : Unsatisfiable (PosFin 57) f942 := by
  apply lratCheckerSound f942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p942
  · intro a ha; simp [p942] at ha; subst a; trivial
  · exact checked942
theorem derived942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c942 := by
  apply localUnsat_implies_entails f942 [c934, c825, c912, c941, c248, c939, c927, c936, c91, c29, c26, c8, c95, c293, c765, c603, c758] c942 unsat942 (by rfl) a
  have h0 : Entails.eval a c934 := derived934 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c941 := derived941 a h
  have h4 : Entails.eval a c248 := h 247 (by decide)
  have h5 : Entails.eval a c939 := derived939 a h
  have h6 : Entails.eval a c927 := derived927 a h
  have h7 : Entails.eval a c936 := derived936 a h
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c95 := h 94 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c765 := derived765 a h
  have h15 : Entails.eval a c603 := derived603 a h
  have h16 : Entails.eval a c758 := derived758 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c943 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c934, some c825, some c912, some c731, some c941, some c248, some c939, some c927, some c936, some c91, some c942, some c613, some c2, some c143, some c18, some c14, some c765, some c140, some c181, some c185, some c758, some c111, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked943 : lratChecker f943 p943 = .success := by decide +kernel
theorem unsat943 : Unsatisfiable (PosFin 57) f943 := by
  apply lratCheckerSound f943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p943
  · intro a ha; simp [p943] at ha; subst a; trivial
  · exact checked943
theorem derived943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c943 := by
  apply localUnsat_implies_entails f943 [c934, c825, c912, c731, c941, c248, c939, c927, c936, c91, c942, c613, c2, c143, c18, c14, c765, c140, c181, c185, c758, c111] c943 unsat943 (by rfl) a
  have h0 : Entails.eval a c934 := derived934 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c731 := derived731 a h
  have h4 : Entails.eval a c941 := derived941 a h
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c939 := derived939 a h
  have h7 : Entails.eval a c927 := derived927 a h
  have h8 : Entails.eval a c936 := derived936 a h
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c942 := derived942 a h
  have h11 : Entails.eval a c613 := derived613 a h
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c765 := derived765 a h
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c181 := h 180 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c758 := derived758 a h
  have h21 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c944 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c912, some c825, some c934, some c936, some c91, some c941, some c939, some c299, some c943, some c92, some c59, some c238, some c89, some c70, some c380, some c927, some c382, some c138, some c472, some c102, some c283, some c38, some c379, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked944 : lratChecker f944 p944 = .success := by decide +kernel
theorem unsat944 : Unsatisfiable (PosFin 57) f944 := by
  apply lratCheckerSound f944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p944
  · intro a ha; simp [p944] at ha; subst a; trivial
  · exact checked944
theorem derived944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c944 := by
  apply localUnsat_implies_entails f944 [c731, c912, c825, c934, c936, c91, c941, c939, c299, c943, c92, c59, c238, c89, c70, c380, c927, c382, c138, c472, c102, c283, c38, c379] c944 unsat944 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c934 := derived934 a h
  have h4 : Entails.eval a c936 := derived936 a h
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c941 := derived941 a h
  have h7 : Entails.eval a c939 := derived939 a h
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c943 := derived943 a h
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c238 := h 237 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c380 := derived380 a h
  have h16 : Entails.eval a c927 := derived927 a h
  have h17 : Entails.eval a c382 := derived382 a h
  have h18 : Entails.eval a c138 := h 137 (by decide)
  have h19 : Entails.eval a c472 := derived472 a h
  have h20 : Entails.eval a c102 := h 101 (by decide)
  have h21 : Entails.eval a c283 := h 282 (by decide)
  have h22 : Entails.eval a c38 := h 37 (by decide)
  have h23 : Entails.eval a c379 := derived379 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c945 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c825, some c941, some c248, some c939, some c927, some c143, some c137, some c110, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked945 : lratChecker f945 p945 = .success := by decide +kernel
theorem unsat945 : Unsatisfiable (PosFin 57) f945 := by
  apply lratCheckerSound f945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p945
  · intro a ha; simp [p945] at ha; subst a; trivial
  · exact checked945
theorem derived945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c945 := by
  apply localUnsat_implies_entails f945 [c731, c825, c941, c248, c939, c927, c143, c137, c110] c945 unsat945 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c941 := derived941 a h
  have h3 : Entails.eval a c248 := h 247 (by decide)
  have h4 : Entails.eval a c939 := derived939 a h
  have h5 : Entails.eval a c927 := derived927 a h
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c137 := h 136 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c946 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c825, some c934, some c912, some c936, some c91, some c939, some c299, some c927, some c941, some c248, some c943, some c92, some c70, some c945, some c18, some c138, some c944, some c102, some c110, some c29, some c38, some c37, some c95, some c660, some c16, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked946 : lratChecker f946 p946 = .success := by decide +kernel
theorem unsat946 : Unsatisfiable (PosFin 57) f946 := by
  apply lratCheckerSound f946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p946
  · intro a ha; simp [p946] at ha; subst a; trivial
  · exact checked946
theorem derived946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c946 := by
  apply localUnsat_implies_entails f946 [c731, c825, c934, c912, c936, c91, c939, c299, c927, c941, c248, c943, c92, c70, c945, c18, c138, c944, c102, c110, c29, c38, c37, c95, c660, c16] c946 unsat946 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c934 := derived934 a h
  have h3 : Entails.eval a c912 := derived912 a h
  have h4 : Entails.eval a c936 := derived936 a h
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c939 := derived939 a h
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c927 := derived927 a h
  have h9 : Entails.eval a c941 := derived941 a h
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c943 := derived943 a h
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c945 := derived945 a h
  have h15 : Entails.eval a c18 := h 17 (by decide)
  have h16 : Entails.eval a c138 := h 137 (by decide)
  have h17 : Entails.eval a c944 := derived944 a h
  have h18 : Entails.eval a c102 := h 101 (by decide)
  have h19 : Entails.eval a c110 := h 109 (by decide)
  have h20 : Entails.eval a c29 := h 28 (by decide)
  have h21 : Entails.eval a c38 := h 37 (by decide)
  have h22 : Entails.eval a c37 := h 36 (by decide)
  have h23 : Entails.eval a c95 := h 94 (by decide)
  have h24 : Entails.eval a c660 := derived660 a h
  have h25 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c947 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c946, some c912, some c25, some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked947 : lratChecker f947 p947 = .success := by decide +kernel
theorem unsat947 : Unsatisfiable (PosFin 57) f947 := by
  apply lratCheckerSound f947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p947
  · intro a ha; simp [p947] at ha; subst a; trivial
  · exact checked947
theorem derived947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c947 := by
  apply localUnsat_implies_entails f947 [c946, c912, c25] c947 unsat947 (by rfl) a
  have h0 : Entails.eval a c946 := derived946 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c948 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c946, some c912, some c7, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked948 : lratChecker f948 p948 = .success := by decide +kernel
theorem unsat948 : Unsatisfiable (PosFin 57) f948 := by
  apply lratCheckerSound f948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p948
  · intro a ha; simp [p948] at ha; subst a; trivial
  · exact checked948
theorem derived948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c948 := by
  apply localUnsat_implies_entails f948 [c946, c912, c7] c948 unsat948 (by rfl) a
  have h0 : Entails.eval a c946 := derived946 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c949 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c946, some c825, some c912, some c656, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked949 : lratChecker f949 p949 = .success := by decide +kernel
theorem unsat949 : Unsatisfiable (PosFin 57) f949 := by
  apply lratCheckerSound f949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p949
  · intro a ha; simp [p949] at ha; subst a; trivial
  · exact checked949
theorem derived949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c949 := by
  apply localUnsat_implies_entails f949 [c946, c825, c912, c656] c949 unsat949 (by rfl) a
  have h0 : Entails.eval a c946 := derived946 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c656 := derived656 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c950 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c947, some c731, some c296, some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked950 : lratChecker f950 p950 = .success := by decide +kernel
theorem unsat950 : Unsatisfiable (PosFin 57) f950 := by
  apply lratCheckerSound f950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p950
  · intro a ha; simp [p950] at ha; subst a; trivial
  · exact checked950
theorem derived950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c950 := by
  apply localUnsat_implies_entails f950 [c947, c731, c296] c950 unsat950 (by rfl) a
  have h0 : Entails.eval a c947 := derived947 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c951 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c947, some c731, some c299, some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked951 : lratChecker f951 p951 = .success := by decide +kernel
theorem unsat951 : Unsatisfiable (PosFin 57) f951 := by
  apply lratCheckerSound f951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p951
  · intro a ha; simp [p951] at ha; subst a; trivial
  · exact checked951
theorem derived951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c951 := by
  apply localUnsat_implies_entails f951 [c947, c731, c299] c951 unsat951 (by rfl) a
  have h0 : Entails.eval a c947 := derived947 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c952 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c948, some c731, some c947, some c143, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked952 : lratChecker f952 p952 = .success := by decide +kernel
theorem unsat952 : Unsatisfiable (PosFin 57) f952 := by
  apply lratCheckerSound f952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p952
  · intro a ha; simp [p952] at ha; subst a; trivial
  · exact checked952
theorem derived952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c952 := by
  apply localUnsat_implies_entails f952 [c948, c731, c947, c143] c952 unsat952 (by rfl) a
  have h0 : Entails.eval a c948 := derived948 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c947 := derived947 a h
  have h3 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c953 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c952, some c949, some c825, some c947, some c934, some c951, some c946, some c102, some c254, some c110, some c92, some c38, some c24, some c195, some c247, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked953 : lratChecker f953 p953 = .success := by decide +kernel
theorem unsat953 : Unsatisfiable (PosFin 57) f953 := by
  apply lratCheckerSound f953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p953
  · intro a ha; simp [p953] at ha; subst a; trivial
  · exact checked953
theorem derived953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c953 := by
  apply localUnsat_implies_entails f953 [c952, c949, c825, c947, c934, c951, c946, c102, c254, c110, c92, c38, c24, c195, c247] c953 unsat953 (by rfl) a
  have h0 : Entails.eval a c952 := derived952 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c947 := derived947 a h
  have h4 : Entails.eval a c934 := derived934 a h
  have h5 : Entails.eval a c951 := derived951 a h
  have h6 : Entails.eval a c946 := derived946 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c195 := h 194 (by decide)
  have h14 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c954 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c949, some c946, some c731, some c825, some c951, some c950, some c912, some c952, some c36, some c110, some c953, some c32, some c613, some c246, some c247, some c459, some c205, some c65, some c765, some c11, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked954 : lratChecker f954 p954 = .success := by decide +kernel
theorem unsat954 : Unsatisfiable (PosFin 57) f954 := by
  apply lratCheckerSound f954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p954
  · intro a ha; simp [p954] at ha; subst a; trivial
  · exact checked954
theorem derived954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c954 := by
  apply localUnsat_implies_entails f954 [c949, c946, c731, c825, c951, c950, c912, c952, c36, c110, c953, c32, c613, c246, c247, c459, c205, c65, c765, c11] c954 unsat954 (by rfl) a
  have h0 : Entails.eval a c949 := derived949 a h
  have h1 : Entails.eval a c946 := derived946 a h
  have h2 : Entails.eval a c731 := derived731 a h
  have h3 : Entails.eval a c825 := derived825 a h
  have h4 : Entails.eval a c951 := derived951 a h
  have h5 : Entails.eval a c950 := derived950 a h
  have h6 : Entails.eval a c912 := derived912 a h
  have h7 : Entails.eval a c952 := derived952 a h
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c953 := derived953 a h
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c613 := derived613 a h
  have h13 : Entails.eval a c246 := h 245 (by decide)
  have h14 : Entails.eval a c247 := h 246 (by decide)
  have h15 : Entails.eval a c459 := derived459 a h
  have h16 : Entails.eval a c205 := h 204 (by decide)
  have h17 : Entails.eval a c65 := h 64 (by decide)
  have h18 : Entails.eval a c765 := derived765 a h
  have h19 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c955 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c950, some c946, some c912, some c731, some c825, some c934, some c36, some c954, some c242, some c913, some c32, some c380, some c92, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked955 : lratChecker f955 p955 = .success := by decide +kernel
theorem unsat955 : Unsatisfiable (PosFin 57) f955 := by
  apply lratCheckerSound f955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p955
  · intro a ha; simp [p955] at ha; subst a; trivial
  · exact checked955
theorem derived955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c955 := by
  apply localUnsat_implies_entails f955 [c950, c946, c912, c731, c825, c934, c36, c954, c242, c913, c32, c380, c92] c955 unsat955 (by rfl) a
  have h0 : Entails.eval a c950 := derived950 a h
  have h1 : Entails.eval a c946 := derived946 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c731 := derived731 a h
  have h4 : Entails.eval a c825 := derived825 a h
  have h5 : Entails.eval a c934 := derived934 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c954 := derived954 a h
  have h8 : Entails.eval a c242 := h 241 (by decide)
  have h9 : Entails.eval a c913 := derived913 a h
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c380 := derived380 a h
  have h12 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c956 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c955, some c934, some c93, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked956 : lratChecker f956 p956 = .success := by decide +kernel
theorem unsat956 : Unsatisfiable (PosFin 57) f956 := by
  apply lratCheckerSound f956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p956
  · intro a ha; simp [p956] at ha; subst a; trivial
  · exact checked956
theorem derived956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c956 := by
  apply localUnsat_implies_entails f956 [c955, c934, c93] c956 unsat956 (by rfl) a
  have h0 : Entails.eval a c955 := derived955 a h
  have h1 : Entails.eval a c934 := derived934 a h
  have h2 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c957 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c955, some c934, some c91, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked957 : lratChecker f957 p957 = .success := by decide +kernel
theorem unsat957 : Unsatisfiable (PosFin 57) f957 := by
  apply lratCheckerSound f957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p957
  · intro a ha; simp [p957] at ha; subst a; trivial
  · exact checked957
theorem derived957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c957 := by
  apply localUnsat_implies_entails f957 [c955, c934, c91] c957 unsat957 (by rfl) a
  have h0 : Entails.eval a c955 := derived955 a h
  have h1 : Entails.eval a c934 := derived934 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c958 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c956, some c912, some c946, some c32, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked958 : lratChecker f958 p958 = .success := by decide +kernel
theorem unsat958 : Unsatisfiable (PosFin 57) f958 := by
  apply lratCheckerSound f958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p958
  · intro a ha; simp [p958] at ha; subst a; trivial
  · exact checked958
theorem derived958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c958 := by
  apply localUnsat_implies_entails f958 [c956, c912, c946, c32] c958 unsat958 (by rfl) a
  have h0 : Entails.eval a c956 := derived956 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c946 := derived946 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c959 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c957, some c825, some c956, some c591, some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked959 : lratChecker f959 p959 = .success := by decide +kernel
theorem unsat959 : Unsatisfiable (PosFin 57) f959 := by
  apply lratCheckerSound f959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p959
  · intro a ha; simp [p959] at ha; subst a; trivial
  · exact checked959
theorem derived959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c959 := by
  apply localUnsat_implies_entails f959 [c957, c825, c956, c591] c959 unsat959 (by rfl) a
  have h0 : Entails.eval a c957 := derived957 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c956 := derived956 a h
  have h3 : Entails.eval a c591 := derived591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c960 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c957, some c950, some c956, some c65, some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked960 : lratChecker f960 p960 = .success := by decide +kernel
theorem unsat960 : Unsatisfiable (PosFin 57) f960 := by
  apply lratCheckerSound f960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p960
  · intro a ha; simp [p960] at ha; subst a; trivial
  · exact checked960
theorem derived960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c960 := by
  apply localUnsat_implies_entails f960 [c957, c950, c956, c65] c960 unsat960 (by rfl) a
  have h0 : Entails.eval a c957 := derived957 a h
  have h1 : Entails.eval a c950 := derived950 a h
  have h2 : Entails.eval a c956 := derived956 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c961 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c958, some c946, some c959, some c242, some c241, some c902, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked961 : lratChecker f961 p961 = .success := by decide +kernel
theorem unsat961 : Unsatisfiable (PosFin 57) f961 := by
  apply lratCheckerSound f961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p961
  · intro a ha; simp [p961] at ha; subst a; trivial
  · exact checked961
theorem derived961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c961 := by
  apply localUnsat_implies_entails f961 [c958, c946, c959, c242, c241, c902] c961 unsat961 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c946 := derived946 a h
  have h2 : Entails.eval a c959 := derived959 a h
  have h3 : Entails.eval a c242 := h 241 (by decide)
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c902 := derived902 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c962 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c961, some c949, some c952, some c110, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked962 : lratChecker f962 p962 = .success := by decide +kernel
theorem unsat962 : Unsatisfiable (PosFin 57) f962 := by
  apply lratCheckerSound f962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p962
  · intro a ha; simp [p962] at ha; subst a; trivial
  · exact checked962
theorem derived962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c962 := by
  apply localUnsat_implies_entails f962 [c961, c949, c952, c110] c962 unsat962 (by rfl) a
  have h0 : Entails.eval a c961 := derived961 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c952 := derived952 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c963 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f963 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c962, some c956, some c957, some c732, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p963 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked963 : lratChecker f963 p963 = .success := by decide +kernel
theorem unsat963 : Unsatisfiable (PosFin 57) f963 := by
  apply lratCheckerSound f963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p963
  · intro a ha; simp [p963] at ha; subst a; trivial
  · exact checked963
theorem derived963 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c963 := by
  apply localUnsat_implies_entails f963 [c962, c956, c957, c732] c963 unsat963 (by rfl) a
  have h0 : Entails.eval a c962 := derived962 a h
  have h1 : Entails.eval a c956 := derived956 a h
  have h2 : Entails.eval a c957 := derived957 a h
  have h3 : Entails.eval a c732 := derived732 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c964 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f964 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c962, some c958, some c247, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p964 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked964 : lratChecker f964 p964 = .success := by decide +kernel
theorem unsat964 : Unsatisfiable (PosFin 57) f964 := by
  apply lratCheckerSound f964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p964
  · intro a ha; simp [p964] at ha; subst a; trivial
  · exact checked964
theorem derived964 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c964 := by
  apply localUnsat_implies_entails f964 [c962, c958, c247] c964 unsat964 (by rfl) a
  have h0 : Entails.eval a c962 := derived962 a h
  have h1 : Entails.eval a c958 := derived958 a h
  have h2 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c965 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f965 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c963, some c964, some c825, some c960, some c731, some c459]
def p965 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked965 : lratChecker f965 p965 = .success := by decide +kernel
theorem unsat965 : Unsatisfiable (PosFin 57) f965 := by
  apply lratCheckerSound f965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p965
  · intro a ha; simp [p965] at ha; subst a; trivial
  · exact checked965
theorem derived965 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c965 := by
  apply localUnsat_implies_entails f965 [c963, c964, c825, c960, c731, c459] c965 unsat965 (by rfl) a
  have h0 : Entails.eval a c963 := derived963 a h
  have h1 : Entails.eval a c964 := derived964 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c960 := derived960 a h
  have h4 : Entails.eval a c731 := derived731 a h
  have h5 : Entails.eval a c459 := derived459 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived965

end CochromaticTwenty.Certificates.B16_0_1
