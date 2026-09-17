import MerLeanExperiment.Certificates.B16_8_0Enumerating.Steps0300_0399

/-! Generated from the actual pinned b16_8_0-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_0Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c819 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c168, some c181, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 57) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c169, c168, c181] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨9, by decide⟩, false), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c819, some c1, some c87, some c86, some c99, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 57) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c819, c1, c87, c86, c99] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c819 := derived819 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c821 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c369, some c813, some c147, some c816, some c820, some c382, some c384, some c782, some c356, some c781, some c376, some c817, some c12, some c180, some c178, some c81, some c808, some c172, some c102, some c15, some c2, some c806, some c90, some c22, some c99, some c772, some c327, some c321, some c805, some c58, some c187, some c133, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 57) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c375, c369, c813, c147, c816, c820, c382, c384, c782, c356, c781, c376, c817, c12, c180, c178, c81, c808, c172, c102, c15, c2, c806, c90, c22, c99, c772, c327, c321, c805, c58, c187, c133] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c816 := derived816 a h
  have h5 : Entails.eval a c820 := derived820 a h
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c384 := h 383 (by decide)
  have h8 : Entails.eval a c782 := derived782 a h
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c781 := derived781 a h
  have h11 : Entails.eval a c376 := h 375 (by decide)
  have h12 : Entails.eval a c817 := derived817 a h
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c180 := h 179 (by decide)
  have h15 : Entails.eval a c178 := h 177 (by decide)
  have h16 : Entails.eval a c81 := h 80 (by decide)
  have h17 : Entails.eval a c808 := derived808 a h
  have h18 : Entails.eval a c172 := h 171 (by decide)
  have h19 : Entails.eval a c102 := h 101 (by decide)
  have h20 : Entails.eval a c15 := h 14 (by decide)
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c806 := derived806 a h
  have h23 : Entails.eval a c90 := h 89 (by decide)
  have h24 : Entails.eval a c22 := h 21 (by decide)
  have h25 : Entails.eval a c99 := h 98 (by decide)
  have h26 : Entails.eval a c772 := derived772 a h
  have h27 : Entails.eval a c327 := h 326 (by decide)
  have h28 : Entails.eval a c321 := h 320 (by decide)
  have h29 : Entails.eval a c805 := derived805 a h
  have h30 : Entails.eval a c58 := h 57 (by decide)
  have h31 : Entails.eval a c187 := h 186 (by decide)
  have h32 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c384, some c378, some c782, some c781, some c808, some c780, some c12, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 57) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c382, c384, c378, c782, c781, c808, c780, c12] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c382 := h 381 (by decide)
  have h1 : Entails.eval a c384 := h 383 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c782 := derived782 a h
  have h4 : Entails.eval a c781 := derived781 a h
  have h5 : Entails.eval a c808 := derived808 a h
  have h6 : Entails.eval a c780 := derived780 a h
  have h7 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c823 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c184, some c186, some c169, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 57) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c184, c186, c169] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c184 := h 183 (by decide)
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c824 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨14, by decide⟩, false), (⟨53, by decide⟩, true), (⟨16, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c86, some c93, some c102, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 57) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c17, c86, c93, c102] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c825 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨53, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c175, some c151, some c824, some c81, some c373, some c376, some c359, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 57) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c175, c151, c824, c81, c373, c376, c359] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c175 := h 174 (by decide)
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c824 := derived824 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c826 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c90, some c60, some c64, some c339, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 57) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c813, c90, c60, c64, c339] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c827 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨16, by decide⟩, false), (⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c818, some c825, some c184, some c169, some c148, some c168, some c824, some c81, some c373, some c69, some c14, some c87, some c71, some c95, some c90, some c826, some c324, some c58, some c62, some c339, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 57) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c813, c818, c825, c184, c169, c148, c168, c824, c81, c373, c69, c14, c87, c71, c95, c90, c826, c324, c58, c62, c339] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c825 := derived825 a h
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c148 := h 147 (by decide)
  have h6 : Entails.eval a c168 := h 167 (by decide)
  have h7 : Entails.eval a c824 := derived824 a h
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c373 := h 372 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c826 := derived826 a h
  have h17 : Entails.eval a c324 := h 323 (by decide)
  have h18 : Entails.eval a c58 := h 57 (by decide)
  have h19 : Entails.eval a c62 := h 61 (by decide)
  have h20 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c818, some c87, some c71, some c95, some c90, some c826, some c324, some c58, some c62, some c339, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 57) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c813, c818, c87, c71, c95, c90, c826, c324, c58, c62, c339] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c826 := derived826 a h
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c829 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c562, some c42, some c339, some c343, some c59, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 57) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c562, c42, c339, c343, c59] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c562 := derived562 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c343 := h 342 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c830 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c59, some c58, some c340, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 57) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c59, c58, c340] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c59 := h 58 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c831 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c14, some c86, some c91, some c95, some c830, some c321, some c61, some c63, some c340, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 57) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c99, c14, c86, c91, c95, c830, c321, c61, c63, c340] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c830 := derived830 a h
  have h6 : Entails.eval a c321 := h 320 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c832 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨16, by decide⟩, false), (⟨4, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c829, some c17, some c91, some c830, some c321, some c61, some c63, some c340, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 57) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c829, c17, c91, c830, c321, c61, c63, c340] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c829 := derived829 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c830 := derived830 a h
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c833 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c369, some c821, some c822, some c813, some c820, some c156, some c827, some c818, some c184, some c823, some c169, some c168, some c831, some c87, some c95, some c90, some c832, some c15, some c815, some c828, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 57) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c375, c369, c821, c822, c813, c820, c156, c827, c818, c184, c823, c169, c168, c831, c87, c95, c90, c832, c15, c815, c828] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c821 := derived821 a h
  have h3 : Entails.eval a c822 := derived822 a h
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c820 := derived820 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c827 := derived827 a h
  have h8 : Entails.eval a c818 := derived818 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c823 := derived823 a h
  have h11 : Entails.eval a c169 := h 168 (by decide)
  have h12 : Entails.eval a c168 := h 167 (by decide)
  have h13 : Entails.eval a c831 := derived831 a h
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c95 := h 94 (by decide)
  have h16 : Entails.eval a c90 := h 89 (by decide)
  have h17 : Entails.eval a c832 := derived832 a h
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c815 := derived815 a h
  have h20 : Entails.eval a c828 := derived828 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨45, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c376, some c359, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 57) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c373, c376, c359] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c87, some c86, some c99, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 57) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c87, c86, c99] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c87 := h 86 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c369, some c375, some c821, some c822, some c818, some c820, some c156, some c827, some c833, some c155, some c834, some c68, some c81, some c835, some c9, some c95, some c102, some c168, some c830, some c17, some c321, some c61, some c63, some c340, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 57) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c813, c369, c375, c821, c822, c818, c820, c156, c827, c833, c155, c834, c68, c81, c835, c9, c95, c102, c168, c830, c17, c321, c61, c63, c340] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c821 := derived821 a h
  have h4 : Entails.eval a c822 := derived822 a h
  have h5 : Entails.eval a c818 := derived818 a h
  have h6 : Entails.eval a c820 := derived820 a h
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c827 := derived827 a h
  have h9 : Entails.eval a c833 := derived833 a h
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c834 := derived834 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c835 := derived835 a h
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c95 := h 94 (by decide)
  have h17 : Entails.eval a c102 := h 101 (by decide)
  have h18 : Entails.eval a c168 := h 167 (by decide)
  have h19 : Entails.eval a c830 := derived830 a h
  have h20 : Entails.eval a c17 := h 16 (by decide)
  have h21 : Entails.eval a c321 := h 320 (by decide)
  have h22 : Entails.eval a c61 := h 60 (by decide)
  have h23 : Entails.eval a c63 := h 62 (by decide)
  have h24 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c837 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨48, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, false), (⟨45, by decide⟩, true), (⟨9, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c155, some c156, some c184, some c14, some c169, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 57) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c155, c156, c184, c14, c169] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c155 := h 154 (by decide)
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c838 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c368, some c371, some c359, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 57) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c368, c371, c359] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c368 := h 367 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c839 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c836, some c813, some c818, some c820, some c835, some c95, some c77, some c834, some c78, some c102, some c828, some c838, some c155, some c8, some c14, some c169, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 57) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c836, c813, c818, c820, c835, c95, c77, c834, c78, c102, c828, c838, c155, c8, c14, c169] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c836 := derived836 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c820 := derived820 a h
  have h4 : Entails.eval a c835 := derived835 a h
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c834 := derived834 a h
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c828 := derived828 a h
  have h11 : Entails.eval a c838 := derived838 a h
  have h12 : Entails.eval a c155 := h 154 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c14 := h 13 (by decide)
  have h15 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c836, some c839, some c382, some c384, some c362, some c433, some c361, some c371, some c376, some c147, some c360, some c378, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 57) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c813, c836, c839, c382, c384, c362, c433, c361, c371, c376, c147, c360, c378] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c836 := derived836 a h
  have h2 : Entails.eval a c839 := derived839 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c384 := h 383 (by decide)
  have h5 : Entails.eval a c362 := h 361 (by decide)
  have h6 : Entails.eval a c433 := derived433 a h
  have h7 : Entails.eval a c361 := h 360 (by decide)
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c77, some c372, some c156, some c81, some c17, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 57) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c77, c372, c156, c81, c17] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c77 := h 76 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c842 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c840, some c813, some c70, some c99, some c97, some c90, some c382, some c358, some c835, some c818, some c812, some c152, some c841, some c834, some c828, some c102, some c17, some c78, some c156, some c372, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 57) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c840, c813, c70, c99, c97, c90, c382, c358, c835, c818, c812, c152, c841, c834, c828, c102, c17, c78, c156, c372] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c840 := derived840 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c835 := derived835 a h
  have h9 : Entails.eval a c818 := derived818 a h
  have h10 : Entails.eval a c812 := derived812 a h
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c841 := derived841 a h
  have h13 : Entails.eval a c834 := derived834 a h
  have h14 : Entails.eval a c828 := derived828 a h
  have h15 : Entails.eval a c102 := h 101 (by decide)
  have h16 : Entails.eval a c17 := h 16 (by decide)
  have h17 : Entails.eval a c78 := h 77 (by decide)
  have h18 : Entails.eval a c156 := h 155 (by decide)
  have h19 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c843 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c840, some c70, some c99, some c97, some c90, some c382, some c818, some c358, some c842, some c367, some c368, some c77, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 57) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c813, c840, c70, c99, c97, c90, c382, c818, c358, c842, c367, c368, c77] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c818 := derived818 a h
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c842 := derived842 a h
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨44, by decide⟩, true), (⟨41, by decide⟩, false), (⟨4, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c67, some c362, some c97, some c371, some c80, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 57) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c67, c362, c97, c371, c80] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c67 := h 66 (by decide)
  have h1 : Entails.eval a c362 := h 361 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c97, some c90, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 57) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c99, c97, c90] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c846 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, false), (⟨4, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c845, some c844, some c80, some c369, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 57) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c845, c844, c80, c369] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c845 := derived845 a h
  have h1 : Entails.eval a c844 := derived844 a h
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c846, some c370, some c368, some c359, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 57) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c818, c846, c370, c368, c359] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c846 := derived846 a h
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c848 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c88, some c830, some c321, some c61, some c63, some c340, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 57) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c88, c830, c321, c61, c63, c340] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c88 := h 87 (by decide)
  have h1 : Entails.eval a c830 := derived830 a h
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c849 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨2, by decide⟩, true), (⟨46, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c321, some c56, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 57) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c317, c321, c56] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c321 := h 320 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c56, some c318, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 57) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c61, c56, c318] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c851 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c288, some c301, some c258, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 57) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c288, c301, c258] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c288 := h 287 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c852 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c834, some c843, some c385, some c847, some c818, some c845, some c71, some c359, some c362, some c816, some c372, some c147, some c837, some c69, some c82, some c848, some c95, some c850, some c332, some c345, some c851, some c45, some c52, some c50, some c308, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 57) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c813, c834, c843, c385, c847, c818, c845, c71, c359, c362, c816, c372, c147, c837, c69, c82, c848, c95, c850, c332, c345, c851, c45, c52, c50, c308] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c834 := derived834 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c847 := derived847 a h
  have h5 : Entails.eval a c818 := derived818 a h
  have h6 : Entails.eval a c845 := derived845 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c362 := h 361 (by decide)
  have h10 : Entails.eval a c816 := derived816 a h
  have h11 : Entails.eval a c372 := h 371 (by decide)
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c837 := derived837 a h
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c82 := h 81 (by decide)
  have h16 : Entails.eval a c848 := derived848 a h
  have h17 : Entails.eval a c95 := h 94 (by decide)
  have h18 : Entails.eval a c850 := derived850 a h
  have h19 : Entails.eval a c332 := h 331 (by decide)
  have h20 : Entails.eval a c345 := h 344 (by decide)
  have h21 : Entails.eval a c851 := derived851 a h
  have h22 : Entails.eval a c45 := h 44 (by decide)
  have h23 : Entails.eval a c52 := h 51 (by decide)
  have h24 : Entails.eval a c50 := h 49 (by decide)
  have h25 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c853 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨28, by decide⟩, false), (⟨30, by decide⟩, true), (⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c45, some c274, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 57) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c66, c45, c274] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c854 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨38, by decide⟩, false), (⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c345, some c852, some c813, some c818, some c385, some c845, some c332, some c851, some c50, some c280, some c853, some c95, some c90, some c88, some c287, some c187, some c258, some c18, some c22, some c237, some c197, some c193, some c307, some c309, some c324, some c48, some c62, some c102, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 57) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c843, c345, c852, c813, c818, c385, c845, c332, c851, c50, c280, c853, c95, c90, c88, c287, c187, c258, c18, c22, c237, c197, c193, c307, c309, c324, c48, c62, c102] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c345 := h 344 (by decide)
  have h2 : Entails.eval a c852 := derived852 a h
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c818 := derived818 a h
  have h5 : Entails.eval a c385 := h 384 (by decide)
  have h6 : Entails.eval a c845 := derived845 a h
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c851 := derived851 a h
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c853 := derived853 a h
  have h12 : Entails.eval a c95 := h 94 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c287 := h 286 (by decide)
  have h16 : Entails.eval a c187 := h 186 (by decide)
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c18 := h 17 (by decide)
  have h19 : Entails.eval a c22 := h 21 (by decide)
  have h20 : Entails.eval a c237 := h 236 (by decide)
  have h21 : Entails.eval a c197 := h 196 (by decide)
  have h22 : Entails.eval a c193 := h 192 (by decide)
  have h23 : Entails.eval a c307 := h 306 (by decide)
  have h24 : Entails.eval a c309 := h 308 (by decide)
  have h25 : Entails.eval a c324 := h 323 (by decide)
  have h26 : Entails.eval a c48 := h 47 (by decide)
  have h27 : Entails.eval a c62 := h 61 (by decide)
  have h28 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c855 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c147, some c95, some c421, some c90, some c169, some c5, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 57) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c847, c147, c95, c421, c90, c169, c5] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c421 := derived421 a h
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c856 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c147, some c855, some c87, some c5, some c169, some c172, some c177, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 57) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c847, c147, c855, c87, c5, c169, c172, c177] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c855 := derived855 a h
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c857 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨38, by decide⟩, true), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c850, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 57) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c66, c850] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c850 := derived850 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c858 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c843, some c385, some c856, some c818, some c845, some c852, some c854, some c61, some c40, some c324, some c288, some c301, some c857, some c95, some c90, some c88, some c331, some c851, some c187, some c18, some c22, some c237, some c208, some c193, some c353, some c351, some c280, some c633, some c51, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c813, c843, c385, c856, c818, c845, c852, c854, c61, c40, c324, c288, c301, c857, c95, c90, c88, c331, c851, c187, c18, c22, c237, c208, c193, c353, c351, c280, c633, c51] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c856 := derived856 a h
  have h4 : Entails.eval a c818 := derived818 a h
  have h5 : Entails.eval a c845 := derived845 a h
  have h6 : Entails.eval a c852 := derived852 a h
  have h7 : Entails.eval a c854 := derived854 a h
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c324 := h 323 (by decide)
  have h11 : Entails.eval a c288 := h 287 (by decide)
  have h12 : Entails.eval a c301 := h 300 (by decide)
  have h13 : Entails.eval a c857 := derived857 a h
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c88 := h 87 (by decide)
  have h17 : Entails.eval a c331 := h 330 (by decide)
  have h18 : Entails.eval a c851 := derived851 a h
  have h19 : Entails.eval a c187 := h 186 (by decide)
  have h20 : Entails.eval a c18 := h 17 (by decide)
  have h21 : Entails.eval a c22 := h 21 (by decide)
  have h22 : Entails.eval a c237 := h 236 (by decide)
  have h23 : Entails.eval a c208 := h 207 (by decide)
  have h24 : Entails.eval a c193 := h 192 (by decide)
  have h25 : Entails.eval a c353 := h 352 (by decide)
  have h26 : Entails.eval a c351 := h 350 (by decide)
  have h27 : Entails.eval a c280 := h 279 (by decide)
  have h28 : Entails.eval a c633 := derived633 a h
  have h29 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨44, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c95, some c67, some c375, some c81, some c102, some c89, some c848, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c80, c95, c67, c375, c81, c102, c89, c848] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c848 := derived848 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c67, some c849, some c37, some c273, some c277, some c45, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c67, c849, c37, c273, c277, c45] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c67 := h 66 (by decide)
  have h1 : Entails.eval a c849 := derived849 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c277 := h 276 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨3, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c40, some c50, some c45, some c332, some c287, some c273, some c187, some c189, some c19, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c40, c50, c45, c332, c287, c273, c187, c189, c19] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c332 := h 331 (by decide)
  have h4 : Entails.eval a c287 := h 286 (by decide)
  have h5 : Entails.eval a c273 := h 272 (by decide)
  have h6 : Entails.eval a c187 := h 186 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c385, some c813, some c845, some c818, some c858, some c80, some c859, some c66, some c860, some c68, some c856, some c375, some c849, some c81, some c861, some c288, some c301, some c277, some c189, some c28, some c19, some c196, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c843, c385, c813, c845, c818, c858, c80, c859, c66, c860, c68, c856, c375, c849, c81, c861, c288, c301, c277, c189, c28, c19, c196] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c845 := derived845 a h
  have h4 : Entails.eval a c818 := derived818 a h
  have h5 : Entails.eval a c858 := derived858 a h
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c859 := derived859 a h
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c860 := derived860 a h
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c856 := derived856 a h
  have h12 : Entails.eval a c375 := h 374 (by decide)
  have h13 : Entails.eval a c849 := derived849 a h
  have h14 : Entails.eval a c81 := h 80 (by decide)
  have h15 : Entails.eval a c861 := derived861 a h
  have h16 : Entails.eval a c288 := h 287 (by decide)
  have h17 : Entails.eval a c301 := h 300 (by decide)
  have h18 : Entails.eval a c277 := h 276 (by decide)
  have h19 : Entails.eval a c189 := h 188 (by decide)
  have h20 : Entails.eval a c28 := h 27 (by decide)
  have h21 : Entails.eval a c19 := h 18 (by decide)
  have h22 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c331, some c332, some c61, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c331, c332, c61] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c331 := h 330 (by decide)
  have h1 : Entails.eval a c332 := h 331 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c813, some c385, some c845, some c818, some c856, some c858, some c68, some c863, some c862, some c362, some c859, some c66, some c87, some c80, some c288, some c301, some c283, some c851, some c187, some c345, some c22, some c237, some c61, some c56, some c193, some c205, some c355, some c320, some c63, some c215, some c81, some c32, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c843, c813, c385, c845, c818, c856, c858, c68, c863, c862, c362, c859, c66, c87, c80, c288, c301, c283, c851, c187, c345, c22, c237, c61, c56, c193, c205, c355, c320, c63, c215, c81, c32] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c845 := derived845 a h
  have h4 : Entails.eval a c818 := derived818 a h
  have h5 : Entails.eval a c856 := derived856 a h
  have h6 : Entails.eval a c858 := derived858 a h
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c863 := derived863 a h
  have h9 : Entails.eval a c862 := derived862 a h
  have h10 : Entails.eval a c362 := h 361 (by decide)
  have h11 : Entails.eval a c859 := derived859 a h
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c288 := h 287 (by decide)
  have h16 : Entails.eval a c301 := h 300 (by decide)
  have h17 : Entails.eval a c283 := h 282 (by decide)
  have h18 : Entails.eval a c851 := derived851 a h
  have h19 : Entails.eval a c187 := h 186 (by decide)
  have h20 : Entails.eval a c345 := h 344 (by decide)
  have h21 : Entails.eval a c22 := h 21 (by decide)
  have h22 : Entails.eval a c237 := h 236 (by decide)
  have h23 : Entails.eval a c61 := h 60 (by decide)
  have h24 : Entails.eval a c56 := h 55 (by decide)
  have h25 : Entails.eval a c193 := h 192 (by decide)
  have h26 : Entails.eval a c205 := h 204 (by decide)
  have h27 : Entails.eval a c355 := h 354 (by decide)
  have h28 : Entails.eval a c320 := h 319 (by decide)
  have h29 : Entails.eval a c63 := h 62 (by decide)
  have h30 : Entails.eval a c215 := h 214 (by decide)
  have h31 : Entails.eval a c81 := h 80 (by decide)
  have h32 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c843, some c385, some c845, some c818, some c856, some c858, some c68, some c80, some c859, some c87, some c66, some c860, some c862, some c362, some c863, some c864, some c40, some c50, some c45, some c345, some c327, some c287, some c308, some c258, some c187, some c52, some c307, some c276, some c22, some c19, some c200, some c81, some c216, some c32, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c813, c843, c385, c845, c818, c856, c858, c68, c80, c859, c87, c66, c860, c862, c362, c863, c864, c40, c50, c45, c345, c327, c287, c308, c258, c187, c52, c307, c276, c22, c19, c200, c81, c216, c32] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c845 := derived845 a h
  have h4 : Entails.eval a c818 := derived818 a h
  have h5 : Entails.eval a c856 := derived856 a h
  have h6 : Entails.eval a c858 := derived858 a h
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c859 := derived859 a h
  have h10 : Entails.eval a c87 := h 86 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c860 := derived860 a h
  have h13 : Entails.eval a c862 := derived862 a h
  have h14 : Entails.eval a c362 := h 361 (by decide)
  have h15 : Entails.eval a c863 := derived863 a h
  have h16 : Entails.eval a c864 := derived864 a h
  have h17 : Entails.eval a c40 := h 39 (by decide)
  have h18 : Entails.eval a c50 := h 49 (by decide)
  have h19 : Entails.eval a c45 := h 44 (by decide)
  have h20 : Entails.eval a c345 := h 344 (by decide)
  have h21 : Entails.eval a c327 := h 326 (by decide)
  have h22 : Entails.eval a c287 := h 286 (by decide)
  have h23 : Entails.eval a c308 := h 307 (by decide)
  have h24 : Entails.eval a c258 := h 257 (by decide)
  have h25 : Entails.eval a c187 := h 186 (by decide)
  have h26 : Entails.eval a c52 := h 51 (by decide)
  have h27 : Entails.eval a c307 := h 306 (by decide)
  have h28 : Entails.eval a c276 := h 275 (by decide)
  have h29 : Entails.eval a c22 := h 21 (by decide)
  have h30 : Entails.eval a c19 := h 18 (by decide)
  have h31 : Entails.eval a c200 := h 199 (by decide)
  have h32 : Entails.eval a c81 := h 80 (by decide)
  have h33 : Entails.eval a c216 := h 215 (by decide)
  have h34 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨44, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c865, some c384, some c813, some c843, some c385, some c845, some c68, some c80, some c846, some c859, some c378, some c772, some c540, some c147, some c356, some c345, some c42, some c816, some c194, some c327, some c250, some c267, some c281, some c283, some c52, some c204, some c32, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c865, c384, c813, c843, c385, c845, c68, c80, c846, c859, c378, c772, c540, c147, c356, c345, c42, c816, c194, c327, c250, c267, c281, c283, c52, c204, c32] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c865 := derived865 a h
  have h1 : Entails.eval a c384 := h 383 (by decide)
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c845 := derived845 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c846 := derived846 a h
  have h9 : Entails.eval a c859 := derived859 a h
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c772 := derived772 a h
  have h12 : Entails.eval a c540 := derived540 a h
  have h13 : Entails.eval a c147 := h 146 (by decide)
  have h14 : Entails.eval a c356 := h 355 (by decide)
  have h15 : Entails.eval a c345 := h 344 (by decide)
  have h16 : Entails.eval a c42 := h 41 (by decide)
  have h17 : Entails.eval a c816 := derived816 a h
  have h18 : Entails.eval a c194 := h 193 (by decide)
  have h19 : Entails.eval a c327 := h 326 (by decide)
  have h20 : Entails.eval a c250 := h 249 (by decide)
  have h21 : Entails.eval a c267 := h 266 (by decide)
  have h22 : Entails.eval a c281 := h 280 (by decide)
  have h23 : Entails.eval a c283 := h 282 (by decide)
  have h24 : Entails.eval a c52 := h 51 (by decide)
  have h25 : Entails.eval a c204 := h 203 (by decide)
  have h26 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c345, some c813, some c385, some c98, some c90, some c71, some c865, some c845, some c96, some c540, some c384, some c371, some c419, some c327, some c147, some c356, some c267, some c3, some c2, some c283, some c531, some c817, some c171, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c843, c345, c813, c385, c98, c90, c71, c865, c845, c96, c540, c384, c371, c419, c327, c147, c356, c267, c3, c2, c283, c531, c817, c171] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c345 := h 344 (by decide)
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c865 := derived865 a h
  have h8 : Entails.eval a c845 := derived845 a h
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c540 := derived540 a h
  have h11 : Entails.eval a c384 := h 383 (by decide)
  have h12 : Entails.eval a c371 := h 370 (by decide)
  have h13 : Entails.eval a c419 := derived419 a h
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c147 := h 146 (by decide)
  have h16 : Entails.eval a c356 := h 355 (by decide)
  have h17 : Entails.eval a c267 := h 266 (by decide)
  have h18 : Entails.eval a c3 := h 2 (by decide)
  have h19 : Entails.eval a c2 := h 1 (by decide)
  have h20 : Entails.eval a c283 := h 282 (by decide)
  have h21 : Entails.eval a c531 := derived531 a h
  have h22 : Entails.eval a c817 := derived817 a h
  have h23 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c325, some c319, some c57, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c325, c319, c57] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c325 := h 324 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨45, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c281, some c275, some c46, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c281, c275, c46] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c281 := h 280 (by decide)
  have h1 : Entails.eval a c275 := h 274 (by decide)
  have h2 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c98, some c71, some c843, some c865, some c385, some c845, some c96, some c540, some c384, some c345, some c194, some c42, some c867, some c75, some c768, some c868, some c869, some c39, some c191, some c32, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c813, c98, c71, c843, c865, c385, c845, c96, c540, c384, c345, c194, c42, c867, c75, c768, c868, c869, c39, c191, c32] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c865 := derived865 a h
  have h5 : Entails.eval a c385 := h 384 (by decide)
  have h6 : Entails.eval a c845 := derived845 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c540 := derived540 a h
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c345 := h 344 (by decide)
  have h11 : Entails.eval a c194 := h 193 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c867 := derived867 a h
  have h14 : Entails.eval a c75 := h 74 (by decide)
  have h15 : Entails.eval a c768 := derived768 a h
  have h16 : Entails.eval a c868 := derived868 a h
  have h17 : Entails.eval a c869 := derived869 a h
  have h18 : Entails.eval a c39 := h 38 (by decide)
  have h19 : Entails.eval a c191 := h 190 (by decide)
  have h20 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c843, some c385, some c98, some c90, some c71, some c865, some c845, some c96, some c540, some c384, some c538, some c870, some c40, some c56, some c337, some c335, some c194, some c265, some c517, some c250, some c46, some c213, some c283, some c306, some c311, some c20, some c75, some c195, some c768, some c319, some c29, some c63, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c813, c843, c385, c98, c90, c71, c865, c845, c96, c540, c384, c538, c870, c40, c56, c337, c335, c194, c265, c517, c250, c46, c213, c283, c306, c311, c20, c75, c195, c768, c319, c29, c63] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c865 := derived865 a h
  have h7 : Entails.eval a c845 := derived845 a h
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c540 := derived540 a h
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c538 := derived538 a h
  have h12 : Entails.eval a c870 := derived870 a h
  have h13 : Entails.eval a c40 := h 39 (by decide)
  have h14 : Entails.eval a c56 := h 55 (by decide)
  have h15 : Entails.eval a c337 := h 336 (by decide)
  have h16 : Entails.eval a c335 := h 334 (by decide)
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c265 := h 264 (by decide)
  have h19 : Entails.eval a c517 := derived517 a h
  have h20 : Entails.eval a c250 := h 249 (by decide)
  have h21 : Entails.eval a c46 := h 45 (by decide)
  have h22 : Entails.eval a c213 := h 212 (by decide)
  have h23 : Entails.eval a c283 := h 282 (by decide)
  have h24 : Entails.eval a c306 := h 305 (by decide)
  have h25 : Entails.eval a c311 := h 310 (by decide)
  have h26 : Entails.eval a c20 := h 19 (by decide)
  have h27 : Entails.eval a c75 := h 74 (by decide)
  have h28 : Entails.eval a c195 := h 194 (by decide)
  have h29 : Entails.eval a c768 := derived768 a h
  have h30 : Entails.eval a c319 := h 318 (by decide)
  have h31 : Entails.eval a c29 := h 28 (by decide)
  have h32 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c865, some c813, some c843, some c385, some c845, some c345, some c337, some c56, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c865, c813, c843, c385, c845, c345, c337, c56] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c865 := derived865 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c845 := derived845 a h
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c337 := h 336 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c171, some c172, some c186, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c171, c172, c186] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c171 := h 170 (by decide)
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c872, some c871, some c865, some c813, some c843, some c385, some c845, some c40, some c56, some c851, some c329, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c96, c872, c871, c865, c813, c843, c385, c845, c40, c56, c851, c329] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c872 := derived872 a h
  have h2 : Entails.eval a c871 := derived871 a h
  have h3 : Entails.eval a c865 := derived865 a h
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c843 := derived843 a h
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c845 := derived845 a h
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c851 := derived851 a h
  have h11 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c865, some c813, some c843, some c385, some c845, some c96, some c540, some c871, some c872, some c874, some c332, some c851, some c258, some c45, some c285, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c865, c813, c843, c385, c845, c96, c540, c871, c872, c874, c332, c851, c258, c45, c285] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c865 := derived865 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c845 := derived845 a h
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c540 := derived540 a h
  have h7 : Entails.eval a c871 := derived871 a h
  have h8 : Entails.eval a c872 := derived872 a h
  have h9 : Entails.eval a c874 := derived874 a h
  have h10 : Entails.eval a c332 := h 331 (by decide)
  have h11 : Entails.eval a c851 := derived851 a h
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨38, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c872, some c843, some c865, some c813, some c385, some c845, some c540, some c332, some c851, some c258, some c45, some c285, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c872, c843, c865, c813, c385, c845, c540, c332, c851, c258, c45, c285] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c872 := derived872 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c865 := derived865 a h
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c845 := derived845 a h
  have h6 : Entails.eval a c540 := derived540 a h
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c851 := derived851 a h
  have h9 : Entails.eval a c258 := h 257 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨22, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c45, some c308, some c52, some c204, some c32, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c50, c45, c308, c52, c204, c32] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c308 := h 307 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true), (⟨44, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c845, some c376, some c373, some c362, some c816, some c75, some c147, some c369, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c845, c376, c373, c362, c816, c75, c147, c369] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c845 := derived845 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c816 := derived816 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨40, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c845, some c878, some c356, some c768, some c542, some c75, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c845, c878, c356, c768, c542, c75] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c845 := derived845 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c768 := derived768 a h
  have h4 : Entails.eval a c542 := derived542 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c875, some c866, some c865, some c384, some c813, some c843, some c385, some c845, some c540, some c872, some c194, some c42, some c250, some c877, some c879, some c851, some c876, some c329, some c56, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c875, c866, c865, c384, c813, c843, c385, c845, c540, c872, c194, c42, c250, c877, c879, c851, c876, c329, c56] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c875 := derived875 a h
  have h1 : Entails.eval a c866 := derived866 a h
  have h2 : Entails.eval a c865 := derived865 a h
  have h3 : Entails.eval a c384 := h 383 (by decide)
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c843 := derived843 a h
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c845 := derived845 a h
  have h8 : Entails.eval a c540 := derived540 a h
  have h9 : Entails.eval a c872 := derived872 a h
  have h10 : Entails.eval a c194 := h 193 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c250 := h 249 (by decide)
  have h13 : Entails.eval a c877 := derived877 a h
  have h14 : Entails.eval a c879 := derived879 a h
  have h15 : Entails.eval a c851 := derived851 a h
  have h16 : Entails.eval a c876 := derived876 a h
  have h17 : Entails.eval a c329 := h 328 (by decide)
  have h18 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c385, some c875, some c880, some c95, some c88, some c865, some c384, some c89, some c102, some c475, some c378, some c866, some c813, some c845, some c61, some c40, some c335, some c301, some c545, some c188, some c51, some c18, some c196, some c305, some c270, some c260, some c147, some c324, some c816, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c843, c385, c875, c880, c95, c88, c865, c384, c89, c102, c475, c378, c866, c813, c845, c61, c40, c335, c301, c545, c188, c51, c18, c196, c305, c270, c260, c147, c324, c816] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c875 := derived875 a h
  have h3 : Entails.eval a c880 := derived880 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c865 := derived865 a h
  have h7 : Entails.eval a c384 := h 383 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c475 := derived475 a h
  have h11 : Entails.eval a c378 := h 377 (by decide)
  have h12 : Entails.eval a c866 := derived866 a h
  have h13 : Entails.eval a c813 := derived813 a h
  have h14 : Entails.eval a c845 := derived845 a h
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c40 := h 39 (by decide)
  have h17 : Entails.eval a c335 := h 334 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c545 := derived545 a h
  have h20 : Entails.eval a c188 := h 187 (by decide)
  have h21 : Entails.eval a c51 := h 50 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c196 := h 195 (by decide)
  have h24 : Entails.eval a c305 := h 304 (by decide)
  have h25 : Entails.eval a c270 := h 269 (by decide)
  have h26 : Entails.eval a c260 := h 259 (by decide)
  have h27 : Entails.eval a c147 := h 146 (by decide)
  have h28 : Entails.eval a c324 := h 323 (by decide)
  have h29 : Entails.eval a c816 := derived816 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c843, some c385, some c845, some c865, some c384, some c875, some c866, some c880, some c95, some c88, some c89, some c378, some c102, some c475, some c881, some c345, some c42, some c62, some c301, some c335, some c50, some c545, some c188, some c18, some c207, some c350, some c314, some c260, some c147, some c280, some c816, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c813, c843, c385, c845, c865, c384, c875, c866, c880, c95, c88, c89, c378, c102, c475, c881, c345, c42, c62, c301, c335, c50, c545, c188, c18, c207, c350, c314, c260, c147, c280, c816] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c845 := derived845 a h
  have h4 : Entails.eval a c865 := derived865 a h
  have h5 : Entails.eval a c384 := h 383 (by decide)
  have h6 : Entails.eval a c875 := derived875 a h
  have h7 : Entails.eval a c866 := derived866 a h
  have h8 : Entails.eval a c880 := derived880 a h
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c378 := h 377 (by decide)
  have h13 : Entails.eval a c102 := h 101 (by decide)
  have h14 : Entails.eval a c475 := derived475 a h
  have h15 : Entails.eval a c881 := derived881 a h
  have h16 : Entails.eval a c345 := h 344 (by decide)
  have h17 : Entails.eval a c42 := h 41 (by decide)
  have h18 : Entails.eval a c62 := h 61 (by decide)
  have h19 : Entails.eval a c301 := h 300 (by decide)
  have h20 : Entails.eval a c335 := h 334 (by decide)
  have h21 : Entails.eval a c50 := h 49 (by decide)
  have h22 : Entails.eval a c545 := derived545 a h
  have h23 : Entails.eval a c188 := h 187 (by decide)
  have h24 : Entails.eval a c18 := h 17 (by decide)
  have h25 : Entails.eval a c207 := h 206 (by decide)
  have h26 : Entails.eval a c350 := h 349 (by decide)
  have h27 : Entails.eval a c314 := h 313 (by decide)
  have h28 : Entails.eval a c260 := h 259 (by decide)
  have h29 : Entails.eval a c147 := h 146 (by decide)
  have h30 : Entails.eval a c280 := h 279 (by decide)
  have h31 : Entails.eval a c816 := derived816 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨40, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c65, some c813, some c370, some c368, some c596, some c359, some c102, some c384, some c84, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c882, c65, c813, c370, c368, c596, c359, c102, c384, c84] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c596 := derived596 a h
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c384 := h 383 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨40, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c813, some c65, some c883, some c80, some c371, some c369, some c362, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c882, c813, c65, c883, c80, c371, c369, c362] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c883 := derived883 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c371 := h 370 (by decide)
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c882, some c345, some c884, some c332, some c55, some c35, some c851, some c100, some c50, some c88, some c287, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c385, c882, c345, c884, c332, c55, c35, c851, c100, c50, c88, c287] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c882 := derived882 a h
  have h2 : Entails.eval a c345 := h 344 (by decide)
  have h3 : Entails.eval a c884 := derived884 a h
  have h4 : Entails.eval a c332 := h 331 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c851 := derived851 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨32, by decide⟩, true), (⟨30, by decide⟩, false), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c288, some c35, some c44, some c331, some c100, some c88, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c288, c35, c44, c331, c100, c88] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c288 := h 287 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c331 := h 330 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨49, by decide⟩, true), (⟨38, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c102, some c100, some c84, some c63, some c88, some c340, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c61, c102, c100, c84, c63, c88, c340] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c882, some c885, some c61, some c40, some c301, some c886, some c65, some c887, some c447, some c44, some c80, some c271, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c385, c882, c885, c61, c40, c301, c886, c65, c887, c447, c44, c80, c271] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c882 := derived882 a h
  have h2 : Entails.eval a c885 := derived885 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c886 := derived886 a h
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c887 := derived887 a h
  have h9 : Entails.eval a c447 := derived447 a h
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨32, by decide⟩, true), (⟨37, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c813, some c65, some c84, some c384, some c343, some c42, some c100, some c67, some c367, some c369, some c450, some c359, some c82, some c281, some c325, some c267, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c882, c813, c65, c84, c384, c343, c42, c100, c67, c367, c369, c450, c359, c82, c281, c325, c267] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c384 := h 383 (by decide)
  have h5 : Entails.eval a c343 := h 342 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c450 := derived450 a h
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c281 := h 280 (by decide)
  have h15 : Entails.eval a c325 := h 324 (by decide)
  have h16 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c888, some c101, some c385, some c882, some c813, some c40, some c63, some c301, some c889, some c288, some c44, some c43, some c100, some c90, some c89, some c343, some c194, some c250, some c26, some c208, some c352, some c265, some c213, some c308, some c311, some c30, some c198, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c888, c101, c385, c882, c813, c40, c63, c301, c889, c288, c44, c43, c100, c90, c89, c343, c194, c250, c26, c208, c352, c265, c213, c308, c311, c30, c198] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c888 := derived888 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c882 := derived882 a h
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c889 := derived889 a h
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c100 := h 99 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c89 := h 88 (by decide)
  have h15 : Entails.eval a c343 := h 342 (by decide)
  have h16 : Entails.eval a c194 := h 193 (by decide)
  have h17 : Entails.eval a c250 := h 249 (by decide)
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c208 := h 207 (by decide)
  have h20 : Entails.eval a c352 := h 351 (by decide)
  have h21 : Entails.eval a c265 := h 264 (by decide)
  have h22 : Entails.eval a c213 := h 212 (by decide)
  have h23 : Entails.eval a c308 := h 307 (by decide)
  have h24 : Entails.eval a c311 := h 310 (by decide)
  have h25 : Entails.eval a c30 := h 29 (by decide)
  have h26 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c890, some c345, some c888, some c101, some c385, some c882, some c813, some c332, some c55, some c35, some c851, some c54, some c100, some c52, some c90, some c89, some c299, some c194, some c250, some c26, some c197, some c303, some c202, some c265, some c30, some c355, some c352, some c209, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c890, c345, c888, c101, c385, c882, c813, c332, c55, c35, c851, c54, c100, c52, c90, c89, c299, c194, c250, c26, c197, c303, c202, c265, c30, c355, c352, c209] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c890 := derived890 a h
  have h1 : Entails.eval a c345 := h 344 (by decide)
  have h2 : Entails.eval a c888 := derived888 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c882 := derived882 a h
  have h6 : Entails.eval a c813 := derived813 a h
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c851 := derived851 a h
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c100 := h 99 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c299 := h 298 (by decide)
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c250 := h 249 (by decide)
  have h19 : Entails.eval a c26 := h 25 (by decide)
  have h20 : Entails.eval a c197 := h 196 (by decide)
  have h21 : Entails.eval a c303 := h 302 (by decide)
  have h22 : Entails.eval a c202 := h 201 (by decide)
  have h23 : Entails.eval a c265 := h 264 (by decide)
  have h24 : Entails.eval a c30 := h 29 (by decide)
  have h25 : Entails.eval a c355 := h 354 (by decide)
  have h26 : Entails.eval a c352 := h 351 (by decide)
  have h27 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨49, by decide⟩, true), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c84, some c65, some c100, some c67, some c450, some c299, some c889, some c633, some c54, some c348, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c882, c84, c65, c100, c67, c450, c299, c889, c633, c54, c348] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c450 := derived450 a h
  have h6 : Entails.eval a c299 := h 298 (by decide)
  have h7 : Entails.eval a c889 := derived889 a h
  have h8 : Entails.eval a c633 := derived633 a h
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c882, some c888, some c101, some c890, some c345, some c891, some c84, some c892, some c42, some c301, some c299, some c52, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c385, c882, c888, c101, c890, c345, c891, c84, c892, c42, c301, c299, c52] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c882 := derived882 a h
  have h2 : Entails.eval a c888 := derived888 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c890 := derived890 a h
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c891 := derived891 a h
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c892 := derived892 a h
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c894 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨38, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c345, some c893, some c882, some c55, some c42, some c350, some c315, some c301, some c64, some c75, some c45, some c104, some c731, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked894 : lratChecker f894 p894 = .success := by decide +kernel
theorem unsat894 : Unsatisfiable (PosFin 57) f894 := by
  apply lratCheckerSound f894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p894
  · intro a ha; simp [p894] at ha; subst a; trivial
  · exact checked894
theorem derived894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c894 := by
  apply localUnsat_implies_entails f894 [c345, c893, c882, c55, c42, c350, c315, c301, c64, c75, c45, c104, c731] c894 unsat894 (by rfl) a
  have h0 : Entails.eval a c345 := h 344 (by decide)
  have h1 : Entails.eval a c893 := derived893 a h
  have h2 : Entails.eval a c882 := derived882 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c350 := h 349 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c731 := derived731 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c895 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨41, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c893, some c882, some c813, some c301, some c540, some c45, some c87, some c66, some c309, some c104, some c268, some c43, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked895 : lratChecker f895 p895 = .success := by decide +kernel
theorem unsat895 : Unsatisfiable (PosFin 57) f895 := by
  apply lratCheckerSound f895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p895
  · intro a ha; simp [p895] at ha; subst a; trivial
  · exact checked895
theorem derived895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c895 := by
  apply localUnsat_implies_entails f895 [c893, c882, c813, c301, c540, c45, c87, c66, c309, c104, c268, c43] c895 unsat895 (by rfl) a
  have h0 : Entails.eval a c893 := derived893 a h
  have h1 : Entails.eval a c882 := derived882 a h
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c301 := h 300 (by decide)
  have h4 : Entails.eval a c540 := derived540 a h
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c896 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨24, by decide⟩, false), (⟨8, by decide⟩, false), (⟨49, by decide⟩, true), (⟨38, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c65, some c813, some c84, some c384, some c248, some c87, some c66, some c368, some c367, some c67, some c362, some c149, some c28, some c371, some c11, some c82, some c374, some c163, some c13, some c169, some c178, some c183, some c105, some c114, some c221, some c140, some c211, some c212, some c325, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked896 : lratChecker f896 p896 = .success := by decide +kernel
theorem unsat896 : Unsatisfiable (PosFin 57) f896 := by
  apply lratCheckerSound f896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p896
  · intro a ha; simp [p896] at ha; subst a; trivial
  · exact checked896
theorem derived896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c896 := by
  apply localUnsat_implies_entails f896 [c882, c65, c813, c84, c384, c248, c87, c66, c368, c367, c67, c362, c149, c28, c371, c11, c82, c374, c163, c13, c169, c178, c183, c105, c114, c221, c140, c211, c212, c325] c896 unsat896 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c384 := h 383 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c362 := h 361 (by decide)
  have h12 : Entails.eval a c149 := h 148 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c371 := h 370 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c82 := h 81 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c163 := h 162 (by decide)
  have h19 : Entails.eval a c13 := h 12 (by decide)
  have h20 : Entails.eval a c169 := h 168 (by decide)
  have h21 : Entails.eval a c178 := h 177 (by decide)
  have h22 : Entails.eval a c183 := h 182 (by decide)
  have h23 : Entails.eval a c105 := h 104 (by decide)
  have h24 : Entails.eval a c114 := h 113 (by decide)
  have h25 : Entails.eval a c221 := h 220 (by decide)
  have h26 : Entails.eval a c140 := h 139 (by decide)
  have h27 : Entails.eval a c211 := h 210 (by decide)
  have h28 : Entails.eval a c212 := h 211 (by decide)
  have h29 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c897 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨38, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c345, some c893, some c385, some c882, some c813, some c65, some c894, some c895, some c194, some c250, some c896, some c32, some c104, some c71, some c87, some c371, some c384, some c75, some c768, some c868, some c869, some c191, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked897 : lratChecker f897 p897 = .success := by decide +kernel
theorem unsat897 : Unsatisfiable (PosFin 57) f897 := by
  apply lratCheckerSound f897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p897
  · intro a ha; simp [p897] at ha; subst a; trivial
  · exact checked897
theorem derived897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c897 := by
  apply localUnsat_implies_entails f897 [c345, c893, c385, c882, c813, c65, c894, c895, c194, c250, c896, c32, c104, c71, c87, c371, c384, c75, c768, c868, c869, c191] c897 unsat897 (by rfl) a
  have h0 : Entails.eval a c345 := h 344 (by decide)
  have h1 : Entails.eval a c893 := derived893 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c882 := derived882 a h
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c894 := derived894 a h
  have h7 : Entails.eval a c895 := derived895 a h
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c896 := derived896 a h
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c384 := h 383 (by decide)
  have h17 : Entails.eval a c75 := h 74 (by decide)
  have h18 : Entails.eval a c768 := derived768 a h
  have h19 : Entails.eval a c868 := derived868 a h
  have h20 : Entails.eval a c869 := derived869 a h
  have h21 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c898 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c893, some c882, some c813, some c345, some c897, some c332, some c35, some c851, some c45, some c285, some c87, some c66, some c104, some c268, some c52, some c73, some c275, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked898 : lratChecker f898 p898 = .success := by decide +kernel
theorem unsat898 : Unsatisfiable (PosFin 57) f898 := by
  apply lratCheckerSound f898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p898
  · intro a ha; simp [p898] at ha; subst a; trivial
  · exact checked898
theorem derived898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c898 := by
  apply localUnsat_implies_entails f898 [c893, c882, c813, c345, c897, c332, c35, c851, c45, c285, c87, c66, c104, c268, c52, c73, c275] c898 unsat898 (by rfl) a
  have h0 : Entails.eval a c893 := derived893 a h
  have h1 : Entails.eval a c882 := derived882 a h
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c897 := derived897 a h
  have h5 : Entails.eval a c332 := h 331 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c851 := derived851 a h
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c285 := h 284 (by decide)
  have h10 : Entails.eval a c87 := h 86 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c52 := h 51 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c899 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c893, some c898, some c56, some c40, some c882, some c813, some c288, some c35, some c329, some c87, some c66, some c104, some c312, some c63, some c73, some c319, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked899 : lratChecker f899 p899 = .success := by decide +kernel
theorem unsat899 : Unsatisfiable (PosFin 57) f899 := by
  apply lratCheckerSound f899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p899
  · intro a ha; simp [p899] at ha; subst a; trivial
  · exact checked899
theorem derived899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c899 := by
  apply localUnsat_implies_entails f899 [c893, c898, c56, c40, c882, c813, c288, c35, c329, c87, c66, c104, c312, c63, c73, c319] c899 unsat899 (by rfl) a
  have h0 : Entails.eval a c893 := derived893 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c882 := derived882 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c329 := h 328 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c312 := h 311 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  have h15 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c900 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨49, by decide⟩, true), (⟨38, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c65, some c56, some c40, some c84, some c63, some c384, some c66, some c312, some c319, some c35, some c82, some c271, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked900 : lratChecker f900 p900 = .success := by decide +kernel
theorem unsat900 : Unsatisfiable (PosFin 57) f900 := by
  apply lratCheckerSound f900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p900
  · intro a ha; simp [p900] at ha; subst a; trivial
  · exact checked900
theorem derived900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c900 := by
  apply localUnsat_implies_entails f900 [c882, c65, c56, c40, c84, c63, c384, c66, c312, c319, c35, c82, c271] c900 unsat900 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c312 := h 311 (by decide)
  have h9 : Entails.eval a c319 := h 318 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c901 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c893, some c385, some c882, some c813, some c898, some c56, some c899, some c65, some c900, some c104, some c71, some c90, some c87, some c371, some c384, some c75, some c483, some c768, some c312, some c746, some c868, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked901 : lratChecker f901 p901 = .success := by decide +kernel
theorem unsat901 : Unsatisfiable (PosFin 57) f901 := by
  apply lratCheckerSound f901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p901
  · intro a ha; simp [p901] at ha; subst a; trivial
  · exact checked901
theorem derived901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c901 := by
  apply localUnsat_implies_entails f901 [c893, c385, c882, c813, c898, c56, c899, c65, c900, c104, c71, c90, c87, c371, c384, c75, c483, c768, c312, c746, c868] c901 unsat901 (by rfl) a
  have h0 : Entails.eval a c893 := derived893 a h
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c882 := derived882 a h
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c898 := derived898 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c899 := derived899 a h
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c900 := derived900 a h
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c371 := h 370 (by decide)
  have h14 : Entails.eval a c384 := h 383 (by decide)
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c483 := derived483 a h
  have h17 : Entails.eval a c768 := derived768 a h
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c746 := derived746 a h
  have h20 : Entails.eval a c868 := derived868 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c902 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c368, some c367, some c80, some c362, some c371, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked902 : lratChecker f902 p902 = .success := by decide +kernel
theorem unsat902 : Unsatisfiable (PosFin 57) f902 := by
  apply lratCheckerSound f902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p902
  · intro a ha; simp [p902] at ha; subst a; trivial
  · exact checked902
theorem derived902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c902 := by
  apply localUnsat_implies_entails f902 [c368, c367, c80, c362, c371] c902 unsat902 (by rfl) a
  have h0 : Entails.eval a c368 := h 367 (by decide)
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c903 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c902, some c75, some c371, some c369, some c362, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked903 : lratChecker f903 p903 = .success := by decide +kernel
theorem unsat903 : Unsatisfiable (PosFin 57) f903 := by
  apply lratCheckerSound f903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p903
  · intro a ha; simp [p903] at ha; subst a; trivial
  · exact checked903
theorem derived903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c903 := by
  apply localUnsat_implies_entails f903 [c902, c75, c371, c369, c362] c903 unsat903 (by rfl) a
  have h0 : Entails.eval a c902 := derived902 a h
  have h1 : Entails.eval a c75 := h 74 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c369 := h 368 (by decide)
  have h4 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c904 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c40, some c56, some c347, some c288, some c35, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked904 : lratChecker f904 p904 = .success := by decide +kernel
theorem unsat904 : Unsatisfiable (PosFin 57) f904 := by
  apply lratCheckerSound f904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p904
  · intro a ha; simp [p904] at ha; subst a; trivial
  · exact checked904
theorem derived904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c904 := by
  apply localUnsat_implies_entails f904 [c61, c40, c56, c347, c288, c35] c904 unsat904 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c288 := h 287 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c905 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c882, some c813, some c893, some c901, some c903, some c65, some c904, some c345, some c332, some c35, some c851, some c50, some c45, some c303, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked905 : lratChecker f905 p905 = .success := by decide +kernel
theorem unsat905 : Unsatisfiable (PosFin 57) f905 := by
  apply lratCheckerSound f905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p905
  · intro a ha; simp [p905] at ha; subst a; trivial
  · exact checked905
theorem derived905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c905 := by
  apply localUnsat_implies_entails f905 [c385, c882, c813, c893, c901, c903, c65, c904, c345, c332, c35, c851, c50, c45, c303] c905 unsat905 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c882 := derived882 a h
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c893 := derived893 a h
  have h4 : Entails.eval a c901 := derived901 a h
  have h5 : Entails.eval a c903 := derived903 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c904 := derived904 a h
  have h8 : Entails.eval a c345 := h 344 (by decide)
  have h9 : Entails.eval a c332 := h 331 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c851 := derived851 a h
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c906 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨37, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, true), (⟨8, by decide⟩, false), (⟨33, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c54, some c35, some c250, some c32, some c202, some c593, some c206, some c251, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked906 : lratChecker f906 p906 = .success := by decide +kernel
theorem unsat906 : Unsatisfiable (PosFin 57) f906 := by
  apply lratCheckerSound f906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p906
  · intro a ha; simp [p906] at ha; subst a; trivial
  · exact checked906
theorem derived906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c906 := by
  apply localUnsat_implies_entails f906 [c882, c54, c35, c250, c32, c202, c593, c206, c251] c906 unsat906 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c250 := h 249 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c593 := derived593 a h
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c907 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c905, some c385, some c882, some c55, some c35, some c103, some c88, some c287, some c38, some c47, some c302, some c36, some c352, some c906, some c207, some c236, some c237, some c202, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked907 : lratChecker f907 p907 = .success := by decide +kernel
theorem unsat907 : Unsatisfiable (PosFin 57) f907 := by
  apply lratCheckerSound f907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p907
  · intro a ha; simp [p907] at ha; subst a; trivial
  · exact checked907
theorem derived907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c907 := by
  apply localUnsat_implies_entails f907 [c905, c385, c882, c55, c35, c103, c88, c287, c38, c47, c302, c36, c352, c906, c207, c236, c237, c202] c907 unsat907 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c882 := derived882 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c287 := h 286 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c302 := h 301 (by decide)
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c352 := h 351 (by decide)
  have h13 : Entails.eval a c906 := derived906 a h
  have h14 : Entails.eval a c207 := h 206 (by decide)
  have h15 : Entails.eval a c236 := h 235 (by decide)
  have h16 : Entails.eval a c237 := h 236 (by decide)
  have h17 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c908 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨24, by decide⟩, true), (⟨22, by decide⟩, false), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c349, some c57, some c216, some c33, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked908 : lratChecker f908 p908 = .success := by decide +kernel
theorem unsat908 : Unsatisfiable (PosFin 57) f908 := by
  apply lratCheckerSound f908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p908
  · intro a ha; simp [p908] at ha; subst a; trivial
  · exact checked908
theorem derived908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c908 := by
  apply localUnsat_implies_entails f908 [c347, c349, c57, c216, c33] c908 unsat908 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c349 := h 348 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c909 : DefaultClause 57 := directClause ((⟨12, by decide⟩, true) :: (⟨11, by decide⟩, false) :: (⟨1, by decide⟩, true) :: (⟨2, by decide⟩, true) :: (⟨3, by decide⟩, true) :: (⟨4, by decide⟩, true) :: (⟨7, by decide⟩, false) :: (⟨5, by decide⟩, false) :: (⟨6, by decide⟩, false) :: (⟨8, by decide⟩, false) :: (⟨56, by decide⟩, false) :: (⟨9, by decide⟩, true) :: (⟨13, by decide⟩, true) :: (⟨14, by decide⟩, true) :: (⟨15, by decide⟩, false) :: (⟨16, by decide⟩, false) :: (⟨17, by decide⟩, true) :: (⟨18, by decide⟩, true) :: (⟨19, by decide⟩, true) :: (⟨20, by decide⟩, false) :: (⟨21, by decide⟩, false) :: (⟨22, by decide⟩, false) :: (⟨23, by decide⟩, true) :: (⟨24, by decide⟩, true) :: (⟨25, by decide⟩, true) :: (⟨26, by decide⟩, false) :: (⟨27, by decide⟩, true) :: (⟨28, by decide⟩, false) :: (⟨29, by decide⟩, true) :: (⟨30, by decide⟩, true) :: (⟨31, by decide⟩, false) :: (⟨32, by decide⟩, false) :: (⟨33, by decide⟩, false) :: (⟨34, by decide⟩, true) :: (⟨35, by decide⟩, false) :: (⟨36, by decide⟩, true) :: (⟨37, by decide⟩, false) :: (⟨38, by decide⟩, true) :: (⟨39, by decide⟩, false) :: (⟨40, by decide⟩, true) :: (⟨41, by decide⟩, true) :: (⟨42, by decide⟩, false) :: (⟨43, by decide⟩, false) :: (⟨44, by decide⟩, true) :: (⟨45, by decide⟩, false) :: (⟨46, by decide⟩, false) :: (⟨47, by decide⟩, true) :: (⟨48, by decide⟩, true) :: (⟨49, by decide⟩, false) :: (⟨50, by decide⟩, true) :: (⟨51, by decide⟩, true) :: (⟨52, by decide⟩, false) :: (⟨53, by decide⟩, true) :: (⟨54, by decide⟩, false) :: (⟨55, by decide⟩, true) :: []) (by decide +kernel) (by decide +kernel)
def f909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c182, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked909 : lratChecker f909 p909 = .success := by decide +kernel
theorem unsat909 : Unsatisfiable (PosFin 57) f909 := by
  apply lratCheckerSound f909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p909
  · intro a ha; simp [p909] at ha; subst a; trivial
  · exact checked909
theorem derived909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c909 := by
  apply localUnsat_implies_entails f909 [c391, c182] c909 unsat909 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c910 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨46, by decide⟩, false), (⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c905, some c907, some c332, some c192, some c813, some c385, some c250, some c908, some c62, some c103, some c90, some c33, some c67, some c88, some c378, some c66, some c594, some c36, some c273, some c226, some c201, some c214, some c237, some c38, some c287, some c308, some c195, some c254, some c245, some c266, some c882, some c43, some c274, some c372, some c216, some c58, some c194, some c153, some c16, some c14, some c135, some c127, some c151, some c171, some c156, some c909, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]]
theorem checked910 : lratChecker f910 p910 = .success := by decide +kernel
theorem unsat910 : Unsatisfiable (PosFin 57) f910 := by
  apply lratCheckerSound f910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p910
  · intro a ha; simp [p910] at ha; subst a; trivial
  · exact checked910
theorem derived910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c910 := by
  apply localUnsat_implies_entails f910 [c905, c907, c332, c192, c813, c385, c250, c908, c62, c103, c90, c33, c67, c88, c378, c66, c594, c36, c273, c226, c201, c214, c237, c38, c287, c308, c195, c254, c245, c266, c882, c43, c274, c372, c216, c58, c194, c153, c16, c14, c135, c127, c151, c171, c156, c909] c910 unsat910 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c907 := derived907 a h
  have h2 : Entails.eval a c332 := h 331 (by decide)
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c385 := h 384 (by decide)
  have h6 : Entails.eval a c250 := h 249 (by decide)
  have h7 : Entails.eval a c908 := derived908 a h
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c378 := h 377 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c594 := derived594 a h
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c273 := h 272 (by decide)
  have h19 : Entails.eval a c226 := h 225 (by decide)
  have h20 : Entails.eval a c201 := h 200 (by decide)
  have h21 : Entails.eval a c214 := h 213 (by decide)
  have h22 : Entails.eval a c237 := h 236 (by decide)
  have h23 : Entails.eval a c38 := h 37 (by decide)
  have h24 : Entails.eval a c287 := h 286 (by decide)
  have h25 : Entails.eval a c308 := h 307 (by decide)
  have h26 : Entails.eval a c195 := h 194 (by decide)
  have h27 : Entails.eval a c254 := h 253 (by decide)
  have h28 : Entails.eval a c245 := h 244 (by decide)
  have h29 : Entails.eval a c266 := h 265 (by decide)
  have h30 : Entails.eval a c882 := derived882 a h
  have h31 : Entails.eval a c43 := h 42 (by decide)
  have h32 : Entails.eval a c274 := h 273 (by decide)
  have h33 : Entails.eval a c372 := h 371 (by decide)
  have h34 : Entails.eval a c216 := h 215 (by decide)
  have h35 : Entails.eval a c58 := h 57 (by decide)
  have h36 : Entails.eval a c194 := h 193 (by decide)
  have h37 : Entails.eval a c153 := h 152 (by decide)
  have h38 : Entails.eval a c16 := h 15 (by decide)
  have h39 : Entails.eval a c14 := h 13 (by decide)
  have h40 : Entails.eval a c135 := h 134 (by decide)
  have h41 : Entails.eval a c127 := h 126 (by decide)
  have h42 : Entails.eval a c151 := h 150 (by decide)
  have h43 : Entails.eval a c171 := h 170 (by decide)
  have h44 : Entails.eval a c156 := h 155 (by decide)
  have h45 : Entails.eval a c909 := derived909 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c911 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨41, by decide⟩, true), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨44, by decide⟩, true), (⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨35, by decide⟩, false), (⟨7, by decide⟩, false), (⟨33, by decide⟩, false), (⟨4, by decide⟩, true), (⟨51, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c837, some c815, some c132, some c873, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked911 : lratChecker f911 p911 = .success := by decide +kernel
theorem unsat911 : Unsatisfiable (PosFin 57) f911 := by
  apply lratCheckerSound f911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p911
  · intro a ha; simp [p911] at ha; subst a; trivial
  · exact checked911
theorem derived911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c911 := by
  apply localUnsat_implies_entails f911 [c151, c837, c815, c132, c873] c911 unsat911 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c837 := derived837 a h
  have h2 : Entails.eval a c815 := derived815 a h
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c873 := derived873 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c912 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c907, some c332, some c192, some c250, some c905, some c908, some c214, some c237, some c38, some c385, some c62, some c103, some c88, some c287, some c594, some c36, some c308, some c195, some c254, some c245, some c266, some c882, some c43, some c378, some c66, some c274, some c67, some c372, some c273, some c813, some c90, some c33, some c216, some c58, some c194, some c911, some c325, some c153, some c910, some c16, some c14, some c135, some c162, some c171, some c156, some c127, some c121, some c201, some c392, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]]
theorem checked912 : lratChecker f912 p912 = .success := by decide +kernel
theorem unsat912 : Unsatisfiable (PosFin 57) f912 := by
  apply lratCheckerSound f912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p912
  · intro a ha; simp [p912] at ha; subst a; trivial
  · exact checked912
theorem derived912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c912 := by
  apply localUnsat_implies_entails f912 [c907, c332, c192, c250, c905, c908, c214, c237, c38, c385, c62, c103, c88, c287, c594, c36, c308, c195, c254, c245, c266, c882, c43, c378, c66, c274, c67, c372, c273, c813, c90, c33, c216, c58, c194, c911, c325, c153, c910, c16, c14, c135, c162, c171, c156, c127, c121, c201, c392] c912 unsat912 (by rfl) a
  have h0 : Entails.eval a c907 := derived907 a h
  have h1 : Entails.eval a c332 := h 331 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c250 := h 249 (by decide)
  have h4 : Entails.eval a c905 := derived905 a h
  have h5 : Entails.eval a c908 := derived908 a h
  have h6 : Entails.eval a c214 := h 213 (by decide)
  have h7 : Entails.eval a c237 := h 236 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c287 := h 286 (by decide)
  have h14 : Entails.eval a c594 := derived594 a h
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c308 := h 307 (by decide)
  have h17 : Entails.eval a c195 := h 194 (by decide)
  have h18 : Entails.eval a c254 := h 253 (by decide)
  have h19 : Entails.eval a c245 := h 244 (by decide)
  have h20 : Entails.eval a c266 := h 265 (by decide)
  have h21 : Entails.eval a c882 := derived882 a h
  have h22 : Entails.eval a c43 := h 42 (by decide)
  have h23 : Entails.eval a c378 := h 377 (by decide)
  have h24 : Entails.eval a c66 := h 65 (by decide)
  have h25 : Entails.eval a c274 := h 273 (by decide)
  have h26 : Entails.eval a c67 := h 66 (by decide)
  have h27 : Entails.eval a c372 := h 371 (by decide)
  have h28 : Entails.eval a c273 := h 272 (by decide)
  have h29 : Entails.eval a c813 := derived813 a h
  have h30 : Entails.eval a c90 := h 89 (by decide)
  have h31 : Entails.eval a c33 := h 32 (by decide)
  have h32 : Entails.eval a c216 := h 215 (by decide)
  have h33 : Entails.eval a c58 := h 57 (by decide)
  have h34 : Entails.eval a c194 := h 193 (by decide)
  have h35 : Entails.eval a c911 := derived911 a h
  have h36 : Entails.eval a c325 := h 324 (by decide)
  have h37 : Entails.eval a c153 := h 152 (by decide)
  have h38 : Entails.eval a c910 := derived910 a h
  have h39 : Entails.eval a c16 := h 15 (by decide)
  have h40 : Entails.eval a c14 := h 13 (by decide)
  have h41 : Entails.eval a c135 := h 134 (by decide)
  have h42 : Entails.eval a c162 := h 161 (by decide)
  have h43 : Entails.eval a c171 := h 170 (by decide)
  have h44 : Entails.eval a c156 := h 155 (by decide)
  have h45 : Entails.eval a c127 := h 126 (by decide)
  have h46 : Entails.eval a c121 := h 120 (by decide)
  have h47 : Entails.eval a c201 := h 200 (by decide)
  have h48 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c913 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c905, some c385, some c907, some c332, some c192, some c250, some c908, some c62, some c103, some c88, some c67, some c378, some c66, some c912, some c367, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked913 : lratChecker f913 p913 = .success := by decide +kernel
theorem unsat913 : Unsatisfiable (PosFin 57) f913 := by
  apply lratCheckerSound f913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p913
  · intro a ha; simp [p913] at ha; subst a; trivial
  · exact checked913
theorem derived913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c913 := by
  apply localUnsat_implies_entails f913 [c905, c385, c907, c332, c192, c250, c908, c62, c103, c88, c67, c378, c66, c912, c367] c913 unsat913 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c907 := derived907 a h
  have h3 : Entails.eval a c332 := h 331 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c250 := h 249 (by decide)
  have h6 : Entails.eval a c908 := derived908 a h
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c378 := h 377 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c912 := derived912 a h
  have h14 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c914 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, false), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c913, some c345, some c192, some c237, some c905, some c385, some c882, some c813, some c90, some c88, some c67, some c594, some c58, some c33, some c378, some c287, some c36, some c322, some c313, some c66, some c308, some c274, some c43, some c195, some c266, some c343, some c911, some c224, some c209, some c325, some c153, some c14, some c135, some c171, some c156, some c141, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked914 : lratChecker f914 p914 = .success := by decide +kernel
theorem unsat914 : Unsatisfiable (PosFin 57) f914 := by
  apply lratCheckerSound f914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p914
  · intro a ha; simp [p914] at ha; subst a; trivial
  · exact checked914
theorem derived914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c914 := by
  apply localUnsat_implies_entails f914 [c38, c913, c345, c192, c237, c905, c385, c882, c813, c90, c88, c67, c594, c58, c33, c378, c287, c36, c322, c313, c66, c308, c274, c43, c195, c266, c343, c911, c224, c209, c325, c153, c14, c135, c171, c156, c141] c914 unsat914 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c913 := derived913 a h
  have h2 : Entails.eval a c345 := h 344 (by decide)
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  have h5 : Entails.eval a c905 := derived905 a h
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c882 := derived882 a h
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c594 := derived594 a h
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c378 := h 377 (by decide)
  have h16 : Entails.eval a c287 := h 286 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c322 := h 321 (by decide)
  have h19 : Entails.eval a c313 := h 312 (by decide)
  have h20 : Entails.eval a c66 := h 65 (by decide)
  have h21 : Entails.eval a c308 := h 307 (by decide)
  have h22 : Entails.eval a c274 := h 273 (by decide)
  have h23 : Entails.eval a c43 := h 42 (by decide)
  have h24 : Entails.eval a c195 := h 194 (by decide)
  have h25 : Entails.eval a c266 := h 265 (by decide)
  have h26 : Entails.eval a c343 := h 342 (by decide)
  have h27 : Entails.eval a c911 := derived911 a h
  have h28 : Entails.eval a c224 := h 223 (by decide)
  have h29 : Entails.eval a c209 := h 208 (by decide)
  have h30 : Entails.eval a c325 := h 324 (by decide)
  have h31 : Entails.eval a c153 := h 152 (by decide)
  have h32 : Entails.eval a c14 := h 13 (by decide)
  have h33 : Entails.eval a c135 := h 134 (by decide)
  have h34 : Entails.eval a c171 := h 170 (by decide)
  have h35 : Entails.eval a c156 := h 155 (by decide)
  have h36 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c915 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨42, by decide⟩, false), (⟨40, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c276, some c320, some c36, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked915 : lratChecker f915 p915 = .success := by decide +kernel
theorem unsat915 : Unsatisfiable (PosFin 57) f915 := by
  apply lratCheckerSound f915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p915
  · intro a ha; simp [p915] at ha; subst a; trivial
  · exact checked915
theorem derived915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c915 := by
  apply localUnsat_implies_entails f915 [c276, c320, c36] c915 unsat915 (by rfl) a
  have h0 : Entails.eval a c276 := h 275 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c916 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨33, by decide⟩, false), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c913, some c345, some c192, some c250, some c237, some c905, some c882, some c38, some c914, some c103, some c667, some c66, some c735, some c287, some c196, some c915, some c74, some c81, some c368, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked916 : lratChecker f916 p916 = .success := by decide +kernel
theorem unsat916 : Unsatisfiable (PosFin 57) f916 := by
  apply lratCheckerSound f916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p916
  · intro a ha; simp [p916] at ha; subst a; trivial
  · exact checked916
theorem derived916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c916 := by
  apply localUnsat_implies_entails f916 [c913, c345, c192, c250, c237, c905, c882, c38, c914, c103, c667, c66, c735, c287, c196, c915, c74, c81, c368] c916 unsat916 (by rfl) a
  have h0 : Entails.eval a c913 := derived913 a h
  have h1 : Entails.eval a c345 := h 344 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c250 := h 249 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  have h5 : Entails.eval a c905 := derived905 a h
  have h6 : Entails.eval a c882 := derived882 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c914 := derived914 a h
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c667 := derived667 a h
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c735 := derived735 a h
  have h13 : Entails.eval a c287 := h 286 (by decide)
  have h14 : Entails.eval a c196 := h 195 (by decide)
  have h15 : Entails.eval a c915 := derived915 a h
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c917 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c905, some c385, some c882, some c916, some c347, some c331, some c349, some c88, some c57, some c103, some c736, some c667, some c66, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked917 : lratChecker f917 p917 = .success := by decide +kernel
theorem unsat917 : Unsatisfiable (PosFin 57) f917 := by
  apply lratCheckerSound f917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p917
  · intro a ha; simp [p917] at ha; subst a; trivial
  · exact checked917
theorem derived917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c917 := by
  apply localUnsat_implies_entails f917 [c905, c385, c882, c916, c347, c331, c349, c88, c57, c103, c736, c667, c66] c917 unsat917 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c882 := derived882 a h
  have h3 : Entails.eval a c916 := derived916 a h
  have h4 : Entails.eval a c347 := h 346 (by decide)
  have h5 : Entails.eval a c331 := h 330 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c736 := derived736 a h
  have h11 : Entails.eval a c667 := derived667 a h
  have h12 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c918 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c905, some c385, some c882, some c667, some c378, some c103, some c88, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked918 : lratChecker f918 p918 = .success := by decide +kernel
theorem unsat918 : Unsatisfiable (PosFin 57) f918 := by
  apply lratCheckerSound f918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p918
  · intro a ha; simp [p918] at ha; subst a; trivial
  · exact checked918
theorem derived918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c918 := by
  apply localUnsat_implies_entails f918 [c905, c385, c882, c667, c378, c103, c88] c918 unsat918 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c882 := derived882 a h
  have h3 : Entails.eval a c667 := derived667 a h
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived918

end CochromaticTwenty.Certificates.B16_8_0Enumerating
