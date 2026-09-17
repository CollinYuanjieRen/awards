import MerLeanExperiment.Certificates.B16_2_1.Steps0400_0499

/-! Generated from the actual pinned b16_2_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c823 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨46, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨43, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c820, some c774, some c88, some c89, some c86, some c293, some c317, some c80, some c159, some c93, some c822, some c458, some c16, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 57) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c773, c622, c820, c774, c88, c89, c86, c293, c317, c80, c159, c93, c822, c458, c16] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c774 := derived774 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c822 := derived822 a h
  have h13 : Entails.eval a c458 := derived458 a h
  have h14 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c824 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c820, some c89, some c8, some c67, some c145, some c302, some c88, some c431, some c774, some c22, some c63, some c73, some c303, some c823, some c320, some c230, some c80, some c159, some c24, some c93, some c822, some c458, some c16, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 57) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c773, c622, c820, c89, c8, c67, c145, c302, c88, c431, c774, c22, c63, c73, c303, c823, c320, c230, c80, c159, c24, c93, c822, c458, c16] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c302 := h 301 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c431 := derived431 a h
  have h10 : Entails.eval a c774 := derived774 a h
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c303 := h 302 (by decide)
  have h15 : Entails.eval a c823 := derived823 a h
  have h16 : Entails.eval a c320 := h 319 (by decide)
  have h17 : Entails.eval a c230 := h 229 (by decide)
  have h18 : Entails.eval a c80 := h 79 (by decide)
  have h19 : Entails.eval a c159 := h 158 (by decide)
  have h20 : Entails.eval a c24 := h 23 (by decide)
  have h21 : Entails.eval a c93 := h 92 (by decide)
  have h22 : Entails.eval a c822 := derived822 a h
  have h23 : Entails.eval a c458 := derived458 a h
  have h24 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c825 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨3, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c89, some c774, some c824, some c90, some c86, some c320, some c80, some c93, some c88, some c74, some c75, some c303, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 57) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c773, c622, c89, c774, c824, c90, c86, c320, c80, c93, c88, c74, c75, c303] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c774 := derived774 a h
  have h4 : Entails.eval a c824 := derived824 a h
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c75 := h 74 (by decide)
  have h13 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c826 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c820, some c89, some c88, some c774, some c8, some c67, some c145, some c824, some c90, some c86, some c320, some c80, some c159, some c93, some c825, some c157, some c16, some c15, some c178, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 57) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c773, c622, c820, c89, c88, c774, c8, c67, c145, c824, c90, c86, c320, c80, c159, c93, c825, c157, c16, c15, c178] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c774 := derived774 a h
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c145 := h 144 (by decide)
  have h9 : Entails.eval a c824 := derived824 a h
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c86 := h 85 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c159 := h 158 (by decide)
  have h15 : Entails.eval a c93 := h 92 (by decide)
  have h16 : Entails.eval a c825 := derived825 a h
  have h17 : Entails.eval a c157 := h 156 (by decide)
  have h18 : Entails.eval a c16 := h 15 (by decide)
  have h19 : Entails.eval a c15 := h 14 (by decide)
  have h20 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c827 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c826, some c407, some c729, some c299, some c73, some c25, some c301, some c675, some c233, some c24, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 57) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c826, c407, c729, c299, c73, c25, c301, c675, c233, c24] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c826 := derived826 a h
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c299 := h 298 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c301 := h 300 (by decide)
  have h7 : Entails.eval a c675 := derived675 a h
  have h8 : Entails.eval a c233 := h 232 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c826, some c827, some c91, some c87, some c431, some c21, some c62, some c72, some c227, some c303, some c25, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 57) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c773, c622, c826, c827, c91, c87, c431, c21, c62, c72, c227, c303, c25] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c826 := derived826 a h
  have h3 : Entails.eval a c827 := derived827 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c431 := derived431 a h
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  have h11 : Entails.eval a c303 := h 302 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c829 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c33, some c245, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 57) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c35, c33, c245] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c830 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c67, some c8, some c5, some c64, some c157, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 57) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c622, c67, c8, c5, c64, c157] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c831 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨47, by decide⟩, true), (⟨4, by decide⟩, false), (⟨51, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨44, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c820, some c773, some c86, some c67, some c8, some c320, some c227, some c80, some c159, some c211, some c95, some c829, some c236, some c242, some c830, some c226, some c213, some c157, some c15, some c178, some c177, some c369, some c118, some c188, some c50, some c42, some c120, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 57) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c622, c820, c773, c86, c67, c8, c320, c227, c80, c159, c211, c95, c829, c236, c242, c830, c226, c213, c157, c15, c178, c177, c369, c118, c188, c50, c42, c120] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c773 := derived773 a h
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c829 := derived829 a h
  have h13 : Entails.eval a c236 := h 235 (by decide)
  have h14 : Entails.eval a c242 := h 241 (by decide)
  have h15 : Entails.eval a c830 := derived830 a h
  have h16 : Entails.eval a c226 := h 225 (by decide)
  have h17 : Entails.eval a c213 := h 212 (by decide)
  have h18 : Entails.eval a c157 := h 156 (by decide)
  have h19 : Entails.eval a c15 := h 14 (by decide)
  have h20 : Entails.eval a c178 := h 177 (by decide)
  have h21 : Entails.eval a c177 := h 176 (by decide)
  have h22 : Entails.eval a c369 := derived369 a h
  have h23 : Entails.eval a c118 := h 117 (by decide)
  have h24 : Entails.eval a c188 := h 187 (by decide)
  have h25 : Entails.eval a c50 := h 49 (by decide)
  have h26 : Entails.eval a c42 := h 41 (by decide)
  have h27 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c832 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c820, some c773, some c828, some c826, some c8, some c67, some c536, some c86, some c145, some c300, some c21, some c62, some c71, some c72, some c303, some c831, some c294, some c319, some c80, some c159, some c95, some c830, some c226, some c23, some c157, some c15, some c178, some c177, some c369, some c118, some c125, some c50, some c268, some c120, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 57) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c622, c820, c773, c828, c826, c8, c67, c536, c86, c145, c300, c21, c62, c71, c72, c303, c831, c294, c319, c80, c159, c95, c830, c226, c23, c157, c15, c178, c177, c369, c118, c125, c50, c268, c120] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c773 := derived773 a h
  have h3 : Entails.eval a c828 := derived828 a h
  have h4 : Entails.eval a c826 := derived826 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c536 := derived536 a h
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c300 := h 299 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c62 := h 61 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c303 := h 302 (by decide)
  have h16 : Entails.eval a c831 := derived831 a h
  have h17 : Entails.eval a c294 := h 293 (by decide)
  have h18 : Entails.eval a c319 := h 318 (by decide)
  have h19 : Entails.eval a c80 := h 79 (by decide)
  have h20 : Entails.eval a c159 := h 158 (by decide)
  have h21 : Entails.eval a c95 := h 94 (by decide)
  have h22 : Entails.eval a c830 := derived830 a h
  have h23 : Entails.eval a c226 := h 225 (by decide)
  have h24 : Entails.eval a c23 := h 22 (by decide)
  have h25 : Entails.eval a c157 := h 156 (by decide)
  have h26 : Entails.eval a c15 := h 14 (by decide)
  have h27 : Entails.eval a c178 := h 177 (by decide)
  have h28 : Entails.eval a c177 := h 176 (by decide)
  have h29 : Entails.eval a c369 := derived369 a h
  have h30 : Entails.eval a c118 := h 117 (by decide)
  have h31 : Entails.eval a c125 := h 124 (by decide)
  have h32 : Entails.eval a c50 := h 49 (by decide)
  have h33 : Entails.eval a c268 := h 267 (by decide)
  have h34 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c833 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c320, some c82, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 57) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c317, c320, c82] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c820, some c622, some c407, some c729, some c300, some c833, some c291, some c409, some c146, some c141, some c159, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 57) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c820, c622, c407, c729, c300, c833, c291, c409, c146, c141, c159] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c820 := derived820 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c407 := derived407 a h
  have h3 : Entails.eval a c729 := derived729 a h
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c833 := derived833 a h
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c409 := derived409 a h
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c826, some c832, some c91, some c834, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 57) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c773, c826, c832, c91, c834] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c826 := derived826 a h
  have h2 : Entails.eval a c832 := derived832 a h
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c834 := derived834 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c835, some c92, some c90, some c826, some c729, some c299, some c300, some c73, some c25, some c301, some c675, some c320, some c233, some c755, some c214, some c212, some c245, some c244, some c30, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 57) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c773, c835, c92, c90, c826, c729, c299, c300, c73, c25, c301, c675, c320, c233, c755, c214, c212, c245, c244, c30] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c835 := derived835 a h
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c826 := derived826 a h
  have h5 : Entails.eval a c729 := derived729 a h
  have h6 : Entails.eval a c299 := h 298 (by decide)
  have h7 : Entails.eval a c300 := h 299 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c675 := derived675 a h
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c233 := h 232 (by decide)
  have h14 : Entails.eval a c755 := derived755 a h
  have h15 : Entails.eval a c214 := h 213 (by decide)
  have h16 : Entails.eval a c212 := h 211 (by decide)
  have h17 : Entails.eval a c245 := h 244 (by decide)
  have h18 : Entails.eval a c244 := h 243 (by decide)
  have h19 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c837 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨50, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c820, some c835, some c90, some c826, some c836, some c71, some c302, some c291, some c142, some c147, some c159, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 57) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c773, c622, c820, c835, c90, c826, c836, c71, c302, c291, c142, c147, c159] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c835 := derived835 a h
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c826 := derived826 a h
  have h6 : Entails.eval a c836 := derived836 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c302 := h 301 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c838 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c820, some c835, some c92, some c90, some c826, some c837, some c12, some c14, some c175, some c169, some c159, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 57) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c773, c820, c835, c92, c90, c826, c837, c12, c14, c175, c169, c159] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c835 := derived835 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c826 := derived826 a h
  have h6 : Entails.eval a c837 := derived837 a h
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c175 := h 174 (by decide)
  have h10 : Entails.eval a c169 := h 168 (by decide)
  have h11 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c839 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c826, some c835, some c90, some c92, some c836, some c62, some c71, some c675, some c838, some c317, some c319, some c83, some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 57) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c773, c826, c835, c90, c92, c836, c62, c71, c675, c838, c317, c319, c83] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c826 := derived826 a h
  have h2 : Entails.eval a c835 := derived835 a h
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c836 := derived836 a h
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c675 := derived675 a h
  have h9 : Entails.eval a c838 := derived838 a h
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c319 := h 318 (by decide)
  have h12 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c820, some c290, some c310, some c584, some c71, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 57) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c839, c820, c290, c310, c584, c71] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c310 := h 309 (by decide)
  have h4 : Entails.eval a c584 := derived584 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c774, some c7, some c66, some c83, some c319, some c318, some c840, some c297, some c806, some c158, some c812, some c165, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 57) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c622, c774, c7, c66, c83, c319, c318, c840, c297, c806, c158, c812, c165] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c774 := derived774 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c319 := h 318 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c840 := derived840 a h
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c806 := derived806 a h
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c812 := derived812 a h
  have h12 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c842 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c405, some c169, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 57) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c405, c169] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c405 := derived405 a h
  have h1 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c843 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨15, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c839, some c820, some c622, some c774, some c841, some c92, some c842, some c290, some c840, some c160, some c298, some c554, some c319, some c63, some c4, some c154, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 57) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c773, c839, c820, c622, c774, c841, c92, c842, c290, c840, c160, c298, c554, c319, c63, c4, c154] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c839 := derived839 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c622 := derived622 a h
  have h4 : Entails.eval a c774 := derived774 a h
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c842 := derived842 a h
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c840 := derived840 a h
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c298 := h 297 (by decide)
  have h12 : Entails.eval a c554 := derived554 a h
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c63 := h 62 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c318, some c81, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 57) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c316, c318, c81] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c774, some c844, some c843, some c168, some c166, some c812, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 57) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c622, c774, c844, c843, c168, c166, c812] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c774 := derived774 a h
  have h2 : Entails.eval a c844 := derived844 a h
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c812 := derived812 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c846 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨55, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c622, some c773, some c820, some c845, some c289, some c774, some c168, some c7, some c92, some c409, some c170, some c159, some c146, some c71, some c72, some c307, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 57) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c839, c622, c773, c820, c845, c289, c774, c168, c7, c92, c409, c170, c159, c146, c71, c72, c307] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c773 := derived773 a h
  have h3 : Entails.eval a c820 := derived820 a h
  have h4 : Entails.eval a c845 := derived845 a h
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c774 := derived774 a h
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c409 := derived409 a h
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨55, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c820, some c773, some c846, some c845, some c289, some c774, some c175, some c150, some c409, some c66, some c92, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 57) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c839, c820, c773, c846, c845, c289, c774, c175, c150, c409, c66, c92] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c773 := derived773 a h
  have h3 : Entails.eval a c846 := derived846 a h
  have h4 : Entails.eval a c845 := derived845 a h
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c774 := derived774 a h
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c150 := h 149 (by decide)
  have h9 : Entails.eval a c409 := derived409 a h
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c848 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨55, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c820, some c845, some c847, some c159, some c774, some c172, some c170, some c12, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 57) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c820, c845, c847, c159, c774, c172, c170, c12] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c820 := derived820 a h
  have h1 : Entails.eval a c845 := derived845 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c159 := h 158 (by decide)
  have h4 : Entails.eval a c774 := derived774 a h
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c849 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c845, some c847, some c848, some c161, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 57) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c622, c845, c847, c848, c161] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c845 := derived845 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c848 := derived848 a h
  have h4 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨10, by decide⟩, false), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c175, some c146, some c71, some c307, some c147, some c72, some c14, some c92, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 57) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c773, c175, c146, c71, c307, c147, c72, c14, c92] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c175 := h 174 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c307 := h 306 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c851 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c622, some c820, some c773, some c8, some c89, some c289, some c161, some c850, some c12, some c409, some c147, some c92, some c73, some c71, some c305, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 57) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c839, c622, c820, c773, c8, c89, c289, c161, c850, c12, c409, c147, c92, c73, c71, c305] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c773 := derived773 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c161 := h 160 (by decide)
  have h8 : Entails.eval a c850 := derived850 a h
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c409 := derived409 a h
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c852 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c820, some c849, some c8, some c89, some c851, some c317, some c320, some c833, some c844, some c62, some c92, some c426, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 57) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c622, c773, c820, c849, c8, c89, c851, c317, c320, c833, c844, c62, c92, c426] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c849 := derived849 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c851 := derived851 a h
  have h7 : Entails.eval a c317 := h 316 (by decide)
  have h8 : Entails.eval a c320 := h 319 (by decide)
  have h9 : Entails.eval a c833 := derived833 a h
  have h10 : Entails.eval a c844 := derived844 a h
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c426 := derived426 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c853 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c820, some c849, some c320, some c317, some c833, some c844, some c62, some c92, some c425, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 57) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c773, c820, c849, c320, c317, c833, c844, c62, c92, c425] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c849 := derived849 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c317 := h 316 (by decide)
  have h5 : Entails.eval a c833 := derived833 a h
  have h6 : Entails.eval a c844 := derived844 a h
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c425 := derived425 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c854 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c820, some c853, some c88, some c89, some c849, some c320, some c317, some c852, some c472, some c63, some c4, some c475, some c476, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 57) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c773, c820, c853, c88, c89, c849, c320, c317, c852, c472, c63, c4, c475, c476] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c853 := derived853 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c849 := derived849 a h
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c317 := h 316 (by decide)
  have h8 : Entails.eval a c852 := derived852 a h
  have h9 : Entails.eval a c472 := derived472 a h
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c475 := derived475 a h
  have h13 : Entails.eval a c476 := derived476 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c855 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c839, some c820, some c852, some c849, some c317, some c320, some c853, some c89, some c88, some c67, some c457, some c854, some c318, some c290, some c160, some c157, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 57) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c773, c622, c839, c820, c852, c849, c317, c320, c853, c89, c88, c67, c457, c854, c318, c290, c160, c157] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c839 := derived839 a h
  have h3 : Entails.eval a c820 := derived820 a h
  have h4 : Entails.eval a c852 := derived852 a h
  have h5 : Entails.eval a c849 := derived849 a h
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c853 := derived853 a h
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c457 := derived457 a h
  have h13 : Entails.eval a c854 := derived854 a h
  have h14 : Entails.eval a c318 := h 317 (by decide)
  have h15 : Entails.eval a c290 := h 289 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c856 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c820, some c839, some c773, some c622, some c855, some c289, some c392, some c290, some c306, some c71, some c89, some c80, some c830, some c93, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 57) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c820, c839, c773, c622, c855, c289, c392, c290, c306, c71, c89, c80, c830, c93] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c820 := derived820 a h
  have h1 : Entails.eval a c839 := derived839 a h
  have h2 : Entails.eval a c773 := derived773 a h
  have h3 : Entails.eval a c622 := derived622 a h
  have h4 : Entails.eval a c855 := derived855 a h
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c392 := derived392 a h
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c306 := h 305 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c830 := derived830 a h
  have h13 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c857 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true), (⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨46, by decide⟩, true), (⟨52, by decide⟩, false), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨43, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c230, some c210, some c240, some c366, some c122, some c130, some c285, some c268, some c120, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 57) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c773, c230, c210, c240, c366, c122, c130, c285, c268, c120] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c230 := h 229 (by decide)
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c366 := derived366 a h
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c285 := h 284 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c858 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c622, some c820, some c773, some c855, some c89, some c80, some c93, some c67, some c88, some c856, some c289, some c852, some c849, some c755, some c306, some c157, some c22, some c63, some c73, some c16, some c229, some c323, some c150, some c34, some c159, some c103, some c172, some c170, some c173, some c15, some c857, some c457, some c227, some c210, some c243, some c366, some c128, some c130, some c266, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c839, c622, c820, c773, c855, c89, c80, c93, c67, c88, c856, c289, c852, c849, c755, c306, c157, c22, c63, c73, c16, c229, c323, c150, c34, c159, c103, c172, c170, c173, c15, c857, c457, c227, c210, c243, c366, c128, c130, c266] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c773 := derived773 a h
  have h4 : Entails.eval a c855 := derived855 a h
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c856 := derived856 a h
  have h11 : Entails.eval a c289 := h 288 (by decide)
  have h12 : Entails.eval a c852 := derived852 a h
  have h13 : Entails.eval a c849 := derived849 a h
  have h14 : Entails.eval a c755 := derived755 a h
  have h15 : Entails.eval a c306 := h 305 (by decide)
  have h16 : Entails.eval a c157 := h 156 (by decide)
  have h17 : Entails.eval a c22 := h 21 (by decide)
  have h18 : Entails.eval a c63 := h 62 (by decide)
  have h19 : Entails.eval a c73 := h 72 (by decide)
  have h20 : Entails.eval a c16 := h 15 (by decide)
  have h21 : Entails.eval a c229 := h 228 (by decide)
  have h22 : Entails.eval a c323 := derived323 a h
  have h23 : Entails.eval a c150 := h 149 (by decide)
  have h24 : Entails.eval a c34 := h 33 (by decide)
  have h25 : Entails.eval a c159 := h 158 (by decide)
  have h26 : Entails.eval a c103 := h 102 (by decide)
  have h27 : Entails.eval a c172 := h 171 (by decide)
  have h28 : Entails.eval a c170 := h 169 (by decide)
  have h29 : Entails.eval a c173 := h 172 (by decide)
  have h30 : Entails.eval a c15 := h 14 (by decide)
  have h31 : Entails.eval a c857 := derived857 a h
  have h32 : Entails.eval a c457 := derived457 a h
  have h33 : Entails.eval a c227 := h 226 (by decide)
  have h34 : Entails.eval a c210 := h 209 (by decide)
  have h35 : Entails.eval a c243 := h 242 (by decide)
  have h36 : Entails.eval a c366 := derived366 a h
  have h37 : Entails.eval a c128 := h 127 (by decide)
  have h38 : Entails.eval a c130 := h 129 (by decide)
  have h39 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c856, some c22, some c63, some c229, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c856, c22, c63, c229] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c856 := derived856 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c122, some c128, some c51, some c37, some c181, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c773, c122, c128, c51, c37, c181] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c128 := h 127 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c622, some c820, some c773, some c856, some c855, some c289, some c852, some c89, some c88, some c67, some c80, some c93, some c858, some c671, some c23, some c323, some c305, some c74, some c859, some c156, some c4, some c14, some c229, some c150, some c32, some c159, some c103, some c170, some c173, some c860, some c366, some c243, some c239, some c210, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c839, c622, c820, c773, c856, c855, c289, c852, c89, c88, c67, c80, c93, c858, c671, c23, c323, c305, c74, c859, c156, c4, c14, c229, c150, c32, c159, c103, c170, c173, c860, c366, c243, c239, c210] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c773 := derived773 a h
  have h4 : Entails.eval a c856 := derived856 a h
  have h5 : Entails.eval a c855 := derived855 a h
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c852 := derived852 a h
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c93 := h 92 (by decide)
  have h13 : Entails.eval a c858 := derived858 a h
  have h14 : Entails.eval a c671 := derived671 a h
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c323 := derived323 a h
  have h17 : Entails.eval a c305 := h 304 (by decide)
  have h18 : Entails.eval a c74 := h 73 (by decide)
  have h19 : Entails.eval a c859 := derived859 a h
  have h20 : Entails.eval a c156 := h 155 (by decide)
  have h21 : Entails.eval a c4 := h 3 (by decide)
  have h22 : Entails.eval a c14 := h 13 (by decide)
  have h23 : Entails.eval a c229 := h 228 (by decide)
  have h24 : Entails.eval a c150 := h 149 (by decide)
  have h25 : Entails.eval a c32 := h 31 (by decide)
  have h26 : Entails.eval a c159 := h 158 (by decide)
  have h27 : Entails.eval a c103 := h 102 (by decide)
  have h28 : Entails.eval a c170 := h 169 (by decide)
  have h29 : Entails.eval a c173 := h 172 (by decide)
  have h30 : Entails.eval a c860 := derived860 a h
  have h31 : Entails.eval a c366 := derived366 a h
  have h32 : Entails.eval a c243 := h 242 (by decide)
  have h33 : Entails.eval a c239 := h 238 (by decide)
  have h34 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c820, some c855, some c289, some c852, some c147, some c172, some c159, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c839, c820, c855, c289, c852, c147, c172, c159] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c855 := derived855 a h
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c852 := derived852 a h
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c820, some c861, some c855, some c852, some c12, some c14, some c175, some c170, some c159, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c820, c861, c855, c852, c12, c14, c175, c170, c159] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c820 := derived820 a h
  have h1 : Entails.eval a c861 := derived861 a h
  have h2 : Entails.eval a c855 := derived855 a h
  have h3 : Entails.eval a c852 := derived852 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c175 := h 174 (by decide)
  have h7 : Entails.eval a c170 := h 169 (by decide)
  have h8 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c820, some c861, some c855, some c289, some c863, some c862, some c71, some c73, some c305, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c839, c820, c861, c855, c289, c863, c862, c71, c73, c305] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c861 := derived861 a h
  have h3 : Entails.eval a c855 := derived855 a h
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c863 := derived863 a h
  have h6 : Entails.eval a c862 := derived862 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c773, some c820, some c852, some c855, some c289, some c861, some c864, some c92, some c409, some c170, some c850, some c159, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c839, c773, c820, c852, c855, c289, c861, c864, c92, c409, c170, c850, c159] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c852 := derived852 a h
  have h4 : Entails.eval a c855 := derived855 a h
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c861 := derived861 a h
  have h7 : Entails.eval a c864 := derived864 a h
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c409 := derived409 a h
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c850 := derived850 a h
  have h12 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c865, some c773, some c91, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c865, c773, c91] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c865 := derived865 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c865, some c773, some c90, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c865, c773, c90] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c865 := derived865 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c866, some c622, some c8, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c866, c622, c8] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c866 := derived866 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c866, some c622, some c67, some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c866, c622, c67] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c866 := derived866 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c866, some c867, some c622, some c86, some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c866, c867, c622, c86] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c866 := derived866 a h
  have h1 : Entails.eval a c867 := derived867 a h
  have h2 : Entails.eval a c622 := derived622 a h
  have h3 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c868, some c865, some c867, some c180, some c172, some c95, some c789, some c15, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c868, c865, c867, c180, c172, c95, c789, c15] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c868 := derived868 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c867 := derived867 a h
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c789 := derived789 a h
  have h7 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c820, some c622, some c866, some c870, some c869, some c868, some c172, some c180, some c160, some c871, some c80, some c320, some c319, some c316, some c774, some c292, some c3, some c153, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c820, c622, c866, c870, c869, c868, c172, c180, c160, c871, c80, c320, c319, c316, c774, c292, c3, c153] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c820 := derived820 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c866 := derived866 a h
  have h3 : Entails.eval a c870 := derived870 a h
  have h4 : Entails.eval a c869 := derived869 a h
  have h5 : Entails.eval a c868 := derived868 a h
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c871 := derived871 a h
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c774 := derived774 a h
  have h15 : Entails.eval a c292 := h 291 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c820, some c868, some c869, some c290, some c160, some c157, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c839, c820, c868, c869, c290, c160, c157] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c868 := derived868 a h
  have h3 : Entails.eval a c869 := derived869 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c870, some c872, some c320, some c319, some c316, some c538, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c870, c872, c320, c319, c316, c538] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c870 := derived870 a h
  have h1 : Entails.eval a c872 := derived872 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c538 := derived538 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨3, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c866, some c622, some c865, some c867, some c820, some c80, some c95, some c671, some c74, some c323, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c866, c622, c865, c867, c820, c80, c95, c671, c74, c323] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c866 := derived866 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c865 := derived865 a h
  have h3 : Entails.eval a c867 := derived867 a h
  have h4 : Entails.eval a c820 := derived820 a h
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c671 := derived671 a h
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c323 := derived323 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c866, some c622, some c865, some c773, some c868, some c869, some c867, some c80, some c95, some c88, some c875, some c157, some c15, some c16, some c178, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c866, c622, c865, c773, c868, c869, c867, c80, c95, c88, c875, c157, c15, c16, c178] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c866 := derived866 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c865 := derived865 a h
  have h3 : Entails.eval a c773 := derived773 a h
  have h4 : Entails.eval a c868 := derived868 a h
  have h5 : Entails.eval a c869 := derived869 a h
  have h6 : Entails.eval a c867 := derived867 a h
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c875 := derived875 a h
  have h11 : Entails.eval a c157 := h 156 (by decide)
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨10, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c868, some c869, some c866, some c867, some c157, some c591, some c15, some c149, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c868, c869, c866, c867, c157, c591, c15, c149] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c868 := derived868 a h
  have h1 : Entails.eval a c869 := derived869 a h
  have h2 : Entails.eval a c866 := derived866 a h
  have h3 : Entails.eval a c867 := derived867 a h
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c591 := derived591 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨5, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c867, some c866, some c877, some c74, some c149, some c593, some c15, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c867, c866, c877, c74, c149, c593, c15] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c867 := derived867 a h
  have h1 : Entails.eval a c866 := derived866 a h
  have h2 : Entails.eval a c877 := derived877 a h
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c593 := derived593 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c839, some c622, some c866, some c820, some c865, some c873, some c874, some c289, some c80, some c159, some c95, some c876, some c878, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c839, c622, c866, c820, c865, c873, c874, c289, c80, c159, c95, c876, c878] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c839 := derived839 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c866 := derived866 a h
  have h3 : Entails.eval a c820 := derived820 a h
  have h4 : Entails.eval a c865 := derived865 a h
  have h5 : Entails.eval a c873 := derived873 a h
  have h6 : Entails.eval a c874 := derived874 a h
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c876 := derived876 a h
  have h12 : Entails.eval a c878 := derived878 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c870, some c320, some c319, some c164, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c870, c320, c319, c164] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c870 := derived870 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c866, some c867, some c74, some c591, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c866, c867, c74, c591] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c866 := derived866 a h
  have h1 : Entails.eval a c867 := derived867 a h
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c591 := derived591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨3, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c866, some c868, some c869, some c867, some c865, some c773, some c872, some c879, some c170, some c13, some c173, some c880, some c80, some c95, some c830, some c3, some c755, some c157, some c21, some c16, some c226, some c369, some c33, some c102, some c181, some c50, some c52, some c138, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c622, c866, c868, c869, c867, c865, c773, c872, c879, c170, c13, c173, c880, c80, c95, c830, c3, c755, c157, c21, c16, c226, c369, c33, c102, c181, c50, c52, c138] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c866 := derived866 a h
  have h2 : Entails.eval a c868 := derived868 a h
  have h3 : Entails.eval a c869 := derived869 a h
  have h4 : Entails.eval a c867 := derived867 a h
  have h5 : Entails.eval a c865 := derived865 a h
  have h6 : Entails.eval a c773 := derived773 a h
  have h7 : Entails.eval a c872 := derived872 a h
  have h8 : Entails.eval a c879 := derived879 a h
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c173 := h 172 (by decide)
  have h12 : Entails.eval a c880 := derived880 a h
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c830 := derived830 a h
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c755 := derived755 a h
  have h18 : Entails.eval a c157 := h 156 (by decide)
  have h19 : Entails.eval a c21 := h 20 (by decide)
  have h20 : Entails.eval a c16 := h 15 (by decide)
  have h21 : Entails.eval a c226 := h 225 (by decide)
  have h22 : Entails.eval a c369 := derived369 a h
  have h23 : Entails.eval a c33 := h 32 (by decide)
  have h24 : Entails.eval a c102 := h 101 (by decide)
  have h25 : Entails.eval a c181 := h 180 (by decide)
  have h26 : Entails.eval a c50 := h 49 (by decide)
  have h27 : Entails.eval a c52 := h 51 (by decide)
  have h28 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c868, some c622, some c866, some c820, some c867, some c865, some c773, some c879, some c170, some c872, some c3, some c13, some c173, some c880, some c80, some c95, some c830, some c881, some c323, some c882, some c23, some c75, some c226, some c369, some c31, some c102, some c181, some c50, some c52, some c138, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c868, c622, c866, c820, c867, c865, c773, c879, c170, c872, c3, c13, c173, c880, c80, c95, c830, c881, c323, c882, c23, c75, c226, c369, c31, c102, c181, c50, c52, c138] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c868 := derived868 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c866 := derived866 a h
  have h3 : Entails.eval a c820 := derived820 a h
  have h4 : Entails.eval a c867 := derived867 a h
  have h5 : Entails.eval a c865 := derived865 a h
  have h6 : Entails.eval a c773 := derived773 a h
  have h7 : Entails.eval a c879 := derived879 a h
  have h8 : Entails.eval a c170 := h 169 (by decide)
  have h9 : Entails.eval a c872 := derived872 a h
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c880 := derived880 a h
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c95 := h 94 (by decide)
  have h16 : Entails.eval a c830 := derived830 a h
  have h17 : Entails.eval a c881 := derived881 a h
  have h18 : Entails.eval a c323 := derived323 a h
  have h19 : Entails.eval a c882 := derived882 a h
  have h20 : Entails.eval a c23 := h 22 (by decide)
  have h21 : Entails.eval a c75 := h 74 (by decide)
  have h22 : Entails.eval a c226 := h 225 (by decide)
  have h23 : Entails.eval a c369 := derived369 a h
  have h24 : Entails.eval a c31 := h 30 (by decide)
  have h25 : Entails.eval a c102 := h 101 (by decide)
  have h26 : Entails.eval a c181 := h 180 (by decide)
  have h27 : Entails.eval a c50 := h 49 (by decide)
  have h28 : Entails.eval a c52 := h 51 (by decide)
  have h29 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c870, some c622, some c866, some c865, some c868, some c869, some c867, some c879, some c883, some c88, some c774, some c320, some c80, some c875, some c95, some c157, some c15, some c16, some c173, some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c773, c870, c622, c866, c865, c868, c869, c867, c879, c883, c88, c774, c320, c80, c875, c95, c157, c15, c16, c173] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c870 := derived870 a h
  have h2 : Entails.eval a c622 := derived622 a h
  have h3 : Entails.eval a c866 := derived866 a h
  have h4 : Entails.eval a c865 := derived865 a h
  have h5 : Entails.eval a c868 := derived868 a h
  have h6 : Entails.eval a c869 := derived869 a h
  have h7 : Entails.eval a c867 := derived867 a h
  have h8 : Entails.eval a c879 := derived879 a h
  have h9 : Entails.eval a c883 := derived883 a h
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c774 := derived774 a h
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c875 := derived875 a h
  have h15 : Entails.eval a c95 := h 94 (by decide)
  have h16 : Entails.eval a c157 := h 156 (by decide)
  have h17 : Entails.eval a c15 := h 14 (by decide)
  have h18 : Entails.eval a c16 := h 15 (by decide)
  have h19 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c884, some c869, some c310, some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c884, c869, c310] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c884 := derived884 a h
  have h1 : Entails.eval a c869 := derived869 a h
  have h2 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c885, some c839, some c820, some c290, some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c885, c839, c820, c290] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c885 := derived885 a h
  have h1 : Entails.eval a c839 := derived839 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c885, some c870, some c774, some c875, some c320, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c885, c870, c774, c875, c320] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c885 := derived885 a h
  have h1 : Entails.eval a c870 := derived870 a h
  have h2 : Entails.eval a c774 := derived774 a h
  have h3 : Entails.eval a c875 := derived875 a h
  have h4 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c887, some c868, some c869, some c884, some c484, some c62, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c887, c868, c869, c884, c484, c62] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c887 := derived887 a h
  have h1 : Entails.eval a c868 := derived868 a h
  have h2 : Entails.eval a c869 := derived869 a h
  have h3 : Entails.eval a c884 := derived884 a h
  have h4 : Entails.eval a c484 := derived484 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c870, some c886, some c319, some c316, some c888, some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c870, c886, c319, c316, c888] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c870 := derived870 a h
  have h1 : Entails.eval a c886 := derived886 a h
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c888 := derived888 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c889, some c839, some c820, some c289, some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c889, c839, c820, c289] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c889 := derived889 a h
  have h1 : Entails.eval a c839 := derived839 a h
  have h2 : Entails.eval a c820 := derived820 a h
  have h3 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c889, some c866, some c622, some c80, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c889, c866, c622, c80] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c889 := derived889 a h
  have h1 : Entails.eval a c866 := derived866 a h
  have h2 : Entails.eval a c622 := derived622 a h
  have h3 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c890, some c884, some c307, some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c890, c884, c307] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c890 := derived890 a h
  have h1 : Entails.eval a c884 := derived884 a h
  have h2 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c891, some c865, some c95, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c891, c865, c95] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c891 := derived891 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c894 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c892, some c893, some c867, some c885, some c74]
def p894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked894 : lratChecker f894 p894 = .success := by decide +kernel
theorem unsat894 : Unsatisfiable (PosFin 57) f894 := by
  apply lratCheckerSound f894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p894
  · intro a ha; simp [p894] at ha; subst a; trivial
  · exact checked894
theorem derived894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c894 := by
  apply localUnsat_implies_entails f894 [c892, c893, c867, c885, c74] c894 unsat894 (by rfl) a
  have h0 : Entails.eval a c892 := derived892 a h
  have h1 : Entails.eval a c893 := derived893 a h
  have h2 : Entails.eval a c867 := derived867 a h
  have h3 : Entails.eval a c885 := derived885 a h
  have h4 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived894

end CochromaticTwenty.Certificates.B16_2_1
