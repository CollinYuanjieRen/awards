import MerLeanExperiment.Certificates.FixedCore1.Steps0900_0999

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6881 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨38, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6881 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4442, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6881 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6881 : lratChecker f6881 p6881 = .success := by decide +kernel
theorem unsat6881 : Unsatisfiable (PosFin 65) f6881 := by
  apply lratCheckerSound f6881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6881
  · intro a ha; simp [p6881] at ha; subst a; trivial
  · exact checked6881
theorem derived6881 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6881 := by
  apply localUnsat_implies_entails f6881 [c6581, c4442] c6881 unsat6881 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4442 := h 4441 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6882 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨39, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6882 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4451, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p6882 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6882 : lratChecker f6882 p6882 = .success := by decide +kernel
theorem unsat6882 : Unsatisfiable (PosFin 65) f6882 := by
  apply lratCheckerSound f6882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6882
  · intro a ha; simp [p6882] at ha; subst a; trivial
  · exact checked6882
theorem derived6882 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6882 := by
  apply localUnsat_implies_entails f6882 [c6581, c4451] c6882 unsat6882 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4451 := h 4450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6883 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨56, by decide⟩, true), (⟨39, by decide⟩, true), (⟨44, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6883 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4454, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6883 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6883 : lratChecker f6883 p6883 = .success := by decide +kernel
theorem unsat6883 : Unsatisfiable (PosFin 65) f6883 := by
  apply lratCheckerSound f6883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6883
  · intro a ha; simp [p6883] at ha; subst a; trivial
  · exact checked6883
theorem derived6883 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6883 := by
  apply localUnsat_implies_entails f6883 [c6581, c4454] c6883 unsat6883 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4454 := h 4453 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6884 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨35, by decide⟩, true), (⟨49, by decide⟩, true), (⟨45, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6884 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4459, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p6884 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6884 : lratChecker f6884 p6884 = .success := by decide +kernel
theorem unsat6884 : Unsatisfiable (PosFin 65) f6884 := by
  apply lratCheckerSound f6884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6884
  · intro a ha; simp [p6884] at ha; subst a; trivial
  · exact checked6884
theorem derived6884 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6884 := by
  apply localUnsat_implies_entails f6884 [c6581, c4459] c6884 unsat6884 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4459 := h 4458 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6885 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨35, by decide⟩, true), (⟨45, by decide⟩, true), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6885 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4471, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6885 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6885 : lratChecker f6885 p6885 = .success := by decide +kernel
theorem unsat6885 : Unsatisfiable (PosFin 65) f6885 := by
  apply lratCheckerSound f6885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6885
  · intro a ha; simp [p6885] at ha; subst a; trivial
  · exact checked6885
theorem derived6885 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6885 := by
  apply localUnsat_implies_entails f6885 [c6581, c4471] c6885 unsat6885 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4471 := h 4470 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6886 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨45, by decide⟩, true), (⟨39, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6886 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4474, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6886 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6886 : lratChecker f6886 p6886 = .success := by decide +kernel
theorem unsat6886 : Unsatisfiable (PosFin 65) f6886 := by
  apply lratCheckerSound f6886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6886
  · intro a ha; simp [p6886] at ha; subst a; trivial
  · exact checked6886
theorem derived6886 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6886 := by
  apply localUnsat_implies_entails f6886 [c6581, c4474] c6886 unsat6886 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4474 := h 4473 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6887 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6887 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4475, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p6887 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6887 : lratChecker f6887 p6887 = .success := by decide +kernel
theorem unsat6887 : Unsatisfiable (PosFin 65) f6887 := by
  apply lratCheckerSound f6887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6887
  · intro a ha; simp [p6887] at ha; subst a; trivial
  · exact checked6887
theorem derived6887 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6887 := by
  apply localUnsat_implies_entails f6887 [c6581, c4475] c6887 unsat6887 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4475 := h 4474 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6888 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨57, by decide⟩, true), (⟨40, by decide⟩, false), (⟨43, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6888 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4490, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6888 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6888 : lratChecker f6888 p6888 = .success := by decide +kernel
theorem unsat6888 : Unsatisfiable (PosFin 65) f6888 := by
  apply lratCheckerSound f6888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6888
  · intro a ha; simp [p6888] at ha; subst a; trivial
  · exact checked6888
theorem derived6888 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6888 := by
  apply localUnsat_implies_entails f6888 [c6581, c4490] c6888 unsat6888 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4490 := h 4489 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6889 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨60, by decide⟩, true), (⟨40, by decide⟩, false), (⟨43, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6889 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4492, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6889 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6889 : lratChecker f6889 p6889 = .success := by decide +kernel
theorem unsat6889 : Unsatisfiable (PosFin 65) f6889 := by
  apply lratCheckerSound f6889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6889
  · intro a ha; simp [p6889] at ha; subst a; trivial
  · exact checked6889
theorem derived6889 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6889 := by
  apply localUnsat_implies_entails f6889 [c6581, c4492] c6889 unsat6889 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4492 := h 4491 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6890 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨40, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6890 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4494, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p6890 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6890 : lratChecker f6890 p6890 = .success := by decide +kernel
theorem unsat6890 : Unsatisfiable (PosFin 65) f6890 := by
  apply lratCheckerSound f6890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6890
  · intro a ha; simp [p6890] at ha; subst a; trivial
  · exact checked6890
theorem derived6890 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6890 := by
  apply localUnsat_implies_entails f6890 [c6581, c4494] c6890 unsat6890 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4494 := h 4493 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6891 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6891 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4517, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p6891 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6891 : lratChecker f6891 p6891 = .success := by decide +kernel
theorem unsat6891 : Unsatisfiable (PosFin 65) f6891 := by
  apply lratCheckerSound f6891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6891
  · intro a ha; simp [p6891] at ha; subst a; trivial
  · exact checked6891
theorem derived6891 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6891 := by
  apply localUnsat_implies_entails f6891 [c6581, c4517] c6891 unsat6891 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4517 := h 4516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6892 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6892 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4518, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6892 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6892 : lratChecker f6892 p6892 = .success := by decide +kernel
theorem unsat6892 : Unsatisfiable (PosFin 65) f6892 := by
  apply lratCheckerSound f6892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6892
  · intro a ha; simp [p6892] at ha; subst a; trivial
  · exact checked6892
theorem derived6892 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6892 := by
  apply localUnsat_implies_entails f6892 [c6581, c4518] c6892 unsat6892 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4518 := h 4517 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6893 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6893 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4520, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p6893 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6893 : lratChecker f6893 p6893 = .success := by decide +kernel
theorem unsat6893 : Unsatisfiable (PosFin 65) f6893 := by
  apply lratCheckerSound f6893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6893
  · intro a ha; simp [p6893] at ha; subst a; trivial
  · exact checked6893
theorem derived6893 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6893 := by
  apply localUnsat_implies_entails f6893 [c6581, c4520] c6893 unsat6893 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4520 := h 4519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6894 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨47, by decide⟩, true), (⟨49, by decide⟩, true), (⟨35, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6894 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4534, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p6894 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6894 : lratChecker f6894 p6894 = .success := by decide +kernel
theorem unsat6894 : Unsatisfiable (PosFin 65) f6894 := by
  apply lratCheckerSound f6894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6894
  · intro a ha; simp [p6894] at ha; subst a; trivial
  · exact checked6894
theorem derived6894 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6894 := by
  apply localUnsat_implies_entails f6894 [c6581, c4534] c6894 unsat6894 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4534 := h 4533 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6895 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨35, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6895 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4537, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6895 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6895 : lratChecker f6895 p6895 = .success := by decide +kernel
theorem unsat6895 : Unsatisfiable (PosFin 65) f6895 := by
  apply lratCheckerSound f6895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6895
  · intro a ha; simp [p6895] at ha; subst a; trivial
  · exact checked6895
theorem derived6895 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6895 := by
  apply localUnsat_implies_entails f6895 [c6581, c4537] c6895 unsat6895 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4537 := h 4536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6896 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨50, by decide⟩, true), (⟨47, by decide⟩, true), (⟨41, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6896 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4538, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6896 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6896 : lratChecker f6896 p6896 = .success := by decide +kernel
theorem unsat6896 : Unsatisfiable (PosFin 65) f6896 := by
  apply lratCheckerSound f6896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6896
  · intro a ha; simp [p6896] at ha; subst a; trivial
  · exact checked6896
theorem derived6896 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6896 := by
  apply localUnsat_implies_entails f6896 [c6581, c4538] c6896 unsat6896 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4538 := h 4537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6897 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨60, by decide⟩, true), (⟨47, by decide⟩, true), (⟨41, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6897 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4550, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6897 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6897 : lratChecker f6897 p6897 = .success := by decide +kernel
theorem unsat6897 : Unsatisfiable (PosFin 65) f6897 := by
  apply lratCheckerSound f6897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6897
  · intro a ha; simp [p6897] at ha; subst a; trivial
  · exact checked6897
theorem derived6897 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6897 := by
  apply localUnsat_implies_entails f6897 [c6581, c4550] c6897 unsat6897 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4550 := h 4549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6898 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨35, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6898 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4553, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p6898 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6898 : lratChecker f6898 p6898 = .success := by decide +kernel
theorem unsat6898 : Unsatisfiable (PosFin 65) f6898 := by
  apply lratCheckerSound f6898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6898
  · intro a ha; simp [p6898] at ha; subst a; trivial
  · exact checked6898
theorem derived6898 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6898 := by
  apply localUnsat_implies_entails f6898 [c6581, c4553] c6898 unsat6898 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4553 := h 4552 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6899 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨56, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6899 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4554, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p6899 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6899 : lratChecker f6899 p6899 = .success := by decide +kernel
theorem unsat6899 : Unsatisfiable (PosFin 65) f6899 := by
  apply lratCheckerSound f6899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6899
  · intro a ha; simp [p6899] at ha; subst a; trivial
  · exact checked6899
theorem derived6899 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6899 := by
  apply localUnsat_implies_entails f6899 [c6581, c4554] c6899 unsat6899 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4554 := h 4553 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6900 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6900 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4555, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6900 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6900 : lratChecker f6900 p6900 = .success := by decide +kernel
theorem unsat6900 : Unsatisfiable (PosFin 65) f6900 := by
  apply lratCheckerSound f6900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6900
  · intro a ha; simp [p6900] at ha; subst a; trivial
  · exact checked6900
theorem derived6900 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6900 := by
  apply localUnsat_implies_entails f6900 [c6581, c4555] c6900 unsat6900 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4555 := h 4554 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6901 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6901 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4568, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p6901 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6901 : lratChecker f6901 p6901 = .success := by decide +kernel
theorem unsat6901 : Unsatisfiable (PosFin 65) f6901 := by
  apply lratCheckerSound f6901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6901
  · intro a ha; simp [p6901] at ha; subst a; trivial
  · exact checked6901
theorem derived6901 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6901 := by
  apply localUnsat_implies_entails f6901 [c6581, c4568] c6901 unsat6901 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4568 := h 4567 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6902 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨35, by decide⟩, false), (⟨46, by decide⟩, false), (⟨42, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6902 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4570, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6902 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6902 : lratChecker f6902 p6902 = .success := by decide +kernel
theorem unsat6902 : Unsatisfiable (PosFin 65) f6902 := by
  apply lratCheckerSound f6902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6902
  · intro a ha; simp [p6902] at ha; subst a; trivial
  · exact checked6902
theorem derived6902 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6902 := by
  apply localUnsat_implies_entails f6902 [c6581, c4570] c6902 unsat6902 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4570 := h 4569 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6903 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨54, by decide⟩, true), (⟨47, by decide⟩, true), (⟨49, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6903 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4622, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p6903 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6903 : lratChecker f6903 p6903 = .success := by decide +kernel
theorem unsat6903 : Unsatisfiable (PosFin 65) f6903 := by
  apply lratCheckerSound f6903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6903
  · intro a ha; simp [p6903] at ha; subst a; trivial
  · exact checked6903
theorem derived6903 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6903 := by
  apply localUnsat_implies_entails f6903 [c6581, c4622] c6903 unsat6903 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4622 := h 4621 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6904 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨47, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6904 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4626, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6904 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6904 : lratChecker f6904 p6904 = .success := by decide +kernel
theorem unsat6904 : Unsatisfiable (PosFin 65) f6904 := by
  apply lratCheckerSound f6904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6904
  · intro a ha; simp [p6904] at ha; subst a; trivial
  · exact checked6904
theorem derived6904 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6904 := by
  apply localUnsat_implies_entails f6904 [c6581, c4626] c6904 unsat6904 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4626 := h 4625 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6905 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨35, by decide⟩, true), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6905 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4636, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6905 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6905 : lratChecker f6905 p6905 = .success := by decide +kernel
theorem unsat6905 : Unsatisfiable (PosFin 65) f6905 := by
  apply lratCheckerSound f6905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6905
  · intro a ha; simp [p6905] at ha; subst a; trivial
  · exact checked6905
theorem derived6905 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6905 := by
  apply localUnsat_implies_entails f6905 [c6581, c4636] c6905 unsat6905 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4636 := h 4635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6906 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6906 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4641, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6906 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6906 : lratChecker f6906 p6906 = .success := by decide +kernel
theorem unsat6906 : Unsatisfiable (PosFin 65) f6906 := by
  apply lratCheckerSound f6906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6906
  · intro a ha; simp [p6906] at ha; subst a; trivial
  · exact checked6906
theorem derived6906 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6906 := by
  apply localUnsat_implies_entails f6906 [c6581, c4641] c6906 unsat6906 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4641 := h 4640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6907 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6907 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4642, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6907 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6907 : lratChecker f6907 p6907 = .success := by decide +kernel
theorem unsat6907 : Unsatisfiable (PosFin 65) f6907 := by
  apply lratCheckerSound f6907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6907
  · intro a ha; simp [p6907] at ha; subst a; trivial
  · exact checked6907
theorem derived6907 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6907 := by
  apply localUnsat_implies_entails f6907 [c6581, c4642] c6907 unsat6907 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4642 := h 4641 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6908 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨36, by decide⟩, true), (⟨37, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6908 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4644, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p6908 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6908 : lratChecker f6908 p6908 = .success := by decide +kernel
theorem unsat6908 : Unsatisfiable (PosFin 65) f6908 := by
  apply lratCheckerSound f6908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6908
  · intro a ha; simp [p6908] at ha; subst a; trivial
  · exact checked6908
theorem derived6908 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6908 := by
  apply localUnsat_implies_entails f6908 [c6581, c4644] c6908 unsat6908 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4644 := h 4643 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6909 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨42, by decide⟩, true), (⟨49, by decide⟩, true), (⟨36, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6909 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4645, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6909 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6909 : lratChecker f6909 p6909 = .success := by decide +kernel
theorem unsat6909 : Unsatisfiable (PosFin 65) f6909 := by
  apply lratCheckerSound f6909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6909
  · intro a ha; simp [p6909] at ha; subst a; trivial
  · exact checked6909
theorem derived6909 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6909 := by
  apply localUnsat_implies_entails f6909 [c6581, c4645] c6909 unsat6909 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4645 := h 4644 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6910 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨36, by decide⟩, true), (⟨62, by decide⟩, true), (⟨49, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6910 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4646, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6910 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6910 : lratChecker f6910 p6910 = .success := by decide +kernel
theorem unsat6910 : Unsatisfiable (PosFin 65) f6910 := by
  apply lratCheckerSound f6910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6910
  · intro a ha; simp [p6910] at ha; subst a; trivial
  · exact checked6910
theorem derived6910 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6910 := by
  apply localUnsat_implies_entails f6910 [c6581, c4646] c6910 unsat6910 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4646 := h 4645 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6911 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨42, by decide⟩, true), (⟨36, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6911 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4654, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6911 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6911 : lratChecker f6911 p6911 = .success := by decide +kernel
theorem unsat6911 : Unsatisfiable (PosFin 65) f6911 := by
  apply lratCheckerSound f6911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6911
  · intro a ha; simp [p6911] at ha; subst a; trivial
  · exact checked6911
theorem derived6911 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6911 := by
  apply localUnsat_implies_entails f6911 [c6581, c4654] c6911 unsat6911 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4654 := h 4653 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6912 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨42, by decide⟩, true), (⟨56, by decide⟩, true), (⟨36, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6912 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4659, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6912 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6912 : lratChecker f6912 p6912 = .success := by decide +kernel
theorem unsat6912 : Unsatisfiable (PosFin 65) f6912 := by
  apply lratCheckerSound f6912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6912
  · intro a ha; simp [p6912] at ha; subst a; trivial
  · exact checked6912
theorem derived6912 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6912 := by
  apply localUnsat_implies_entails f6912 [c6581, c4659] c6912 unsat6912 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4659 := h 4658 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6913 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨36, by decide⟩, true), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6913 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4660, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p6913 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6913 : lratChecker f6913 p6913 = .success := by decide +kernel
theorem unsat6913 : Unsatisfiable (PosFin 65) f6913 := by
  apply lratCheckerSound f6913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6913
  · intro a ha; simp [p6913] at ha; subst a; trivial
  · exact checked6913
theorem derived6913 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6913 := by
  apply localUnsat_implies_entails f6913 [c6581, c4660] c6913 unsat6913 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4660 := h 4659 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6914 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨42, by decide⟩, true), (⟨36, by decide⟩, true), (⟨62, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6914 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4664, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6914 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6914 : lratChecker f6914 p6914 = .success := by decide +kernel
theorem unsat6914 : Unsatisfiable (PosFin 65) f6914 := by
  apply lratCheckerSound f6914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6914
  · intro a ha; simp [p6914] at ha; subst a; trivial
  · exact checked6914
theorem derived6914 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6914 := by
  apply localUnsat_implies_entails f6914 [c6581, c4664] c6914 unsat6914 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4664 := h 4663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6915 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨56, by decide⟩, true), (⟨49, by decide⟩, true), (⟨37, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6915 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4666, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p6915 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6915 : lratChecker f6915 p6915 = .success := by decide +kernel
theorem unsat6915 : Unsatisfiable (PosFin 65) f6915 := by
  apply lratCheckerSound f6915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6915
  · intro a ha; simp [p6915] at ha; subst a; trivial
  · exact checked6915
theorem derived6915 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6915 := by
  apply localUnsat_implies_entails f6915 [c6581, c4666] c6915 unsat6915 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4666 := h 4665 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6916 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨36, by decide⟩, true), (⟨49, by decide⟩, true), (⟨37, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6916 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4668, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6916 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6916 : lratChecker f6916 p6916 = .success := by decide +kernel
theorem unsat6916 : Unsatisfiable (PosFin 65) f6916 := by
  apply lratCheckerSound f6916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6916
  · intro a ha; simp [p6916] at ha; subst a; trivial
  · exact checked6916
theorem derived6916 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6916 := by
  apply localUnsat_implies_entails f6916 [c6581, c4668] c6916 unsat6916 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4668 := h 4667 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6917 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨36, by decide⟩, true), (⟨37, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6917 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4681, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p6917 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6917 : lratChecker f6917 p6917 = .success := by decide +kernel
theorem unsat6917 : Unsatisfiable (PosFin 65) f6917 := by
  apply lratCheckerSound f6917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6917
  · intro a ha; simp [p6917] at ha; subst a; trivial
  · exact checked6917
theorem derived6917 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6917 := by
  apply localUnsat_implies_entails f6917 [c6581, c4681] c6917 unsat6917 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4681 := h 4680 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6918 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6918 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4692, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p6918 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6918 : lratChecker f6918 p6918 = .success := by decide +kernel
theorem unsat6918 : Unsatisfiable (PosFin 65) f6918 := by
  apply lratCheckerSound f6918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6918
  · intro a ha; simp [p6918] at ha; subst a; trivial
  · exact checked6918
theorem derived6918 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6918 := by
  apply localUnsat_implies_entails f6918 [c6581, c4692] c6918 unsat6918 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4692 := h 4691 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6919 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨36, by decide⟩, true), (⟨62, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6919 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4693, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6919 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6919 : lratChecker f6919 p6919 = .success := by decide +kernel
theorem unsat6919 : Unsatisfiable (PosFin 65) f6919 := by
  apply lratCheckerSound f6919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6919
  · intro a ha; simp [p6919] at ha; subst a; trivial
  · exact checked6919
theorem derived6919 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6919 := by
  apply localUnsat_implies_entails f6919 [c6581, c4693] c6919 unsat6919 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4693 := h 4692 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6920 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true), (⟨41, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6920 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4707, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6920 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6920 : lratChecker f6920 p6920 = .success := by decide +kernel
theorem unsat6920 : Unsatisfiable (PosFin 65) f6920 := by
  apply lratCheckerSound f6920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6920
  · intro a ha; simp [p6920] at ha; subst a; trivial
  · exact checked6920
theorem derived6920 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6920 := by
  apply localUnsat_implies_entails f6920 [c6581, c4707] c6920 unsat6920 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4707 := h 4706 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6921 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨56, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6921 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4708, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p6921 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6921 : lratChecker f6921 p6921 = .success := by decide +kernel
theorem unsat6921 : Unsatisfiable (PosFin 65) f6921 := by
  apply lratCheckerSound f6921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6921
  · intro a ha; simp [p6921] at ha; subst a; trivial
  · exact checked6921
theorem derived6921 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6921 := by
  apply localUnsat_implies_entails f6921 [c6581, c4708] c6921 unsat6921 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4708 := h 4707 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6922 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨36, by decide⟩, true), (⟨62, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6922 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4711, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6922 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6922 : lratChecker f6922 p6922 = .success := by decide +kernel
theorem unsat6922 : Unsatisfiable (PosFin 65) f6922 := by
  apply lratCheckerSound f6922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6922
  · intro a ha; simp [p6922] at ha; subst a; trivial
  · exact checked6922
theorem derived6922 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6922 := by
  apply localUnsat_implies_entails f6922 [c6581, c4711] c6922 unsat6922 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4711 := h 4710 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6923 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨56, by decide⟩, true), (⟨43, by decide⟩, true), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6923 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4724, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p6923 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6923 : lratChecker f6923 p6923 = .success := by decide +kernel
theorem unsat6923 : Unsatisfiable (PosFin 65) f6923 := by
  apply lratCheckerSound f6923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6923
  · intro a ha; simp [p6923] at ha; subst a; trivial
  · exact checked6923
theorem derived6923 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6923 := by
  apply localUnsat_implies_entails f6923 [c6581, c4724] c6923 unsat6923 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4724 := h 4723 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6924 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true), (⟨57, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6924 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4727, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p6924 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6924 : lratChecker f6924 p6924 = .success := by decide +kernel
theorem unsat6924 : Unsatisfiable (PosFin 65) f6924 := by
  apply lratCheckerSound f6924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6924
  · intro a ha; simp [p6924] at ha; subst a; trivial
  · exact checked6924
theorem derived6924 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6924 := by
  apply localUnsat_implies_entails f6924 [c6581, c4727] c6924 unsat6924 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4727 := h 4726 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6925 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨49, by decide⟩, true), (⟨40, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6925 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4732, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6925 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6925 : lratChecker f6925 p6925 = .success := by decide +kernel
theorem unsat6925 : Unsatisfiable (PosFin 65) f6925 := by
  apply lratCheckerSound f6925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6925
  · intro a ha; simp [p6925] at ha; subst a; trivial
  · exact checked6925
theorem derived6925 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6925 := by
  apply localUnsat_implies_entails f6925 [c6581, c4732] c6925 unsat6925 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4732 := h 4731 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6926 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6926 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4745, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p6926 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6926 : lratChecker f6926 p6926 = .success := by decide +kernel
theorem unsat6926 : Unsatisfiable (PosFin 65) f6926 := by
  apply lratCheckerSound f6926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6926
  · intro a ha; simp [p6926] at ha; subst a; trivial
  · exact checked6926
theorem derived6926 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6926 := by
  apply localUnsat_implies_entails f6926 [c6581, c4745] c6926 unsat6926 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4745 := h 4744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6927 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6927 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4751, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6927 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6927 : lratChecker f6927 p6927 = .success := by decide +kernel
theorem unsat6927 : Unsatisfiable (PosFin 65) f6927 := by
  apply lratCheckerSound f6927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6927
  · intro a ha; simp [p6927] at ha; subst a; trivial
  · exact checked6927
theorem derived6927 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6927 := by
  apply localUnsat_implies_entails f6927 [c6581, c4751] c6927 unsat6927 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4751 := h 4750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6928 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6928 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4752, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6928 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6928 : lratChecker f6928 p6928 = .success := by decide +kernel
theorem unsat6928 : Unsatisfiable (PosFin 65) f6928 := by
  apply lratCheckerSound f6928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6928
  · intro a ha; simp [p6928] at ha; subst a; trivial
  · exact checked6928
theorem derived6928 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6928 := by
  apply localUnsat_implies_entails f6928 [c6581, c4752] c6928 unsat6928 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4752 := h 4751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6929 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨39, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6929 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4765, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6929 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6929 : lratChecker f6929 p6929 = .success := by decide +kernel
theorem unsat6929 : Unsatisfiable (PosFin 65) f6929 := by
  apply lratCheckerSound f6929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6929
  · intro a ha; simp [p6929] at ha; subst a; trivial
  · exact checked6929
theorem derived6929 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6929 := by
  apply localUnsat_implies_entails f6929 [c6581, c4765] c6929 unsat6929 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4765 := h 4764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6930 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6930 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4771, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p6930 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6930 : lratChecker f6930 p6930 = .success := by decide +kernel
theorem unsat6930 : Unsatisfiable (PosFin 65) f6930 := by
  apply lratCheckerSound f6930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6930
  · intro a ha; simp [p6930] at ha; subst a; trivial
  · exact checked6930
theorem derived6930 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6930 := by
  apply localUnsat_implies_entails f6930 [c6581, c4771] c6930 unsat6930 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4771 := h 4770 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6931 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6931 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4773, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6931 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6931 : lratChecker f6931 p6931 = .success := by decide +kernel
theorem unsat6931 : Unsatisfiable (PosFin 65) f6931 := by
  apply lratCheckerSound f6931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6931
  · intro a ha; simp [p6931] at ha; subst a; trivial
  · exact checked6931
theorem derived6931 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6931 := by
  apply localUnsat_implies_entails f6931 [c6581, c4773] c6931 unsat6931 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4773 := h 4772 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6932 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6932 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4783, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p6932 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6932 : lratChecker f6932 p6932 = .success := by decide +kernel
theorem unsat6932 : Unsatisfiable (PosFin 65) f6932 := by
  apply lratCheckerSound f6932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6932
  · intro a ha; simp [p6932] at ha; subst a; trivial
  · exact checked6932
theorem derived6932 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6932 := by
  apply localUnsat_implies_entails f6932 [c6581, c4783] c6932 unsat6932 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4783 := h 4782 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6933 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨62, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6933 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4785, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p6933 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6933 : lratChecker f6933 p6933 = .success := by decide +kernel
theorem unsat6933 : Unsatisfiable (PosFin 65) f6933 := by
  apply lratCheckerSound f6933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6933
  · intro a ha; simp [p6933] at ha; subst a; trivial
  · exact checked6933
theorem derived6933 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6933 := by
  apply localUnsat_implies_entails f6933 [c6581, c4785] c6933 unsat6933 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4785 := h 4784 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6934 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6934 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4789, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p6934 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6934 : lratChecker f6934 p6934 = .success := by decide +kernel
theorem unsat6934 : Unsatisfiable (PosFin 65) f6934 := by
  apply lratCheckerSound f6934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6934
  · intro a ha; simp [p6934] at ha; subst a; trivial
  · exact checked6934
theorem derived6934 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6934 := by
  apply localUnsat_implies_entails f6934 [c6581, c4789] c6934 unsat6934 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4789 := h 4788 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6935 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨36, by decide⟩, true), (⟨62, by decide⟩, true), (⟨40, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6935 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4811, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p6935 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6935 : lratChecker f6935 p6935 = .success := by decide +kernel
theorem unsat6935 : Unsatisfiable (PosFin 65) f6935 := by
  apply lratCheckerSound f6935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6935
  · intro a ha; simp [p6935] at ha; subst a; trivial
  · exact checked6935
theorem derived6935 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6935 := by
  apply localUnsat_implies_entails f6935 [c6581, c4811] c6935 unsat6935 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4811 := h 4810 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6936 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨42, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6936 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4814, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6936 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6936 : lratChecker f6936 p6936 = .success := by decide +kernel
theorem unsat6936 : Unsatisfiable (PosFin 65) f6936 := by
  apply lratCheckerSound f6936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6936
  · intro a ha; simp [p6936] at ha; subst a; trivial
  · exact checked6936
theorem derived6936 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6936 := by
  apply localUnsat_implies_entails f6936 [c6581, c4814] c6936 unsat6936 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4814 := h 4813 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6937 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨49, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6937 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4816, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6937 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6937 : lratChecker f6937 p6937 = .success := by decide +kernel
theorem unsat6937 : Unsatisfiable (PosFin 65) f6937 := by
  apply lratCheckerSound f6937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6937
  · intro a ha; simp [p6937] at ha; subst a; trivial
  · exact checked6937
theorem derived6937 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6937 := by
  apply localUnsat_implies_entails f6937 [c6581, c4816] c6937 unsat6937 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4816 := h 4815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6938 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨50, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6938 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4818, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6938 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6938 : lratChecker f6938 p6938 = .success := by decide +kernel
theorem unsat6938 : Unsatisfiable (PosFin 65) f6938 := by
  apply lratCheckerSound f6938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6938
  · intro a ha; simp [p6938] at ha; subst a; trivial
  · exact checked6938
theorem derived6938 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6938 := by
  apply localUnsat_implies_entails f6938 [c6581, c4818] c6938 unsat6938 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4818 := h 4817 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6939 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨42, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6939 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4833, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6939 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6939 : lratChecker f6939 p6939 = .success := by decide +kernel
theorem unsat6939 : Unsatisfiable (PosFin 65) f6939 := by
  apply lratCheckerSound f6939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6939
  · intro a ha; simp [p6939] at ha; subst a; trivial
  · exact checked6939
theorem derived6939 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6939 := by
  apply localUnsat_implies_entails f6939 [c6581, c4833] c6939 unsat6939 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4833 := h 4832 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6940 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨36, by decide⟩, true), (⟨62, by decide⟩, true), (⟨42, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6940 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4852, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6940 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6940 : lratChecker f6940 p6940 = .success := by decide +kernel
theorem unsat6940 : Unsatisfiable (PosFin 65) f6940 := by
  apply lratCheckerSound f6940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6940
  · intro a ha; simp [p6940] at ha; subst a; trivial
  · exact checked6940
theorem derived6940 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6940 := by
  apply localUnsat_implies_entails f6940 [c6581, c4852] c6940 unsat6940 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4852 := h 4851 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6941 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨42, by decide⟩, true), (⟨36, by decide⟩, true), (⟨50, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6941 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4856, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p6941 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6941 : lratChecker f6941 p6941 = .success := by decide +kernel
theorem unsat6941 : Unsatisfiable (PosFin 65) f6941 := by
  apply lratCheckerSound f6941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6941
  · intro a ha; simp [p6941] at ha; subst a; trivial
  · exact checked6941
theorem derived6941 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6941 := by
  apply localUnsat_implies_entails f6941 [c6581, c4856] c6941 unsat6941 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4856 := h 4855 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6942 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨42, by decide⟩, true), (⟨36, by decide⟩, true), (⟨62, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6942 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4858, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p6942 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6942 : lratChecker f6942 p6942 = .success := by decide +kernel
theorem unsat6942 : Unsatisfiable (PosFin 65) f6942 := by
  apply lratCheckerSound f6942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6942
  · intro a ha; simp [p6942] at ha; subst a; trivial
  · exact checked6942
theorem derived6942 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6942 := by
  apply localUnsat_implies_entails f6942 [c6581, c4858] c6942 unsat6942 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4858 := h 4857 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6943 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6943 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4873, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6943 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6943 : lratChecker f6943 p6943 = .success := by decide +kernel
theorem unsat6943 : Unsatisfiable (PosFin 65) f6943 := by
  apply lratCheckerSound f6943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6943
  · intro a ha; simp [p6943] at ha; subst a; trivial
  · exact checked6943
theorem derived6943 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6943 := by
  apply localUnsat_implies_entails f6943 [c6581, c4873] c6943 unsat6943 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4873 := h 4872 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6944 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨56, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6944 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4874, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6944 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6944 : lratChecker f6944 p6944 = .success := by decide +kernel
theorem unsat6944 : Unsatisfiable (PosFin 65) f6944 := by
  apply lratCheckerSound f6944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6944
  · intro a ha; simp [p6944] at ha; subst a; trivial
  · exact checked6944
theorem derived6944 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6944 := by
  apply localUnsat_implies_entails f6944 [c6581, c4874] c6944 unsat6944 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4874 := h 4873 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6945 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6945 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4889, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6945 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6945 : lratChecker f6945 p6945 = .success := by decide +kernel
theorem unsat6945 : Unsatisfiable (PosFin 65) f6945 := by
  apply lratCheckerSound f6945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6945
  · intro a ha; simp [p6945] at ha; subst a; trivial
  · exact checked6945
theorem derived6945 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6945 := by
  apply localUnsat_implies_entails f6945 [c6581, c4889] c6945 unsat6945 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4889 := h 4888 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6946 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6946 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4890, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6946 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6946 : lratChecker f6946 p6946 = .success := by decide +kernel
theorem unsat6946 : Unsatisfiable (PosFin 65) f6946 := by
  apply lratCheckerSound f6946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6946
  · intro a ha; simp [p6946] at ha; subst a; trivial
  · exact checked6946
theorem derived6946 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6946 := by
  apply localUnsat_implies_entails f6946 [c6581, c4890] c6946 unsat6946 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4890 := h 4889 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6947 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨47, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6947 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4913, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6947 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6947 : lratChecker f6947 p6947 = .success := by decide +kernel
theorem unsat6947 : Unsatisfiable (PosFin 65) f6947 := by
  apply lratCheckerSound f6947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6947
  · intro a ha; simp [p6947] at ha; subst a; trivial
  · exact checked6947
theorem derived6947 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6947 := by
  apply localUnsat_implies_entails f6947 [c6581, c4913] c6947 unsat6947 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4913 := h 4912 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6948 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6948 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4926, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6948 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6948 : lratChecker f6948 p6948 = .success := by decide +kernel
theorem unsat6948 : Unsatisfiable (PosFin 65) f6948 := by
  apply lratCheckerSound f6948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6948
  · intro a ha; simp [p6948] at ha; subst a; trivial
  · exact checked6948
theorem derived6948 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6948 := by
  apply localUnsat_implies_entails f6948 [c6581, c4926] c6948 unsat6948 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4926 := h 4925 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6949 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨62, by decide⟩, true), (⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6949 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4955, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6949 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6949 : lratChecker f6949 p6949 = .success := by decide +kernel
theorem unsat6949 : Unsatisfiable (PosFin 65) f6949 := by
  apply lratCheckerSound f6949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6949
  · intro a ha; simp [p6949] at ha; subst a; trivial
  · exact checked6949
theorem derived6949 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6949 := by
  apply localUnsat_implies_entails f6949 [c6581, c4955] c6949 unsat6949 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4955 := h 4954 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6950 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false), (⟨62, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6950 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4958, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p6950 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6950 : lratChecker f6950 p6950 = .success := by decide +kernel
theorem unsat6950 : Unsatisfiable (PosFin 65) f6950 := by
  apply lratCheckerSound f6950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6950
  · intro a ha; simp [p6950] at ha; subst a; trivial
  · exact checked6950
theorem derived6950 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6950 := by
  apply localUnsat_implies_entails f6950 [c6581, c4958] c6950 unsat6950 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4958 := h 4957 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6951 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨37, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6951 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4969, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6951 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6951 : lratChecker f6951 p6951 = .success := by decide +kernel
theorem unsat6951 : Unsatisfiable (PosFin 65) f6951 := by
  apply lratCheckerSound f6951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6951
  · intro a ha; simp [p6951] at ha; subst a; trivial
  · exact checked6951
theorem derived6951 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6951 := by
  apply localUnsat_implies_entails f6951 [c6581, c4969] c6951 unsat6951 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4969 := h 4968 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6952 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6952 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4975, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6952 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6952 : lratChecker f6952 p6952 = .success := by decide +kernel
theorem unsat6952 : Unsatisfiable (PosFin 65) f6952 := by
  apply lratCheckerSound f6952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6952
  · intro a ha; simp [p6952] at ha; subst a; trivial
  · exact checked6952
theorem derived6952 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6952 := by
  apply localUnsat_implies_entails f6952 [c6581, c4975] c6952 unsat6952 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4975 := h 4974 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6953 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨62, by decide⟩, true), (⟨40, by decide⟩, false), (⟨49, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6953 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4980, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6953 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6953 : lratChecker f6953 p6953 = .success := by decide +kernel
theorem unsat6953 : Unsatisfiable (PosFin 65) f6953 := by
  apply lratCheckerSound f6953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6953
  · intro a ha; simp [p6953] at ha; subst a; trivial
  · exact checked6953
theorem derived6953 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6953 := by
  apply localUnsat_implies_entails f6953 [c6581, c4980] c6953 unsat6953 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4980 := h 4979 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6954 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨50, by decide⟩, true), (⟨40, by decide⟩, false), (⟨62, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6954 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4982, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6954 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6954 : lratChecker f6954 p6954 = .success := by decide +kernel
theorem unsat6954 : Unsatisfiable (PosFin 65) f6954 := by
  apply lratCheckerSound f6954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6954
  · intro a ha; simp [p6954] at ha; subst a; trivial
  · exact checked6954
theorem derived6954 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6954 := by
  apply localUnsat_implies_entails f6954 [c6581, c4982] c6954 unsat6954 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4982 := h 4981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6955 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6955 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4994, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6955 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6955 : lratChecker f6955 p6955 = .success := by decide +kernel
theorem unsat6955 : Unsatisfiable (PosFin 65) f6955 := by
  apply lratCheckerSound f6955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6955
  · intro a ha; simp [p6955] at ha; subst a; trivial
  · exact checked6955
theorem derived6955 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6955 := by
  apply localUnsat_implies_entails f6955 [c6581, c4994] c6955 unsat6955 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4994 := h 4993 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6956 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6956 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4997, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6956 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6956 : lratChecker f6956 p6956 = .success := by decide +kernel
theorem unsat6956 : Unsatisfiable (PosFin 65) f6956 := by
  apply lratCheckerSound f6956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6956
  · intro a ha; simp [p6956] at ha; subst a; trivial
  · exact checked6956
theorem derived6956 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6956 := by
  apply localUnsat_implies_entails f6956 [c6581, c4997] c6956 unsat6956 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4997 := h 4996 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6957 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨39, by decide⟩, false), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6957 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4999, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6957 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6957 : lratChecker f6957 p6957 = .success := by decide +kernel
theorem unsat6957 : Unsatisfiable (PosFin 65) f6957 := by
  apply lratCheckerSound f6957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6957
  · intro a ha; simp [p6957] at ha; subst a; trivial
  · exact checked6957
theorem derived6957 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6957 := by
  apply localUnsat_implies_entails f6957 [c6581, c4999] c6957 unsat6957 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4999 := h 4998 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6958 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨56, by decide⟩, true), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6958 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5000, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6958 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6958 : lratChecker f6958 p6958 = .success := by decide +kernel
theorem unsat6958 : Unsatisfiable (PosFin 65) f6958 := by
  apply lratCheckerSound f6958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6958
  · intro a ha; simp [p6958] at ha; subst a; trivial
  · exact checked6958
theorem derived6958 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6958 := by
  apply localUnsat_implies_entails f6958 [c6581, c5000] c6958 unsat6958 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5000 := h 4999 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6959 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨39, by decide⟩, false), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6959 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5003, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p6959 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6959 : lratChecker f6959 p6959 = .success := by decide +kernel
theorem unsat6959 : Unsatisfiable (PosFin 65) f6959 := by
  apply lratCheckerSound f6959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6959
  · intro a ha; simp [p6959] at ha; subst a; trivial
  · exact checked6959
theorem derived6959 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6959 := by
  apply localUnsat_implies_entails f6959 [c6581, c5003] c6959 unsat6959 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5003 := h 5002 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6960 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨50, by decide⟩, true), (⟨41, by decide⟩, false), (⟨62, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6960 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5004, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6960 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6960 : lratChecker f6960 p6960 = .success := by decide +kernel
theorem unsat6960 : Unsatisfiable (PosFin 65) f6960 := by
  apply lratCheckerSound f6960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6960
  · intro a ha; simp [p6960] at ha; subst a; trivial
  · exact checked6960
theorem derived6960 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6960 := by
  apply localUnsat_implies_entails f6960 [c6581, c5004] c6960 unsat6960 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5004 := h 5003 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6961 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨39, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6961 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5019, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p6961 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6961 : lratChecker f6961 p6961 = .success := by decide +kernel
theorem unsat6961 : Unsatisfiable (PosFin 65) f6961 := by
  apply lratCheckerSound f6961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6961
  · intro a ha; simp [p6961] at ha; subst a; trivial
  · exact checked6961
theorem derived6961 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6961 := by
  apply localUnsat_implies_entails f6961 [c6581, c5019] c6961 unsat6961 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5019 := h 5018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6962 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨40, by decide⟩, false), (⟨43, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6962 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5049, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6962 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6962 : lratChecker f6962 p6962 = .success := by decide +kernel
theorem unsat6962 : Unsatisfiable (PosFin 65) f6962 := by
  apply lratCheckerSound f6962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6962
  · intro a ha; simp [p6962] at ha; subst a; trivial
  · exact checked6962
theorem derived6962 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6962 := by
  apply localUnsat_implies_entails f6962 [c6581, c5049] c6962 unsat6962 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5049 := h 5048 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6963 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨43, by decide⟩, false), (⟨40, by decide⟩, false), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6963 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5055, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6963 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6963 : lratChecker f6963 p6963 = .success := by decide +kernel
theorem unsat6963 : Unsatisfiable (PosFin 65) f6963 := by
  apply lratCheckerSound f6963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6963
  · intro a ha; simp [p6963] at ha; subst a; trivial
  · exact checked6963
theorem derived6963 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6963 := by
  apply localUnsat_implies_entails f6963 [c6581, c5055] c6963 unsat6963 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5055 := h 5054 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6964 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨40, by decide⟩, false), (⟨43, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6964 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5070, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6964 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6964 : lratChecker f6964 p6964 = .success := by decide +kernel
theorem unsat6964 : Unsatisfiable (PosFin 65) f6964 := by
  apply lratCheckerSound f6964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6964
  · intro a ha; simp [p6964] at ha; subst a; trivial
  · exact checked6964
theorem derived6964 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6964 := by
  apply localUnsat_implies_entails f6964 [c6581, c5070] c6964 unsat6964 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5070 := h 5069 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6965 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨40, by decide⟩, false), (⟨43, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6965 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5077, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6965 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6965 : lratChecker f6965 p6965 = .success := by decide +kernel
theorem unsat6965 : Unsatisfiable (PosFin 65) f6965 := by
  apply lratCheckerSound f6965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6965
  · intro a ha; simp [p6965] at ha; subst a; trivial
  · exact checked6965
theorem derived6965 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6965 := by
  apply localUnsat_implies_entails f6965 [c6581, c5077] c6965 unsat6965 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5077 := h 5076 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6966 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨40, by decide⟩, false), (⟨43, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6966 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5079, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6966 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6966 : lratChecker f6966 p6966 = .success := by decide +kernel
theorem unsat6966 : Unsatisfiable (PosFin 65) f6966 := by
  apply lratCheckerSound f6966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6966
  · intro a ha; simp [p6966] at ha; subst a; trivial
  · exact checked6966
theorem derived6966 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6966 := by
  apply localUnsat_implies_entails f6966 [c6581, c5079] c6966 unsat6966 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5079 := h 5078 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6967 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6967 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5081, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6967 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6967 : lratChecker f6967 p6967 = .success := by decide +kernel
theorem unsat6967 : Unsatisfiable (PosFin 65) f6967 := by
  apply lratCheckerSound f6967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6967
  · intro a ha; simp [p6967] at ha; subst a; trivial
  · exact checked6967
theorem derived6967 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6967 := by
  apply localUnsat_implies_entails f6967 [c6581, c5081] c6967 unsat6967 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5081 := h 5080 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6968 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6968 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5085, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6968 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6968 : lratChecker f6968 p6968 = .success := by decide +kernel
theorem unsat6968 : Unsatisfiable (PosFin 65) f6968 := by
  apply lratCheckerSound f6968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6968
  · intro a ha; simp [p6968] at ha; subst a; trivial
  · exact checked6968
theorem derived6968 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6968 := by
  apply localUnsat_implies_entails f6968 [c6581, c5085] c6968 unsat6968 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5085 := h 5084 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6969 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6969 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5097, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6969 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6969 : lratChecker f6969 p6969 = .success := by decide +kernel
theorem unsat6969 : Unsatisfiable (PosFin 65) f6969 := by
  apply lratCheckerSound f6969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6969
  · intro a ha; simp [p6969] at ha; subst a; trivial
  · exact checked6969
theorem derived6969 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6969 := by
  apply localUnsat_implies_entails f6969 [c6581, c5097] c6969 unsat6969 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5097 := h 5096 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6970 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6970 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5105, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6970 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6970 : lratChecker f6970 p6970 = .success := by decide +kernel
theorem unsat6970 : Unsatisfiable (PosFin 65) f6970 := by
  apply lratCheckerSound f6970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6970
  · intro a ha; simp [p6970] at ha; subst a; trivial
  · exact checked6970
theorem derived6970 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6970 := by
  apply localUnsat_implies_entails f6970 [c6581, c5105] c6970 unsat6970 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5105 := h 5104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6971 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6971 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5107, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6971 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6971 : lratChecker f6971 p6971 = .success := by decide +kernel
theorem unsat6971 : Unsatisfiable (PosFin 65) f6971 := by
  apply lratCheckerSound f6971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6971
  · intro a ha; simp [p6971] at ha; subst a; trivial
  · exact checked6971
theorem derived6971 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6971 := by
  apply localUnsat_implies_entails f6971 [c6581, c5107] c6971 unsat6971 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5107 := h 5106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6972 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6972 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5110, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6972 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6972 : lratChecker f6972 p6972 = .success := by decide +kernel
theorem unsat6972 : Unsatisfiable (PosFin 65) f6972 := by
  apply lratCheckerSound f6972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6972
  · intro a ha; simp [p6972] at ha; subst a; trivial
  · exact checked6972
theorem derived6972 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6972 := by
  apply localUnsat_implies_entails f6972 [c6581, c5110] c6972 unsat6972 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5110 := h 5109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6973 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨62, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6973 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5113, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6973 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6973 : lratChecker f6973 p6973 = .success := by decide +kernel
theorem unsat6973 : Unsatisfiable (PosFin 65) f6973 := by
  apply lratCheckerSound f6973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6973
  · intro a ha; simp [p6973] at ha; subst a; trivial
  · exact checked6973
theorem derived6973 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6973 := by
  apply localUnsat_implies_entails f6973 [c6581, c5113] c6973 unsat6973 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5113 := h 5112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6974 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨62, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6974 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5133, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6974 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6974 : lratChecker f6974 p6974 = .success := by decide +kernel
theorem unsat6974 : Unsatisfiable (PosFin 65) f6974 := by
  apply lratCheckerSound f6974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6974
  · intro a ha; simp [p6974] at ha; subst a; trivial
  · exact checked6974
theorem derived6974 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6974 := by
  apply localUnsat_implies_entails f6974 [c6581, c5133] c6974 unsat6974 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5133 := h 5132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6975 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6975 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5136, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p6975 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6975 : lratChecker f6975 p6975 = .success := by decide +kernel
theorem unsat6975 : Unsatisfiable (PosFin 65) f6975 := by
  apply lratCheckerSound f6975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6975
  · intro a ha; simp [p6975] at ha; subst a; trivial
  · exact checked6975
theorem derived6975 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6975 := by
  apply localUnsat_implies_entails f6975 [c6581, c5136] c6975 unsat6975 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5136 := h 5135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6976 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨45, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6976 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5138, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6976 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6976 : lratChecker f6976 p6976 = .success := by decide +kernel
theorem unsat6976 : Unsatisfiable (PosFin 65) f6976 := by
  apply lratCheckerSound f6976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6976
  · intro a ha; simp [p6976] at ha; subst a; trivial
  · exact checked6976
theorem derived6976 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6976 := by
  apply localUnsat_implies_entails f6976 [c6581, c5138] c6976 unsat6976 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5138 := h 5137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6977 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6977 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5140, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p6977 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6977 : lratChecker f6977 p6977 = .success := by decide +kernel
theorem unsat6977 : Unsatisfiable (PosFin 65) f6977 := by
  apply lratCheckerSound f6977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6977
  · intro a ha; simp [p6977] at ha; subst a; trivial
  · exact checked6977
theorem derived6977 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6977 := by
  apply localUnsat_implies_entails f6977 [c6581, c5140] c6977 unsat6977 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5140 := h 5139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6978 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6978 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5143, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p6978 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6978 : lratChecker f6978 p6978 = .success := by decide +kernel
theorem unsat6978 : Unsatisfiable (PosFin 65) f6978 := by
  apply lratCheckerSound f6978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6978
  · intro a ha; simp [p6978] at ha; subst a; trivial
  · exact checked6978
theorem derived6978 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6978 := by
  apply localUnsat_implies_entails f6978 [c6581, c5143] c6978 unsat6978 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5143 := h 5142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6979 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨50, by decide⟩, true), (⟨62, by decide⟩, true), (⟨45, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6979 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5145, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6979 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6979 : lratChecker f6979 p6979 = .success := by decide +kernel
theorem unsat6979 : Unsatisfiable (PosFin 65) f6979 := by
  apply lratCheckerSound f6979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6979
  · intro a ha; simp [p6979] at ha; subst a; trivial
  · exact checked6979
theorem derived6979 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6979 := by
  apply localUnsat_implies_entails f6979 [c6581, c5145] c6979 unsat6979 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5145 := h 5144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6980 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6980 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5153, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6980 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6980 : lratChecker f6980 p6980 = .success := by decide +kernel
theorem unsat6980 : Unsatisfiable (PosFin 65) f6980 := by
  apply lratCheckerSound f6980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6980
  · intro a ha; simp [p6980] at ha; subst a; trivial
  · exact checked6980
theorem derived6980 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6980 := by
  apply localUnsat_implies_entails f6980 [c6581, c5153] c6980 unsat6980 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5153 := h 5152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived6980

end CochromaticTwenty.Certificates.FixedCore1
