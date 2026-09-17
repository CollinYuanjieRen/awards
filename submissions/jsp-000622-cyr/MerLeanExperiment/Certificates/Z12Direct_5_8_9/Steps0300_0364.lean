import MerLeanExperiment.Certificates.Z12Direct_5_8_9.Steps0200_0299

/-! Generated from the actual pinned z12direct_5_8_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c858 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨27, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c122, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p858 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 31) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c812, c122] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c859 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c124, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p859 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 31) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c812, c124] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c860 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨21, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c125, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p860 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 31) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c812, c125] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c861 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c164, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p861 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 31) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c800, c164] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c862 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨13, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c165, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p862 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 31) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c681, c165] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c863 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c166, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p863 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 31) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c681, c166] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c864 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c168, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p864 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 31) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c752, c681, c168] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c681, some c177, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p865 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 31) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c752, c800, c681, c177] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c178, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p866 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 31) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c752, c800, c178] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c208, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p867 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 31) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c752, c208] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c868 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c210, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p868 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 31) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c800, c210] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c869 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨12, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c211, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p869 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 31) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c800, c211] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c870 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c212, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p870 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 31) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c812, c212] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c871 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c213, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p871 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 31) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c812, c213] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c872 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨22, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c223, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p872 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 31) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c812, c223] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c873 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c260, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p873 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 31) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c800, c752, c260] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c275, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p874 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 31) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c800, c275] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c875 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c296, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p875 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 31) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c681, c296] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c876 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨28, by decide⟩, true), (⟨10, by decide⟩, true), (⟨23, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c326, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p876 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 31) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c800, c326] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c877 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c812, some c371, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p877 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 31) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c752, c812, c371] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c812 := derived812 a h
  have h2 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c812, some c372, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p878 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 31) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c752, c812, c372] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c812 := derived812 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨22, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c377, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p879 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 31) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c681, c377] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c880 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c428, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p880 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 31) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c800, c428] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c428 := h 427 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c881 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨22, by decide⟩, false), (⟨19, by decide⟩, false), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c440, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p881 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 31) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c800, c440] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c440 := h 439 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c882 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨19, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c455, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p882 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 31) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c800, c455] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c455 := h 454 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c883 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨9, by decide⟩, false), (⟨25, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c812, some c489, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p883 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 31) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c752, c812, c489] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c812 := derived812 a h
  have h2 : Entails.eval a c489 := h 488 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨25, by decide⟩, true), (⟨23, by decide⟩, true), (⟨9, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c532, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p884 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 31) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c800, c532] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c532 := h 531 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c885 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c557, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p885 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 31) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c800, c557] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c557 := h 556 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c886 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c655, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p886 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 31) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c800, c655] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c655 := derived655 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c887 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c854, some c160, some c846, some c66, some c33, some c855, some c875, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p887 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 31) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c854, c160, c846, c66, c33, c855, c875] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c854 := derived854 a h
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c846 := derived846 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c855 := derived855 a h
  have h6 : Entails.eval a c875 := derived875 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c844, some c854, some c160, some c870, some c886, some c815, some c244, some c862, some c887, some c48, some c860, some c90, some c876, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p888 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 31) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c844, c854, c160, c870, c886, c815, c244, c862, c887, c48, c860, c90, c876] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c844 := derived844 a h
  have h1 : Entails.eval a c854 := derived854 a h
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c870 := derived870 a h
  have h4 : Entails.eval a c886 := derived886 a h
  have h5 : Entails.eval a c815 := derived815 a h
  have h6 : Entails.eval a c244 := h 243 (by decide)
  have h7 : Entails.eval a c862 := derived862 a h
  have h8 : Entails.eval a c887 := derived887 a h
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c860 := derived860 a h
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c876 := derived876 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c844, some c853, some c870, some c850, some c868, some c886, some c244, some c873, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p889 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 31) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c844, c853, c870, c850, c868, c886, c244, c873] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c844 := derived844 a h
  have h1 : Entails.eval a c853 := derived853 a h
  have h2 : Entails.eval a c870 := derived870 a h
  have h3 : Entails.eval a c850 := derived850 a h
  have h4 : Entails.eval a c868 := derived868 a h
  have h5 : Entails.eval a c886 := derived886 a h
  have h6 : Entails.eval a c244 := h 243 (by decide)
  have h7 : Entails.eval a c873 := derived873 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c844, some c868, some c886, some c873, some c815, some c244, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p890 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 31) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c844, c868, c886, c873, c815, c244] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c844 := derived844 a h
  have h1 : Entails.eval a c868 := derived868 a h
  have h2 : Entails.eval a c886 := derived886 a h
  have h3 : Entails.eval a c873 := derived873 a h
  have h4 : Entails.eval a c815 := derived815 a h
  have h5 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c844, some c888, some c853, some c890, some c846, some c399, some c509, some c872, some c847, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p891 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 31) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c844, c888, c853, c890, c846, c399, c509, c872, c847] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c844 := derived844 a h
  have h1 : Entails.eval a c888 := derived888 a h
  have h2 : Entails.eval a c853 := derived853 a h
  have h3 : Entails.eval a c890 := derived890 a h
  have h4 : Entails.eval a c846 := derived846 a h
  have h5 : Entails.eval a c399 := h 398 (by decide)
  have h6 : Entails.eval a c509 := h 508 (by decide)
  have h7 : Entails.eval a c872 := derived872 a h
  have h8 : Entails.eval a c847 := derived847 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c888, some c889, some c844, some c853, some c890, some c253, some c873, some c248, some c846, some c891, some c827, some c834, some c66, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p892 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 31) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c888, c889, c844, c853, c890, c253, c873, c248, c846, c891, c827, c834, c66] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c888 := derived888 a h
  have h1 : Entails.eval a c889 := derived889 a h
  have h2 : Entails.eval a c844 := derived844 a h
  have h3 : Entails.eval a c853 := derived853 a h
  have h4 : Entails.eval a c890 := derived890 a h
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c873 := derived873 a h
  have h7 : Entails.eval a c248 := h 247 (by decide)
  have h8 : Entails.eval a c846 := derived846 a h
  have h9 : Entails.eval a c891 := derived891 a h
  have h10 : Entails.eval a c827 := derived827 a h
  have h11 : Entails.eval a c834 := derived834 a h
  have h12 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c844, some c846, some c888, some c853, some c889, some c890, some c253, some c873, some c248, some c892, some c848, some c815, some c885, some c882, some c273, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p893 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 31) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c844, c846, c888, c853, c889, c890, c253, c873, c248, c892, c848, c815, c885, c882, c273] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c844 := derived844 a h
  have h1 : Entails.eval a c846 := derived846 a h
  have h2 : Entails.eval a c888 := derived888 a h
  have h3 : Entails.eval a c853 := derived853 a h
  have h4 : Entails.eval a c889 := derived889 a h
  have h5 : Entails.eval a c890 := derived890 a h
  have h6 : Entails.eval a c253 := h 252 (by decide)
  have h7 : Entails.eval a c873 := derived873 a h
  have h8 : Entails.eval a c248 := h 247 (by decide)
  have h9 : Entails.eval a c892 := derived892 a h
  have h10 : Entails.eval a c848 := derived848 a h
  have h11 : Entails.eval a c815 := derived815 a h
  have h12 : Entails.eval a c885 := derived885 a h
  have h13 : Entails.eval a c882 := derived882 a h
  have h14 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c894 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f894 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c893, some c849, some c844, some c846, some c870, some c253, some c873, some c861, some c248, some c350, some c853, some c866, some c864, some c346, some c266, some c874, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p894 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked894 : lratChecker f894 p894 = .success := by decide +kernel
theorem unsat894 : Unsatisfiable (PosFin 31) f894 := by
  apply lratCheckerSound f894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p894
  · intro a ha; simp [p894] at ha; subst a; trivial
  · exact checked894
theorem derived894 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c894 := by
  apply localUnsat_implies_entails f894 [c893, c849, c844, c846, c870, c253, c873, c861, c248, c350, c853, c866, c864, c346, c266, c874] c894 unsat894 (by rfl) a
  have h0 : Entails.eval a c893 := derived893 a h
  have h1 : Entails.eval a c849 := derived849 a h
  have h2 : Entails.eval a c844 := derived844 a h
  have h3 : Entails.eval a c846 := derived846 a h
  have h4 : Entails.eval a c870 := derived870 a h
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c873 := derived873 a h
  have h7 : Entails.eval a c861 := derived861 a h
  have h8 : Entails.eval a c248 := h 247 (by decide)
  have h9 : Entails.eval a c350 := h 349 (by decide)
  have h10 : Entails.eval a c853 := derived853 a h
  have h11 : Entails.eval a c866 := derived866 a h
  have h12 : Entails.eval a c864 := derived864 a h
  have h13 : Entails.eval a c346 := h 345 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c874 := derived874 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c895 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f895 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c844, some c846, some c893, some c849, some c894, some c886, some c890, some c815, some c507, some c554, some c851, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p895 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked895 : lratChecker f895 p895 = .success := by decide +kernel
theorem unsat895 : Unsatisfiable (PosFin 31) f895 := by
  apply lratCheckerSound f895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p895
  · intro a ha; simp [p895] at ha; subst a; trivial
  · exact checked895
theorem derived895 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c895 := by
  apply localUnsat_implies_entails f895 [c844, c846, c893, c849, c894, c886, c890, c815, c507, c554, c851] c895 unsat895 (by rfl) a
  have h0 : Entails.eval a c844 := derived844 a h
  have h1 : Entails.eval a c846 := derived846 a h
  have h2 : Entails.eval a c893 := derived893 a h
  have h3 : Entails.eval a c849 := derived849 a h
  have h4 : Entails.eval a c894 := derived894 a h
  have h5 : Entails.eval a c886 := derived886 a h
  have h6 : Entails.eval a c890 := derived890 a h
  have h7 : Entails.eval a c815 := derived815 a h
  have h8 : Entails.eval a c507 := h 506 (by decide)
  have h9 : Entails.eval a c554 := h 553 (by decide)
  have h10 : Entails.eval a c851 := derived851 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c896 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f896 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c895, some c873, some c868, some c250, some c129, some c861, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p896 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked896 : lratChecker f896 p896 = .success := by decide +kernel
theorem unsat896 : Unsatisfiable (PosFin 31) f896 := by
  apply lratCheckerSound f896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p896
  · intro a ha; simp [p896] at ha; subst a; trivial
  · exact checked896
theorem derived896 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c896 := by
  apply localUnsat_implies_entails f896 [c895, c873, c868, c250, c129, c861] c896 unsat896 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c873 := derived873 a h
  have h2 : Entails.eval a c868 := derived868 a h
  have h3 : Entails.eval a c250 := h 249 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c861 := derived861 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c897 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f897 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c895, some c871, some c254, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p897 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked897 : lratChecker f897 p897 = .success := by decide +kernel
theorem unsat897 : Unsatisfiable (PosFin 31) f897 := by
  apply lratCheckerSound f897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p897
  · intro a ha; simp [p897] at ha; subst a; trivial
  · exact checked897
theorem derived897 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c897 := by
  apply localUnsat_implies_entails f897 [c895, c871, c254] c897 unsat897 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c871 := derived871 a h
  have h2 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c898 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨26, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f898 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c795, some c834, some c881, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p898 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked898 : lratChecker f898 p898 = .success := by decide +kernel
theorem unsat898 : Unsatisfiable (PosFin 31) f898 := by
  apply lratCheckerSound f898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p898
  · intro a ha; simp [p898] at ha; subst a; trivial
  · exact checked898
theorem derived898 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c898 := by
  apply localUnsat_implies_entails f898 [c795, c834, c881] c898 unsat898 (by rfl) a
  have h0 : Entails.eval a c795 := derived795 a h
  have h1 : Entails.eval a c834 := derived834 a h
  have h2 : Entails.eval a c881 := derived881 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c899 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f899 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c895, some c896, some c897, some c886, some c856, some c849, some c898, some c250, some c410, some c516, some c857, some c852, some c859, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p899 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked899 : lratChecker f899 p899 = .success := by decide +kernel
theorem unsat899 : Unsatisfiable (PosFin 31) f899 := by
  apply lratCheckerSound f899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p899
  · intro a ha; simp [p899] at ha; subst a; trivial
  · exact checked899
theorem derived899 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c899 := by
  apply localUnsat_implies_entails f899 [c895, c896, c897, c886, c856, c849, c898, c250, c410, c516, c857, c852, c859] c899 unsat899 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c896 := derived896 a h
  have h2 : Entails.eval a c897 := derived897 a h
  have h3 : Entails.eval a c886 := derived886 a h
  have h4 : Entails.eval a c856 := derived856 a h
  have h5 : Entails.eval a c849 := derived849 a h
  have h6 : Entails.eval a c898 := derived898 a h
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c410 := h 409 (by decide)
  have h9 : Entails.eval a c516 := h 515 (by decide)
  have h10 : Entails.eval a c857 := derived857 a h
  have h11 : Entails.eval a c852 := derived852 a h
  have h12 : Entails.eval a c859 := derived859 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c900 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f900 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c896, some c897, some c886, some c899, some c129, some c136, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p900 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked900 : lratChecker f900 p900 = .success := by decide +kernel
theorem unsat900 : Unsatisfiable (PosFin 31) f900 := by
  apply lratCheckerSound f900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p900
  · intro a ha; simp [p900] at ha; subst a; trivial
  · exact checked900
theorem derived900 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c900 := by
  apply localUnsat_implies_entails f900 [c896, c897, c886, c899, c129, c136] c900 unsat900 (by rfl) a
  have h0 : Entails.eval a c896 := derived896 a h
  have h1 : Entails.eval a c897 := derived897 a h
  have h2 : Entails.eval a c886 := derived886 a h
  have h3 : Entails.eval a c899 := derived899 a h
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c901 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f901 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c895, some c900, some c856, some c841, some c229, some c857, some c845, some c473, some c359, some c859, some c852, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p901 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked901 : lratChecker f901 p901 = .success := by decide +kernel
theorem unsat901 : Unsatisfiable (PosFin 31) f901 := by
  apply lratCheckerSound f901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p901
  · intro a ha; simp [p901] at ha; subst a; trivial
  · exact checked901
theorem derived901 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c901 := by
  apply localUnsat_implies_entails f901 [c895, c900, c856, c841, c229, c857, c845, c473, c359, c859, c852] c901 unsat901 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c900 := derived900 a h
  have h2 : Entails.eval a c856 := derived856 a h
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c229 := h 228 (by decide)
  have h5 : Entails.eval a c857 := derived857 a h
  have h6 : Entails.eval a c845 := derived845 a h
  have h7 : Entails.eval a c473 := h 472 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c859 := derived859 a h
  have h10 : Entails.eval a c852 := derived852 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c902 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f902 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c895, some c229, some c209, some c207, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p902 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked902 : lratChecker f902 p902 = .success := by decide +kernel
theorem unsat902 : Unsatisfiable (PosFin 31) f902 := by
  apply lratCheckerSound f902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p902
  · intro a ha; simp [p902] at ha; subst a; trivial
  · exact checked902
theorem derived902 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c902 := by
  apply localUnsat_implies_entails f902 [c895, c229, c209, c207] c902 unsat902 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c229 := h 228 (by decide)
  have h2 : Entails.eval a c209 := h 208 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c903 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f903 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c900, some c902, some c873, some c901, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p903 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked903 : lratChecker f903 p903 = .success := by decide +kernel
theorem unsat903 : Unsatisfiable (PosFin 31) f903 := by
  apply lratCheckerSound f903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p903
  · intro a ha; simp [p903] at ha; subst a; trivial
  · exact checked903
theorem derived903 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c903 := by
  apply localUnsat_implies_entails f903 [c900, c902, c873, c901] c903 unsat903 (by rfl) a
  have h0 : Entails.eval a c900 := derived900 a h
  have h1 : Entails.eval a c902 := derived902 a h
  have h2 : Entails.eval a c873 := derived873 a h
  have h3 : Entails.eval a c901 := derived901 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c904 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f904 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c895, some c868, some c886, some c873, some c871, some c254, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p904 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked904 : lratChecker f904 p904 = .success := by decide +kernel
theorem unsat904 : Unsatisfiable (PosFin 31) f904 := by
  apply lratCheckerSound f904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p904
  · intro a ha; simp [p904] at ha; subst a; trivial
  · exact checked904
theorem derived904 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c904 := by
  apply localUnsat_implies_entails f904 [c895, c868, c886, c873, c871, c254] c904 unsat904 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c868 := derived868 a h
  have h2 : Entails.eval a c886 := derived886 a h
  have h3 : Entails.eval a c873 := derived873 a h
  have h4 : Entails.eval a c871 := derived871 a h
  have h5 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c905 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f905 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c903, some c904, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p905 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked905 : lratChecker f905 p905 = .success := by decide +kernel
theorem unsat905 : Unsatisfiable (PosFin 31) f905 := by
  apply lratCheckerSound f905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p905
  · intro a ha; simp [p905] at ha; subst a; trivial
  · exact checked905
theorem derived905 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c905 := by
  apply localUnsat_implies_entails f905 [c903, c904] c905 unsat905 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c904 := derived904 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c906 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f906 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c895, some c897, some c873, some c867, some c153, some c849, some c878, some c883, some c854, some c856, some c884, some c880, some c865, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p906 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked906 : lratChecker f906 p906 = .success := by decide +kernel
theorem unsat906 : Unsatisfiable (PosFin 31) f906 := by
  apply lratCheckerSound f906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p906
  · intro a ha; simp [p906] at ha; subst a; trivial
  · exact checked906
theorem derived906 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c906 := by
  apply localUnsat_implies_entails f906 [c895, c897, c873, c867, c153, c849, c878, c883, c854, c856, c884, c880, c865] c906 unsat906 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c897 := derived897 a h
  have h2 : Entails.eval a c873 := derived873 a h
  have h3 : Entails.eval a c867 := derived867 a h
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c849 := derived849 a h
  have h6 : Entails.eval a c878 := derived878 a h
  have h7 : Entails.eval a c883 := derived883 a h
  have h8 : Entails.eval a c854 := derived854 a h
  have h9 : Entails.eval a c856 := derived856 a h
  have h10 : Entails.eval a c884 := derived884 a h
  have h11 : Entails.eval a c880 := derived880 a h
  have h12 : Entails.eval a c865 := derived865 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c907 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f907 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c895, some c906, some c905, some c873, some c867, some c153, some c849, some c37, some c854, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p907 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked907 : lratChecker f907 p907 = .success := by decide +kernel
theorem unsat907 : Unsatisfiable (PosFin 31) f907 := by
  apply lratCheckerSound f907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p907
  · intro a ha; simp [p907] at ha; subst a; trivial
  · exact checked907
theorem derived907 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c907 := by
  apply localUnsat_implies_entails f907 [c895, c906, c905, c873, c867, c153, c849, c37, c854] c907 unsat907 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c906 := derived906 a h
  have h2 : Entails.eval a c905 := derived905 a h
  have h3 : Entails.eval a c873 := derived873 a h
  have h4 : Entails.eval a c867 := derived867 a h
  have h5 : Entails.eval a c153 := h 152 (by decide)
  have h6 : Entails.eval a c849 := derived849 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c854 := derived854 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c908 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f908 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c906, some c895, some c907, some c905, some c153, some c849, some c37, some c160, some c726, some c250, some c879, some c877, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p908 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked908 : lratChecker f908 p908 = .success := by decide +kernel
theorem unsat908 : Unsatisfiable (PosFin 31) f908 := by
  apply lratCheckerSound f908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p908
  · intro a ha; simp [p908] at ha; subst a; trivial
  · exact checked908
theorem derived908 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c908 := by
  apply localUnsat_implies_entails f908 [c906, c895, c907, c905, c153, c849, c37, c160, c726, c250, c879, c877] c908 unsat908 (by rfl) a
  have h0 : Entails.eval a c906 := derived906 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c907 := derived907 a h
  have h3 : Entails.eval a c905 := derived905 a h
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c849 := derived849 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c726 := derived726 a h
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c879 := derived879 a h
  have h11 : Entails.eval a c877 := derived877 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c909 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f909 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c906, some c846, some c869, some c908, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p909 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked909 : lratChecker f909 p909 = .success := by decide +kernel
theorem unsat909 : Unsatisfiable (PosFin 31) f909 := by
  apply lratCheckerSound f909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p909
  · intro a ha; simp [p909] at ha; subst a; trivial
  · exact checked909
theorem derived909 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c909 := by
  apply localUnsat_implies_entails f909 [c906, c846, c869, c908] c909 unsat909 (by rfl) a
  have h0 : Entails.eval a c906 := derived906 a h
  have h1 : Entails.eval a c846 := derived846 a h
  have h2 : Entails.eval a c869 := derived869 a h
  have h3 : Entails.eval a c908 := derived908 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c910 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f910 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c909, some c895, some c856, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p910 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked910 : lratChecker f910 p910 = .success := by decide +kernel
theorem unsat910 : Unsatisfiable (PosFin 31) f910 := by
  apply lratCheckerSound f910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p910
  · intro a ha; simp [p910] at ha; subst a; trivial
  · exact checked910
theorem derived910 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c910 := by
  apply localUnsat_implies_entails f910 [c909, c895, c856] c910 unsat910 (by rfl) a
  have h0 : Entails.eval a c909 := derived909 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c856 := derived856 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c911 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f911 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c909, some c895, some c907, some c801, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p911 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked911 : lratChecker f911 p911 = .success := by decide +kernel
theorem unsat911 : Unsatisfiable (PosFin 31) f911 := by
  apply lratCheckerSound f911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p911
  · intro a ha; simp [p911] at ha; subst a; trivial
  · exact checked911
theorem derived911 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c911 := by
  apply localUnsat_implies_entails f911 [c909, c895, c907, c801] c911 unsat911 (by rfl) a
  have h0 : Entails.eval a c909 := derived909 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c907 := derived907 a h
  have h3 : Entails.eval a c801 := derived801 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c912 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f912 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c911, some c905, some c906, some c26, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p912 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked912 : lratChecker f912 p912 = .success := by decide +kernel
theorem unsat912 : Unsatisfiable (PosFin 31) f912 := by
  apply lratCheckerSound f912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p912
  · intro a ha; simp [p912] at ha; subst a; trivial
  · exact checked912
theorem derived912 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c912 := by
  apply localUnsat_implies_entails f912 [c911, c905, c906, c26] c912 unsat912 (by rfl) a
  have h0 : Entails.eval a c911 := derived911 a h
  have h1 : Entails.eval a c905 := derived905 a h
  have h2 : Entails.eval a c906 := derived906 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c913 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f913 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c895, some c867, some c908, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p913 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked913 : lratChecker f913 p913 = .success := by decide +kernel
theorem unsat913 : Unsatisfiable (PosFin 31) f913 := by
  apply lratCheckerSound f913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p913
  · intro a ha; simp [p913] at ha; subst a; trivial
  · exact checked913
theorem derived913 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c913 := by
  apply localUnsat_implies_entails f913 [c895, c867, c908] c913 unsat913 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c867 := derived867 a h
  have h2 : Entails.eval a c908 := derived908 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c914 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f914 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c913, some c909, some c857, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p914 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked914 : lratChecker f914 p914 = .success := by decide +kernel
theorem unsat914 : Unsatisfiable (PosFin 31) f914 := by
  apply lratCheckerSound f914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p914
  · intro a ha; simp [p914] at ha; subst a; trivial
  · exact checked914
theorem derived914 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c914 := by
  apply localUnsat_implies_entails f914 [c913, c909, c857] c914 unsat914 (by rfl) a
  have h0 : Entails.eval a c913 := derived913 a h
  have h1 : Entails.eval a c909 := derived909 a h
  have h2 : Entails.eval a c857 := derived857 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c915 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f915 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c913, some c909, some c906, some c136, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p915 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked915 : lratChecker f915 p915 = .success := by decide +kernel
theorem unsat915 : Unsatisfiable (PosFin 31) f915 := by
  apply lratCheckerSound f915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p915
  · intro a ha; simp [p915] at ha; subst a; trivial
  · exact checked915
theorem derived915 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c915 := by
  apply localUnsat_implies_entails f915 [c913, c909, c906, c136] c915 unsat915 (by rfl) a
  have h0 : Entails.eval a c913 := derived913 a h
  have h1 : Entails.eval a c909 := derived909 a h
  have h2 : Entails.eval a c906 := derived906 a h
  have h3 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c916 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f916 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c915, some c849, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p916 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked916 : lratChecker f916 p916 = .success := by decide +kernel
theorem unsat916 : Unsatisfiable (PosFin 31) f916 := by
  apply lratCheckerSound f916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p916
  · intro a ha; simp [p916] at ha; subst a; trivial
  · exact checked916
theorem derived916 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c916 := by
  apply localUnsat_implies_entails f916 [c915, c849] c916 unsat916 (by rfl) a
  have h0 : Entails.eval a c915 := derived915 a h
  have h1 : Entails.eval a c849 := derived849 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c917 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f917 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c912, some c911, some c863, some c862, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p917 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked917 : lratChecker f917 p917 = .success := by decide +kernel
theorem unsat917 : Unsatisfiable (PosFin 31) f917 := by
  apply lratCheckerSound f917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p917
  · intro a ha; simp [p917] at ha; subst a; trivial
  · exact checked917
theorem derived917 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c917 := by
  apply localUnsat_implies_entails f917 [c912, c911, c863, c862] c917 unsat917 (by rfl) a
  have h0 : Entails.eval a c912 := derived912 a h
  have h1 : Entails.eval a c911 := derived911 a h
  have h2 : Entails.eval a c863 := derived863 a h
  have h3 : Entails.eval a c862 := derived862 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c918 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f918 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c905, some c906, some c915, some c907, some c917, some c284, some c858, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p918 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked918 : lratChecker f918 p918 = .success := by decide +kernel
theorem unsat918 : Unsatisfiable (PosFin 31) f918 := by
  apply lratCheckerSound f918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p918
  · intro a ha; simp [p918] at ha; subst a; trivial
  · exact checked918
theorem derived918 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c918 := by
  apply localUnsat_implies_entails f918 [c905, c906, c915, c907, c917, c284, c858] c918 unsat918 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c906 := derived906 a h
  have h2 : Entails.eval a c915 := derived915 a h
  have h3 : Entails.eval a c907 := derived907 a h
  have h4 : Entails.eval a c917 := derived917 a h
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c858 := derived858 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c919 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f919 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c916, some c909, some c895, some c912, some c913, some c410, some c516, some c852, some c918, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p919 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked919 : lratChecker f919 p919 = .success := by decide +kernel
theorem unsat919 : Unsatisfiable (PosFin 31) f919 := by
  apply lratCheckerSound f919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p919
  · intro a ha; simp [p919] at ha; subst a; trivial
  · exact checked919
theorem derived919 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c919 := by
  apply localUnsat_implies_entails f919 [c916, c909, c895, c912, c913, c410, c516, c852, c918] c919 unsat919 (by rfl) a
  have h0 : Entails.eval a c916 := derived916 a h
  have h1 : Entails.eval a c909 := derived909 a h
  have h2 : Entails.eval a c895 := derived895 a h
  have h3 : Entails.eval a c912 := derived912 a h
  have h4 : Entails.eval a c913 := derived913 a h
  have h5 : Entails.eval a c410 := h 409 (by decide)
  have h6 : Entails.eval a c516 := h 515 (by decide)
  have h7 : Entails.eval a c852 := derived852 a h
  have h8 : Entails.eval a c918 := derived918 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c920 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f920 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c919, some c915, some c905, some c911, some c914, some c422, some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p920 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked920 : lratChecker f920 p920 = .success := by decide +kernel
theorem unsat920 : Unsatisfiable (PosFin 31) f920 := by
  apply lratCheckerSound f920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p920
  · intro a ha; simp [p920] at ha; subst a; trivial
  · exact checked920
theorem derived920 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c920 := by
  apply localUnsat_implies_entails f920 [c919, c915, c905, c911, c914, c422] c920 unsat920 (by rfl) a
  have h0 : Entails.eval a c919 := derived919 a h
  have h1 : Entails.eval a c915 := derived915 a h
  have h2 : Entails.eval a c905 := derived905 a h
  have h3 : Entails.eval a c911 := derived911 a h
  have h4 : Entails.eval a c914 := derived914 a h
  have h5 : Entails.eval a c422 := h 421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c921 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f921 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c919, some c915, some c905, some c911, some c914, some c526, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p921 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked921 : lratChecker f921 p921 = .success := by decide +kernel
theorem unsat921 : Unsatisfiable (PosFin 31) f921 := by
  apply lratCheckerSound f921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p921
  · intro a ha; simp [p921] at ha; subst a; trivial
  · exact checked921
theorem derived921 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c921 := by
  apply localUnsat_implies_entails f921 [c919, c915, c905, c911, c914, c526] c921 unsat921 (by rfl) a
  have h0 : Entails.eval a c919 := derived919 a h
  have h1 : Entails.eval a c915 := derived915 a h
  have h2 : Entails.eval a c905 := derived905 a h
  have h3 : Entails.eval a c911 := derived911 a h
  have h4 : Entails.eval a c914 := derived914 a h
  have h5 : Entails.eval a c526 := h 525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c922 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f922 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c921, some c920, some c910, some c69]
def p922 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked922 : lratChecker f922 p922 = .success := by decide +kernel
theorem unsat922 : Unsatisfiable (PosFin 31) f922 := by
  apply lratCheckerSound f922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p922
  · intro a ha; simp [p922] at ha; subst a; trivial
  · exact checked922
theorem derived922 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c922 := by
  apply localUnsat_implies_entails f922 [c921, c920, c910, c69] c922 unsat922 (by rfl) a
  have h0 : Entails.eval a c921 := derived921 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c910 := derived910 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived922

end CochromaticTwenty.Certificates.Z12Direct_5_8_9
