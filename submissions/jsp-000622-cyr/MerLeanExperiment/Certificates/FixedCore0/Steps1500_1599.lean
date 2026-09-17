import MerLeanExperiment.Certificates.FixedCore0.Steps1400_1499

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9051 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9051 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9049, some c9048, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9051 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9051 : lratChecker f9051 p9051 = .success := by decide +kernel
theorem unsat9051 : Unsatisfiable (PosFin 65) f9051 := by
  apply lratCheckerSound f9051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9051
  · intro a ha; simp [p9051] at ha; subst a; trivial
  · exact checked9051
theorem derived9051 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9051 := by
  apply localUnsat_implies_entails f9051 [c9049, c9048] c9051 unsat9051 (by rfl) a
  have h0 : Entails.eval a c9049 := derived9049 a h
  have h1 : Entails.eval a c9048 := derived9048 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9052 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9052 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8847, some c8905, some c9018, some c9046, some c9047, some c9034, some c9050, some c9051, some c7994, some c5822, some c5477, some c1272, some c4452, some c158, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9052 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9052 : lratChecker f9052 p9052 = .success := by decide +kernel
theorem unsat9052 : Unsatisfiable (PosFin 65) f9052 := by
  apply lratCheckerSound f9052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9052
  · intro a ha; simp [p9052] at ha; subst a; trivial
  · exact checked9052
theorem derived9052 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9052 := by
  apply localUnsat_implies_entails f9052 [c8686, c8847, c8905, c9018, c9046, c9047, c9034, c9050, c9051, c7994, c5822, c5477, c1272, c4452, c158] c9052 unsat9052 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c9018 := derived9018 a h
  have h4 : Entails.eval a c9046 := derived9046 a h
  have h5 : Entails.eval a c9047 := derived9047 a h
  have h6 : Entails.eval a c9034 := derived9034 a h
  have h7 : Entails.eval a c9050 := derived9050 a h
  have h8 : Entails.eval a c9051 := derived9051 a h
  have h9 : Entails.eval a c7994 := derived7994 a h
  have h10 : Entails.eval a c5822 := h 5821 (by decide)
  have h11 : Entails.eval a c5477 := h 5476 (by decide)
  have h12 : Entails.eval a c1272 := h 1271 (by decide)
  have h13 : Entails.eval a c4452 := h 4451 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9053 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨63, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9053 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8604, some c4906, some c4917, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p9053 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9053 : lratChecker f9053 p9053 = .success := by decide +kernel
theorem unsat9053 : Unsatisfiable (PosFin 65) f9053 := by
  apply lratCheckerSound f9053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9053
  · intro a ha; simp [p9053] at ha; subst a; trivial
  · exact checked9053
theorem derived9053 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9053 := by
  apply localUnsat_implies_entails f9053 [c8604, c4906, c4917] c9053 unsat9053 (by rfl) a
  have h0 : Entails.eval a c8604 := derived8604 a h
  have h1 : Entails.eval a c4906 := h 4905 (by decide)
  have h2 : Entails.eval a c4917 := h 4916 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9054 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9054 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5482, some c770, some c176, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9054 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9054 : lratChecker f9054 p9054 = .success := by decide +kernel
theorem unsat9054 : Unsatisfiable (PosFin 65) f9054 := by
  apply lratCheckerSound f9054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9054
  · intro a ha; simp [p9054] at ha; subst a; trivial
  · exact checked9054
theorem derived9054 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9054 := by
  apply localUnsat_implies_entails f9054 [c5482, c770, c176] c9054 unsat9054 (by rfl) a
  have h0 : Entails.eval a c5482 := h 5481 (by decide)
  have h1 : Entails.eval a c770 := h 769 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9055 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨63, by decide⟩, true), (⟨54, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9055 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5814, some c5495, some c5305, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p9055 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9055 : lratChecker f9055 p9055 = .success := by decide +kernel
theorem unsat9055 : Unsatisfiable (PosFin 65) f9055 := by
  apply lratCheckerSound f9055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9055
  · intro a ha; simp [p9055] at ha; subst a; trivial
  · exact checked9055
theorem derived9055 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9055 := by
  apply localUnsat_implies_entails f9055 [c5814, c5495, c5305] c9055 unsat9055 (by rfl) a
  have h0 : Entails.eval a c5814 := h 5813 (by decide)
  have h1 : Entails.eval a c5495 := h 5494 (by decide)
  have h2 : Entails.eval a c5305 := h 5304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9056 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨62, by decide⟩, false), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9056 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9054, some c8861, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9056 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9056 : lratChecker f9056 p9056 = .success := by decide +kernel
theorem unsat9056 : Unsatisfiable (PosFin 65) f9056 := by
  apply lratCheckerSound f9056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9056
  · intro a ha; simp [p9056] at ha; subst a; trivial
  · exact checked9056
theorem derived9056 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9056 := by
  apply localUnsat_implies_entails f9056 [c9054, c8861] c9056 unsat9056 (by rfl) a
  have h0 : Entails.eval a c9054 := derived9054 a h
  have h1 : Entails.eval a c8861 := derived8861 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9057 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨20, by decide⟩, true), (⟨54, by decide⟩, true), (⟨11, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9057 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8963, some c5482, some c5448, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9057 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9057 : lratChecker f9057 p9057 = .success := by decide +kernel
theorem unsat9057 : Unsatisfiable (PosFin 65) f9057 := by
  apply lratCheckerSound f9057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9057
  · intro a ha; simp [p9057] at ha; subst a; trivial
  · exact checked9057
theorem derived9057 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9057 := by
  apply localUnsat_implies_entails f9057 [c8963, c5482, c5448] c9057 unsat9057 (by rfl) a
  have h0 : Entails.eval a c8963 := derived8963 a h
  have h1 : Entails.eval a c5482 := h 5481 (by decide)
  have h2 : Entails.eval a c5448 := h 5447 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9058 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9058 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9052, some c8686, some c8847, some c8905, some c9018, some c9046, some c9047, some c9034, some c8421, some c9053, some c9055, some c9056, some c9057, some c5485, some c2782, some c5931, some c826, some c4203, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9058 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9058 : lratChecker f9058 p9058 = .success := by decide +kernel
theorem unsat9058 : Unsatisfiable (PosFin 65) f9058 := by
  apply lratCheckerSound f9058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9058
  · intro a ha; simp [p9058] at ha; subst a; trivial
  · exact checked9058
theorem derived9058 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9058 := by
  apply localUnsat_implies_entails f9058 [c9052, c8686, c8847, c8905, c9018, c9046, c9047, c9034, c8421, c9053, c9055, c9056, c9057, c5485, c2782, c5931, c826, c4203] c9058 unsat9058 (by rfl) a
  have h0 : Entails.eval a c9052 := derived9052 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8905 := derived8905 a h
  have h4 : Entails.eval a c9018 := derived9018 a h
  have h5 : Entails.eval a c9046 := derived9046 a h
  have h6 : Entails.eval a c9047 := derived9047 a h
  have h7 : Entails.eval a c9034 := derived9034 a h
  have h8 : Entails.eval a c8421 := derived8421 a h
  have h9 : Entails.eval a c9053 := derived9053 a h
  have h10 : Entails.eval a c9055 := derived9055 a h
  have h11 : Entails.eval a c9056 := derived9056 a h
  have h12 : Entails.eval a c9057 := derived9057 a h
  have h13 : Entails.eval a c5485 := h 5484 (by decide)
  have h14 : Entails.eval a c2782 := h 2781 (by decide)
  have h15 : Entails.eval a c5931 := h 5930 (by decide)
  have h16 : Entails.eval a c826 := h 825 (by decide)
  have h17 : Entails.eval a c4203 := h 4202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9059 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9059 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9018, some c8905, some c8686, some c9054, some c824, some c828, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9059 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9059 : lratChecker f9059 p9059 = .success := by decide +kernel
theorem unsat9059 : Unsatisfiable (PosFin 65) f9059 := by
  apply lratCheckerSound f9059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9059
  · intro a ha; simp [p9059] at ha; subst a; trivial
  · exact checked9059
theorem derived9059 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9059 := by
  apply localUnsat_implies_entails f9059 [c9018, c8905, c8686, c9054, c824, c828] c9059 unsat9059 (by rfl) a
  have h0 : Entails.eval a c9018 := derived9018 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c9054 := derived9054 a h
  have h4 : Entails.eval a c824 := h 823 (by decide)
  have h5 : Entails.eval a c828 := h 827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9060 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9060 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9034, some c9018, some c8905, some c8847, some c8686, some c8421, some c9046, some c9047, some c9052, some c9058, some c7994, some c8604, some c2735, some c4722, some c3193, some c4182, some c9059, some c9057, some c5922, some c828, some c826, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9060 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked9060 : lratChecker f9060 p9060 = .success := by decide +kernel
theorem unsat9060 : Unsatisfiable (PosFin 65) f9060 := by
  apply lratCheckerSound f9060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9060
  · intro a ha; simp [p9060] at ha; subst a; trivial
  · exact checked9060
theorem derived9060 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9060 := by
  apply localUnsat_implies_entails f9060 [c9034, c9018, c8905, c8847, c8686, c8421, c9046, c9047, c9052, c9058, c7994, c8604, c2735, c4722, c3193, c4182, c9059, c9057, c5922, c828, c826] c9060 unsat9060 (by rfl) a
  have h0 : Entails.eval a c9034 := derived9034 a h
  have h1 : Entails.eval a c9018 := derived9018 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c9046 := derived9046 a h
  have h7 : Entails.eval a c9047 := derived9047 a h
  have h8 : Entails.eval a c9052 := derived9052 a h
  have h9 : Entails.eval a c9058 := derived9058 a h
  have h10 : Entails.eval a c7994 := derived7994 a h
  have h11 : Entails.eval a c8604 := derived8604 a h
  have h12 : Entails.eval a c2735 := h 2734 (by decide)
  have h13 : Entails.eval a c4722 := h 4721 (by decide)
  have h14 : Entails.eval a c3193 := h 3192 (by decide)
  have h15 : Entails.eval a c4182 := h 4181 (by decide)
  have h16 : Entails.eval a c9059 := derived9059 a h
  have h17 : Entails.eval a c9057 := derived9057 a h
  have h18 : Entails.eval a c5922 := h 5921 (by decide)
  have h19 : Entails.eval a c828 := h 827 (by decide)
  have h20 : Entails.eval a c826 := h 825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9061 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9061 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9035, some c1221, some c1428, some c1231, some c1429, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9061 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9061 : lratChecker f9061 p9061 = .success := by decide +kernel
theorem unsat9061 : Unsatisfiable (PosFin 65) f9061 := by
  apply lratCheckerSound f9061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9061
  · intro a ha; simp [p9061] at ha; subst a; trivial
  · exact checked9061
theorem derived9061 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9061 := by
  apply localUnsat_implies_entails f9061 [c9035, c1221, c1428, c1231, c1429] c9061 unsat9061 (by rfl) a
  have h0 : Entails.eval a c9035 := derived9035 a h
  have h1 : Entails.eval a c1221 := h 1220 (by decide)
  have h2 : Entails.eval a c1428 := h 1427 (by decide)
  have h3 : Entails.eval a c1231 := h 1230 (by decide)
  have h4 : Entails.eval a c1429 := h 1428 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9062 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9062 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9051, some c9029, some c748, some c8941, some c760, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9062 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9062 : lratChecker f9062 p9062 = .success := by decide +kernel
theorem unsat9062 : Unsatisfiable (PosFin 65) f9062 := by
  apply lratCheckerSound f9062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9062
  · intro a ha; simp [p9062] at ha; subst a; trivial
  · exact checked9062
theorem derived9062 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9062 := by
  apply localUnsat_implies_entails f9062 [c9051, c9029, c748, c8941, c760] c9062 unsat9062 (by rfl) a
  have h0 : Entails.eval a c9051 := derived9051 a h
  have h1 : Entails.eval a c9029 := derived9029 a h
  have h2 : Entails.eval a c748 := h 747 (by decide)
  have h3 : Entails.eval a c8941 := derived8941 a h
  have h4 : Entails.eval a c760 := h 759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9063 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9063 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8905, some c9034, some c9061, some c9060, some c8847, some c8421, some c9062, some c8956, some c4905, some c3681, some c1272, some c9029, some c4483, some c4482, some c4484, some c6051, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9063 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9063 : lratChecker f9063 p9063 = .success := by decide +kernel
theorem unsat9063 : Unsatisfiable (PosFin 65) f9063 := by
  apply lratCheckerSound f9063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9063
  · intro a ha; simp [p9063] at ha; subst a; trivial
  · exact checked9063
theorem derived9063 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9063 := by
  apply localUnsat_implies_entails f9063 [c8686, c8905, c9034, c9061, c9060, c8847, c8421, c9062, c8956, c4905, c3681, c1272, c9029, c4483, c4482, c4484, c6051] c9063 unsat9063 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c9034 := derived9034 a h
  have h3 : Entails.eval a c9061 := derived9061 a h
  have h4 : Entails.eval a c9060 := derived9060 a h
  have h5 : Entails.eval a c8847 := derived8847 a h
  have h6 : Entails.eval a c8421 := derived8421 a h
  have h7 : Entails.eval a c9062 := derived9062 a h
  have h8 : Entails.eval a c8956 := derived8956 a h
  have h9 : Entails.eval a c4905 := h 4904 (by decide)
  have h10 : Entails.eval a c3681 := h 3680 (by decide)
  have h11 : Entails.eval a c1272 := h 1271 (by decide)
  have h12 : Entails.eval a c9029 := derived9029 a h
  have h13 : Entails.eval a c4483 := h 4482 (by decide)
  have h14 : Entails.eval a c4482 := h 4481 (by decide)
  have h15 : Entails.eval a c4484 := h 4483 (by decide)
  have h16 : Entails.eval a c6051 := h 6050 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9064 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨26, by decide⟩, true), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨27, by decide⟩, true), (⟨31, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9064 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5665, some c6198, some c230, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9064 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9064 : lratChecker f9064 p9064 = .success := by decide +kernel
theorem unsat9064 : Unsatisfiable (PosFin 65) f9064 := by
  apply lratCheckerSound f9064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9064
  · intro a ha; simp [p9064] at ha; subst a; trivial
  · exact checked9064
theorem derived9064 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9064 := by
  apply localUnsat_implies_entails f9064 [c5665, c6198, c230] c9064 unsat9064 (by rfl) a
  have h0 : Entails.eval a c5665 := h 5664 (by decide)
  have h1 : Entails.eval a c6198 := h 6197 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9065 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨8, by decide⟩, false), (⟨63, by decide⟩, true), (⟨54, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9065 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8941, some c9064, some c8893, some c5889, some c6197, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9065 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9065 : lratChecker f9065 p9065 = .success := by decide +kernel
theorem unsat9065 : Unsatisfiable (PosFin 65) f9065 := by
  apply lratCheckerSound f9065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9065
  · intro a ha; simp [p9065] at ha; subst a; trivial
  · exact checked9065
theorem derived9065 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9065 := by
  apply localUnsat_implies_entails f9065 [c8941, c9064, c8893, c5889, c6197] c9065 unsat9065 (by rfl) a
  have h0 : Entails.eval a c8941 := derived8941 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c8893 := derived8893 a h
  have h3 : Entails.eval a c5889 := h 5888 (by decide)
  have h4 : Entails.eval a c6197 := h 6196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9066 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨20, by decide⟩, true), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9066 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8905, some c9034, some c9061, some c9060, some c8847, some c8963, some c9064, some c5444, some c6214, some c5501, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9066 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9066 : lratChecker f9066 p9066 = .success := by decide +kernel
theorem unsat9066 : Unsatisfiable (PosFin 65) f9066 := by
  apply lratCheckerSound f9066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9066
  · intro a ha; simp [p9066] at ha; subst a; trivial
  · exact checked9066
theorem derived9066 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9066 := by
  apply localUnsat_implies_entails f9066 [c8686, c8905, c9034, c9061, c9060, c8847, c8963, c9064, c5444, c6214, c5501] c9066 unsat9066 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c9034 := derived9034 a h
  have h3 : Entails.eval a c9061 := derived9061 a h
  have h4 : Entails.eval a c9060 := derived9060 a h
  have h5 : Entails.eval a c8847 := derived8847 a h
  have h6 : Entails.eval a c8963 := derived8963 a h
  have h7 : Entails.eval a c9064 := derived9064 a h
  have h8 : Entails.eval a c5444 := h 5443 (by decide)
  have h9 : Entails.eval a c6214 := h 6213 (by decide)
  have h10 : Entails.eval a c5501 := h 5500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9067 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9067 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9063, some c8686, some c8905, some c9034, some c9061, some c9060, some c8847, some c8421, some c9053, some c9065, some c9066, some c8893, some c8918, some c9016, some c5841, some c835, some c6049, some c797, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9067 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9067 : lratChecker f9067 p9067 = .success := by decide +kernel
theorem unsat9067 : Unsatisfiable (PosFin 65) f9067 := by
  apply lratCheckerSound f9067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9067
  · intro a ha; simp [p9067] at ha; subst a; trivial
  · exact checked9067
theorem derived9067 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9067 := by
  apply localUnsat_implies_entails f9067 [c9063, c8686, c8905, c9034, c9061, c9060, c8847, c8421, c9053, c9065, c9066, c8893, c8918, c9016, c5841, c835, c6049, c797] c9067 unsat9067 (by rfl) a
  have h0 : Entails.eval a c9063 := derived9063 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c9034 := derived9034 a h
  have h4 : Entails.eval a c9061 := derived9061 a h
  have h5 : Entails.eval a c9060 := derived9060 a h
  have h6 : Entails.eval a c8847 := derived8847 a h
  have h7 : Entails.eval a c8421 := derived8421 a h
  have h8 : Entails.eval a c9053 := derived9053 a h
  have h9 : Entails.eval a c9065 := derived9065 a h
  have h10 : Entails.eval a c9066 := derived9066 a h
  have h11 : Entails.eval a c8893 := derived8893 a h
  have h12 : Entails.eval a c8918 := derived8918 a h
  have h13 : Entails.eval a c9016 := derived9016 a h
  have h14 : Entails.eval a c5841 := h 5840 (by decide)
  have h15 : Entails.eval a c835 := h 834 (by decide)
  have h16 : Entails.eval a c6049 := h 6048 (by decide)
  have h17 : Entails.eval a c797 := h 796 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9068 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9068 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5946, some c5890, some c9064, some c840, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9068 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9068 : lratChecker f9068 p9068 = .success := by decide +kernel
theorem unsat9068 : Unsatisfiable (PosFin 65) f9068 := by
  apply lratCheckerSound f9068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9068
  · intro a ha; simp [p9068] at ha; subst a; trivial
  · exact checked9068
theorem derived9068 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9068 := by
  apply localUnsat_implies_entails f9068 [c5946, c5890, c9064, c840] c9068 unsat9068 (by rfl) a
  have h0 : Entails.eval a c5946 := h 5945 (by decide)
  have h1 : Entails.eval a c5890 := h 5889 (by decide)
  have h2 : Entails.eval a c9064 := derived9064 a h
  have h3 : Entails.eval a c840 := h 839 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9069 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9069 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8905, some c9034, some c9061, some c9060, some c8847, some c8421, some c9063, some c9067, some c7994, some c8604, some c2735, some c4722, some c3193, some c4182, some c9068, some c9066, some c5922, some c5842, some c6013, some c6053, some c6054, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9069 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9069 : lratChecker f9069 p9069 = .success := by decide +kernel
theorem unsat9069 : Unsatisfiable (PosFin 65) f9069 := by
  apply lratCheckerSound f9069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9069
  · intro a ha; simp [p9069] at ha; subst a; trivial
  · exact checked9069
theorem derived9069 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9069 := by
  apply localUnsat_implies_entails f9069 [c8686, c8905, c9034, c9061, c9060, c8847, c8421, c9063, c9067, c7994, c8604, c2735, c4722, c3193, c4182, c9068, c9066, c5922, c5842, c6013, c6053, c6054] c9069 unsat9069 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c9034 := derived9034 a h
  have h3 : Entails.eval a c9061 := derived9061 a h
  have h4 : Entails.eval a c9060 := derived9060 a h
  have h5 : Entails.eval a c8847 := derived8847 a h
  have h6 : Entails.eval a c8421 := derived8421 a h
  have h7 : Entails.eval a c9063 := derived9063 a h
  have h8 : Entails.eval a c9067 := derived9067 a h
  have h9 : Entails.eval a c7994 := derived7994 a h
  have h10 : Entails.eval a c8604 := derived8604 a h
  have h11 : Entails.eval a c2735 := h 2734 (by decide)
  have h12 : Entails.eval a c4722 := h 4721 (by decide)
  have h13 : Entails.eval a c3193 := h 3192 (by decide)
  have h14 : Entails.eval a c4182 := h 4181 (by decide)
  have h15 : Entails.eval a c9068 := derived9068 a h
  have h16 : Entails.eval a c9066 := derived9066 a h
  have h17 : Entails.eval a c5922 := h 5921 (by decide)
  have h18 : Entails.eval a c5842 := h 5841 (by decide)
  have h19 : Entails.eval a c6013 := h 6012 (by decide)
  have h20 : Entails.eval a c6053 := h 6052 (by decide)
  have h21 : Entails.eval a c6054 := h 6053 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9070 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9070 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9069, some c8686, some c8905, some c9034, some c9061, some c9018, some c8847, some c9051, some c738, some c9029, some c744, some c170, some c155, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9070 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9070 : lratChecker f9070 p9070 = .success := by decide +kernel
theorem unsat9070 : Unsatisfiable (PosFin 65) f9070 := by
  apply lratCheckerSound f9070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9070
  · intro a ha; simp [p9070] at ha; subst a; trivial
  · exact checked9070
theorem derived9070 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9070 := by
  apply localUnsat_implies_entails f9070 [c9069, c8686, c8905, c9034, c9061, c9018, c8847, c9051, c738, c9029, c744, c170, c155] c9070 unsat9070 (by rfl) a
  have h0 : Entails.eval a c9069 := derived9069 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c9034 := derived9034 a h
  have h4 : Entails.eval a c9061 := derived9061 a h
  have h5 : Entails.eval a c9018 := derived9018 a h
  have h6 : Entails.eval a c8847 := derived8847 a h
  have h7 : Entails.eval a c9051 := derived9051 a h
  have h8 : Entails.eval a c738 := h 737 (by decide)
  have h9 : Entails.eval a c9029 := derived9029 a h
  have h10 : Entails.eval a c744 := h 743 (by decide)
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9071 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9071 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9069, some c9018, some c8905, some c9070, some c5822, some c5477, some c147, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9071 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9071 : lratChecker f9071 p9071 = .success := by decide +kernel
theorem unsat9071 : Unsatisfiable (PosFin 65) f9071 := by
  apply lratCheckerSound f9071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9071
  · intro a ha; simp [p9071] at ha; subst a; trivial
  · exact checked9071
theorem derived9071 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9071 := by
  apply localUnsat_implies_entails f9071 [c9069, c9018, c8905, c9070, c5822, c5477, c147] c9071 unsat9071 (by rfl) a
  have h0 : Entails.eval a c9069 := derived9069 a h
  have h1 : Entails.eval a c9018 := derived9018 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c9070 := derived9070 a h
  have h4 : Entails.eval a c5822 := h 5821 (by decide)
  have h5 : Entails.eval a c5477 := h 5476 (by decide)
  have h6 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9072 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9072 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5482, some c9064, some c176, some c769, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9072 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9072 : lratChecker f9072 p9072 = .success := by decide +kernel
theorem unsat9072 : Unsatisfiable (PosFin 65) f9072 := by
  apply lratCheckerSound f9072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9072
  · intro a ha; simp [p9072] at ha; subst a; trivial
  · exact checked9072
theorem derived9072 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9072 := by
  apply localUnsat_implies_entails f9072 [c5482, c9064, c176, c769] c9072 unsat9072 (by rfl) a
  have h0 : Entails.eval a c5482 := h 5481 (by decide)
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c769 := h 768 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9073 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨63, by decide⟩, true), (⟨54, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9073 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5814, some c5495, some c156, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9073 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9073 : lratChecker f9073 p9073 = .success := by decide +kernel
theorem unsat9073 : Unsatisfiable (PosFin 65) f9073 := by
  apply lratCheckerSound f9073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9073
  · intro a ha; simp [p9073] at ha; subst a; trivial
  · exact checked9073
theorem derived9073 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9073 := by
  apply localUnsat_implies_entails f9073 [c5814, c5495, c156] c9073 unsat9073 (by rfl) a
  have h0 : Entails.eval a c5814 := h 5813 (by decide)
  have h1 : Entails.eval a c5495 := h 5494 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9074 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨62, by decide⟩, false), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9074 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9072, some c8867, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9074 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9074 : lratChecker f9074 p9074 = .success := by decide +kernel
theorem unsat9074 : Unsatisfiable (PosFin 65) f9074 := by
  apply lratCheckerSound f9074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9074
  · intro a ha; simp [p9074] at ha; subst a; trivial
  · exact checked9074
theorem derived9074 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9074 := by
  apply localUnsat_implies_entails f9074 [c9072, c8867] c9074 unsat9074 (by rfl) a
  have h0 : Entails.eval a c9072 := derived9072 a h
  have h1 : Entails.eval a c8867 := derived8867 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9075 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9075 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9071, some c9069, some c8686, some c8905, some c9034, some c9061, some c9060, some c9018, some c8847, some c8421, some c9053, some c9073, some c9074, some c9066, some c8903, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9075 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9075 : lratChecker f9075 p9075 = .success := by decide +kernel
theorem unsat9075 : Unsatisfiable (PosFin 65) f9075 := by
  apply lratCheckerSound f9075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9075
  · intro a ha; simp [p9075] at ha; subst a; trivial
  · exact checked9075
theorem derived9075 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9075 := by
  apply localUnsat_implies_entails f9075 [c9071, c9069, c8686, c8905, c9034, c9061, c9060, c9018, c8847, c8421, c9053, c9073, c9074, c9066, c8903] c9075 unsat9075 (by rfl) a
  have h0 : Entails.eval a c9071 := derived9071 a h
  have h1 : Entails.eval a c9069 := derived9069 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8905 := derived8905 a h
  have h4 : Entails.eval a c9034 := derived9034 a h
  have h5 : Entails.eval a c9061 := derived9061 a h
  have h6 : Entails.eval a c9060 := derived9060 a h
  have h7 : Entails.eval a c9018 := derived9018 a h
  have h8 : Entails.eval a c8847 := derived8847 a h
  have h9 : Entails.eval a c8421 := derived8421 a h
  have h10 : Entails.eval a c9053 := derived9053 a h
  have h11 : Entails.eval a c9073 := derived9073 a h
  have h12 : Entails.eval a c9074 := derived9074 a h
  have h13 : Entails.eval a c9066 := derived9066 a h
  have h14 : Entails.eval a c8903 := derived8903 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9076 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9076 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c9071, some c8847, some c9075, some c7994, some c8686, some c8905, some c9034, some c9061, some c8604, some c2735, some c4722, some c3193, some c4182, some c9069, some c9060, some c9018, some c9072, some c9074, some c828, some c5814, some c153, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9076 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9076 : lratChecker f9076 p9076 = .success := by decide +kernel
theorem unsat9076 : Unsatisfiable (PosFin 65) f9076 := by
  apply lratCheckerSound f9076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9076
  · intro a ha; simp [p9076] at ha; subst a; trivial
  · exact checked9076
theorem derived9076 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9076 := by
  apply localUnsat_implies_entails f9076 [c8421, c9071, c8847, c9075, c7994, c8686, c8905, c9034, c9061, c8604, c2735, c4722, c3193, c4182, c9069, c9060, c9018, c9072, c9074, c828, c5814, c153] c9076 unsat9076 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c9071 := derived9071 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c9075 := derived9075 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c8686 := derived8686 a h
  have h6 : Entails.eval a c8905 := derived8905 a h
  have h7 : Entails.eval a c9034 := derived9034 a h
  have h8 : Entails.eval a c9061 := derived9061 a h
  have h9 : Entails.eval a c8604 := derived8604 a h
  have h10 : Entails.eval a c2735 := h 2734 (by decide)
  have h11 : Entails.eval a c4722 := h 4721 (by decide)
  have h12 : Entails.eval a c3193 := h 3192 (by decide)
  have h13 : Entails.eval a c4182 := h 4181 (by decide)
  have h14 : Entails.eval a c9069 := derived9069 a h
  have h15 : Entails.eval a c9060 := derived9060 a h
  have h16 : Entails.eval a c9018 := derived9018 a h
  have h17 : Entails.eval a c9072 := derived9072 a h
  have h18 : Entails.eval a c9074 := derived9074 a h
  have h19 : Entails.eval a c828 := h 827 (by decide)
  have h20 : Entails.eval a c5814 := h 5813 (by decide)
  have h21 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9077 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9077 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8905, some c8847, some c8686, some c8421, some c9034, some c9061, some c9071, some c9075, some c7994, some c8604, some c9076, some c9066, some c5922, some c5842, some c6013, some c6053, some c6054, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9077 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9077 : lratChecker f9077 p9077 = .success := by decide +kernel
theorem unsat9077 : Unsatisfiable (PosFin 65) f9077 := by
  apply lratCheckerSound f9077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9077
  · intro a ha; simp [p9077] at ha; subst a; trivial
  · exact checked9077
theorem derived9077 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9077 := by
  apply localUnsat_implies_entails f9077 [c8905, c8847, c8686, c8421, c9034, c9061, c9071, c9075, c7994, c8604, c9076, c9066, c5922, c5842, c6013, c6053, c6054] c9077 unsat9077 (by rfl) a
  have h0 : Entails.eval a c8905 := derived8905 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c9034 := derived9034 a h
  have h5 : Entails.eval a c9061 := derived9061 a h
  have h6 : Entails.eval a c9071 := derived9071 a h
  have h7 : Entails.eval a c9075 := derived9075 a h
  have h8 : Entails.eval a c7994 := derived7994 a h
  have h9 : Entails.eval a c8604 := derived8604 a h
  have h10 : Entails.eval a c9076 := derived9076 a h
  have h11 : Entails.eval a c9066 := derived9066 a h
  have h12 : Entails.eval a c5922 := h 5921 (by decide)
  have h13 : Entails.eval a c5842 := h 5841 (by decide)
  have h14 : Entails.eval a c6013 := h 6012 (by decide)
  have h15 : Entails.eval a c6053 := h 6052 (by decide)
  have h16 : Entails.eval a c6054 := h 6053 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9078 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9078 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8847, some c8905, some c9018, some c9027, some c9035, some c9077, some c9021, some c9033, some c762, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9078 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9078 : lratChecker f9078 p9078 = .success := by decide +kernel
theorem unsat9078 : Unsatisfiable (PosFin 65) f9078 := by
  apply lratCheckerSound f9078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9078
  · intro a ha; simp [p9078] at ha; subst a; trivial
  · exact checked9078
theorem derived9078 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9078 := by
  apply localUnsat_implies_entails f9078 [c8686, c8847, c8905, c9018, c9027, c9035, c9077, c9021, c9033, c762] c9078 unsat9078 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c9018 := derived9018 a h
  have h4 : Entails.eval a c9027 := derived9027 a h
  have h5 : Entails.eval a c9035 := derived9035 a h
  have h6 : Entails.eval a c9077 := derived9077 a h
  have h7 : Entails.eval a c9021 := derived9021 a h
  have h8 : Entails.eval a c9033 := derived9033 a h
  have h9 : Entails.eval a c762 := h 761 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9079 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9079 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8905, some c9035, some c9077, some c9018, some c8847, some c8421, some c9027, some c9078, some c7994, some c6245, some c6126, some c6268, some c9028, some c5854, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9079 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9079 : lratChecker f9079 p9079 = .success := by decide +kernel
theorem unsat9079 : Unsatisfiable (PosFin 65) f9079 := by
  apply lratCheckerSound f9079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9079
  · intro a ha; simp [p9079] at ha; subst a; trivial
  · exact checked9079
theorem derived9079 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9079 := by
  apply localUnsat_implies_entails f9079 [c8686, c8905, c9035, c9077, c9018, c8847, c8421, c9027, c9078, c7994, c6245, c6126, c6268, c9028, c5854] c9079 unsat9079 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c9035 := derived9035 a h
  have h3 : Entails.eval a c9077 := derived9077 a h
  have h4 : Entails.eval a c9018 := derived9018 a h
  have h5 : Entails.eval a c8847 := derived8847 a h
  have h6 : Entails.eval a c8421 := derived8421 a h
  have h7 : Entails.eval a c9027 := derived9027 a h
  have h8 : Entails.eval a c9078 := derived9078 a h
  have h9 : Entails.eval a c7994 := derived7994 a h
  have h10 : Entails.eval a c6245 := h 6244 (by decide)
  have h11 : Entails.eval a c6126 := h 6125 (by decide)
  have h12 : Entails.eval a c6268 := h 6267 (by decide)
  have h13 : Entails.eval a c9028 := derived9028 a h
  have h14 : Entails.eval a c5854 := h 5853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9080 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, true), (⟨63, by decide⟩, true), (⟨32, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9080 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6120, some c6083, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9080 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9080 : lratChecker f9080 p9080 = .success := by decide +kernel
theorem unsat9080 : Unsatisfiable (PosFin 65) f9080 := by
  apply lratCheckerSound f9080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9080
  · intro a ha; simp [p9080] at ha; subst a; trivial
  · exact checked9080
theorem derived9080 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9080 := by
  apply localUnsat_implies_entails f9080 [c6120, c6083] c9080 unsat9080 (by rfl) a
  have h0 : Entails.eval a c6120 := h 6119 (by decide)
  have h1 : Entails.eval a c6083 := h 6082 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9081 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, true), (⟨54, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9081 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9051, some c9053, some c762, some c764, some c757, some c739, some c742, some c9080, some c802, some c803, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9081 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9081 : lratChecker f9081 p9081 = .success := by decide +kernel
theorem unsat9081 : Unsatisfiable (PosFin 65) f9081 := by
  apply lratCheckerSound f9081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9081
  · intro a ha; simp [p9081] at ha; subst a; trivial
  · exact checked9081
theorem derived9081 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9081 := by
  apply localUnsat_implies_entails f9081 [c9051, c9053, c762, c764, c757, c739, c742, c9080, c802, c803] c9081 unsat9081 (by rfl) a
  have h0 : Entails.eval a c9051 := derived9051 a h
  have h1 : Entails.eval a c9053 := derived9053 a h
  have h2 : Entails.eval a c762 := h 761 (by decide)
  have h3 : Entails.eval a c764 := h 763 (by decide)
  have h4 : Entails.eval a c757 := h 756 (by decide)
  have h5 : Entails.eval a c739 := h 738 (by decide)
  have h6 : Entails.eval a c742 := h 741 (by decide)
  have h7 : Entails.eval a c9080 := derived9080 a h
  have h8 : Entails.eval a c802 := h 801 (by decide)
  have h9 : Entails.eval a c803 := h 802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9082 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨29, by decide⟩, false), (⟨54, by decide⟩, false), (⟨31, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9082 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c762, some c4486, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9082 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9082 : lratChecker f9082 p9082 = .success := by decide +kernel
theorem unsat9082 : Unsatisfiable (PosFin 65) f9082 := by
  apply lratCheckerSound f9082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9082
  · intro a ha; simp [p9082] at ha; subst a; trivial
  · exact checked9082
theorem derived9082 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9082 := by
  apply localUnsat_implies_entails f9082 [c762, c4486] c9082 unsat9082 (by rfl) a
  have h0 : Entails.eval a c762 := h 761 (by decide)
  have h1 : Entails.eval a c4486 := h 4485 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9083 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨12, by decide⟩, true), (⟨63, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨31, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9083 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c4473, some c4452, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9083 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9083 : lratChecker f9083 p9083 = .success := by decide +kernel
theorem unsat9083 : Unsatisfiable (PosFin 65) f9083 := by
  apply lratCheckerSound f9083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9083
  · intro a ha; simp [p9083] at ha; subst a; trivial
  · exact checked9083
theorem derived9083 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9083 := by
  apply localUnsat_implies_entails f9083 [c7994, c4473, c4452] c9083 unsat9083 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c4473 := h 4472 (by decide)
  have h2 : Entails.eval a c4452 := h 4451 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9084 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9084 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9079, some c8686, some c8905, some c9035, some c9077, some c9018, some c8847, some c8421, some c9081, some c4905, some c3681, some c1272, some c9017, some c4729, some c4080, some c9082, some c8956, some c9083, some c764, some c6168, some c6076, some c5915, some c271, some c76, some c6040, some c56, some c5792, some c955, some c5268, some c765, some c736, some c968, some c969, some c114, some c5368, some c5288, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9084 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked9084 : lratChecker f9084 p9084 = .success := by decide +kernel
theorem unsat9084 : Unsatisfiable (PosFin 65) f9084 := by
  apply lratCheckerSound f9084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9084
  · intro a ha; simp [p9084] at ha; subst a; trivial
  · exact checked9084
theorem derived9084 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9084 := by
  apply localUnsat_implies_entails f9084 [c9079, c8686, c8905, c9035, c9077, c9018, c8847, c8421, c9081, c4905, c3681, c1272, c9017, c4729, c4080, c9082, c8956, c9083, c764, c6168, c6076, c5915, c271, c76, c6040, c56, c5792, c955, c5268, c765, c736, c968, c969, c114, c5368, c5288] c9084 unsat9084 (by rfl) a
  have h0 : Entails.eval a c9079 := derived9079 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c9035 := derived9035 a h
  have h4 : Entails.eval a c9077 := derived9077 a h
  have h5 : Entails.eval a c9018 := derived9018 a h
  have h6 : Entails.eval a c8847 := derived8847 a h
  have h7 : Entails.eval a c8421 := derived8421 a h
  have h8 : Entails.eval a c9081 := derived9081 a h
  have h9 : Entails.eval a c4905 := h 4904 (by decide)
  have h10 : Entails.eval a c3681 := h 3680 (by decide)
  have h11 : Entails.eval a c1272 := h 1271 (by decide)
  have h12 : Entails.eval a c9017 := derived9017 a h
  have h13 : Entails.eval a c4729 := h 4728 (by decide)
  have h14 : Entails.eval a c4080 := h 4079 (by decide)
  have h15 : Entails.eval a c9082 := derived9082 a h
  have h16 : Entails.eval a c8956 := derived8956 a h
  have h17 : Entails.eval a c9083 := derived9083 a h
  have h18 : Entails.eval a c764 := h 763 (by decide)
  have h19 : Entails.eval a c6168 := h 6167 (by decide)
  have h20 : Entails.eval a c6076 := h 6075 (by decide)
  have h21 : Entails.eval a c5915 := h 5914 (by decide)
  have h22 : Entails.eval a c271 := h 270 (by decide)
  have h23 : Entails.eval a c76 := h 75 (by decide)
  have h24 : Entails.eval a c6040 := h 6039 (by decide)
  have h25 : Entails.eval a c56 := h 55 (by decide)
  have h26 : Entails.eval a c5792 := h 5791 (by decide)
  have h27 : Entails.eval a c955 := h 954 (by decide)
  have h28 : Entails.eval a c5268 := h 5267 (by decide)
  have h29 : Entails.eval a c765 := h 764 (by decide)
  have h30 : Entails.eval a c736 := h 735 (by decide)
  have h31 : Entails.eval a c968 := h 967 (by decide)
  have h32 : Entails.eval a c969 := h 968 (by decide)
  have h33 : Entails.eval a c114 := h 113 (by decide)
  have h34 : Entails.eval a c5368 := h 5367 (by decide)
  have h35 : Entails.eval a c5288 := h 5287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9085 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9085 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9084, some c9079, some c8686, some c8905, some c9035, some c9018, some c8847, some c9051, some c738, some c744, some c146, some c155, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9085 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9085 : lratChecker f9085 p9085 = .success := by decide +kernel
theorem unsat9085 : Unsatisfiable (PosFin 65) f9085 := by
  apply lratCheckerSound f9085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9085
  · intro a ha; simp [p9085] at ha; subst a; trivial
  · exact checked9085
theorem derived9085 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9085 := by
  apply localUnsat_implies_entails f9085 [c9084, c9079, c8686, c8905, c9035, c9018, c8847, c9051, c738, c744, c146, c155] c9085 unsat9085 (by rfl) a
  have h0 : Entails.eval a c9084 := derived9084 a h
  have h1 : Entails.eval a c9079 := derived9079 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8905 := derived8905 a h
  have h4 : Entails.eval a c9035 := derived9035 a h
  have h5 : Entails.eval a c9018 := derived9018 a h
  have h6 : Entails.eval a c8847 := derived8847 a h
  have h7 : Entails.eval a c9051 := derived9051 a h
  have h8 : Entails.eval a c738 := h 737 (by decide)
  have h9 : Entails.eval a c744 := h 743 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9086 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9086 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9018, some c8905, some c9084, some c9085, some c5822, some c5477, some c147, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9086 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9086 : lratChecker f9086 p9086 = .success := by decide +kernel
theorem unsat9086 : Unsatisfiable (PosFin 65) f9086 := by
  apply lratCheckerSound f9086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9086
  · intro a ha; simp [p9086] at ha; subst a; trivial
  · exact checked9086
theorem derived9086 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9086 := by
  apply localUnsat_implies_entails f9086 [c9018, c8905, c9084, c9085, c5822, c5477, c147] c9086 unsat9086 (by rfl) a
  have h0 : Entails.eval a c9018 := derived9018 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c9084 := derived9084 a h
  have h3 : Entails.eval a c9085 := derived9085 a h
  have h4 : Entails.eval a c5822 := h 5821 (by decide)
  have h5 : Entails.eval a c5477 := h 5476 (by decide)
  have h6 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9087 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9087 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9086, some c9077, some c8905, some c8847, some c8686, some c8421, some c8930, some c8689, some c9033, some c808, some c6246, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9087 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9087 : lratChecker f9087 p9087 = .success := by decide +kernel
theorem unsat9087 : Unsatisfiable (PosFin 65) f9087 := by
  apply lratCheckerSound f9087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9087
  · intro a ha; simp [p9087] at ha; subst a; trivial
  · exact checked9087
theorem derived9087 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9087 := by
  apply localUnsat_implies_entails f9087 [c9086, c9077, c8905, c8847, c8686, c8421, c8930, c8689, c9033, c808, c6246] c9087 unsat9087 (by rfl) a
  have h0 : Entails.eval a c9086 := derived9086 a h
  have h1 : Entails.eval a c9077 := derived9077 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8930 := derived8930 a h
  have h7 : Entails.eval a c8689 := derived8689 a h
  have h8 : Entails.eval a c9033 := derived9033 a h
  have h9 : Entails.eval a c808 := h 807 (by decide)
  have h10 : Entails.eval a c6246 := h 6245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9088 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨8, by decide⟩, false), (⟨29, by decide⟩, false), (⟨54, by decide⟩, true), (⟨31, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9088 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c808, some c6246, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9088 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9088 : lratChecker f9088 p9088 = .success := by decide +kernel
theorem unsat9088 : Unsatisfiable (PosFin 65) f9088 := by
  apply lratCheckerSound f9088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9088
  · intro a ha; simp [p9088] at ha; subst a; trivial
  · exact checked9088
theorem derived9088 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9088 := by
  apply localUnsat_implies_entails f9088 [c808, c6246] c9088 unsat9088 (by rfl) a
  have h0 : Entails.eval a c808 := h 807 (by decide)
  have h1 : Entails.eval a c6246 := h 6245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9089 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9089 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5665, some c6195, some c230, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9089 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9089 : lratChecker f9089 p9089 = .success := by decide +kernel
theorem unsat9089 : Unsatisfiable (PosFin 65) f9089 := by
  apply lratCheckerSound f9089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9089
  · intro a ha; simp [p9089] at ha; subst a; trivial
  · exact checked9089
theorem derived9089 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9089 := by
  apply localUnsat_implies_entails f9089 [c5665, c6195, c230] c9089 unsat9089 (by rfl) a
  have h0 : Entails.eval a c5665 := h 5664 (by decide)
  have h1 : Entails.eval a c6195 := h 6194 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9090 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9090 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8941, some c9089, some c8893, some c5889, some c6197, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9090 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9090 : lratChecker f9090 p9090 = .success := by decide +kernel
theorem unsat9090 : Unsatisfiable (PosFin 65) f9090 := by
  apply lratCheckerSound f9090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9090
  · intro a ha; simp [p9090] at ha; subst a; trivial
  · exact checked9090
theorem derived9090 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9090 := by
  apply localUnsat_implies_entails f9090 [c8941, c9089, c8893, c5889, c6197] c9090 unsat9090 (by rfl) a
  have h0 : Entails.eval a c8941 := derived8941 a h
  have h1 : Entails.eval a c9089 := derived9089 a h
  have h2 : Entails.eval a c8893 := derived8893 a h
  have h3 : Entails.eval a c5889 := h 5888 (by decide)
  have h4 : Entails.eval a c6197 := h 6196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9091 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨8, by decide⟩, false), (⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨54, by decide⟩, true), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9091 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9088, some c6272, some c9089, some c6169, some c9080, some c802, some c803, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9091 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9091 : lratChecker f9091 p9091 = .success := by decide +kernel
theorem unsat9091 : Unsatisfiable (PosFin 65) f9091 := by
  apply lratCheckerSound f9091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9091
  · intro a ha; simp [p9091] at ha; subst a; trivial
  · exact checked9091
theorem derived9091 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9091 := by
  apply localUnsat_implies_entails f9091 [c9088, c6272, c9089, c6169, c9080, c802, c803] c9091 unsat9091 (by rfl) a
  have h0 : Entails.eval a c9088 := derived9088 a h
  have h1 : Entails.eval a c6272 := h 6271 (by decide)
  have h2 : Entails.eval a c9089 := derived9089 a h
  have h3 : Entails.eval a c6169 := h 6168 (by decide)
  have h4 : Entails.eval a c9080 := derived9080 a h
  have h5 : Entails.eval a c802 := h 801 (by decide)
  have h6 : Entails.eval a c803 := h 802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9092 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9092 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9086, some c9077, some c9018, some c8905, some c8847, some c8686, some c8421, some c9087, some c9061, some c9053, some c9088, some c9090, some c9091, some c8893, some c9016, some c6273, some c5857, some c837, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9092 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9092 : lratChecker f9092 p9092 = .success := by decide +kernel
theorem unsat9092 : Unsatisfiable (PosFin 65) f9092 := by
  apply lratCheckerSound f9092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9092
  · intro a ha; simp [p9092] at ha; subst a; trivial
  · exact checked9092
theorem derived9092 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9092 := by
  apply localUnsat_implies_entails f9092 [c9086, c9077, c9018, c8905, c8847, c8686, c8421, c9087, c9061, c9053, c9088, c9090, c9091, c8893, c9016, c6273, c5857, c837] c9092 unsat9092 (by rfl) a
  have h0 : Entails.eval a c9086 := derived9086 a h
  have h1 : Entails.eval a c9077 := derived9077 a h
  have h2 : Entails.eval a c9018 := derived9018 a h
  have h3 : Entails.eval a c8905 := derived8905 a h
  have h4 : Entails.eval a c8847 := derived8847 a h
  have h5 : Entails.eval a c8686 := derived8686 a h
  have h6 : Entails.eval a c8421 := derived8421 a h
  have h7 : Entails.eval a c9087 := derived9087 a h
  have h8 : Entails.eval a c9061 := derived9061 a h
  have h9 : Entails.eval a c9053 := derived9053 a h
  have h10 : Entails.eval a c9088 := derived9088 a h
  have h11 : Entails.eval a c9090 := derived9090 a h
  have h12 : Entails.eval a c9091 := derived9091 a h
  have h13 : Entails.eval a c8893 := derived8893 a h
  have h14 : Entails.eval a c9016 := derived9016 a h
  have h15 : Entails.eval a c6273 := h 6272 (by decide)
  have h16 : Entails.eval a c5857 := h 5856 (by decide)
  have h17 : Entails.eval a c837 := h 836 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9093 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9093 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9086, some c9077, some c8905, some c8847, some c8421, some c9092, some c7994, some c6247, some c6269, some c6163, some c5768, some c8537, some c16, some c253, some c1247, some c1177, some c4699, some c8550, some c4935, some c71, some c502, some c428, some c95, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9093 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9093 : lratChecker f9093 p9093 = .success := by decide +kernel
theorem unsat9093 : Unsatisfiable (PosFin 65) f9093 := by
  apply lratCheckerSound f9093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9093
  · intro a ha; simp [p9093] at ha; subst a; trivial
  · exact checked9093
theorem derived9093 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9093 := by
  apply localUnsat_implies_entails f9093 [c9086, c9077, c8905, c8847, c8421, c9092, c7994, c6247, c6269, c6163, c5768, c8537, c16, c253, c1247, c1177, c4699, c8550, c4935, c71, c502, c428, c95] c9093 unsat9093 (by rfl) a
  have h0 : Entails.eval a c9086 := derived9086 a h
  have h1 : Entails.eval a c9077 := derived9077 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c9092 := derived9092 a h
  have h6 : Entails.eval a c7994 := derived7994 a h
  have h7 : Entails.eval a c6247 := h 6246 (by decide)
  have h8 : Entails.eval a c6269 := h 6268 (by decide)
  have h9 : Entails.eval a c6163 := h 6162 (by decide)
  have h10 : Entails.eval a c5768 := h 5767 (by decide)
  have h11 : Entails.eval a c8537 := derived8537 a h
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c253 := h 252 (by decide)
  have h14 : Entails.eval a c1247 := h 1246 (by decide)
  have h15 : Entails.eval a c1177 := h 1176 (by decide)
  have h16 : Entails.eval a c4699 := h 4698 (by decide)
  have h17 : Entails.eval a c8550 := derived8550 a h
  have h18 : Entails.eval a c4935 := h 4934 (by decide)
  have h19 : Entails.eval a c71 := h 70 (by decide)
  have h20 : Entails.eval a c502 := h 501 (by decide)
  have h21 : Entails.eval a c428 := h 427 (by decide)
  have h22 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9094 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨63, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9094 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c787, some c5816, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9094 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9094 : lratChecker f9094 p9094 = .success := by decide +kernel
theorem unsat9094 : Unsatisfiable (PosFin 65) f9094 := by
  apply lratCheckerSound f9094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9094
  · intro a ha; simp [p9094] at ha; subst a; trivial
  · exact checked9094
theorem derived9094 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9094 := by
  apply localUnsat_implies_entails f9094 [c787, c5816] c9094 unsat9094 (by rfl) a
  have h0 : Entails.eval a c787 := h 786 (by decide)
  have h1 : Entails.eval a c5816 := h 5815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9095 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9095 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c160, some c155, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9095 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9095 : lratChecker f9095 p9095 = .success := by decide +kernel
theorem unsat9095 : Unsatisfiable (PosFin 65) f9095 := by
  apply lratCheckerSound f9095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9095
  · intro a ha; simp [p9095] at ha; subst a; trivial
  · exact checked9095
theorem derived9095 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9095 := by
  apply localUnsat_implies_entails f9095 [c160, c155] c9095 unsat9095 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9096 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9096 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8905, some c8847, some c9018, some c9093, some c9027, some c9061, some c9086, some c8421, some c9073, some c9053, some c9094, some c9095, some c5482, some c5485, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9096 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9096 : lratChecker f9096 p9096 = .success := by decide +kernel
theorem unsat9096 : Unsatisfiable (PosFin 65) f9096 := by
  apply lratCheckerSound f9096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9096
  · intro a ha; simp [p9096] at ha; subst a; trivial
  · exact checked9096
theorem derived9096 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9096 := by
  apply localUnsat_implies_entails f9096 [c8686, c8905, c8847, c9018, c9093, c9027, c9061, c9086, c8421, c9073, c9053, c9094, c9095, c5482, c5485] c9096 unsat9096 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c9018 := derived9018 a h
  have h4 : Entails.eval a c9093 := derived9093 a h
  have h5 : Entails.eval a c9027 := derived9027 a h
  have h6 : Entails.eval a c9061 := derived9061 a h
  have h7 : Entails.eval a c9086 := derived9086 a h
  have h8 : Entails.eval a c8421 := derived8421 a h
  have h9 : Entails.eval a c9073 := derived9073 a h
  have h10 : Entails.eval a c9053 := derived9053 a h
  have h11 : Entails.eval a c9094 := derived9094 a h
  have h12 : Entails.eval a c9095 := derived9095 a h
  have h13 : Entails.eval a c5482 := h 5481 (by decide)
  have h14 : Entails.eval a c5485 := h 5484 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9097 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨29, by decide⟩, true), (⟨54, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9097 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c787, some c5813, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9097 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9097 : lratChecker f9097 p9097 = .success := by decide +kernel
theorem unsat9097 : Unsatisfiable (PosFin 65) f9097 := by
  apply lratCheckerSound f9097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9097
  · intro a ha; simp [p9097] at ha; subst a; trivial
  · exact checked9097
theorem derived9097 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9097 := by
  apply localUnsat_implies_entails f9097 [c787, c5813] c9097 unsat9097 (by rfl) a
  have h0 : Entails.eval a c787 := h 786 (by decide)
  have h1 : Entails.eval a c5813 := h 5812 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9098 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9098 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8686, some c8847, some c8905, some c9018, some c9077, some c9086, some c9093, some c9027, some c9061, some c9096, some c7994, some c8604, some c2735, some c4722, some c9097, some c5798, some c268, some c5806, some c6163, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9098 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9098 : lratChecker f9098 p9098 = .success := by decide +kernel
theorem unsat9098 : Unsatisfiable (PosFin 65) f9098 := by
  apply lratCheckerSound f9098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9098
  · intro a ha; simp [p9098] at ha; subst a; trivial
  · exact checked9098
theorem derived9098 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9098 := by
  apply localUnsat_implies_entails f9098 [c8421, c8686, c8847, c8905, c9018, c9077, c9086, c9093, c9027, c9061, c9096, c7994, c8604, c2735, c4722, c9097, c5798, c268, c5806, c6163] c9098 unsat9098 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8905 := derived8905 a h
  have h4 : Entails.eval a c9018 := derived9018 a h
  have h5 : Entails.eval a c9077 := derived9077 a h
  have h6 : Entails.eval a c9086 := derived9086 a h
  have h7 : Entails.eval a c9093 := derived9093 a h
  have h8 : Entails.eval a c9027 := derived9027 a h
  have h9 : Entails.eval a c9061 := derived9061 a h
  have h10 : Entails.eval a c9096 := derived9096 a h
  have h11 : Entails.eval a c7994 := derived7994 a h
  have h12 : Entails.eval a c8604 := derived8604 a h
  have h13 : Entails.eval a c2735 := h 2734 (by decide)
  have h14 : Entails.eval a c4722 := h 4721 (by decide)
  have h15 : Entails.eval a c9097 := derived9097 a h
  have h16 : Entails.eval a c5798 := h 5797 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c5806 := h 5805 (by decide)
  have h19 : Entails.eval a c6163 := h 6162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9099 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9099 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8486, some c1212, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9099 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9099 : lratChecker f9099 p9099 = .success := by decide +kernel
theorem unsat9099 : Unsatisfiable (PosFin 65) f9099 := by
  apply lratCheckerSound f9099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9099
  · intro a ha; simp [p9099] at ha; subst a; trivial
  · exact checked9099
theorem derived9099 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9099 := by
  apply localUnsat_implies_entails f9099 [c8486, c1212] c9099 unsat9099 (by rfl) a
  have h0 : Entails.eval a c8486 := derived8486 a h
  have h1 : Entails.eval a c1212 := h 1211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9100 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨51, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9100 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c629, some c624, some c628, some c643, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p9100 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9100 : lratChecker f9100 p9100 = .success := by decide +kernel
theorem unsat9100 : Unsatisfiable (PosFin 65) f9100 := by
  apply lratCheckerSound f9100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9100
  · intro a ha; simp [p9100] at ha; subst a; trivial
  · exact checked9100
theorem derived9100 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9100 := by
  apply localUnsat_implies_entails f9100 [c629, c624, c628, c643] c9100 unsat9100 (by rfl) a
  have h0 : Entails.eval a c629 := h 628 (by decide)
  have h1 : Entails.eval a c624 := h 623 (by decide)
  have h2 : Entails.eval a c628 := h 627 (by decide)
  have h3 : Entails.eval a c643 := h 642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9101 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨31, by decide⟩, true), (⟨49, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9101 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8826, some c9100, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9101 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9101 : lratChecker f9101 p9101 = .success := by decide +kernel
theorem unsat9101 : Unsatisfiable (PosFin 65) f9101 := by
  apply lratCheckerSound f9101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9101
  · intro a ha; simp [p9101] at ha; subst a; trivial
  · exact checked9101
theorem derived9101 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9101 := by
  apply localUnsat_implies_entails f9101 [c8826, c9100] c9101 unsat9101 (by rfl) a
  have h0 : Entails.eval a c8826 := derived8826 a h
  have h1 : Entails.eval a c9100 := derived9100 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9102 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨63, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9102 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3530, some c4448, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p9102 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9102 : lratChecker f9102 p9102 = .success := by decide +kernel
theorem unsat9102 : Unsatisfiable (PosFin 65) f9102 := by
  apply lratCheckerSound f9102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9102
  · intro a ha; simp [p9102] at ha; subst a; trivial
  · exact checked9102
theorem derived9102 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9102 := by
  apply localUnsat_implies_entails f9102 [c3530, c4448] c9102 unsat9102 (by rfl) a
  have h0 : Entails.eval a c3530 := h 3529 (by decide)
  have h1 : Entails.eval a c4448 := h 4447 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9103 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9103 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4727, some c4717, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p9103 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9103 : lratChecker f9103 p9103 = .success := by decide +kernel
theorem unsat9103 : Unsatisfiable (PosFin 65) f9103 := by
  apply lratCheckerSound f9103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9103
  · intro a ha; simp [p9103] at ha; subst a; trivial
  · exact checked9103
theorem derived9103 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9103 := by
  apply localUnsat_implies_entails f9103 [c4727, c4717] c9103 unsat9103 (by rfl) a
  have h0 : Entails.eval a c4727 := h 4726 (by decide)
  have h1 : Entails.eval a c4717 := h 4716 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9104 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9104 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4279, some c4283, some c4280, some c4285, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p9104 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9104 : lratChecker f9104 p9104 = .success := by decide +kernel
theorem unsat9104 : Unsatisfiable (PosFin 65) f9104 := by
  apply lratCheckerSound f9104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9104
  · intro a ha; simp [p9104] at ha; subst a; trivial
  · exact checked9104
theorem derived9104 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9104 := by
  apply localUnsat_implies_entails f9104 [c4279, c4283, c4280, c4285] c9104 unsat9104 (by rfl) a
  have h0 : Entails.eval a c4279 := h 4278 (by decide)
  have h1 : Entails.eval a c4283 := h 4282 (by decide)
  have h2 : Entails.eval a c4280 := h 4279 (by decide)
  have h3 : Entails.eval a c4285 := h 4284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9105 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9105 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2642, some c3146, some c3835, some c3842, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9105 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9105 : lratChecker f9105 p9105 = .success := by decide +kernel
theorem unsat9105 : Unsatisfiable (PosFin 65) f9105 := by
  apply lratCheckerSound f9105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9105
  · intro a ha; simp [p9105] at ha; subst a; trivial
  · exact checked9105
theorem derived9105 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9105 := by
  apply localUnsat_implies_entails f9105 [c2642, c3146, c3835, c3842] c9105 unsat9105 (by rfl) a
  have h0 : Entails.eval a c2642 := h 2641 (by decide)
  have h1 : Entails.eval a c3146 := h 3145 (by decide)
  have h2 : Entails.eval a c3835 := h 3834 (by decide)
  have h3 : Entails.eval a c3842 := h 3841 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9106 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9106 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9099, some c8269, some c9098, some c9102, some c9103, some c9105, some c3736, some c1104, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9106 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9106 : lratChecker f9106 p9106 = .success := by decide +kernel
theorem unsat9106 : Unsatisfiable (PosFin 65) f9106 := by
  apply lratCheckerSound f9106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9106
  · intro a ha; simp [p9106] at ha; subst a; trivial
  · exact checked9106
theorem derived9106 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9106 := by
  apply localUnsat_implies_entails f9106 [c9099, c8269, c9098, c9102, c9103, c9105, c3736, c1104] c9106 unsat9106 (by rfl) a
  have h0 : Entails.eval a c9099 := derived9099 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c9098 := derived9098 a h
  have h3 : Entails.eval a c9102 := derived9102 a h
  have h4 : Entails.eval a c9103 := derived9103 a h
  have h5 : Entails.eval a c9105 := derived9105 a h
  have h6 : Entails.eval a c3736 := h 3735 (by decide)
  have h7 : Entails.eval a c1104 := h 1103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9107 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9107 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1291, some c1269, some c1164, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9107 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9107 : lratChecker f9107 p9107 = .success := by decide +kernel
theorem unsat9107 : Unsatisfiable (PosFin 65) f9107 := by
  apply lratCheckerSound f9107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9107
  · intro a ha; simp [p9107] at ha; subst a; trivial
  · exact checked9107
theorem derived9107 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9107 := by
  apply localUnsat_implies_entails f9107 [c1291, c1269, c1164] c9107 unsat9107 (by rfl) a
  have h0 : Entails.eval a c1291 := h 1290 (by decide)
  have h1 : Entails.eval a c1269 := h 1268 (by decide)
  have h2 : Entails.eval a c1164 := h 1163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9108 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9108 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9098, some c9099, some c9107, some c9102, some c9103, some c9106, some c9105, some c9101, some c6130, some c6253, some c6093, some c6202, some c6109, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9108 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9108 : lratChecker f9108 p9108 = .success := by decide +kernel
theorem unsat9108 : Unsatisfiable (PosFin 65) f9108 := by
  apply lratCheckerSound f9108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9108
  · intro a ha; simp [p9108] at ha; subst a; trivial
  · exact checked9108
theorem derived9108 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9108 := by
  apply localUnsat_implies_entails f9108 [c8269, c9098, c9099, c9107, c9102, c9103, c9106, c9105, c9101, c6130, c6253, c6093, c6202, c6109] c9108 unsat9108 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9099 := derived9099 a h
  have h3 : Entails.eval a c9107 := derived9107 a h
  have h4 : Entails.eval a c9102 := derived9102 a h
  have h5 : Entails.eval a c9103 := derived9103 a h
  have h6 : Entails.eval a c9106 := derived9106 a h
  have h7 : Entails.eval a c9105 := derived9105 a h
  have h8 : Entails.eval a c9101 := derived9101 a h
  have h9 : Entails.eval a c6130 := h 6129 (by decide)
  have h10 : Entails.eval a c6253 := h 6252 (by decide)
  have h11 : Entails.eval a c6093 := h 6092 (by decide)
  have h12 : Entails.eval a c6202 := h 6201 (by decide)
  have h13 : Entails.eval a c6109 := h 6108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9109 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9109 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9098, some c1228, some c1229, some c1148, some c3483, some c3725, some c4133, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9109 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9109 : lratChecker f9109 p9109 = .success := by decide +kernel
theorem unsat9109 : Unsatisfiable (PosFin 65) f9109 := by
  apply lratCheckerSound f9109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9109
  · intro a ha; simp [p9109] at ha; subst a; trivial
  · exact checked9109
theorem derived9109 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9109 := by
  apply localUnsat_implies_entails f9109 [c8269, c9098, c1228, c1229, c1148, c3483, c3725, c4133] c9109 unsat9109 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c1228 := h 1227 (by decide)
  have h3 : Entails.eval a c1229 := h 1228 (by decide)
  have h4 : Entails.eval a c1148 := h 1147 (by decide)
  have h5 : Entails.eval a c3483 := h 3482 (by decide)
  have h6 : Entails.eval a c3725 := h 3724 (by decide)
  have h7 : Entails.eval a c4133 := h 4132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9110 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9110 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4455, some c4448, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p9110 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9110 : lratChecker f9110 p9110 = .success := by decide +kernel
theorem unsat9110 : Unsatisfiable (PosFin 65) f9110 := by
  apply lratCheckerSound f9110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9110
  · intro a ha; simp [p9110] at ha; subst a; trivial
  · exact checked9110
theorem derived9110 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9110 := by
  apply localUnsat_implies_entails f9110 [c4455, c4448] c9110 unsat9110 (by rfl) a
  have h0 : Entails.eval a c4455 := h 4454 (by decide)
  have h1 : Entails.eval a c4448 := h 4447 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9111 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9111 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2642, some c2613, some c3770, some c3744, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9111 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9111 : lratChecker f9111 p9111 = .success := by decide +kernel
theorem unsat9111 : Unsatisfiable (PosFin 65) f9111 := by
  apply lratCheckerSound f9111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9111
  · intro a ha; simp [p9111] at ha; subst a; trivial
  · exact checked9111
theorem derived9111 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9111 := by
  apply localUnsat_implies_entails f9111 [c2642, c2613, c3770, c3744] c9111 unsat9111 (by rfl) a
  have h0 : Entails.eval a c2642 := h 2641 (by decide)
  have h1 : Entails.eval a c2613 := h 2612 (by decide)
  have h2 : Entails.eval a c3770 := h 3769 (by decide)
  have h3 : Entails.eval a c3744 := h 3743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9112 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9112 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9110, some c9111, some c3736, some c1094, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9112 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9112 : lratChecker f9112 p9112 = .success := by decide +kernel
theorem unsat9112 : Unsatisfiable (PosFin 65) f9112 := by
  apply lratCheckerSound f9112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9112
  · intro a ha; simp [p9112] at ha; subst a; trivial
  · exact checked9112
theorem derived9112 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9112 := by
  apply localUnsat_implies_entails f9112 [c8269, c9110, c9111, c3736, c1094] c9112 unsat9112 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9110 := derived9110 a h
  have h2 : Entails.eval a c9111 := derived9111 a h
  have h3 : Entails.eval a c3736 := h 3735 (by decide)
  have h4 : Entails.eval a c1094 := h 1093 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9113 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9113 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9098, some c9109, some c9112, some c1286, some c1150, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9113 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9113 : lratChecker f9113 p9113 = .success := by decide +kernel
theorem unsat9113 : Unsatisfiable (PosFin 65) f9113 := by
  apply lratCheckerSound f9113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9113
  · intro a ha; simp [p9113] at ha; subst a; trivial
  · exact checked9113
theorem derived9113 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9113 := by
  apply localUnsat_implies_entails f9113 [c8269, c9098, c9109, c9112, c1286, c1150] c9113 unsat9113 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9109 := derived9109 a h
  have h3 : Entails.eval a c9112 := derived9112 a h
  have h4 : Entails.eval a c1286 := h 1285 (by decide)
  have h5 : Entails.eval a c1150 := h 1149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9114 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨51, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9114 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c647, some c639, some c645, some c638, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p9114 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9114 : lratChecker f9114 p9114 = .success := by decide +kernel
theorem unsat9114 : Unsatisfiable (PosFin 65) f9114 := by
  apply lratCheckerSound f9114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9114
  · intro a ha; simp [p9114] at ha; subst a; trivial
  · exact checked9114
theorem derived9114 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9114 := by
  apply localUnsat_implies_entails f9114 [c647, c639, c645, c638] c9114 unsat9114 (by rfl) a
  have h0 : Entails.eval a c647 := h 646 (by decide)
  have h1 : Entails.eval a c639 := h 638 (by decide)
  have h2 : Entails.eval a c645 := h 644 (by decide)
  have h3 : Entails.eval a c638 := h 637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9115 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9115 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9101, some c9114, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p9115 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9115 : lratChecker f9115 p9115 = .success := by decide +kernel
theorem unsat9115 : Unsatisfiable (PosFin 65) f9115 := by
  apply lratCheckerSound f9115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9115
  · intro a ha; simp [p9115] at ha; subst a; trivial
  · exact checked9115
theorem derived9115 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9115 := by
  apply localUnsat_implies_entails f9115 [c9101, c9114] c9115 unsat9115 (by rfl) a
  have h0 : Entails.eval a c9101 := derived9101 a h
  have h1 : Entails.eval a c9114 := derived9114 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9116 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9116 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9115, some c8269, some c9098, some c9107, some c9108, some c1097, some c3740, some c3744, some c3725, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9116 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9116 : lratChecker f9116 p9116 = .success := by decide +kernel
theorem unsat9116 : Unsatisfiable (PosFin 65) f9116 := by
  apply lratCheckerSound f9116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9116
  · intro a ha; simp [p9116] at ha; subst a; trivial
  · exact checked9116
theorem derived9116 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9116 := by
  apply localUnsat_implies_entails f9116 [c9115, c8269, c9098, c9107, c9108, c1097, c3740, c3744, c3725] c9116 unsat9116 (by rfl) a
  have h0 : Entails.eval a c9115 := derived9115 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c9098 := derived9098 a h
  have h3 : Entails.eval a c9107 := derived9107 a h
  have h4 : Entails.eval a c9108 := derived9108 a h
  have h5 : Entails.eval a c1097 := h 1096 (by decide)
  have h6 : Entails.eval a c3740 := h 3739 (by decide)
  have h7 : Entails.eval a c3744 := h 3743 (by decide)
  have h8 : Entails.eval a c3725 := h 3724 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9117 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9117 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9115, some c9116, some c9113, some c9109, some c9049, some c4724, some c4454, some c4336, some c4295, some c4186, some c3870, some c3724, some c3744, some c3725, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9117 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9117 : lratChecker f9117 p9117 = .success := by decide +kernel
theorem unsat9117 : Unsatisfiable (PosFin 65) f9117 := by
  apply lratCheckerSound f9117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9117
  · intro a ha; simp [p9117] at ha; subst a; trivial
  · exact checked9117
theorem derived9117 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9117 := by
  apply localUnsat_implies_entails f9117 [c9098, c9115, c9116, c9113, c9109, c9049, c4724, c4454, c4336, c4295, c4186, c3870, c3724, c3744, c3725] c9117 unsat9117 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9115 := derived9115 a h
  have h2 : Entails.eval a c9116 := derived9116 a h
  have h3 : Entails.eval a c9113 := derived9113 a h
  have h4 : Entails.eval a c9109 := derived9109 a h
  have h5 : Entails.eval a c9049 := derived9049 a h
  have h6 : Entails.eval a c4724 := h 4723 (by decide)
  have h7 : Entails.eval a c4454 := h 4453 (by decide)
  have h8 : Entails.eval a c4336 := h 4335 (by decide)
  have h9 : Entails.eval a c4295 := h 4294 (by decide)
  have h10 : Entails.eval a c4186 := h 4185 (by decide)
  have h11 : Entails.eval a c3870 := h 3869 (by decide)
  have h12 : Entails.eval a c3724 := h 3723 (by decide)
  have h13 : Entails.eval a c3744 := h 3743 (by decide)
  have h14 : Entails.eval a c3725 := h 3724 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9118 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9118 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9098, some c9107, some c3519, some c3720, some c2615, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9118 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9118 : lratChecker f9118 p9118 = .success := by decide +kernel
theorem unsat9118 : Unsatisfiable (PosFin 65) f9118 := by
  apply lratCheckerSound f9118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9118
  · intro a ha; simp [p9118] at ha; subst a; trivial
  · exact checked9118
theorem derived9118 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9118 := by
  apply localUnsat_implies_entails f9118 [c8269, c9098, c9107, c3519, c3720, c2615] c9118 unsat9118 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9107 := derived9107 a h
  have h3 : Entails.eval a c3519 := h 3518 (by decide)
  have h4 : Entails.eval a c3720 := h 3719 (by decide)
  have h5 : Entails.eval a c2615 := h 2614 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9119 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨12, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9119 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1102, some c3738, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9119 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9119 : lratChecker f9119 p9119 = .success := by decide +kernel
theorem unsat9119 : Unsatisfiable (PosFin 65) f9119 := by
  apply lratCheckerSound f9119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9119
  · intro a ha; simp [p9119] at ha; subst a; trivial
  · exact checked9119
theorem derived9119 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9119 := by
  apply localUnsat_implies_entails f9119 [c1102, c3738] c9119 unsat9119 (by rfl) a
  have h0 : Entails.eval a c1102 := h 1101 (by decide)
  have h1 : Entails.eval a c3738 := h 3737 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9120 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9120 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9048, some c9119, some c3725, some c2624, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9120 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9120 : lratChecker f9120 p9120 = .success := by decide +kernel
theorem unsat9120 : Unsatisfiable (PosFin 65) f9120 := by
  apply lratCheckerSound f9120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9120
  · intro a ha; simp [p9120] at ha; subst a; trivial
  · exact checked9120
theorem derived9120 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9120 := by
  apply localUnsat_implies_entails f9120 [c8269, c9048, c9119, c3725, c2624] c9120 unsat9120 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9048 := derived9048 a h
  have h2 : Entails.eval a c9119 := derived9119 a h
  have h3 : Entails.eval a c3725 := h 3724 (by decide)
  have h4 : Entails.eval a c2624 := h 2623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9121 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9121 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9118, some c8269, some c9098, some c9109, some c9120, some c1286, some c1150, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9121 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9121 : lratChecker f9121 p9121 = .success := by decide +kernel
theorem unsat9121 : Unsatisfiable (PosFin 65) f9121 := by
  apply lratCheckerSound f9121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9121
  · intro a ha; simp [p9121] at ha; subst a; trivial
  · exact checked9121
theorem derived9121 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9121 := by
  apply localUnsat_implies_entails f9121 [c9118, c8269, c9098, c9109, c9120, c1286, c1150] c9121 unsat9121 (by rfl) a
  have h0 : Entails.eval a c9118 := derived9118 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c9098 := derived9098 a h
  have h3 : Entails.eval a c9109 := derived9109 a h
  have h4 : Entails.eval a c9120 := derived9120 a h
  have h5 : Entails.eval a c1286 := h 1285 (by decide)
  have h6 : Entails.eval a c1150 := h 1149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9122 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9122 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9119, some c3723, some c3475, some c3521, some c2622, some c3875, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9122 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9122 : lratChecker f9122 p9122 = .success := by decide +kernel
theorem unsat9122 : Unsatisfiable (PosFin 65) f9122 := by
  apply lratCheckerSound f9122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9122
  · intro a ha; simp [p9122] at ha; subst a; trivial
  · exact checked9122
theorem derived9122 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9122 := by
  apply localUnsat_implies_entails f9122 [c8269, c9119, c3723, c3475, c3521, c2622, c3875] c9122 unsat9122 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9119 := derived9119 a h
  have h2 : Entails.eval a c3723 := h 3722 (by decide)
  have h3 : Entails.eval a c3475 := h 3474 (by decide)
  have h4 : Entails.eval a c3521 := h 3520 (by decide)
  have h5 : Entails.eval a c2622 := h 2621 (by decide)
  have h6 : Entails.eval a c3875 := h 3874 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9123 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9123 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9117, some c9118, some c9121, some c9122, some c1285, some c1286, some c1300, some c1145, some c1278, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9123 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9123 : lratChecker f9123 p9123 = .success := by decide +kernel
theorem unsat9123 : Unsatisfiable (PosFin 65) f9123 := by
  apply lratCheckerSound f9123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9123
  · intro a ha; simp [p9123] at ha; subst a; trivial
  · exact checked9123
theorem derived9123 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9123 := by
  apply localUnsat_implies_entails f9123 [c9098, c9117, c9118, c9121, c9122, c1285, c1286, c1300, c1145, c1278] c9123 unsat9123 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9117 := derived9117 a h
  have h2 : Entails.eval a c9118 := derived9118 a h
  have h3 : Entails.eval a c9121 := derived9121 a h
  have h4 : Entails.eval a c9122 := derived9122 a h
  have h5 : Entails.eval a c1285 := h 1284 (by decide)
  have h6 : Entails.eval a c1286 := h 1285 (by decide)
  have h7 : Entails.eval a c1300 := h 1299 (by decide)
  have h8 : Entails.eval a c1145 := h 1144 (by decide)
  have h9 : Entails.eval a c1278 := h 1277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9124 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9124 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1144, some c1092, some c3734, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9124 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9124 : lratChecker f9124 p9124 = .success := by decide +kernel
theorem unsat9124 : Unsatisfiable (PosFin 65) f9124 := by
  apply lratCheckerSound f9124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9124
  · intro a ha; simp [p9124] at ha; subst a; trivial
  · exact checked9124
theorem derived9124 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9124 := by
  apply localUnsat_implies_entails f9124 [c1144, c1092, c3734] c9124 unsat9124 (by rfl) a
  have h0 : Entails.eval a c1144 := h 1143 (by decide)
  have h1 : Entails.eval a c1092 := h 1091 (by decide)
  have h2 : Entails.eval a c3734 := h 3733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9125 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨63, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9125 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9124, some c3721, some c3519, some c3474, some c1109, some c3876, some c3869, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9125 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9125 : lratChecker f9125 p9125 = .success := by decide +kernel
theorem unsat9125 : Unsatisfiable (PosFin 65) f9125 := by
  apply lratCheckerSound f9125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9125
  · intro a ha; simp [p9125] at ha; subst a; trivial
  · exact checked9125
theorem derived9125 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9125 := by
  apply localUnsat_implies_entails f9125 [c9124, c3721, c3519, c3474, c1109, c3876, c3869] c9125 unsat9125 (by rfl) a
  have h0 : Entails.eval a c9124 := derived9124 a h
  have h1 : Entails.eval a c3721 := h 3720 (by decide)
  have h2 : Entails.eval a c3519 := h 3518 (by decide)
  have h3 : Entails.eval a c3474 := h 3473 (by decide)
  have h4 : Entails.eval a c1109 := h 1108 (by decide)
  have h5 : Entails.eval a c3876 := h 3875 (by decide)
  have h6 : Entails.eval a c3869 := h 3868 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9126 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9126 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9098, some c9125, some c1151, some c1291, some c1269, some c1152, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9126 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9126 : lratChecker f9126 p9126 = .success := by decide +kernel
theorem unsat9126 : Unsatisfiable (PosFin 65) f9126 := by
  apply lratCheckerSound f9126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9126
  · intro a ha; simp [p9126] at ha; subst a; trivial
  · exact checked9126
theorem derived9126 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9126 := by
  apply localUnsat_implies_entails f9126 [c8269, c9098, c9125, c1151, c1291, c1269, c1152] c9126 unsat9126 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9125 := derived9125 a h
  have h3 : Entails.eval a c1151 := h 1150 (by decide)
  have h4 : Entails.eval a c1291 := h 1290 (by decide)
  have h5 : Entails.eval a c1269 := h 1268 (by decide)
  have h6 : Entails.eval a c1152 := h 1151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9127 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9127 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9124, some c3721, some c3474, some c1091, some c1090, some c3869, some c3524, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9127 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9127 : lratChecker f9127 p9127 = .success := by decide +kernel
theorem unsat9127 : Unsatisfiable (PosFin 65) f9127 := by
  apply lratCheckerSound f9127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9127
  · intro a ha; simp [p9127] at ha; subst a; trivial
  · exact checked9127
theorem derived9127 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9127 := by
  apply localUnsat_implies_entails f9127 [c8269, c9124, c3721, c3474, c1091, c1090, c3869, c3524] c9127 unsat9127 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9124 := derived9124 a h
  have h2 : Entails.eval a c3721 := h 3720 (by decide)
  have h3 : Entails.eval a c3474 := h 3473 (by decide)
  have h4 : Entails.eval a c1091 := h 1090 (by decide)
  have h5 : Entails.eval a c1090 := h 1089 (by decide)
  have h6 : Entails.eval a c3869 := h 3868 (by decide)
  have h7 : Entails.eval a c3524 := h 3523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9128 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9128 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9098, some c9123, some c9124, some c9115, some c9126, some c9127, some c2899, some c3420, some c3834, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9128 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9128 : lratChecker f9128 p9128 = .success := by decide +kernel
theorem unsat9128 : Unsatisfiable (PosFin 65) f9128 := by
  apply lratCheckerSound f9128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9128
  · intro a ha; simp [p9128] at ha; subst a; trivial
  · exact checked9128
theorem derived9128 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9128 := by
  apply localUnsat_implies_entails f9128 [c8269, c9098, c9123, c9124, c9115, c9126, c9127, c2899, c3420, c3834] c9128 unsat9128 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9123 := derived9123 a h
  have h3 : Entails.eval a c9124 := derived9124 a h
  have h4 : Entails.eval a c9115 := derived9115 a h
  have h5 : Entails.eval a c9126 := derived9126 a h
  have h6 : Entails.eval a c9127 := derived9127 a h
  have h7 : Entails.eval a c2899 := h 2898 (by decide)
  have h8 : Entails.eval a c3420 := h 3419 (by decide)
  have h9 : Entails.eval a c3834 := h 3833 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9129 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9129 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1210, some c8486, some c1212, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p9129 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9129 : lratChecker f9129 p9129 = .success := by decide +kernel
theorem unsat9129 : Unsatisfiable (PosFin 65) f9129 := by
  apply lratCheckerSound f9129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9129
  · intro a ha; simp [p9129] at ha; subst a; trivial
  · exact checked9129
theorem derived9129 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9129 := by
  apply localUnsat_implies_entails f9129 [c1210, c8486, c1212] c9129 unsat9129 (by rfl) a
  have h0 : Entails.eval a c1210 := h 1209 (by decide)
  have h1 : Entails.eval a c8486 := derived8486 a h
  have h2 : Entails.eval a c1212 := h 1211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9130 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9130 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9129, some c9098, some c8269, some c9124, some c9112, some c4724, some c3195, some c3152, some c3841, some c3837, some c3843, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9130 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9130 : lratChecker f9130 p9130 = .success := by decide +kernel
theorem unsat9130 : Unsatisfiable (PosFin 65) f9130 := by
  apply lratCheckerSound f9130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9130
  · intro a ha; simp [p9130] at ha; subst a; trivial
  · exact checked9130
theorem derived9130 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9130 := by
  apply localUnsat_implies_entails f9130 [c9129, c9098, c8269, c9124, c9112, c4724, c3195, c3152, c3841, c3837, c3843] c9130 unsat9130 (by rfl) a
  have h0 : Entails.eval a c9129 := derived9129 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c9124 := derived9124 a h
  have h4 : Entails.eval a c9112 := derived9112 a h
  have h5 : Entails.eval a c4724 := h 4723 (by decide)
  have h6 : Entails.eval a c3195 := h 3194 (by decide)
  have h7 : Entails.eval a c3152 := h 3151 (by decide)
  have h8 : Entails.eval a c3841 := h 3840 (by decide)
  have h9 : Entails.eval a c3837 := h 3836 (by decide)
  have h10 : Entails.eval a c3843 := h 3842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9131 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9131 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c8269, some c9124, some c9130, some c1269, some c1165, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9131 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9131 : lratChecker f9131 p9131 = .success := by decide +kernel
theorem unsat9131 : Unsatisfiable (PosFin 65) f9131 := by
  apply lratCheckerSound f9131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9131
  · intro a ha; simp [p9131] at ha; subst a; trivial
  · exact checked9131
theorem derived9131 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9131 := by
  apply localUnsat_implies_entails f9131 [c9098, c8269, c9124, c9130, c1269, c1165] c9131 unsat9131 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c9124 := derived9124 a h
  have h3 : Entails.eval a c9130 := derived9130 a h
  have h4 : Entails.eval a c1269 := h 1268 (by decide)
  have h5 : Entails.eval a c1165 := h 1164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9132 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9132 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9124, some c9119, some c4454, some c3725, some c2624, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9132 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9132 : lratChecker f9132 p9132 = .success := by decide +kernel
theorem unsat9132 : Unsatisfiable (PosFin 65) f9132 := by
  apply lratCheckerSound f9132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9132
  · intro a ha; simp [p9132] at ha; subst a; trivial
  · exact checked9132
theorem derived9132 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9132 := by
  apply localUnsat_implies_entails f9132 [c8269, c9124, c9119, c4454, c3725, c2624] c9132 unsat9132 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9124 := derived9124 a h
  have h2 : Entails.eval a c9119 := derived9119 a h
  have h3 : Entails.eval a c4454 := h 4453 (by decide)
  have h4 : Entails.eval a c3725 := h 3724 (by decide)
  have h5 : Entails.eval a c2624 := h 2623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9133 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9133 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9128, some c8269, some c9098, some c9115, some c9124, some c9131, some c9113, some c9109, some c9132, some c1286, some c1150, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9133 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9133 : lratChecker f9133 p9133 = .success := by decide +kernel
theorem unsat9133 : Unsatisfiable (PosFin 65) f9133 := by
  apply lratCheckerSound f9133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9133
  · intro a ha; simp [p9133] at ha; subst a; trivial
  · exact checked9133
theorem derived9133 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9133 := by
  apply localUnsat_implies_entails f9133 [c9128, c8269, c9098, c9115, c9124, c9131, c9113, c9109, c9132, c1286, c1150] c9133 unsat9133 (by rfl) a
  have h0 : Entails.eval a c9128 := derived9128 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c9098 := derived9098 a h
  have h3 : Entails.eval a c9115 := derived9115 a h
  have h4 : Entails.eval a c9124 := derived9124 a h
  have h5 : Entails.eval a c9131 := derived9131 a h
  have h6 : Entails.eval a c9113 := derived9113 a h
  have h7 : Entails.eval a c9109 := derived9109 a h
  have h8 : Entails.eval a c9132 := derived9132 a h
  have h9 : Entails.eval a c1286 := h 1285 (by decide)
  have h10 : Entails.eval a c1150 := h 1149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9134 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9134 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3519, some c3720, some c2615, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9134 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9134 : lratChecker f9134 p9134 = .success := by decide +kernel
theorem unsat9134 : Unsatisfiable (PosFin 65) f9134 := by
  apply lratCheckerSound f9134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9134
  · intro a ha; simp [p9134] at ha; subst a; trivial
  · exact checked9134
theorem derived9134 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9134 := by
  apply localUnsat_implies_entails f9134 [c3519, c3720, c2615] c9134 unsat9134 (by rfl) a
  have h0 : Entails.eval a c3519 := h 3518 (by decide)
  have h1 : Entails.eval a c3720 := h 3719 (by decide)
  have h2 : Entails.eval a c2615 := h 2614 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9135 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9135 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9098, some c9134, some c1267, some c1270, some c1269, some c1152, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9135 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9135 : lratChecker f9135 p9135 = .success := by decide +kernel
theorem unsat9135 : Unsatisfiable (PosFin 65) f9135 := by
  apply lratCheckerSound f9135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9135
  · intro a ha; simp [p9135] at ha; subst a; trivial
  · exact checked9135
theorem derived9135 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9135 := by
  apply localUnsat_implies_entails f9135 [c8269, c9098, c9134, c1267, c1270, c1269, c1152] c9135 unsat9135 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9134 := derived9134 a h
  have h3 : Entails.eval a c1267 := h 1266 (by decide)
  have h4 : Entails.eval a c1270 := h 1269 (by decide)
  have h5 : Entails.eval a c1269 := h 1268 (by decide)
  have h6 : Entails.eval a c1152 := h 1151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9136 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨12, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9136 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9098, some c9124, some c9109, some c9119, some c3725, some c4456, some c2624, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9136 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9136 : lratChecker f9136 p9136 = .success := by decide +kernel
theorem unsat9136 : Unsatisfiable (PosFin 65) f9136 := by
  apply lratCheckerSound f9136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9136
  · intro a ha; simp [p9136] at ha; subst a; trivial
  · exact checked9136
theorem derived9136 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9136 := by
  apply localUnsat_implies_entails f9136 [c8269, c9098, c9124, c9109, c9119, c3725, c4456, c2624] c9136 unsat9136 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9124 := derived9124 a h
  have h3 : Entails.eval a c9109 := derived9109 a h
  have h4 : Entails.eval a c9119 := derived9119 a h
  have h5 : Entails.eval a c3725 := h 3724 (by decide)
  have h6 : Entails.eval a c4456 := h 4455 (by decide)
  have h7 : Entails.eval a c2624 := h 2623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9137 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9137 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9133, some c9135, some c9128, some c8269, some c9098, some c9136, some c9122, some c3721, some c1109, some c1095, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9137 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9137 : lratChecker f9137 p9137 = .success := by decide +kernel
theorem unsat9137 : Unsatisfiable (PosFin 65) f9137 := by
  apply lratCheckerSound f9137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9137
  · intro a ha; simp [p9137] at ha; subst a; trivial
  · exact checked9137
theorem derived9137 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9137 := by
  apply localUnsat_implies_entails f9137 [c9133, c9135, c9128, c8269, c9098, c9136, c9122, c3721, c1109, c1095] c9137 unsat9137 (by rfl) a
  have h0 : Entails.eval a c9133 := derived9133 a h
  have h1 : Entails.eval a c9135 := derived9135 a h
  have h2 : Entails.eval a c9128 := derived9128 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c9098 := derived9098 a h
  have h5 : Entails.eval a c9136 := derived9136 a h
  have h6 : Entails.eval a c9122 := derived9122 a h
  have h7 : Entails.eval a c3721 := h 3720 (by decide)
  have h8 : Entails.eval a c1109 := h 1108 (by decide)
  have h9 : Entails.eval a c1095 := h 1094 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9138 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨12, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9138 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9124, some c1150, some c1286, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9138 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9138 : lratChecker f9138 p9138 = .success := by decide +kernel
theorem unsat9138 : Unsatisfiable (PosFin 65) f9138 := by
  apply lratCheckerSound f9138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9138
  · intro a ha; simp [p9138] at ha; subst a; trivial
  · exact checked9138
theorem derived9138 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9138 := by
  apply localUnsat_implies_entails f9138 [c9098, c9124, c1150, c1286] c9138 unsat9138 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9124 := derived9124 a h
  have h2 : Entails.eval a c1150 := h 1149 (by decide)
  have h3 : Entails.eval a c1286 := h 1285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9139 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9139 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9128, some c9133, some c9135, some c9137, some c9138, some c1146, some c1149, some c1273, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9139 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9139 : lratChecker f9139 p9139 = .success := by decide +kernel
theorem unsat9139 : Unsatisfiable (PosFin 65) f9139 := by
  apply lratCheckerSound f9139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9139
  · intro a ha; simp [p9139] at ha; subst a; trivial
  · exact checked9139
theorem derived9139 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9139 := by
  apply localUnsat_implies_entails f9139 [c8269, c9128, c9133, c9135, c9137, c9138, c1146, c1149, c1273] c9139 unsat9139 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9128 := derived9128 a h
  have h2 : Entails.eval a c9133 := derived9133 a h
  have h3 : Entails.eval a c9135 := derived9135 a h
  have h4 : Entails.eval a c9137 := derived9137 a h
  have h5 : Entails.eval a c9138 := derived9138 a h
  have h6 : Entails.eval a c1146 := h 1145 (by decide)
  have h7 : Entails.eval a c1149 := h 1148 (by decide)
  have h8 : Entails.eval a c1273 := h 1272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9140 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨63, by decide⟩, true), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9140 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1104, some c3739, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9140 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9140 : lratChecker f9140 p9140 = .success := by decide +kernel
theorem unsat9140 : Unsatisfiable (PosFin 65) f9140 := by
  apply lratCheckerSound f9140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9140
  · intro a ha; simp [p9140] at ha; subst a; trivial
  · exact checked9140
theorem derived9140 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9140 := by
  apply localUnsat_implies_entails f9140 [c1104, c3739] c9140 unsat9140 (by rfl) a
  have h0 : Entails.eval a c1104 := h 1103 (by decide)
  have h1 : Entails.eval a c3739 := h 3738 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9141 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9141 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8816, some c8828, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9141 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9141 : lratChecker f9141 p9141 = .success := by decide +kernel
theorem unsat9141 : Unsatisfiable (PosFin 65) f9141 := by
  apply lratCheckerSound f9141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9141
  · intro a ha; simp [p9141] at ha; subst a; trivial
  · exact checked9141
theorem derived9141 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9141 := by
  apply localUnsat_implies_entails f9141 [c8816, c8828] c9141 unsat9141 (by rfl) a
  have h0 : Entails.eval a c8816 := derived8816 a h
  have h1 : Entails.eval a c8828 := derived8828 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9142 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9142 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4448, some c4459, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p9142 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9142 : lratChecker f9142 p9142 = .success := by decide +kernel
theorem unsat9142 : Unsatisfiable (PosFin 65) f9142 := by
  apply lratCheckerSound f9142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9142
  · intro a ha; simp [p9142] at ha; subst a; trivial
  · exact checked9142
theorem derived9142 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9142 := by
  apply localUnsat_implies_entails f9142 [c4448, c4459] c9142 unsat9142 (by rfl) a
  have h0 : Entails.eval a c4448 := h 4447 (by decide)
  have h1 : Entails.eval a c4459 := h 4458 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9143 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9143 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9103, some c9142, some c9105, some c2648, some c3153, some c3838, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9143 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9143 : lratChecker f9143 p9143 = .success := by decide +kernel
theorem unsat9143 : Unsatisfiable (PosFin 65) f9143 := by
  apply lratCheckerSound f9143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9143
  · intro a ha; simp [p9143] at ha; subst a; trivial
  · exact checked9143
theorem derived9143 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9143 := by
  apply localUnsat_implies_entails f9143 [c8269, c9103, c9142, c9105, c2648, c3153, c3838] c9143 unsat9143 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9103 := derived9103 a h
  have h2 : Entails.eval a c9142 := derived9142 a h
  have h3 : Entails.eval a c9105 := derived9105 a h
  have h4 : Entails.eval a c2648 := h 2647 (by decide)
  have h5 : Entails.eval a c3153 := h 3152 (by decide)
  have h6 : Entails.eval a c3838 := h 3837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9144 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9144 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9139, some c9098, some c9129, some c9141, some c9143, some c1270, some c1269, some c1152, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9144 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9144 : lratChecker f9144 p9144 = .success := by decide +kernel
theorem unsat9144 : Unsatisfiable (PosFin 65) f9144 := by
  apply lratCheckerSound f9144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9144
  · intro a ha; simp [p9144] at ha; subst a; trivial
  · exact checked9144
theorem derived9144 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9144 := by
  apply localUnsat_implies_entails f9144 [c9139, c9098, c9129, c9141, c9143, c1270, c1269, c1152] c9144 unsat9144 (by rfl) a
  have h0 : Entails.eval a c9139 := derived9139 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9129 := derived9129 a h
  have h3 : Entails.eval a c9141 := derived9141 a h
  have h4 : Entails.eval a c9143 := derived9143 a h
  have h5 : Entails.eval a c1270 := h 1269 (by decide)
  have h6 : Entails.eval a c1269 := h 1268 (by decide)
  have h7 : Entails.eval a c1152 := h 1151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9145 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨61, by decide⟩, true), (⟨11, by decide⟩, true), (⟨51, by decide⟩, false), (⟨12, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9145 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4461, some c4462, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p9145 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9145 : lratChecker f9145 p9145 = .success := by decide +kernel
theorem unsat9145 : Unsatisfiable (PosFin 65) f9145 := by
  apply lratCheckerSound f9145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9145
  · intro a ha; simp [p9145] at ha; subst a; trivial
  · exact checked9145
theorem derived9145 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9145 := by
  apply localUnsat_implies_entails f9145 [c4461, c4462] c9145 unsat9145 (by rfl) a
  have h0 : Entails.eval a c4461 := h 4460 (by decide)
  have h1 : Entails.eval a c4462 := h 4461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9146 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨58, by decide⟩, true), (⟨51, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9146 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3729, some c3718, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p9146 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9146 : lratChecker f9146 p9146 = .success := by decide +kernel
theorem unsat9146 : Unsatisfiable (PosFin 65) f9146 := by
  apply lratCheckerSound f9146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9146
  · intro a ha; simp [p9146] at ha; subst a; trivial
  · exact checked9146
theorem derived9146 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9146 := by
  apply localUnsat_implies_entails f9146 [c3729, c3718] c9146 unsat9146 (by rfl) a
  have h0 : Entails.eval a c3729 := h 3728 (by decide)
  have h1 : Entails.eval a c3718 := h 3717 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9147 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9147 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1091, some c1090, some c8007, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9147 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9147 : lratChecker f9147 p9147 = .success := by decide +kernel
theorem unsat9147 : Unsatisfiable (PosFin 65) f9147 := by
  apply lratCheckerSound f9147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9147
  · intro a ha; simp [p9147] at ha; subst a; trivial
  · exact checked9147
theorem derived9147 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9147 := by
  apply localUnsat_implies_entails f9147 [c1091, c1090, c8007] c9147 unsat9147 (by rfl) a
  have h0 : Entails.eval a c1091 := h 1090 (by decide)
  have h1 : Entails.eval a c1090 := h 1089 (by decide)
  have h2 : Entails.eval a c8007 := derived8007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9148 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9148 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9144, some c9098, some c9136, some c9147, some c3718, some c3732, some c8007, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9148 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9148 : lratChecker f9148 p9148 = .success := by decide +kernel
theorem unsat9148 : Unsatisfiable (PosFin 65) f9148 := by
  apply lratCheckerSound f9148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9148
  · intro a ha; simp [p9148] at ha; subst a; trivial
  · exact checked9148
theorem derived9148 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9148 := by
  apply localUnsat_implies_entails f9148 [c9144, c9098, c9136, c9147, c3718, c3732, c8007] c9148 unsat9148 (by rfl) a
  have h0 : Entails.eval a c9144 := derived9144 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9136 := derived9136 a h
  have h3 : Entails.eval a c9147 := derived9147 a h
  have h4 : Entails.eval a c3718 := h 3717 (by decide)
  have h5 : Entails.eval a c3732 := h 3731 (by decide)
  have h6 : Entails.eval a c8007 := derived8007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9149 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9149 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9144, some c9148, some c9138, some c1143, some c1142, some c8007, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9149 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9149 : lratChecker f9149 p9149 = .success := by decide +kernel
theorem unsat9149 : Unsatisfiable (PosFin 65) f9149 := by
  apply lratCheckerSound f9149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9149
  · intro a ha; simp [p9149] at ha; subst a; trivial
  · exact checked9149
theorem derived9149 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9149 := by
  apply localUnsat_implies_entails f9149 [c8269, c9144, c9148, c9138, c1143, c1142, c8007] c9149 unsat9149 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9144 := derived9144 a h
  have h2 : Entails.eval a c9148 := derived9148 a h
  have h3 : Entails.eval a c9138 := derived9138 a h
  have h4 : Entails.eval a c1143 := h 1142 (by decide)
  have h5 : Entails.eval a c1142 := h 1141 (by decide)
  have h6 : Entails.eval a c8007 := derived8007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9150 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9150 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9149, some c9135, some c8269, some c9098, some c9136, some c9122, some c9147, some c3721, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9150 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9150 : lratChecker f9150 p9150 = .success := by decide +kernel
theorem unsat9150 : Unsatisfiable (PosFin 65) f9150 := by
  apply lratCheckerSound f9150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9150
  · intro a ha; simp [p9150] at ha; subst a; trivial
  · exact checked9150
theorem derived9150 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9150 := by
  apply localUnsat_implies_entails f9150 [c9149, c9135, c8269, c9098, c9136, c9122, c9147, c3721] c9150 unsat9150 (by rfl) a
  have h0 : Entails.eval a c9149 := derived9149 a h
  have h1 : Entails.eval a c9135 := derived9135 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c9098 := derived9098 a h
  have h4 : Entails.eval a c9136 := derived9136 a h
  have h5 : Entails.eval a c9122 := derived9122 a h
  have h6 : Entails.eval a c9147 := derived9147 a h
  have h7 : Entails.eval a c3721 := h 3720 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9150

end CochromaticTwenty.Certificates.FixedCore0
