import MerLeanExperiment.Certificates.FixedCore1.Steps1000_1099

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6981 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨42, by decide⟩, true), (⟨62, by decide⟩, true), (⟨49, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6981 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5158, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6981 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6981 : lratChecker f6981 p6981 = .success := by decide +kernel
theorem unsat6981 : Unsatisfiable (PosFin 65) f6981 := by
  apply lratCheckerSound f6981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6981
  · intro a ha; simp [p6981] at ha; subst a; trivial
  · exact checked6981
theorem derived6981 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6981 := by
  apply localUnsat_implies_entails f6981 [c6581, c5158] c6981 unsat6981 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5158 := h 5157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6982 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨50, by decide⟩, true), (⟨37, by decide⟩, true), (⟨62, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6982 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5162, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p6982 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6982 : lratChecker f6982 p6982 = .success := by decide +kernel
theorem unsat6982 : Unsatisfiable (PosFin 65) f6982 := by
  apply lratCheckerSound f6982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6982
  · intro a ha; simp [p6982] at ha; subst a; trivial
  · exact checked6982
theorem derived6982 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6982 := by
  apply localUnsat_implies_entails f6982 [c6581, c5162] c6982 unsat6982 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5162 := h 5161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6983 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6983 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5171, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6983 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6983 : lratChecker f6983 p6983 = .success := by decide +kernel
theorem unsat6983 : Unsatisfiable (PosFin 65) f6983 := by
  apply lratCheckerSound f6983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6983
  · intro a ha; simp [p6983] at ha; subst a; trivial
  · exact checked6983
theorem derived6983 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6983 := by
  apply localUnsat_implies_entails f6983 [c6581, c5171] c6983 unsat6983 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5171 := h 5170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6984 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, true), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6984 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5172, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p6984 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6984 : lratChecker f6984 p6984 = .success := by decide +kernel
theorem unsat6984 : Unsatisfiable (PosFin 65) f6984 := by
  apply lratCheckerSound f6984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6984
  · intro a ha; simp [p6984] at ha; subst a; trivial
  · exact checked6984
theorem derived6984 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6984 := by
  apply localUnsat_implies_entails f6984 [c6581, c5172] c6984 unsat6984 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5172 := h 5171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6985 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨47, by decide⟩, true), (⟨62, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6985 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5173, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6985 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6985 : lratChecker f6985 p6985 = .success := by decide +kernel
theorem unsat6985 : Unsatisfiable (PosFin 65) f6985 := by
  apply lratCheckerSound f6985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6985
  · intro a ha; simp [p6985] at ha; subst a; trivial
  · exact checked6985
theorem derived6985 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6985 := by
  apply localUnsat_implies_entails f6985 [c6581, c5173] c6985 unsat6985 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5173 := h 5172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6986 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨46, by decide⟩, true), (⟨49, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6986 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5202, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6986 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6986 : lratChecker f6986 p6986 = .success := by decide +kernel
theorem unsat6986 : Unsatisfiable (PosFin 65) f6986 := by
  apply lratCheckerSound f6986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6986
  · intro a ha; simp [p6986] at ha; subst a; trivial
  · exact checked6986
theorem derived6986 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6986 := by
  apply localUnsat_implies_entails f6986 [c6581, c5202] c6986 unsat6986 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5202 := h 5201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6987 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨46, by decide⟩, true), (⟨49, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6987 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5204, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6987 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6987 : lratChecker f6987 p6987 = .success := by decide +kernel
theorem unsat6987 : Unsatisfiable (PosFin 65) f6987 := by
  apply lratCheckerSound f6987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6987
  · intro a ha; simp [p6987] at ha; subst a; trivial
  · exact checked6987
theorem derived6987 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6987 := by
  apply localUnsat_implies_entails f6987 [c6581, c5204] c6987 unsat6987 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5204 := h 5203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6988 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6988 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5224, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p6988 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6988 : lratChecker f6988 p6988 = .success := by decide +kernel
theorem unsat6988 : Unsatisfiable (PosFin 65) f6988 := by
  apply lratCheckerSound f6988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6988
  · intro a ha; simp [p6988] at ha; subst a; trivial
  · exact checked6988
theorem derived6988 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6988 := by
  apply localUnsat_implies_entails f6988 [c6581, c5224] c6988 unsat6988 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5224 := h 5223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6989 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨56, by decide⟩, true), (⟨39, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6989 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5259, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p6989 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6989 : lratChecker f6989 p6989 = .success := by decide +kernel
theorem unsat6989 : Unsatisfiable (PosFin 65) f6989 := by
  apply lratCheckerSound f6989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6989
  · intro a ha; simp [p6989] at ha; subst a; trivial
  · exact checked6989
theorem derived6989 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6989 := by
  apply localUnsat_implies_entails f6989 [c6581, c5259] c6989 unsat6989 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5259 := h 5258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6990 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6990 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5260, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6990 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6990 : lratChecker f6990 p6990 = .success := by decide +kernel
theorem unsat6990 : Unsatisfiable (PosFin 65) f6990 := by
  apply lratCheckerSound f6990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6990
  · intro a ha; simp [p6990] at ha; subst a; trivial
  · exact checked6990
theorem derived6990 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6990 := by
  apply localUnsat_implies_entails f6990 [c6581, c5260] c6990 unsat6990 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5260 := h 5259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6991 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨56, by decide⟩, true), (⟨50, by decide⟩, true), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6991 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5262, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p6991 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6991 : lratChecker f6991 p6991 = .success := by decide +kernel
theorem unsat6991 : Unsatisfiable (PosFin 65) f6991 := by
  apply lratCheckerSound f6991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6991
  · intro a ha; simp [p6991] at ha; subst a; trivial
  · exact checked6991
theorem derived6991 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6991 := by
  apply localUnsat_implies_entails f6991 [c6581, c5262] c6991 unsat6991 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5262 := h 5261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6992 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨39, by decide⟩, false), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6992 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5274, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p6992 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6992 : lratChecker f6992 p6992 = .success := by decide +kernel
theorem unsat6992 : Unsatisfiable (PosFin 65) f6992 := by
  apply lratCheckerSound f6992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6992
  · intro a ha; simp [p6992] at ha; subst a; trivial
  · exact checked6992
theorem derived6992 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6992 := by
  apply localUnsat_implies_entails f6992 [c6581, c5274] c6992 unsat6992 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5274 := h 5273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6993 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6993 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5275, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6993 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6993 : lratChecker f6993 p6993 = .success := by decide +kernel
theorem unsat6993 : Unsatisfiable (PosFin 65) f6993 := by
  apply lratCheckerSound f6993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6993
  · intro a ha; simp [p6993] at ha; subst a; trivial
  · exact checked6993
theorem derived6993 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6993 := by
  apply localUnsat_implies_entails f6993 [c6581, c5275] c6993 unsat6993 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5275 := h 5274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6994 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6994 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5278, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6994 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6994 : lratChecker f6994 p6994 = .success := by decide +kernel
theorem unsat6994 : Unsatisfiable (PosFin 65) f6994 := by
  apply lratCheckerSound f6994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6994
  · intro a ha; simp [p6994] at ha; subst a; trivial
  · exact checked6994
theorem derived6994 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6994 := by
  apply localUnsat_implies_entails f6994 [c6581, c5278] c6994 unsat6994 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5278 := h 5277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6995 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6995 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5282, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6995 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6995 : lratChecker f6995 p6995 = .success := by decide +kernel
theorem unsat6995 : Unsatisfiable (PosFin 65) f6995 := by
  apply lratCheckerSound f6995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6995
  · intro a ha; simp [p6995] at ha; subst a; trivial
  · exact checked6995
theorem derived6995 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6995 := by
  apply localUnsat_implies_entails f6995 [c6581, c5282] c6995 unsat6995 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5282 := h 5281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6996 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨50, by decide⟩, true), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6996 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5285, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6996 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6996 : lratChecker f6996 p6996 = .success := by decide +kernel
theorem unsat6996 : Unsatisfiable (PosFin 65) f6996 := by
  apply lratCheckerSound f6996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6996
  · intro a ha; simp [p6996] at ha; subst a; trivial
  · exact checked6996
theorem derived6996 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6996 := by
  apply localUnsat_implies_entails f6996 [c6581, c5285] c6996 unsat6996 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5285 := h 5284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6997 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨57, by decide⟩, true), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6997 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5295, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6997 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6997 : lratChecker f6997 p6997 = .success := by decide +kernel
theorem unsat6997 : Unsatisfiable (PosFin 65) f6997 := by
  apply lratCheckerSound f6997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6997
  · intro a ha; simp [p6997] at ha; subst a; trivial
  · exact checked6997
theorem derived6997 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6997 := by
  apply localUnsat_implies_entails f6997 [c6581, c5295] c6997 unsat6997 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5295 := h 5294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6998 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨60, by decide⟩, true), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6998 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5296, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6998 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6998 : lratChecker f6998 p6998 = .success := by decide +kernel
theorem unsat6998 : Unsatisfiable (PosFin 65) f6998 := by
  apply lratCheckerSound f6998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6998
  · intro a ha; simp [p6998] at ha; subst a; trivial
  · exact checked6998
theorem derived6998 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6998 := by
  apply localUnsat_implies_entails f6998 [c6581, c5296] c6998 unsat6998 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5296 := h 5295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6999 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨56, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6999 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5361, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p6999 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6999 : lratChecker f6999 p6999 = .success := by decide +kernel
theorem unsat6999 : Unsatisfiable (PosFin 65) f6999 := by
  apply lratCheckerSound f6999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6999
  · intro a ha; simp [p6999] at ha; subst a; trivial
  · exact checked6999
theorem derived6999 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6999 := by
  apply localUnsat_implies_entails f6999 [c6581, c5361] c6999 unsat6999 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5361 := h 5360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7000 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7000 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5362, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7000 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7000 : lratChecker f7000 p7000 = .success := by decide +kernel
theorem unsat7000 : Unsatisfiable (PosFin 65) f7000 := by
  apply lratCheckerSound f7000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7000
  · intro a ha; simp [p7000] at ha; subst a; trivial
  · exact checked7000
theorem derived7000 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7000 := by
  apply localUnsat_implies_entails f7000 [c6581, c5362] c7000 unsat7000 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5362 := h 5361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7001 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7001 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5396, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p7001 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7001 : lratChecker f7001 p7001 = .success := by decide +kernel
theorem unsat7001 : Unsatisfiable (PosFin 65) f7001 := by
  apply lratCheckerSound f7001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7001
  · intro a ha; simp [p7001] at ha; subst a; trivial
  · exact checked7001
theorem derived7001 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7001 := by
  apply localUnsat_implies_entails f7001 [c6581, c5396] c7001 unsat7001 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5396 := h 5395 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7002 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7002 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5399, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7002 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7002 : lratChecker f7002 p7002 = .success := by decide +kernel
theorem unsat7002 : Unsatisfiable (PosFin 65) f7002 := by
  apply lratCheckerSound f7002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7002
  · intro a ha; simp [p7002] at ha; subst a; trivial
  · exact checked7002
theorem derived7002 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7002 := by
  apply localUnsat_implies_entails f7002 [c6581, c5399] c7002 unsat7002 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5399 := h 5398 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7003 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨38, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7003 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5404, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7003 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7003 : lratChecker f7003 p7003 = .success := by decide +kernel
theorem unsat7003 : Unsatisfiable (PosFin 65) f7003 := by
  apply lratCheckerSound f7003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7003
  · intro a ha; simp [p7003] at ha; subst a; trivial
  · exact checked7003
theorem derived7003 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7003 := by
  apply localUnsat_implies_entails f7003 [c6581, c5404] c7003 unsat7003 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5404 := h 5403 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7004 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨43, by decide⟩, true), (⟨45, by decide⟩, true), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7004 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5422, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7004 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7004 : lratChecker f7004 p7004 = .success := by decide +kernel
theorem unsat7004 : Unsatisfiable (PosFin 65) f7004 := by
  apply lratCheckerSound f7004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7004
  · intro a ha; simp [p7004] at ha; subst a; trivial
  · exact checked7004
theorem derived7004 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7004 := by
  apply localUnsat_implies_entails f7004 [c6581, c5422] c7004 unsat7004 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5422 := h 5421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7005 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨43, by decide⟩, true), (⟨45, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7005 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5423, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7005 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7005 : lratChecker f7005 p7005 = .success := by decide +kernel
theorem unsat7005 : Unsatisfiable (PosFin 65) f7005 := by
  apply lratCheckerSound f7005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7005
  · intro a ha; simp [p7005] at ha; subst a; trivial
  · exact checked7005
theorem derived7005 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7005 := by
  apply localUnsat_implies_entails f7005 [c6581, c5423] c7005 unsat7005 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5423 := h 5422 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7006 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨49, by decide⟩, true), (⟨44, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7006 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5426, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7006 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7006 : lratChecker f7006 p7006 = .success := by decide +kernel
theorem unsat7006 : Unsatisfiable (PosFin 65) f7006 := by
  apply lratCheckerSound f7006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7006
  · intro a ha; simp [p7006] at ha; subst a; trivial
  · exact checked7006
theorem derived7006 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7006 := by
  apply localUnsat_implies_entails f7006 [c6581, c5426] c7006 unsat7006 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5426 := h 5425 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7007 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨50, by decide⟩, true), (⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7007 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5428, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7007 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7007 : lratChecker f7007 p7007 = .success := by decide +kernel
theorem unsat7007 : Unsatisfiable (PosFin 65) f7007 := by
  apply lratCheckerSound f7007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7007
  · intro a ha; simp [p7007] at ha; subst a; trivial
  · exact checked7007
theorem derived7007 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7007 := by
  apply localUnsat_implies_entails f7007 [c6581, c5428] c7007 unsat7007 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5428 := h 5427 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7008 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨57, by decide⟩, true), (⟨47, by decide⟩, false), (⟨46, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7008 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5457, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7008 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7008 : lratChecker f7008 p7008 = .success := by decide +kernel
theorem unsat7008 : Unsatisfiable (PosFin 65) f7008 := by
  apply lratCheckerSound f7008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7008
  · intro a ha; simp [p7008] at ha; subst a; trivial
  · exact checked7008
theorem derived7008 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7008 := by
  apply localUnsat_implies_entails f7008 [c6581, c5457] c7008 unsat7008 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5457 := h 5456 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7009 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7009 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5461, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p7009 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7009 : lratChecker f7009 p7009 = .success := by decide +kernel
theorem unsat7009 : Unsatisfiable (PosFin 65) f7009 := by
  apply lratCheckerSound f7009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7009
  · intro a ha; simp [p7009] at ha; subst a; trivial
  · exact checked7009
theorem derived7009 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7009 := by
  apply localUnsat_implies_entails f7009 [c6581, c5461] c7009 unsat7009 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5461 := h 5460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7010 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨56, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7010 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5462, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p7010 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7010 : lratChecker f7010 p7010 = .success := by decide +kernel
theorem unsat7010 : Unsatisfiable (PosFin 65) f7010 := by
  apply lratCheckerSound f7010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7010
  · intro a ha; simp [p7010] at ha; subst a; trivial
  · exact checked7010
theorem derived7010 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7010 := by
  apply localUnsat_implies_entails f7010 [c6581, c5462] c7010 unsat7010 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5462 := h 5461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7011 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨39, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7011 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5465, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7011 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7011 : lratChecker f7011 p7011 = .success := by decide +kernel
theorem unsat7011 : Unsatisfiable (PosFin 65) f7011 := by
  apply lratCheckerSound f7011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7011
  · intro a ha; simp [p7011] at ha; subst a; trivial
  · exact checked7011
theorem derived7011 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7011 := by
  apply localUnsat_implies_entails f7011 [c6581, c5465] c7011 unsat7011 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5465 := h 5464 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7012 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨39, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7012 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5477, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7012 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7012 : lratChecker f7012 p7012 = .success := by decide +kernel
theorem unsat7012 : Unsatisfiable (PosFin 65) f7012 := by
  apply lratCheckerSound f7012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7012
  · intro a ha; simp [p7012] at ha; subst a; trivial
  · exact checked7012
theorem derived7012 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7012 := by
  apply localUnsat_implies_entails f7012 [c6581, c5477] c7012 unsat7012 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5477 := h 5476 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7013 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨54, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7013 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5503, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7013 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7013 : lratChecker f7013 p7013 = .success := by decide +kernel
theorem unsat7013 : Unsatisfiable (PosFin 65) f7013 := by
  apply lratCheckerSound f7013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7013
  · intro a ha; simp [p7013] at ha; subst a; trivial
  · exact checked7013
theorem derived7013 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7013 := by
  apply localUnsat_implies_entails f7013 [c6581, c5503] c7013 unsat7013 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5503 := h 5502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7014 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7014 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5504, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p7014 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7014 : lratChecker f7014 p7014 = .success := by decide +kernel
theorem unsat7014 : Unsatisfiable (PosFin 65) f7014 := by
  apply lratCheckerSound f7014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7014
  · intro a ha; simp [p7014] at ha; subst a; trivial
  · exact checked7014
theorem derived7014 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7014 := by
  apply localUnsat_implies_entails f7014 [c6581, c5504] c7014 unsat7014 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5504 := h 5503 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7015 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7015 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5506, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7015 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7015 : lratChecker f7015 p7015 = .success := by decide +kernel
theorem unsat7015 : Unsatisfiable (PosFin 65) f7015 := by
  apply lratCheckerSound f7015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7015
  · intro a ha; simp [p7015] at ha; subst a; trivial
  · exact checked7015
theorem derived7015 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7015 := by
  apply localUnsat_implies_entails f7015 [c6581, c5506] c7015 unsat7015 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5506 := h 5505 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7016 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨54, by decide⟩, true), (⟨43, by decide⟩, true), (⟨45, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7016 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5521, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p7016 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7016 : lratChecker f7016 p7016 = .success := by decide +kernel
theorem unsat7016 : Unsatisfiable (PosFin 65) f7016 := by
  apply lratCheckerSound f7016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7016
  · intro a ha; simp [p7016] at ha; subst a; trivial
  · exact checked7016
theorem derived7016 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7016 := by
  apply localUnsat_implies_entails f7016 [c6581, c5521] c7016 unsat7016 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5521 := h 5520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7017 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨45, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7017 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5524, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7017 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7017 : lratChecker f7017 p7017 = .success := by decide +kernel
theorem unsat7017 : Unsatisfiable (PosFin 65) f7017 := by
  apply lratCheckerSound f7017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7017
  · intro a ha; simp [p7017] at ha; subst a; trivial
  · exact checked7017
theorem derived7017 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7017 := by
  apply localUnsat_implies_entails f7017 [c6581, c5524] c7017 unsat7017 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5524 := h 5523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7018 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7018 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5528, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p7018 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7018 : lratChecker f7018 p7018 = .success := by decide +kernel
theorem unsat7018 : Unsatisfiable (PosFin 65) f7018 := by
  apply lratCheckerSound f7018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7018
  · intro a ha; simp [p7018] at ha; subst a; trivial
  · exact checked7018
theorem derived7018 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7018 := by
  apply localUnsat_implies_entails f7018 [c6581, c5528] c7018 unsat7018 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5528 := h 5527 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7019 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7019 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5545, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p7019 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7019 : lratChecker f7019 p7019 = .success := by decide +kernel
theorem unsat7019 : Unsatisfiable (PosFin 65) f7019 := by
  apply lratCheckerSound f7019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7019
  · intro a ha; simp [p7019] at ha; subst a; trivial
  · exact checked7019
theorem derived7019 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7019 := by
  apply localUnsat_implies_entails f7019 [c6581, c5545] c7019 unsat7019 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5545 := h 5544 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7020 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨39, by decide⟩, true), (⟨44, by decide⟩, true), (⟨49, by decide⟩, true), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7020 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5554, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p7020 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7020 : lratChecker f7020 p7020 = .success := by decide +kernel
theorem unsat7020 : Unsatisfiable (PosFin 65) f7020 := by
  apply lratCheckerSound f7020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7020
  · intro a ha; simp [p7020] at ha; subst a; trivial
  · exact checked7020
theorem derived7020 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7020 := by
  apply localUnsat_implies_entails f7020 [c6581, c5554] c7020 unsat7020 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5554 := h 5553 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7021 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨54, by decide⟩, true), (⟨40, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7021 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5599, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p7021 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7021 : lratChecker f7021 p7021 = .success := by decide +kernel
theorem unsat7021 : Unsatisfiable (PosFin 65) f7021 := by
  apply lratCheckerSound f7021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7021
  · intro a ha; simp [p7021] at ha; subst a; trivial
  · exact checked7021
theorem derived7021 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7021 := by
  apply localUnsat_implies_entails f7021 [c6581, c5599] c7021 unsat7021 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5599 := h 5598 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7022 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨42, by decide⟩, true), (⟨40, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7022 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5649, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p7022 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7022 : lratChecker f7022 p7022 = .success := by decide +kernel
theorem unsat7022 : Unsatisfiable (PosFin 65) f7022 := by
  apply lratCheckerSound f7022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7022
  · intro a ha; simp [p7022] at ha; subst a; trivial
  · exact checked7022
theorem derived7022 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7022 := by
  apply localUnsat_implies_entails f7022 [c6581, c5649] c7022 unsat7022 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5649 := h 5648 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7023 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨54, by decide⟩, true), (⟨40, by decide⟩, true), (⟨42, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7023 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5665, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p7023 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7023 : lratChecker f7023 p7023 = .success := by decide +kernel
theorem unsat7023 : Unsatisfiable (PosFin 65) f7023 := by
  apply lratCheckerSound f7023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7023
  · intro a ha; simp [p7023] at ha; subst a; trivial
  · exact checked7023
theorem derived7023 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7023 := by
  apply localUnsat_implies_entails f7023 [c6581, c5665] c7023 unsat7023 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5665 := h 5664 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7024 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨40, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7024 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5669, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p7024 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7024 : lratChecker f7024 p7024 = .success := by decide +kernel
theorem unsat7024 : Unsatisfiable (PosFin 65) f7024 := by
  apply lratCheckerSound f7024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7024
  · intro a ha; simp [p7024] at ha; subst a; trivial
  · exact checked7024
theorem derived7024 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7024 := by
  apply localUnsat_implies_entails f7024 [c6581, c5669] c7024 unsat7024 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5669 := h 5668 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7025 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨62, by decide⟩, true), (⟨40, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7025 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5671, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p7025 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7025 : lratChecker f7025 p7025 = .success := by decide +kernel
theorem unsat7025 : Unsatisfiable (PosFin 65) f7025 := by
  apply lratCheckerSound f7025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7025
  · intro a ha; simp [p7025] at ha; subst a; trivial
  · exact checked7025
theorem derived7025 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7025 := by
  apply localUnsat_implies_entails f7025 [c6581, c5671] c7025 unsat7025 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5671 := h 5670 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7026 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨40, by decide⟩, false), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7026 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5682, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p7026 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7026 : lratChecker f7026 p7026 = .success := by decide +kernel
theorem unsat7026 : Unsatisfiable (PosFin 65) f7026 := by
  apply lratCheckerSound f7026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7026
  · intro a ha; simp [p7026] at ha; subst a; trivial
  · exact checked7026
theorem derived7026 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7026 := by
  apply localUnsat_implies_entails f7026 [c6581, c5682] c7026 unsat7026 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5682 := h 5681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7027 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7027 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5690, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p7027 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7027 : lratChecker f7027 p7027 = .success := by decide +kernel
theorem unsat7027 : Unsatisfiable (PosFin 65) f7027 := by
  apply lratCheckerSound f7027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7027
  · intro a ha; simp [p7027] at ha; subst a; trivial
  · exact checked7027
theorem derived7027 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7027 := by
  apply localUnsat_implies_entails f7027 [c6581, c5690] c7027 unsat7027 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5690 := h 5689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7028 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7028 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5706, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p7028 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7028 : lratChecker f7028 p7028 = .success := by decide +kernel
theorem unsat7028 : Unsatisfiable (PosFin 65) f7028 := by
  apply lratCheckerSound f7028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7028
  · intro a ha; simp [p7028] at ha; subst a; trivial
  · exact checked7028
theorem derived7028 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7028 := by
  apply localUnsat_implies_entails f7028 [c6581, c5706] c7028 unsat7028 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5706 := h 5705 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7029 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7029 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5722, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p7029 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7029 : lratChecker f7029 p7029 = .success := by decide +kernel
theorem unsat7029 : Unsatisfiable (PosFin 65) f7029 := by
  apply lratCheckerSound f7029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7029
  · intro a ha; simp [p7029] at ha; subst a; trivial
  · exact checked7029
theorem derived7029 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7029 := by
  apply localUnsat_implies_entails f7029 [c6581, c5722] c7029 unsat7029 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5722 := h 5721 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7030 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7030 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5726, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p7030 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7030 : lratChecker f7030 p7030 = .success := by decide +kernel
theorem unsat7030 : Unsatisfiable (PosFin 65) f7030 := by
  apply lratCheckerSound f7030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7030
  · intro a ha; simp [p7030] at ha; subst a; trivial
  · exact checked7030
theorem derived7030 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7030 := by
  apply localUnsat_implies_entails f7030 [c6581, c5726] c7030 unsat7030 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5726 := h 5725 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7031 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨50, by decide⟩, true), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7031 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5727, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p7031 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7031 : lratChecker f7031 p7031 = .success := by decide +kernel
theorem unsat7031 : Unsatisfiable (PosFin 65) f7031 := by
  apply lratCheckerSound f7031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7031
  · intro a ha; simp [p7031] at ha; subst a; trivial
  · exact checked7031
theorem derived7031 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7031 := by
  apply localUnsat_implies_entails f7031 [c6581, c5727] c7031 unsat7031 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5727 := h 5726 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7032 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨46, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7032 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5752, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p7032 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7032 : lratChecker f7032 p7032 = .success := by decide +kernel
theorem unsat7032 : Unsatisfiable (PosFin 65) f7032 := by
  apply lratCheckerSound f7032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7032
  · intro a ha; simp [p7032] at ha; subst a; trivial
  · exact checked7032
theorem derived7032 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7032 := by
  apply localUnsat_implies_entails f7032 [c6581, c5752] c7032 unsat7032 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5752 := h 5751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7033 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨41, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7033 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5755, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p7033 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7033 : lratChecker f7033 p7033 = .success := by decide +kernel
theorem unsat7033 : Unsatisfiable (PosFin 65) f7033 := by
  apply lratCheckerSound f7033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7033
  · intro a ha; simp [p7033] at ha; subst a; trivial
  · exact checked7033
theorem derived7033 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7033 := by
  apply localUnsat_implies_entails f7033 [c6581, c5755] c7033 unsat7033 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5755 := h 5754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7034 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨42, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7034 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5769, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p7034 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7034 : lratChecker f7034 p7034 = .success := by decide +kernel
theorem unsat7034 : Unsatisfiable (PosFin 65) f7034 := by
  apply lratCheckerSound f7034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7034
  · intro a ha; simp [p7034] at ha; subst a; trivial
  · exact checked7034
theorem derived7034 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7034 := by
  apply localUnsat_implies_entails f7034 [c6581, c5769] c7034 unsat7034 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5769 := h 5768 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7035 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨42, by decide⟩, true), (⟨45, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7035 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5771, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7035 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7035 : lratChecker f7035 p7035 = .success := by decide +kernel
theorem unsat7035 : Unsatisfiable (PosFin 65) f7035 := by
  apply lratCheckerSound f7035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7035
  · intro a ha; simp [p7035] at ha; subst a; trivial
  · exact checked7035
theorem derived7035 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7035 := by
  apply localUnsat_implies_entails f7035 [c6581, c5771] c7035 unsat7035 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5771 := h 5770 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7036 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨42, by decide⟩, true), (⟨50, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7036 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5776, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p7036 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7036 : lratChecker f7036 p7036 = .success := by decide +kernel
theorem unsat7036 : Unsatisfiable (PosFin 65) f7036 := by
  apply lratCheckerSound f7036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7036
  · intro a ha; simp [p7036] at ha; subst a; trivial
  · exact checked7036
theorem derived7036 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7036 := by
  apply localUnsat_implies_entails f7036 [c6581, c5776] c7036 unsat7036 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5776 := h 5775 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7037 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨42, by decide⟩, true), (⟨50, by decide⟩, true), (⟨45, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7037 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5778, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7037 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7037 : lratChecker f7037 p7037 = .success := by decide +kernel
theorem unsat7037 : Unsatisfiable (PosFin 65) f7037 := by
  apply lratCheckerSound f7037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7037
  · intro a ha; simp [p7037] at ha; subst a; trivial
  · exact checked7037
theorem derived7037 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7037 := by
  apply localUnsat_implies_entails f7037 [c6581, c5778] c7037 unsat7037 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5778 := h 5777 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7038 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨45, by decide⟩, true), (⟨42, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7038 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5791, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p7038 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7038 : lratChecker f7038 p7038 = .success := by decide +kernel
theorem unsat7038 : Unsatisfiable (PosFin 65) f7038 := by
  apply lratCheckerSound f7038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7038
  · intro a ha; simp [p7038] at ha; subst a; trivial
  · exact checked7038
theorem derived7038 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7038 := by
  apply localUnsat_implies_entails f7038 [c6581, c5791] c7038 unsat7038 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5791 := h 5790 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7039 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨42, by decide⟩, true), (⟨45, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7039 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5794, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7039 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7039 : lratChecker f7039 p7039 = .success := by decide +kernel
theorem unsat7039 : Unsatisfiable (PosFin 65) f7039 := by
  apply lratCheckerSound f7039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7039
  · intro a ha; simp [p7039] at ha; subst a; trivial
  · exact checked7039
theorem derived7039 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7039 := by
  apply localUnsat_implies_entails f7039 [c6581, c5794] c7039 unsat7039 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5794 := h 5793 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7040 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨45, by decide⟩, true), (⟨47, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7040 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5798, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p7040 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7040 : lratChecker f7040 p7040 = .success := by decide +kernel
theorem unsat7040 : Unsatisfiable (PosFin 65) f7040 := by
  apply lratCheckerSound f7040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7040
  · intro a ha; simp [p7040] at ha; subst a; trivial
  · exact checked7040
theorem derived7040 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7040 := by
  apply localUnsat_implies_entails f7040 [c6581, c5798] c7040 unsat7040 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5798 := h 5797 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7041 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨50, by decide⟩, true), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7041 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5799, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7041 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7041 : lratChecker f7041 p7041 = .success := by decide +kernel
theorem unsat7041 : Unsatisfiable (PosFin 65) f7041 := by
  apply lratCheckerSound f7041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7041
  · intro a ha; simp [p7041] at ha; subst a; trivial
  · exact checked7041
theorem derived7041 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7041 := by
  apply localUnsat_implies_entails f7041 [c6581, c5799] c7041 unsat7041 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5799 := h 5798 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7042 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨45, by decide⟩, true), (⟨47, by decide⟩, true), (⟨50, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7042 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5800, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7042 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7042 : lratChecker f7042 p7042 = .success := by decide +kernel
theorem unsat7042 : Unsatisfiable (PosFin 65) f7042 := by
  apply lratCheckerSound f7042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7042
  · intro a ha; simp [p7042] at ha; subst a; trivial
  · exact checked7042
theorem derived7042 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7042 := by
  apply localUnsat_implies_entails f7042 [c6581, c5800] c7042 unsat7042 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5800 := h 5799 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7043 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7043 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5810, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7043 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7043 : lratChecker f7043 p7043 = .success := by decide +kernel
theorem unsat7043 : Unsatisfiable (PosFin 65) f7043 := by
  apply lratCheckerSound f7043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7043
  · intro a ha; simp [p7043] at ha; subst a; trivial
  · exact checked7043
theorem derived7043 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7043 := by
  apply localUnsat_implies_entails f7043 [c6581, c5810] c7043 unsat7043 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5810 := h 5809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7044 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7044 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5811, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p7044 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7044 : lratChecker f7044 p7044 = .success := by decide +kernel
theorem unsat7044 : Unsatisfiable (PosFin 65) f7044 := by
  apply lratCheckerSound f7044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7044
  · intro a ha; simp [p7044] at ha; subst a; trivial
  · exact checked7044
theorem derived7044 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7044 := by
  apply localUnsat_implies_entails f7044 [c6581, c5811] c7044 unsat7044 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5811 := h 5810 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7045 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7045 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5813, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p7045 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7045 : lratChecker f7045 p7045 = .success := by decide +kernel
theorem unsat7045 : Unsatisfiable (PosFin 65) f7045 := by
  apply lratCheckerSound f7045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7045
  · intro a ha; simp [p7045] at ha; subst a; trivial
  · exact checked7045
theorem derived7045 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7045 := by
  apply localUnsat_implies_entails f7045 [c6581, c5813] c7045 unsat7045 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5813 := h 5812 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7046 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7046 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5828, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p7046 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7046 : lratChecker f7046 p7046 = .success := by decide +kernel
theorem unsat7046 : Unsatisfiable (PosFin 65) f7046 := by
  apply lratCheckerSound f7046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7046
  · intro a ha; simp [p7046] at ha; subst a; trivial
  · exact checked7046
theorem derived7046 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7046 := by
  apply localUnsat_implies_entails f7046 [c6581, c5828] c7046 unsat7046 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5828 := h 5827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7047 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨46, by decide⟩, false), (⟨62, by decide⟩, true), (⟨48, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7047 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4876, some c4908, some c4878, some c4909, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7047 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7047 : lratChecker f7047 p7047 = .success := by decide +kernel
theorem unsat7047 : Unsatisfiable (PosFin 65) f7047 := by
  apply lratCheckerSound f7047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7047
  · intro a ha; simp [p7047] at ha; subst a; trivial
  · exact checked7047
theorem derived7047 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7047 := by
  apply localUnsat_implies_entails f7047 [c4876, c4908, c4878, c4909] c7047 unsat7047 (by rfl) a
  have h0 : Entails.eval a c4876 := h 4875 (by decide)
  have h1 : Entails.eval a c4908 := h 4907 (by decide)
  have h2 : Entails.eval a c4878 := h 4877 (by decide)
  have h3 : Entails.eval a c4909 := h 4908 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7048 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨52, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7048 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6629, some c6638, some c6653, some c6658, some c6650, some c6659, some c5596, some c5833, some c6660, some c5570, some c4278, some c5551, some c5437, some c7047, some c4787, some c4665, some c4780, some c6924, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7048 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7048 : lratChecker f7048 p7048 = .success := by decide +kernel
theorem unsat7048 : Unsatisfiable (PosFin 65) f7048 := by
  apply lratCheckerSound f7048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7048
  · intro a ha; simp [p7048] at ha; subst a; trivial
  · exact checked7048
theorem derived7048 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7048 := by
  apply localUnsat_implies_entails f7048 [c6629, c6638, c6653, c6658, c6650, c6659, c5596, c5833, c6660, c5570, c4278, c5551, c5437, c7047, c4787, c4665, c4780, c6924] c7048 unsat7048 (by rfl) a
  have h0 : Entails.eval a c6629 := derived6629 a h
  have h1 : Entails.eval a c6638 := derived6638 a h
  have h2 : Entails.eval a c6653 := derived6653 a h
  have h3 : Entails.eval a c6658 := derived6658 a h
  have h4 : Entails.eval a c6650 := derived6650 a h
  have h5 : Entails.eval a c6659 := derived6659 a h
  have h6 : Entails.eval a c5596 := h 5595 (by decide)
  have h7 : Entails.eval a c5833 := h 5832 (by decide)
  have h8 : Entails.eval a c6660 := derived6660 a h
  have h9 : Entails.eval a c5570 := h 5569 (by decide)
  have h10 : Entails.eval a c4278 := h 4277 (by decide)
  have h11 : Entails.eval a c5551 := h 5550 (by decide)
  have h12 : Entails.eval a c5437 := h 5436 (by decide)
  have h13 : Entails.eval a c7047 := derived7047 a h
  have h14 : Entails.eval a c4787 := h 4786 (by decide)
  have h15 : Entails.eval a c4665 := h 4664 (by decide)
  have h16 : Entails.eval a c4780 := h 4779 (by decide)
  have h17 : Entails.eval a c6924 := derived6924 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7049 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7049 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7048, some c6629, some c6653, some c6638, some c6658, some c6650, some c5603, some c5842, some c6660, some c4283, some c5581, some c5526, some c5437, some c4787, some c4665, some c4780, some c6924, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7049 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7049 : lratChecker f7049 p7049 = .success := by decide +kernel
theorem unsat7049 : Unsatisfiable (PosFin 65) f7049 := by
  apply lratCheckerSound f7049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7049
  · intro a ha; simp [p7049] at ha; subst a; trivial
  · exact checked7049
theorem derived7049 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7049 := by
  apply localUnsat_implies_entails f7049 [c7048, c6629, c6653, c6638, c6658, c6650, c5603, c5842, c6660, c4283, c5581, c5526, c5437, c4787, c4665, c4780, c6924] c7049 unsat7049 (by rfl) a
  have h0 : Entails.eval a c7048 := derived7048 a h
  have h1 : Entails.eval a c6629 := derived6629 a h
  have h2 : Entails.eval a c6653 := derived6653 a h
  have h3 : Entails.eval a c6638 := derived6638 a h
  have h4 : Entails.eval a c6658 := derived6658 a h
  have h5 : Entails.eval a c6650 := derived6650 a h
  have h6 : Entails.eval a c5603 := h 5602 (by decide)
  have h7 : Entails.eval a c5842 := h 5841 (by decide)
  have h8 : Entails.eval a c6660 := derived6660 a h
  have h9 : Entails.eval a c4283 := h 4282 (by decide)
  have h10 : Entails.eval a c5581 := h 5580 (by decide)
  have h11 : Entails.eval a c5526 := h 5525 (by decide)
  have h12 : Entails.eval a c5437 := h 5436 (by decide)
  have h13 : Entails.eval a c4787 := h 4786 (by decide)
  have h14 : Entails.eval a c4665 := h 4664 (by decide)
  have h15 : Entails.eval a c4780 := h 4779 (by decide)
  have h16 : Entails.eval a c6924 := derived6924 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7050 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7050 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6629, some c6638, some c6653, some c6658, some c6650, some c7048, some c5603, some c5842, some c5581, some c5526, some c7049, some c4876, some c4903, some c4872, some c6945, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7050 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7050 : lratChecker f7050 p7050 = .success := by decide +kernel
theorem unsat7050 : Unsatisfiable (PosFin 65) f7050 := by
  apply lratCheckerSound f7050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7050
  · intro a ha; simp [p7050] at ha; subst a; trivial
  · exact checked7050
theorem derived7050 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7050 := by
  apply localUnsat_implies_entails f7050 [c6629, c6638, c6653, c6658, c6650, c7048, c5603, c5842, c5581, c5526, c7049, c4876, c4903, c4872, c6945] c7050 unsat7050 (by rfl) a
  have h0 : Entails.eval a c6629 := derived6629 a h
  have h1 : Entails.eval a c6638 := derived6638 a h
  have h2 : Entails.eval a c6653 := derived6653 a h
  have h3 : Entails.eval a c6658 := derived6658 a h
  have h4 : Entails.eval a c6650 := derived6650 a h
  have h5 : Entails.eval a c7048 := derived7048 a h
  have h6 : Entails.eval a c5603 := h 5602 (by decide)
  have h7 : Entails.eval a c5842 := h 5841 (by decide)
  have h8 : Entails.eval a c5581 := h 5580 (by decide)
  have h9 : Entails.eval a c5526 := h 5525 (by decide)
  have h10 : Entails.eval a c7049 := derived7049 a h
  have h11 : Entails.eval a c4876 := h 4875 (by decide)
  have h12 : Entails.eval a c4903 := h 4902 (by decide)
  have h13 : Entails.eval a c4872 := h 4871 (by decide)
  have h14 : Entails.eval a c6945 := derived6945 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7051 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7051 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4903, some c6825, some c6944, some c6837, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p7051 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7051 : lratChecker f7051 p7051 = .success := by decide +kernel
theorem unsat7051 : Unsatisfiable (PosFin 65) f7051 := by
  apply lratCheckerSound f7051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7051
  · intro a ha; simp [p7051] at ha; subst a; trivial
  · exact checked7051
theorem derived7051 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7051 := by
  apply localUnsat_implies_entails f7051 [c4903, c6825, c6944, c6837] c7051 unsat7051 (by rfl) a
  have h0 : Entails.eval a c4903 := h 4902 (by decide)
  have h1 : Entails.eval a c6825 := derived6825 a h
  have h2 : Entails.eval a c6944 := derived6944 a h
  have h3 : Entails.eval a c6837 := derived6837 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7052 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7052 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6653, some c6638, some c6629, some c6658, some c6650, some c7048, some c5603, some c5581, some c5842, some c7050, some c7051, some c6928, some c4759, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7052 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7052 : lratChecker f7052 p7052 = .success := by decide +kernel
theorem unsat7052 : Unsatisfiable (PosFin 65) f7052 := by
  apply lratCheckerSound f7052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7052
  · intro a ha; simp [p7052] at ha; subst a; trivial
  · exact checked7052
theorem derived7052 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7052 := by
  apply localUnsat_implies_entails f7052 [c6653, c6638, c6629, c6658, c6650, c7048, c5603, c5581, c5842, c7050, c7051, c6928, c4759] c7052 unsat7052 (by rfl) a
  have h0 : Entails.eval a c6653 := derived6653 a h
  have h1 : Entails.eval a c6638 := derived6638 a h
  have h2 : Entails.eval a c6629 := derived6629 a h
  have h3 : Entails.eval a c6658 := derived6658 a h
  have h4 : Entails.eval a c6650 := derived6650 a h
  have h5 : Entails.eval a c7048 := derived7048 a h
  have h6 : Entails.eval a c5603 := h 5602 (by decide)
  have h7 : Entails.eval a c5581 := h 5580 (by decide)
  have h8 : Entails.eval a c5842 := h 5841 (by decide)
  have h9 : Entails.eval a c7050 := derived7050 a h
  have h10 : Entails.eval a c7051 := derived7051 a h
  have h11 : Entails.eval a c6928 := derived6928 a h
  have h12 : Entails.eval a c4759 := h 4758 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7053 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨48, by decide⟩, false), (⟨62, by decide⟩, false), (⟨36, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7053 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7052, some c6653, some c6638, some c6629, some c4675, some c4286, some c4022, some c3853, some c5489, some c3685, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7053 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7053 : lratChecker f7053 p7053 = .success := by decide +kernel
theorem unsat7053 : Unsatisfiable (PosFin 65) f7053 := by
  apply lratCheckerSound f7053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7053
  · intro a ha; simp [p7053] at ha; subst a; trivial
  · exact checked7053
theorem derived7053 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7053 := by
  apply localUnsat_implies_entails f7053 [c7052, c6653, c6638, c6629, c4675, c4286, c4022, c3853, c5489, c3685] c7053 unsat7053 (by rfl) a
  have h0 : Entails.eval a c7052 := derived7052 a h
  have h1 : Entails.eval a c6653 := derived6653 a h
  have h2 : Entails.eval a c6638 := derived6638 a h
  have h3 : Entails.eval a c6629 := derived6629 a h
  have h4 : Entails.eval a c4675 := h 4674 (by decide)
  have h5 : Entails.eval a c4286 := h 4285 (by decide)
  have h6 : Entails.eval a c4022 := h 4021 (by decide)
  have h7 : Entails.eval a c3853 := h 3852 (by decide)
  have h8 : Entails.eval a c5489 := h 5488 (by decide)
  have h9 : Entails.eval a c3685 := h 3684 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7054 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨36, by decide⟩, true), (⟨49, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7054 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7052, some c6653, some c6909, some c6915, some c6860, some c6999, some c4054, some c6918, some c5758, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7054 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7054 : lratChecker f7054 p7054 = .success := by decide +kernel
theorem unsat7054 : Unsatisfiable (PosFin 65) f7054 := by
  apply lratCheckerSound f7054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7054
  · intro a ha; simp [p7054] at ha; subst a; trivial
  · exact checked7054
theorem derived7054 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7054 := by
  apply localUnsat_implies_entails f7054 [c7052, c6653, c6909, c6915, c6860, c6999, c4054, c6918, c5758] c7054 unsat7054 (by rfl) a
  have h0 : Entails.eval a c7052 := derived7052 a h
  have h1 : Entails.eval a c6653 := derived6653 a h
  have h2 : Entails.eval a c6909 := derived6909 a h
  have h3 : Entails.eval a c6915 := derived6915 a h
  have h4 : Entails.eval a c6860 := derived6860 a h
  have h5 : Entails.eval a c6999 := derived6999 a h
  have h6 : Entails.eval a c4054 := h 4053 (by decide)
  have h7 : Entails.eval a c6918 := derived6918 a h
  have h8 : Entails.eval a c5758 := h 5757 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7055 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨56, by decide⟩, false), (⟨36, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7055 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7052, some c6653, some c6638, some c6629, some c4675, some c4286, some c7053, some c4186, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7055 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7055 : lratChecker f7055 p7055 = .success := by decide +kernel
theorem unsat7055 : Unsatisfiable (PosFin 65) f7055 := by
  apply lratCheckerSound f7055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7055
  · intro a ha; simp [p7055] at ha; subst a; trivial
  · exact checked7055
theorem derived7055 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7055 := by
  apply localUnsat_implies_entails f7055 [c7052, c6653, c6638, c6629, c4675, c4286, c7053, c4186] c7055 unsat7055 (by rfl) a
  have h0 : Entails.eval a c7052 := derived7052 a h
  have h1 : Entails.eval a c6653 := derived6653 a h
  have h2 : Entails.eval a c6638 := derived6638 a h
  have h3 : Entails.eval a c6629 := derived6629 a h
  have h4 : Entails.eval a c4675 := h 4674 (by decide)
  have h5 : Entails.eval a c4286 := h 4285 (by decide)
  have h6 : Entails.eval a c7053 := derived7053 a h
  have h7 : Entails.eval a c4186 := h 4185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7056 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨49, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7056 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6638, some c7054, some c7055, some c6933, some c6851, some c6849, some c6925, some c7011, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7056 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7056 : lratChecker f7056 p7056 = .success := by decide +kernel
theorem unsat7056 : Unsatisfiable (PosFin 65) f7056 := by
  apply lratCheckerSound f7056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7056
  · intro a ha; simp [p7056] at ha; subst a; trivial
  · exact checked7056
theorem derived7056 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7056 := by
  apply localUnsat_implies_entails f7056 [c6638, c7054, c7055, c6933, c6851, c6849, c6925, c7011] c7056 unsat7056 (by rfl) a
  have h0 : Entails.eval a c6638 := derived6638 a h
  have h1 : Entails.eval a c7054 := derived7054 a h
  have h2 : Entails.eval a c7055 := derived7055 a h
  have h3 : Entails.eval a c6933 := derived6933 a h
  have h4 : Entails.eval a c6851 := derived6851 a h
  have h5 : Entails.eval a c6849 := derived6849 a h
  have h6 : Entails.eval a c6925 := derived6925 a h
  have h7 : Entails.eval a c7011 := derived7011 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7057 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7057 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7052, some c6638, some c4186, some c5631, some c4216, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7057 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7057 : lratChecker f7057 p7057 = .success := by decide +kernel
theorem unsat7057 : Unsatisfiable (PosFin 65) f7057 := by
  apply lratCheckerSound f7057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7057
  · intro a ha; simp [p7057] at ha; subst a; trivial
  · exact checked7057
theorem derived7057 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7057 := by
  apply localUnsat_implies_entails f7057 [c7052, c6638, c4186, c5631, c4216] c7057 unsat7057 (by rfl) a
  have h0 : Entails.eval a c7052 := derived7052 a h
  have h1 : Entails.eval a c6638 := derived6638 a h
  have h2 : Entails.eval a c4186 := h 4185 (by decide)
  have h3 : Entails.eval a c5631 := h 5630 (by decide)
  have h4 : Entails.eval a c4216 := h 4215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7058 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7058 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7057, some c7052, some c6653, some c6629, some c4898, some c4908, some c4899, some c4900, some c4912, some c7051, some c4903, some c4910, some c4893, some c4891, some c5976, some c5588, some c5850, some c5540, some c6946, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7058 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7058 : lratChecker f7058 p7058 = .success := by decide +kernel
theorem unsat7058 : Unsatisfiable (PosFin 65) f7058 := by
  apply lratCheckerSound f7058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7058
  · intro a ha; simp [p7058] at ha; subst a; trivial
  · exact checked7058
theorem derived7058 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7058 := by
  apply localUnsat_implies_entails f7058 [c7057, c7052, c6653, c6629, c4898, c4908, c4899, c4900, c4912, c7051, c4903, c4910, c4893, c4891, c5976, c5588, c5850, c5540, c6946] c7058 unsat7058 (by rfl) a
  have h0 : Entails.eval a c7057 := derived7057 a h
  have h1 : Entails.eval a c7052 := derived7052 a h
  have h2 : Entails.eval a c6653 := derived6653 a h
  have h3 : Entails.eval a c6629 := derived6629 a h
  have h4 : Entails.eval a c4898 := h 4897 (by decide)
  have h5 : Entails.eval a c4908 := h 4907 (by decide)
  have h6 : Entails.eval a c4899 := h 4898 (by decide)
  have h7 : Entails.eval a c4900 := h 4899 (by decide)
  have h8 : Entails.eval a c4912 := h 4911 (by decide)
  have h9 : Entails.eval a c7051 := derived7051 a h
  have h10 : Entails.eval a c4903 := h 4902 (by decide)
  have h11 : Entails.eval a c4910 := h 4909 (by decide)
  have h12 : Entails.eval a c4893 := h 4892 (by decide)
  have h13 : Entails.eval a c4891 := h 4890 (by decide)
  have h14 : Entails.eval a c5976 := derived5976 a h
  have h15 : Entails.eval a c5588 := h 5587 (by decide)
  have h16 : Entails.eval a c5850 := h 5849 (by decide)
  have h17 : Entails.eval a c5540 := h 5539 (by decide)
  have h18 : Entails.eval a c6946 := derived6946 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7059 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7059 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7058, some c7056, some c6638, some c4734, some c4740, some c4736, some c6926, some c4729, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7059 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7059 : lratChecker f7059 p7059 = .success := by decide +kernel
theorem unsat7059 : Unsatisfiable (PosFin 65) f7059 := by
  apply lratCheckerSound f7059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7059
  · intro a ha; simp [p7059] at ha; subst a; trivial
  · exact checked7059
theorem derived7059 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7059 := by
  apply localUnsat_implies_entails f7059 [c7058, c7056, c6638, c4734, c4740, c4736, c6926, c4729] c7059 unsat7059 (by rfl) a
  have h0 : Entails.eval a c7058 := derived7058 a h
  have h1 : Entails.eval a c7056 := derived7056 a h
  have h2 : Entails.eval a c6638 := derived6638 a h
  have h3 : Entails.eval a c4734 := h 4733 (by decide)
  have h4 : Entails.eval a c4740 := h 4739 (by decide)
  have h5 : Entails.eval a c4736 := h 4735 (by decide)
  have h6 : Entails.eval a c6926 := derived6926 a h
  have h7 : Entails.eval a c4729 := h 4728 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7060 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7060 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6638, some c7052, some c7057, some c7059, some c5585, some c5609, some c3742, some c5758, some c4216, some c4260, some c3836, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7060 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7060 : lratChecker f7060 p7060 = .success := by decide +kernel
theorem unsat7060 : Unsatisfiable (PosFin 65) f7060 := by
  apply lratCheckerSound f7060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7060
  · intro a ha; simp [p7060] at ha; subst a; trivial
  · exact checked7060
theorem derived7060 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7060 := by
  apply localUnsat_implies_entails f7060 [c6638, c7052, c7057, c7059, c5585, c5609, c3742, c5758, c4216, c4260, c3836] c7060 unsat7060 (by rfl) a
  have h0 : Entails.eval a c6638 := derived6638 a h
  have h1 : Entails.eval a c7052 := derived7052 a h
  have h2 : Entails.eval a c7057 := derived7057 a h
  have h3 : Entails.eval a c7059 := derived7059 a h
  have h4 : Entails.eval a c5585 := h 5584 (by decide)
  have h5 : Entails.eval a c5609 := h 5608 (by decide)
  have h6 : Entails.eval a c3742 := h 3741 (by decide)
  have h7 : Entails.eval a c5758 := h 5757 (by decide)
  have h8 : Entails.eval a c4216 := h 4215 (by decide)
  have h9 : Entails.eval a c4260 := h 4259 (by decide)
  have h10 : Entails.eval a c3836 := h 3835 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7061 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true), (⟨48, by decide⟩, false), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7061 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5479, some c5765, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7061 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7061 : lratChecker f7061 p7061 = .success := by decide +kernel
theorem unsat7061 : Unsatisfiable (PosFin 65) f7061 := by
  apply lratCheckerSound f7061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7061
  · intro a ha; simp [p7061] at ha; subst a; trivial
  · exact checked7061
theorem derived7061 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7061 := by
  apply localUnsat_implies_entails f7061 [c5479, c5765] c7061 unsat7061 (by rfl) a
  have h0 : Entails.eval a c5479 := h 5478 (by decide)
  have h1 : Entails.eval a c5765 := h 5764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7062 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨57, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨36, by decide⟩, true), (⟨47, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7062 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7043, some c4812, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7062 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7062 : lratChecker f7062 p7062 = .success := by decide +kernel
theorem unsat7062 : Unsatisfiable (PosFin 65) f7062 := by
  apply lratCheckerSound f7062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7062
  · intro a ha; simp [p7062] at ha; subst a; trivial
  · exact checked7062
theorem derived7062 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7062 := by
  apply localUnsat_implies_entails f7062 [c7043, c4812] c7062 unsat7062 (by rfl) a
  have h0 : Entails.eval a c7043 := derived7043 a h
  have h1 : Entails.eval a c4812 := h 4811 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7063 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨35, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7063 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7061, some c7062, some c4583, some c4573, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7063 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7063 : lratChecker f7063 p7063 = .success := by decide +kernel
theorem unsat7063 : Unsatisfiable (PosFin 65) f7063 := by
  apply lratCheckerSound f7063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7063
  · intro a ha; simp [p7063] at ha; subst a; trivial
  · exact checked7063
theorem derived7063 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7063 := by
  apply localUnsat_implies_entails f7063 [c7061, c7062, c4583, c4573] c7063 unsat7063 (by rfl) a
  have h0 : Entails.eval a c7061 := derived7061 a h
  have h1 : Entails.eval a c7062 := derived7062 a h
  have h2 : Entails.eval a c4583 := h 4582 (by decide)
  have h3 : Entails.eval a c4573 := h 4572 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7064 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, true), (⟨46, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨35, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7064 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4583, some c6808, some c4567, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7064 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7064 : lratChecker f7064 p7064 = .success := by decide +kernel
theorem unsat7064 : Unsatisfiable (PosFin 65) f7064 := by
  apply lratCheckerSound f7064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7064
  · intro a ha; simp [p7064] at ha; subst a; trivial
  · exact checked7064
theorem derived7064 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7064 := by
  apply localUnsat_implies_entails f7064 [c4583, c6808, c4567] c7064 unsat7064 (by rfl) a
  have h0 : Entails.eval a c4583 := h 4582 (by decide)
  have h1 : Entails.eval a c6808 := derived6808 a h
  have h2 : Entails.eval a c4567 := h 4566 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7065 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨50, by decide⟩, true), (⟨46, by decide⟩, false), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨35, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨45, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7065 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7064, some c7042, some c7041, some c5790, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7065 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7065 : lratChecker f7065 p7065 = .success := by decide +kernel
theorem unsat7065 : Unsatisfiable (PosFin 65) f7065 := by
  apply lratCheckerSound f7065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7065
  · intro a ha; simp [p7065] at ha; subst a; trivial
  · exact checked7065
theorem derived7065 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7065 := by
  apply localUnsat_implies_entails f7065 [c7064, c7042, c7041, c5790] c7065 unsat7065 (by rfl) a
  have h0 : Entails.eval a c7064 := derived7064 a h
  have h1 : Entails.eval a c7042 := derived7042 a h
  have h2 : Entails.eval a c7041 := derived7041 a h
  have h3 : Entails.eval a c5790 := h 5789 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7066 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨46, by decide⟩, false), (⟨53, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨35, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7066 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7065, some c7036, some c7031, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7066 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7066 : lratChecker f7066 p7066 = .success := by decide +kernel
theorem unsat7066 : Unsatisfiable (PosFin 65) f7066 := by
  apply lratCheckerSound f7066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7066
  · intro a ha; simp [p7066] at ha; subst a; trivial
  · exact checked7066
theorem derived7066 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7066 := by
  apply localUnsat_implies_entails f7066 [c7065, c7036, c7031] c7066 unsat7066 (by rfl) a
  have h0 : Entails.eval a c7065 := derived7065 a h
  have h1 : Entails.eval a c7036 := derived7036 a h
  have h2 : Entails.eval a c7031 := derived7031 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7067 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨49, by decide⟩, true), (⟨50, by decide⟩, false), (⟨41, by decide⟩, false), (⟨35, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨39, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7067 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4583, some c5460, some c4582, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7067 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7067 : lratChecker f7067 p7067 = .success := by decide +kernel
theorem unsat7067 : Unsatisfiable (PosFin 65) f7067 := by
  apply lratCheckerSound f7067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7067
  · intro a ha; simp [p7067] at ha; subst a; trivial
  · exact checked7067
theorem derived7067 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7067 := by
  apply localUnsat_implies_entails f7067 [c4583, c5460, c4582] c7067 unsat7067 (by rfl) a
  have h0 : Entails.eval a c4583 := h 4582 (by decide)
  have h1 : Entails.eval a c5460 := h 5459 (by decide)
  have h2 : Entails.eval a c4582 := h 4581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7068 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨50, by decide⟩, false), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨41, by decide⟩, false), (⟨35, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7068 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7063, some c7067, some c4161, some c5652, some c4813, some c4815, some c4855, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7068 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7068 : lratChecker f7068 p7068 = .success := by decide +kernel
theorem unsat7068 : Unsatisfiable (PosFin 65) f7068 := by
  apply lratCheckerSound f7068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7068
  · intro a ha; simp [p7068] at ha; subst a; trivial
  · exact checked7068
theorem derived7068 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7068 := by
  apply localUnsat_implies_entails f7068 [c7063, c7067, c4161, c5652, c4813, c4815, c4855] c7068 unsat7068 (by rfl) a
  have h0 : Entails.eval a c7063 := derived7063 a h
  have h1 : Entails.eval a c7067 := derived7067 a h
  have h2 : Entails.eval a c4161 := h 4160 (by decide)
  have h3 : Entails.eval a c5652 := h 5651 (by decide)
  have h4 : Entails.eval a c4813 := h 4812 (by decide)
  have h5 : Entails.eval a c4815 := h 4814 (by decide)
  have h6 : Entails.eval a c4855 := h 4854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7069 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7069 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7060, some c5585, some c6305, some c5609, some c3742, some c4605, some c4114, some c4260, some c7066, some c7068, some c3513, some c4340, some c4363, some c6060, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7069 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7069 : lratChecker f7069 p7069 = .success := by decide +kernel
theorem unsat7069 : Unsatisfiable (PosFin 65) f7069 := by
  apply lratCheckerSound f7069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7069
  · intro a ha; simp [p7069] at ha; subst a; trivial
  · exact checked7069
theorem derived7069 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7069 := by
  apply localUnsat_implies_entails f7069 [c7060, c5585, c6305, c5609, c3742, c4605, c4114, c4260, c7066, c7068, c3513, c4340, c4363, c6060] c7069 unsat7069 (by rfl) a
  have h0 : Entails.eval a c7060 := derived7060 a h
  have h1 : Entails.eval a c5585 := h 5584 (by decide)
  have h2 : Entails.eval a c6305 := derived6305 a h
  have h3 : Entails.eval a c5609 := h 5608 (by decide)
  have h4 : Entails.eval a c3742 := h 3741 (by decide)
  have h5 : Entails.eval a c4605 := h 4604 (by decide)
  have h6 : Entails.eval a c4114 := h 4113 (by decide)
  have h7 : Entails.eval a c4260 := h 4259 (by decide)
  have h8 : Entails.eval a c7066 := derived7066 a h
  have h9 : Entails.eval a c7068 := derived7068 a h
  have h10 : Entails.eval a c3513 := h 3512 (by decide)
  have h11 : Entails.eval a c4340 := h 4339 (by decide)
  have h12 : Entails.eval a c4363 := h 4362 (by decide)
  have h13 : Entails.eval a c6060 := derived6060 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7070 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨40, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7070 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4186, some c5631, some c3774, some c3459, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7070 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7070 : lratChecker f7070 p7070 = .success := by decide +kernel
theorem unsat7070 : Unsatisfiable (PosFin 65) f7070 := by
  apply lratCheckerSound f7070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7070
  · intro a ha; simp [p7070] at ha; subst a; trivial
  · exact checked7070
theorem derived7070 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7070 := by
  apply localUnsat_implies_entails f7070 [c4186, c5631, c3774, c3459] c7070 unsat7070 (by rfl) a
  have h0 : Entails.eval a c4186 := h 4185 (by decide)
  have h1 : Entails.eval a c5631 := h 5630 (by decide)
  have h2 : Entails.eval a c3774 := h 3773 (by decide)
  have h3 : Entails.eval a c3459 := h 3458 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7071 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨53, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7071 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7069, some c7070, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7071 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7071 : lratChecker f7071 p7071 = .success := by decide +kernel
theorem unsat7071 : Unsatisfiable (PosFin 65) f7071 := by
  apply lratCheckerSound f7071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7071
  · intro a ha; simp [p7071] at ha; subst a; trivial
  · exact checked7071
theorem derived7071 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7071 := by
  apply localUnsat_implies_entails f7071 [c7069, c7070] c7071 unsat7071 (by rfl) a
  have h0 : Entails.eval a c7069 := derived7069 a h
  have h1 : Entails.eval a c7070 := derived7070 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7072 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨49, by decide⟩, false), (⟨63, by decide⟩, false), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7072 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5459, some c5775, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7072 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7072 : lratChecker f7072 p7072 = .success := by decide +kernel
theorem unsat7072 : Unsatisfiable (PosFin 65) f7072 := by
  apply lratCheckerSound f7072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7072
  · intro a ha; simp [p7072] at ha; subst a; trivial
  · exact checked7072
theorem derived7072 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7072 := by
  apply localUnsat_implies_entails f7072 [c5459, c5775] c7072 unsat7072 (by rfl) a
  have h0 : Entails.eval a c5459 := h 5458 (by decide)
  have h1 : Entails.eval a c5775 := h 5774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7073 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7073 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7072, some c5772, some c5467, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7073 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7073 : lratChecker f7073 p7073 = .success := by decide +kernel
theorem unsat7073 : Unsatisfiable (PosFin 65) f7073 := by
  apply lratCheckerSound f7073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7073
  · intro a ha; simp [p7073] at ha; subst a; trivial
  · exact checked7073
theorem derived7073 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7073 := by
  apply localUnsat_implies_entails f7073 [c7072, c5772, c5467] c7073 unsat7073 (by rfl) a
  have h0 : Entails.eval a c7072 := derived7072 a h
  have h1 : Entails.eval a c5772 := h 5771 (by decide)
  have h2 : Entails.eval a c5467 := h 5466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7074 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7074 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7071, some c7060, some c4119, some c4118, some c6843, some c3468, some c4107, some c5902, some c4125, some c3475, some c4124, some c7073, some c3822, some c3824, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7074 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7074 : lratChecker f7074 p7074 = .success := by decide +kernel
theorem unsat7074 : Unsatisfiable (PosFin 65) f7074 := by
  apply lratCheckerSound f7074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7074
  · intro a ha; simp [p7074] at ha; subst a; trivial
  · exact checked7074
theorem derived7074 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7074 := by
  apply localUnsat_implies_entails f7074 [c7071, c7060, c4119, c4118, c6843, c3468, c4107, c5902, c4125, c3475, c4124, c7073, c3822, c3824] c7074 unsat7074 (by rfl) a
  have h0 : Entails.eval a c7071 := derived7071 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c4119 := h 4118 (by decide)
  have h3 : Entails.eval a c4118 := h 4117 (by decide)
  have h4 : Entails.eval a c6843 := derived6843 a h
  have h5 : Entails.eval a c3468 := h 3467 (by decide)
  have h6 : Entails.eval a c4107 := h 4106 (by decide)
  have h7 : Entails.eval a c5902 := derived5902 a h
  have h8 : Entails.eval a c4125 := h 4124 (by decide)
  have h9 : Entails.eval a c3475 := h 3474 (by decide)
  have h10 : Entails.eval a c4124 := h 4123 (by decide)
  have h11 : Entails.eval a c7073 := derived7073 a h
  have h12 : Entails.eval a c3822 := h 3821 (by decide)
  have h13 : Entails.eval a c3824 := h 3823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7075 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7075 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7071, some c7060, some c7074, some c4194, some c4193, some c4176, some c4195, some c4174, some c4205, some c4204, some c6193, some c7073, some c3822, some c3824, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7075 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7075 : lratChecker f7075 p7075 = .success := by decide +kernel
theorem unsat7075 : Unsatisfiable (PosFin 65) f7075 := by
  apply lratCheckerSound f7075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7075
  · intro a ha; simp [p7075] at ha; subst a; trivial
  · exact checked7075
theorem derived7075 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7075 := by
  apply localUnsat_implies_entails f7075 [c7071, c7060, c7074, c4194, c4193, c4176, c4195, c4174, c4205, c4204, c6193, c7073, c3822, c3824] c7075 unsat7075 (by rfl) a
  have h0 : Entails.eval a c7071 := derived7071 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c7074 := derived7074 a h
  have h3 : Entails.eval a c4194 := h 4193 (by decide)
  have h4 : Entails.eval a c4193 := h 4192 (by decide)
  have h5 : Entails.eval a c4176 := h 4175 (by decide)
  have h6 : Entails.eval a c4195 := h 4194 (by decide)
  have h7 : Entails.eval a c4174 := h 4173 (by decide)
  have h8 : Entails.eval a c4205 := h 4204 (by decide)
  have h9 : Entails.eval a c4204 := h 4203 (by decide)
  have h10 : Entails.eval a c6193 := derived6193 a h
  have h11 : Entails.eval a c7073 := derived7073 a h
  have h12 : Entails.eval a c3822 := h 3821 (by decide)
  have h13 : Entails.eval a c3824 := h 3823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7076 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7076 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3783, some c3764, some c3763, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7076 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7076 : lratChecker f7076 p7076 = .success := by decide +kernel
theorem unsat7076 : Unsatisfiable (PosFin 65) f7076 := by
  apply lratCheckerSound f7076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7076
  · intro a ha; simp [p7076] at ha; subst a; trivial
  · exact checked7076
theorem derived7076 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7076 := by
  apply localUnsat_implies_entails f7076 [c3783, c3764, c3763] c7076 unsat7076 (by rfl) a
  have h0 : Entails.eval a c3783 := h 3782 (by decide)
  have h1 : Entails.eval a c3764 := h 3763 (by decide)
  have h2 : Entails.eval a c3763 := h 3762 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7077 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7077 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7071, some c7076, some c7075, some c6650, some c5625, some c5629, some c5624, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7077 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7077 : lratChecker f7077 p7077 = .success := by decide +kernel
theorem unsat7077 : Unsatisfiable (PosFin 65) f7077 := by
  apply lratCheckerSound f7077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7077
  · intro a ha; simp [p7077] at ha; subst a; trivial
  · exact checked7077
theorem derived7077 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7077 := by
  apply localUnsat_implies_entails f7077 [c7071, c7076, c7075, c6650, c5625, c5629, c5624] c7077 unsat7077 (by rfl) a
  have h0 : Entails.eval a c7071 := derived7071 a h
  have h1 : Entails.eval a c7076 := derived7076 a h
  have h2 : Entails.eval a c7075 := derived7075 a h
  have h3 : Entails.eval a c6650 := derived6650 a h
  have h4 : Entails.eval a c5625 := h 5624 (by decide)
  have h5 : Entails.eval a c5629 := h 5628 (by decide)
  have h6 : Entails.eval a c5624 := h 5623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7078 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7078 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5028, some c5484, some c5773, some c4602, some c3864, some c4382, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7078 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7078 : lratChecker f7078 p7078 = .success := by decide +kernel
theorem unsat7078 : Unsatisfiable (PosFin 65) f7078 := by
  apply lratCheckerSound f7078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7078
  · intro a ha; simp [p7078] at ha; subst a; trivial
  · exact checked7078
theorem derived7078 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7078 := by
  apply localUnsat_implies_entails f7078 [c5028, c5484, c5773, c4602, c3864, c4382] c7078 unsat7078 (by rfl) a
  have h0 : Entails.eval a c5028 := h 5027 (by decide)
  have h1 : Entails.eval a c5484 := h 5483 (by decide)
  have h2 : Entails.eval a c5773 := h 5772 (by decide)
  have h3 : Entails.eval a c4602 := h 4601 (by decide)
  have h4 : Entails.eval a c3864 := h 3863 (by decide)
  have h5 : Entails.eval a c4382 := h 4381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7079 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨43, by decide⟩, true), (⟨34, by decide⟩, true), (⟨63, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨45, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7079 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4153, some c4234, some c5767, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7079 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7079 : lratChecker f7079 p7079 = .success := by decide +kernel
theorem unsat7079 : Unsatisfiable (PosFin 65) f7079 := by
  apply lratCheckerSound f7079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7079
  · intro a ha; simp [p7079] at ha; subst a; trivial
  · exact checked7079
theorem derived7079 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7079 := by
  apply localUnsat_implies_entails f7079 [c4153, c4234, c5767] c7079 unsat7079 (by rfl) a
  have h0 : Entails.eval a c4153 := h 4152 (by decide)
  have h1 : Entails.eval a c4234 := h 4233 (by decide)
  have h2 : Entails.eval a c5767 := h 5766 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7080 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7080 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7077, some c7071, some c7060, some c7078, some c4800, some c3433, some c6369, some c5416, some c7079, some c5257, some c5481, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7080 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7080 : lratChecker f7080 p7080 = .success := by decide +kernel
theorem unsat7080 : Unsatisfiable (PosFin 65) f7080 := by
  apply lratCheckerSound f7080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7080
  · intro a ha; simp [p7080] at ha; subst a; trivial
  · exact checked7080
theorem derived7080 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7080 := by
  apply localUnsat_implies_entails f7080 [c7077, c7071, c7060, c7078, c4800, c3433, c6369, c5416, c7079, c5257, c5481] c7080 unsat7080 (by rfl) a
  have h0 : Entails.eval a c7077 := derived7077 a h
  have h1 : Entails.eval a c7071 := derived7071 a h
  have h2 : Entails.eval a c7060 := derived7060 a h
  have h3 : Entails.eval a c7078 := derived7078 a h
  have h4 : Entails.eval a c4800 := h 4799 (by decide)
  have h5 : Entails.eval a c3433 := h 3432 (by decide)
  have h6 : Entails.eval a c6369 := derived6369 a h
  have h7 : Entails.eval a c5416 := h 5415 (by decide)
  have h8 : Entails.eval a c7079 := derived7079 a h
  have h9 : Entails.eval a c5257 := h 5256 (by decide)
  have h10 : Entails.eval a c5481 := h 5480 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7080

end CochromaticTwenty.Certificates.FixedCore1
