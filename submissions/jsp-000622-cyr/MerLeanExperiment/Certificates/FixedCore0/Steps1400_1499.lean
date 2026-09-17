import MerLeanExperiment.Certificates.FixedCore0.Steps1300_1399

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8951 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8951 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1192, some c1195, some c1204, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8951 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8951 : lratChecker f8951 p8951 = .success := by decide +kernel
theorem unsat8951 : Unsatisfiable (PosFin 65) f8951 := by
  apply lratCheckerSound f8951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8951
  · intro a ha; simp [p8951] at ha; subst a; trivial
  · exact checked8951
theorem derived8951 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8951 := by
  apply localUnsat_implies_entails f8951 [c1192, c1195, c1204] c8951 unsat8951 (by rfl) a
  have h0 : Entails.eval a c1192 := h 1191 (by decide)
  have h1 : Entails.eval a c1195 := h 1194 (by decide)
  have h2 : Entails.eval a c1204 := h 1203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8952 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8952 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8951, some c8937, some c8905, some c8847, some c8941, some c8948, some c748, some c760, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8952 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8952 : lratChecker f8952 p8952 = .success := by decide +kernel
theorem unsat8952 : Unsatisfiable (PosFin 65) f8952 := by
  apply lratCheckerSound f8952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8952
  · intro a ha; simp [p8952] at ha; subst a; trivial
  · exact checked8952
theorem derived8952 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8952 := by
  apply localUnsat_implies_entails f8952 [c8951, c8937, c8905, c8847, c8941, c8948, c748, c760] c8952 unsat8952 (by rfl) a
  have h0 : Entails.eval a c8951 := derived8951 a h
  have h1 : Entails.eval a c8937 := derived8937 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8941 := derived8941 a h
  have h5 : Entails.eval a c8948 := derived8948 a h
  have h6 : Entails.eval a c748 := h 747 (by decide)
  have h7 : Entails.eval a c760 := h 759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8953 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8953 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8951, some c8921, some c8905, some c8421, some c8952, some c4905, some c299, some c5953, some c6194, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8953 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8953 : lratChecker f8953 p8953 = .success := by decide +kernel
theorem unsat8953 : Unsatisfiable (PosFin 65) f8953 := by
  apply lratCheckerSound f8953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8953
  · intro a ha; simp [p8953] at ha; subst a; trivial
  · exact checked8953
theorem derived8953 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8953 := by
  apply localUnsat_implies_entails f8953 [c8951, c8921, c8905, c8421, c8952, c4905, c299, c5953, c6194] c8953 unsat8953 (by rfl) a
  have h0 : Entails.eval a c8951 := derived8951 a h
  have h1 : Entails.eval a c8921 := derived8921 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8952 := derived8952 a h
  have h5 : Entails.eval a c4905 := h 4904 (by decide)
  have h6 : Entails.eval a c299 := h 298 (by decide)
  have h7 : Entails.eval a c5953 := h 5952 (by decide)
  have h8 : Entails.eval a c6194 := h 6193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8954 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8954 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8921, some c8686, some c8950, some c8953, some c5654, some c6234, some c5673, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8954 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8954 : lratChecker f8954 p8954 = .success := by decide +kernel
theorem unsat8954 : Unsatisfiable (PosFin 65) f8954 := by
  apply lratCheckerSound f8954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8954
  · intro a ha; simp [p8954] at ha; subst a; trivial
  · exact checked8954
theorem derived8954 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8954 := by
  apply localUnsat_implies_entails f8954 [c8921, c8686, c8950, c8953, c5654, c6234, c5673] c8954 unsat8954 (by rfl) a
  have h0 : Entails.eval a c8921 := derived8921 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8950 := derived8950 a h
  have h3 : Entails.eval a c8953 := derived8953 a h
  have h4 : Entails.eval a c5654 := h 5653 (by decide)
  have h5 : Entails.eval a c6234 := h 6233 (by decide)
  have h6 : Entails.eval a c5673 := h 5672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8955 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨25, by decide⟩, true), (⟨62, by decide⟩, true), (⟨20, by decide⟩, false), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8955 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5880, some c5905, some c6134, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8955 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8955 : lratChecker f8955 p8955 = .success := by decide +kernel
theorem unsat8955 : Unsatisfiable (PosFin 65) f8955 := by
  apply lratCheckerSound f8955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8955
  · intro a ha; simp [p8955] at ha; subst a; trivial
  · exact checked8955
theorem derived8955 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8955 := by
  apply localUnsat_implies_entails f8955 [c5880, c5905, c6134] c8955 unsat8955 (by rfl) a
  have h0 : Entails.eval a c5880 := h 5879 (by decide)
  have h1 : Entails.eval a c5905 := h 5904 (by decide)
  have h2 : Entails.eval a c6134 := h 6133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8956 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨63, by decide⟩, false), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8956 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4905, some c299, some c5953, some c6194, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8956 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8956 : lratChecker f8956 p8956 = .success := by decide +kernel
theorem unsat8956 : Unsatisfiable (PosFin 65) f8956 := by
  apply lratCheckerSound f8956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8956
  · intro a ha; simp [p8956] at ha; subst a; trivial
  · exact checked8956
theorem derived8956 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8956 := by
  apply localUnsat_implies_entails f8956 [c4905, c299, c5953, c6194] c8956 unsat8956 (by rfl) a
  have h0 : Entails.eval a c4905 := h 4904 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c5953 := h 5952 (by decide)
  have h3 : Entails.eval a c6194 := h 6193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8957 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨62, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8957 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5880, some c5905, some c6146, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8957 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8957 : lratChecker f8957 p8957 = .success := by decide +kernel
theorem unsat8957 : Unsatisfiable (PosFin 65) f8957 := by
  apply lratCheckerSound f8957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8957
  · intro a ha; simp [p8957] at ha; subst a; trivial
  · exact checked8957
theorem derived8957 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8957 := by
  apply localUnsat_implies_entails f8957 [c5880, c5905, c6146] c8957 unsat8957 (by rfl) a
  have h0 : Entails.eval a c5880 := h 5879 (by decide)
  have h1 : Entails.eval a c5905 := h 5904 (by decide)
  have h2 : Entails.eval a c6146 := h 6145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8958 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8958 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8937, some c8921, some c8905, some c8847, some c8686, some c8421, some c8951, some c8954, some c8893, some c8957, some c7994, some c8956, some c5890, some c8593, some c5878, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8958 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8958 : lratChecker f8958 p8958 = .success := by decide +kernel
theorem unsat8958 : Unsatisfiable (PosFin 65) f8958 := by
  apply lratCheckerSound f8958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8958
  · intro a ha; simp [p8958] at ha; subst a; trivial
  · exact checked8958
theorem derived8958 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8958 := by
  apply localUnsat_implies_entails f8958 [c8937, c8921, c8905, c8847, c8686, c8421, c8951, c8954, c8893, c8957, c7994, c8956, c5890, c8593, c5878] c8958 unsat8958 (by rfl) a
  have h0 : Entails.eval a c8937 := derived8937 a h
  have h1 : Entails.eval a c8921 := derived8921 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8951 := derived8951 a h
  have h7 : Entails.eval a c8954 := derived8954 a h
  have h8 : Entails.eval a c8893 := derived8893 a h
  have h9 : Entails.eval a c8957 := derived8957 a h
  have h10 : Entails.eval a c7994 := derived7994 a h
  have h11 : Entails.eval a c8956 := derived8956 a h
  have h12 : Entails.eval a c5890 := h 5889 (by decide)
  have h13 : Entails.eval a c8593 := derived8593 a h
  have h14 : Entails.eval a c5878 := h 5877 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8959 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8959 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1192, some c1195, some c1213, some c6196, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8959 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8959 : lratChecker f8959 p8959 = .success := by decide +kernel
theorem unsat8959 : Unsatisfiable (PosFin 65) f8959 := by
  apply lratCheckerSound f8959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8959
  · intro a ha; simp [p8959] at ha; subst a; trivial
  · exact checked8959
theorem derived8959 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8959 := by
  apply localUnsat_implies_entails f8959 [c1192, c1195, c1213, c6196] c8959 unsat8959 (by rfl) a
  have h0 : Entails.eval a c1192 := h 1191 (by decide)
  have h1 : Entails.eval a c1195 := h 1194 (by decide)
  have h2 : Entails.eval a c1213 := h 1212 (by decide)
  have h3 : Entails.eval a c6196 := h 6195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8960 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨31, by decide⟩, false), (⟨20, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8960 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8933, some c8959, some c8956, some c8941, some c8957, some c8708, some c5696, some c5691, some c5695, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8960 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8960 : lratChecker f8960 p8960 = .success := by decide +kernel
theorem unsat8960 : Unsatisfiable (PosFin 65) f8960 := by
  apply lratCheckerSound f8960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8960
  · intro a ha; simp [p8960] at ha; subst a; trivial
  · exact checked8960
theorem derived8960 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8960 := by
  apply localUnsat_implies_entails f8960 [c8933, c8959, c8956, c8941, c8957, c8708, c5696, c5691, c5695] c8960 unsat8960 (by rfl) a
  have h0 : Entails.eval a c8933 := derived8933 a h
  have h1 : Entails.eval a c8959 := derived8959 a h
  have h2 : Entails.eval a c8956 := derived8956 a h
  have h3 : Entails.eval a c8941 := derived8941 a h
  have h4 : Entails.eval a c8957 := derived8957 a h
  have h5 : Entails.eval a c8708 := derived8708 a h
  have h6 : Entails.eval a c5696 := h 5695 (by decide)
  have h7 : Entails.eval a c5691 := h 5690 (by decide)
  have h8 : Entails.eval a c5695 := h 5694 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8961 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨63, by decide⟩, false), (⟨62, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8961 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1422, some c1221, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8961 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8961 : lratChecker f8961 p8961 = .success := by decide +kernel
theorem unsat8961 : Unsatisfiable (PosFin 65) f8961 := by
  apply lratCheckerSound f8961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8961
  · intro a ha; simp [p8961] at ha; subst a; trivial
  · exact checked8961
theorem derived8961 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8961 := by
  apply localUnsat_implies_entails f8961 [c1422, c1221] c8961 unsat8961 (by rfl) a
  have h0 : Entails.eval a c1422 := h 1421 (by decide)
  have h1 : Entails.eval a c1221 := h 1220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8962 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8962 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8937, some c8921, some c8905, some c8847, some c8686, some c8421, some c8958, some c8960, some c8893, some c8957, some c8961, some c8956, some c5878, some c6162, some c6273, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8962 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8962 : lratChecker f8962 p8962 = .success := by decide +kernel
theorem unsat8962 : Unsatisfiable (PosFin 65) f8962 := by
  apply lratCheckerSound f8962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8962
  · intro a ha; simp [p8962] at ha; subst a; trivial
  · exact checked8962
theorem derived8962 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8962 := by
  apply localUnsat_implies_entails f8962 [c8937, c8921, c8905, c8847, c8686, c8421, c8958, c8960, c8893, c8957, c8961, c8956, c5878, c6162, c6273] c8962 unsat8962 (by rfl) a
  have h0 : Entails.eval a c8937 := derived8937 a h
  have h1 : Entails.eval a c8921 := derived8921 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8958 := derived8958 a h
  have h7 : Entails.eval a c8960 := derived8960 a h
  have h8 : Entails.eval a c8893 := derived8893 a h
  have h9 : Entails.eval a c8957 := derived8957 a h
  have h10 : Entails.eval a c8961 := derived8961 a h
  have h11 : Entails.eval a c8956 := derived8956 a h
  have h12 : Entails.eval a c5878 := h 5877 (by decide)
  have h13 : Entails.eval a c6162 := h 6161 (by decide)
  have h14 : Entails.eval a c6273 := h 6272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8963 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8963 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8918, some c8916, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8963 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8963 : lratChecker f8963 p8963 = .success := by decide +kernel
theorem unsat8963 : Unsatisfiable (PosFin 65) f8963 := by
  apply lratCheckerSound f8963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8963
  · intro a ha; simp [p8963] at ha; subst a; trivial
  · exact checked8963
theorem derived8963 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8963 := by
  apply localUnsat_implies_entails f8963 [c8918, c8916] c8963 unsat8963 (by rfl) a
  have h0 : Entails.eval a c8918 := derived8918 a h
  have h1 : Entails.eval a c8916 := derived8916 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8964 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨25, by decide⟩, false), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8964 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8940, some c6230, some c806, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8964 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8964 : lratChecker f8964 p8964 = .success := by decide +kernel
theorem unsat8964 : Unsatisfiable (PosFin 65) f8964 := by
  apply lratCheckerSound f8964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8964
  · intro a ha; simp [p8964] at ha; subst a; trivial
  · exact checked8964
theorem derived8964 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8964 := by
  apply localUnsat_implies_entails f8964 [c8940, c6230, c806] c8964 unsat8964 (by rfl) a
  have h0 : Entails.eval a c8940 := derived8940 a h
  have h1 : Entails.eval a c6230 := h 6229 (by decide)
  have h2 : Entails.eval a c806 := h 805 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8965 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨25, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8965 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8964, some c4885, some c4882, some c4868, some c4918, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8965 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8965 : lratChecker f8965 p8965 = .success := by decide +kernel
theorem unsat8965 : Unsatisfiable (PosFin 65) f8965 := by
  apply lratCheckerSound f8965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8965
  · intro a ha; simp [p8965] at ha; subst a; trivial
  · exact checked8965
theorem derived8965 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8965 := by
  apply localUnsat_implies_entails f8965 [c8964, c4885, c4882, c4868, c4918] c8965 unsat8965 (by rfl) a
  have h0 : Entails.eval a c8964 := derived8964 a h
  have h1 : Entails.eval a c4885 := h 4884 (by decide)
  have h2 : Entails.eval a c4882 := h 4881 (by decide)
  have h3 : Entails.eval a c4868 := h 4867 (by decide)
  have h4 : Entails.eval a c4918 := h 4917 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8966 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8966 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8965, some c7994, some c6233, some c6021, some c6015, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8966 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8966 : lratChecker f8966 p8966 = .success := by decide +kernel
theorem unsat8966 : Unsatisfiable (PosFin 65) f8966 := by
  apply lratCheckerSound f8966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8966
  · intro a ha; simp [p8966] at ha; subst a; trivial
  · exact checked8966
theorem derived8966 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8966 := by
  apply localUnsat_implies_entails f8966 [c8965, c7994, c6233, c6021, c6015] c8966 unsat8966 (by rfl) a
  have h0 : Entails.eval a c8965 := derived8965 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c6233 := h 6232 (by decide)
  have h3 : Entails.eval a c6021 := h 6020 (by decide)
  have h4 : Entails.eval a c6015 := h 6014 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8967 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8967 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8966, some c5654, some c6234, some c5673, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8967 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8967 : lratChecker f8967 p8967 = .success := by decide +kernel
theorem unsat8967 : Unsatisfiable (PosFin 65) f8967 := by
  apply lratCheckerSound f8967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8967
  · intro a ha; simp [p8967] at ha; subst a; trivial
  · exact checked8967
theorem derived8967 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8967 := by
  apply localUnsat_implies_entails f8967 [c8966, c5654, c6234, c5673] c8967 unsat8967 (by rfl) a
  have h0 : Entails.eval a c8966 := derived8966 a h
  have h1 : Entails.eval a c5654 := h 5653 (by decide)
  have h2 : Entails.eval a c6234 := h 6233 (by decide)
  have h3 : Entails.eval a c5673 := h 5672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8968 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8968 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8962, some c8907, some c8937, some c8921, some c8905, some c8847, some c8686, some c8421, some c8963, some c8967, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8968 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8968 : lratChecker f8968 p8968 = .success := by decide +kernel
theorem unsat8968 : Unsatisfiable (PosFin 65) f8968 := by
  apply lratCheckerSound f8968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8968
  · intro a ha; simp [p8968] at ha; subst a; trivial
  · exact checked8968
theorem derived8968 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8968 := by
  apply localUnsat_implies_entails f8968 [c8962, c8907, c8937, c8921, c8905, c8847, c8686, c8421, c8963, c8967] c8968 unsat8968 (by rfl) a
  have h0 : Entails.eval a c8962 := derived8962 a h
  have h1 : Entails.eval a c8907 := derived8907 a h
  have h2 : Entails.eval a c8937 := derived8937 a h
  have h3 : Entails.eval a c8921 := derived8921 a h
  have h4 : Entails.eval a c8905 := derived8905 a h
  have h5 : Entails.eval a c8847 := derived8847 a h
  have h6 : Entails.eval a c8686 := derived8686 a h
  have h7 : Entails.eval a c8421 := derived8421 a h
  have h8 : Entails.eval a c8963 := derived8963 a h
  have h9 : Entails.eval a c8967 := derived8967 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8969 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8969 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8847, some c8937, some c8962, some c8921, some c8968, some c8893, some c8918, some c8907, some c8905, some c8686, some c8421, some c4900, some c1284, some c5658, some c4453, some c8939, some c761, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8969 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8969 : lratChecker f8969 p8969 = .success := by decide +kernel
theorem unsat8969 : Unsatisfiable (PosFin 65) f8969 := by
  apply lratCheckerSound f8969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8969
  · intro a ha; simp [p8969] at ha; subst a; trivial
  · exact checked8969
theorem derived8969 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8969 := by
  apply localUnsat_implies_entails f8969 [c8847, c8937, c8962, c8921, c8968, c8893, c8918, c8907, c8905, c8686, c8421, c4900, c1284, c5658, c4453, c8939, c761] c8969 unsat8969 (by rfl) a
  have h0 : Entails.eval a c8847 := derived8847 a h
  have h1 : Entails.eval a c8937 := derived8937 a h
  have h2 : Entails.eval a c8962 := derived8962 a h
  have h3 : Entails.eval a c8921 := derived8921 a h
  have h4 : Entails.eval a c8968 := derived8968 a h
  have h5 : Entails.eval a c8893 := derived8893 a h
  have h6 : Entails.eval a c8918 := derived8918 a h
  have h7 : Entails.eval a c8907 := derived8907 a h
  have h8 : Entails.eval a c8905 := derived8905 a h
  have h9 : Entails.eval a c8686 := derived8686 a h
  have h10 : Entails.eval a c8421 := derived8421 a h
  have h11 : Entails.eval a c4900 := h 4899 (by decide)
  have h12 : Entails.eval a c1284 := h 1283 (by decide)
  have h13 : Entails.eval a c5658 := h 5657 (by decide)
  have h14 : Entails.eval a c4453 := h 4452 (by decide)
  have h15 : Entails.eval a c8939 := derived8939 a h
  have h16 : Entails.eval a c761 := h 760 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8970 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8970 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8847, some c8937, some c8962, some c8921, some c8968, some c8893, some c8918, some c8905, some c8969, some c7994, some c6233, some c6021, some c6015, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8970 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8970 : lratChecker f8970 p8970 = .success := by decide +kernel
theorem unsat8970 : Unsatisfiable (PosFin 65) f8970 := by
  apply lratCheckerSound f8970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8970
  · intro a ha; simp [p8970] at ha; subst a; trivial
  · exact checked8970
theorem derived8970 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8970 := by
  apply localUnsat_implies_entails f8970 [c8847, c8937, c8962, c8921, c8968, c8893, c8918, c8905, c8969, c7994, c6233, c6021, c6015] c8970 unsat8970 (by rfl) a
  have h0 : Entails.eval a c8847 := derived8847 a h
  have h1 : Entails.eval a c8937 := derived8937 a h
  have h2 : Entails.eval a c8962 := derived8962 a h
  have h3 : Entails.eval a c8921 := derived8921 a h
  have h4 : Entails.eval a c8968 := derived8968 a h
  have h5 : Entails.eval a c8893 := derived8893 a h
  have h6 : Entails.eval a c8918 := derived8918 a h
  have h7 : Entails.eval a c8905 := derived8905 a h
  have h8 : Entails.eval a c8969 := derived8969 a h
  have h9 : Entails.eval a c7994 := derived7994 a h
  have h10 : Entails.eval a c6233 := h 6232 (by decide)
  have h11 : Entails.eval a c6021 := h 6020 (by decide)
  have h12 : Entails.eval a c6015 := h 6014 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8971 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8971 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8962, some c8937, some c8921, some c8847, some c8686, some c8907, some c8968, some c8893, some c8918, some c8970, some c5652, some c1280, some c4721, some c5632, some c5512, some c273, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8971 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8971 : lratChecker f8971 p8971 = .success := by decide +kernel
theorem unsat8971 : Unsatisfiable (PosFin 65) f8971 := by
  apply lratCheckerSound f8971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8971
  · intro a ha; simp [p8971] at ha; subst a; trivial
  · exact checked8971
theorem derived8971 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8971 := by
  apply localUnsat_implies_entails f8971 [c8962, c8937, c8921, c8847, c8686, c8907, c8968, c8893, c8918, c8970, c5652, c1280, c4721, c5632, c5512, c273] c8971 unsat8971 (by rfl) a
  have h0 : Entails.eval a c8962 := derived8962 a h
  have h1 : Entails.eval a c8937 := derived8937 a h
  have h2 : Entails.eval a c8921 := derived8921 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8907 := derived8907 a h
  have h6 : Entails.eval a c8968 := derived8968 a h
  have h7 : Entails.eval a c8893 := derived8893 a h
  have h8 : Entails.eval a c8918 := derived8918 a h
  have h9 : Entails.eval a c8970 := derived8970 a h
  have h10 : Entails.eval a c5652 := h 5651 (by decide)
  have h11 : Entails.eval a c1280 := h 1279 (by decide)
  have h12 : Entails.eval a c4721 := h 4720 (by decide)
  have h13 : Entails.eval a c5632 := h 5631 (by decide)
  have h14 : Entails.eval a c5512 := h 5511 (by decide)
  have h15 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8972 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8972 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1199, some c1207, some c1190, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8972 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8972 : lratChecker f8972 p8972 = .success := by decide +kernel
theorem unsat8972 : Unsatisfiable (PosFin 65) f8972 := by
  apply lratCheckerSound f8972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8972
  · intro a ha; simp [p8972] at ha; subst a; trivial
  · exact checked8972
theorem derived8972 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8972 := by
  apply localUnsat_implies_entails f8972 [c1199, c1207, c1190] c8972 unsat8972 (by rfl) a
  have h0 : Entails.eval a c1199 := h 1198 (by decide)
  have h1 : Entails.eval a c1207 := h 1206 (by decide)
  have h2 : Entails.eval a c1190 := h 1189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8973 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨31, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8973 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5694, some c5691, some c5695, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8973 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8973 : lratChecker f8973 p8973 = .success := by decide +kernel
theorem unsat8973 : Unsatisfiable (PosFin 65) f8973 := by
  apply lratCheckerSound f8973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8973
  · intro a ha; simp [p8973] at ha; subst a; trivial
  · exact checked8973
theorem derived8973 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8973 := by
  apply localUnsat_implies_entails f8973 [c5694, c5691, c5695] c8973 unsat8973 (by rfl) a
  have h0 : Entails.eval a c5694 := h 5693 (by decide)
  have h1 : Entails.eval a c5691 := h 5690 (by decide)
  have h2 : Entails.eval a c5695 := h 5694 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8974 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨31, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8974 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6176, some c6178, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8974 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8974 : lratChecker f8974 p8974 = .success := by decide +kernel
theorem unsat8974 : Unsatisfiable (PosFin 65) f8974 := by
  apply lratCheckerSound f8974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8974
  · intro a ha; simp [p8974] at ha; subst a; trivial
  · exact checked8974
theorem derived8974 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8974 := by
  apply localUnsat_implies_entails f8974 [c6176, c6178] c8974 unsat8974 (by rfl) a
  have h0 : Entails.eval a c6176 := h 6175 (by decide)
  have h1 : Entails.eval a c6178 := h 6177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8975 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨31, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8975 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8933, some c8973, some c8974, some c5633, some c5630, some c5634, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8975 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8975 : lratChecker f8975 p8975 = .success := by decide +kernel
theorem unsat8975 : Unsatisfiable (PosFin 65) f8975 := by
  apply lratCheckerSound f8975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8975
  · intro a ha; simp [p8975] at ha; subst a; trivial
  · exact checked8975
theorem derived8975 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8975 := by
  apply localUnsat_implies_entails f8975 [c8933, c8973, c8974, c5633, c5630, c5634] c8975 unsat8975 (by rfl) a
  have h0 : Entails.eval a c8933 := derived8933 a h
  have h1 : Entails.eval a c8973 := derived8973 a h
  have h2 : Entails.eval a c8974 := derived8974 a h
  have h3 : Entails.eval a c5633 := h 5632 (by decide)
  have h4 : Entails.eval a c5630 := h 5629 (by decide)
  have h5 : Entails.eval a c5634 := h 5633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8976 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8976 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8937, some c8921, some c8686, some c8905, some c8971, some c8975, some c8893, some c8962, some c8972, some c8847, some c8421, some c4900, some c1284, some c3679, some c4453, some c4227, some c758, some c958, some c956, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8976 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8976 : lratChecker f8976 p8976 = .success := by decide +kernel
theorem unsat8976 : Unsatisfiable (PosFin 65) f8976 := by
  apply lratCheckerSound f8976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8976
  · intro a ha; simp [p8976] at ha; subst a; trivial
  · exact checked8976
theorem derived8976 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8976 := by
  apply localUnsat_implies_entails f8976 [c8937, c8921, c8686, c8905, c8971, c8975, c8893, c8962, c8972, c8847, c8421, c4900, c1284, c3679, c4453, c4227, c758, c958, c956] c8976 unsat8976 (by rfl) a
  have h0 : Entails.eval a c8937 := derived8937 a h
  have h1 : Entails.eval a c8921 := derived8921 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8905 := derived8905 a h
  have h4 : Entails.eval a c8971 := derived8971 a h
  have h5 : Entails.eval a c8975 := derived8975 a h
  have h6 : Entails.eval a c8893 := derived8893 a h
  have h7 : Entails.eval a c8962 := derived8962 a h
  have h8 : Entails.eval a c8972 := derived8972 a h
  have h9 : Entails.eval a c8847 := derived8847 a h
  have h10 : Entails.eval a c8421 := derived8421 a h
  have h11 : Entails.eval a c4900 := h 4899 (by decide)
  have h12 : Entails.eval a c1284 := h 1283 (by decide)
  have h13 : Entails.eval a c3679 := h 3678 (by decide)
  have h14 : Entails.eval a c4453 := h 4452 (by decide)
  have h15 : Entails.eval a c4227 := h 4226 (by decide)
  have h16 : Entails.eval a c758 := h 757 (by decide)
  have h17 : Entails.eval a c958 := h 957 (by decide)
  have h18 : Entails.eval a c956 := h 955 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8977 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨31, by decide⟩, false), (⟨53, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8977 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c839, some c831, some c829, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8977 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8977 : lratChecker f8977 p8977 = .success := by decide +kernel
theorem unsat8977 : Unsatisfiable (PosFin 65) f8977 := by
  apply lratCheckerSound f8977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8977
  · intro a ha; simp [p8977] at ha; subst a; trivial
  · exact checked8977
theorem derived8977 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8977 := by
  apply localUnsat_implies_entails f8977 [c839, c831, c829] c8977 unsat8977 (by rfl) a
  have h0 : Entails.eval a c839 := h 838 (by decide)
  have h1 : Entails.eval a c831 := h 830 (by decide)
  have h2 : Entails.eval a c829 := h 828 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8978 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8978 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8921, some c8937, some c8971, some c8686, some c8905, some c8975, some c8977, some c8962, some c8972, some c8421, some c8976, some c4905, some c3681, some c4221, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8978 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8978 : lratChecker f8978 p8978 = .success := by decide +kernel
theorem unsat8978 : Unsatisfiable (PosFin 65) f8978 := by
  apply lratCheckerSound f8978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8978
  · intro a ha; simp [p8978] at ha; subst a; trivial
  · exact checked8978
theorem derived8978 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8978 := by
  apply localUnsat_implies_entails f8978 [c8921, c8937, c8971, c8686, c8905, c8975, c8977, c8962, c8972, c8421, c8976, c4905, c3681, c4221] c8978 unsat8978 (by rfl) a
  have h0 : Entails.eval a c8921 := derived8921 a h
  have h1 : Entails.eval a c8937 := derived8937 a h
  have h2 : Entails.eval a c8971 := derived8971 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c8905 := derived8905 a h
  have h5 : Entails.eval a c8975 := derived8975 a h
  have h6 : Entails.eval a c8977 := derived8977 a h
  have h7 : Entails.eval a c8962 := derived8962 a h
  have h8 : Entails.eval a c8972 := derived8972 a h
  have h9 : Entails.eval a c8421 := derived8421 a h
  have h10 : Entails.eval a c8976 := derived8976 a h
  have h11 : Entails.eval a c4905 := h 4904 (by decide)
  have h12 : Entails.eval a c3681 := h 3680 (by decide)
  have h13 : Entails.eval a c4221 := h 4220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8979 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8979 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8905, some c8847, some c8686, some c8921, some c8937, some c8971, some c8975, some c8893, some c8978, some c5692, some c6173, some c5632, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8979 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8979 : lratChecker f8979 p8979 = .success := by decide +kernel
theorem unsat8979 : Unsatisfiable (PosFin 65) f8979 := by
  apply lratCheckerSound f8979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8979
  · intro a ha; simp [p8979] at ha; subst a; trivial
  · exact checked8979
theorem derived8979 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8979 := by
  apply localUnsat_implies_entails f8979 [c8905, c8847, c8686, c8921, c8937, c8971, c8975, c8893, c8978, c5692, c6173, c5632] c8979 unsat8979 (by rfl) a
  have h0 : Entails.eval a c8905 := derived8905 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8921 := derived8921 a h
  have h4 : Entails.eval a c8937 := derived8937 a h
  have h5 : Entails.eval a c8971 := derived8971 a h
  have h6 : Entails.eval a c8975 := derived8975 a h
  have h7 : Entails.eval a c8893 := derived8893 a h
  have h8 : Entails.eval a c8978 := derived8978 a h
  have h9 : Entails.eval a c5692 := h 5691 (by decide)
  have h10 : Entails.eval a c6173 := h 6172 (by decide)
  have h11 : Entails.eval a c5632 := h 5631 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8980 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8980 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8853, some c794, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8980 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8980 : lratChecker f8980 p8980 = .success := by decide +kernel
theorem unsat8980 : Unsatisfiable (PosFin 65) f8980 := by
  apply lratCheckerSound f8980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8980
  · intro a ha; simp [p8980] at ha; subst a; trivial
  · exact checked8980
theorem derived8980 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8980 := by
  apply localUnsat_implies_entails f8980 [c8853, c794] c8980 unsat8980 (by rfl) a
  have h0 : Entails.eval a c8853 := derived8853 a h
  have h1 : Entails.eval a c794 := h 793 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8981 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8981 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8421, some c8905, some c8930, some c8689, some c8847, some c8980, some c8914, some c8910, some c8909, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8981 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8981 : lratChecker f8981 p8981 = .success := by decide +kernel
theorem unsat8981 : Unsatisfiable (PosFin 65) f8981 := by
  apply lratCheckerSound f8981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8981
  · intro a ha; simp [p8981] at ha; subst a; trivial
  · exact checked8981
theorem derived8981 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8981 := by
  apply localUnsat_implies_entails f8981 [c8686, c8421, c8905, c8930, c8689, c8847, c8980, c8914, c8910, c8909] c8981 unsat8981 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8930 := derived8930 a h
  have h4 : Entails.eval a c8689 := derived8689 a h
  have h5 : Entails.eval a c8847 := derived8847 a h
  have h6 : Entails.eval a c8980 := derived8980 a h
  have h7 : Entails.eval a c8914 := derived8914 a h
  have h8 : Entails.eval a c8910 := derived8910 a h
  have h9 : Entails.eval a c8909 := derived8909 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8982 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8982 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5902, some c5876, some c8928, some c6136, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p8982 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8982 : lratChecker f8982 p8982 = .success := by decide +kernel
theorem unsat8982 : Unsatisfiable (PosFin 65) f8982 := by
  apply lratCheckerSound f8982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8982
  · intro a ha; simp [p8982] at ha; subst a; trivial
  · exact checked8982
theorem derived8982 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8982 := by
  apply localUnsat_implies_entails f8982 [c5902, c5876, c8928, c6136] c8982 unsat8982 (by rfl) a
  have h0 : Entails.eval a c5902 := h 5901 (by decide)
  have h1 : Entails.eval a c5876 := h 5875 (by decide)
  have h2 : Entails.eval a c8928 := derived8928 a h
  have h3 : Entails.eval a c6136 := h 6135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8983 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8983 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8905, some c8847, some c8686, some c8421, some c8930, some c8689, some c8981, some c8929, some c8982, some c7994, some c295, some c6192, some c6139, some c5870, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8983 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8983 : lratChecker f8983 p8983 = .success := by decide +kernel
theorem unsat8983 : Unsatisfiable (PosFin 65) f8983 := by
  apply lratCheckerSound f8983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8983
  · intro a ha; simp [p8983] at ha; subst a; trivial
  · exact checked8983
theorem derived8983 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8983 := by
  apply localUnsat_implies_entails f8983 [c8905, c8847, c8686, c8421, c8930, c8689, c8981, c8929, c8982, c7994, c295, c6192, c6139, c5870] c8983 unsat8983 (by rfl) a
  have h0 : Entails.eval a c8905 := derived8905 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8930 := derived8930 a h
  have h5 : Entails.eval a c8689 := derived8689 a h
  have h6 : Entails.eval a c8981 := derived8981 a h
  have h7 : Entails.eval a c8929 := derived8929 a h
  have h8 : Entails.eval a c8982 := derived8982 a h
  have h9 : Entails.eval a c7994 := derived7994 a h
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c6192 := h 6191 (by decide)
  have h12 : Entails.eval a c6139 := h 6138 (by decide)
  have h13 : Entails.eval a c5870 := h 5869 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8984 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8984 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1191, some c1407, some c8938, some c1408, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8984 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8984 : lratChecker f8984 p8984 = .success := by decide +kernel
theorem unsat8984 : Unsatisfiable (PosFin 65) f8984 := by
  apply lratCheckerSound f8984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8984
  · intro a ha; simp [p8984] at ha; subst a; trivial
  · exact checked8984
theorem derived8984 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8984 := by
  apply localUnsat_implies_entails f8984 [c1191, c1407, c8938, c1408] c8984 unsat8984 (by rfl) a
  have h0 : Entails.eval a c1191 := h 1190 (by decide)
  have h1 : Entails.eval a c1407 := h 1406 (by decide)
  have h2 : Entails.eval a c8938 := derived8938 a h
  have h3 : Entails.eval a c1408 := h 1407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8985 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8985 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1129, some c4438, some c747, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8985 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8985 : lratChecker f8985 p8985 = .success := by decide +kernel
theorem unsat8985 : Unsatisfiable (PosFin 65) f8985 := by
  apply lratCheckerSound f8985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8985
  · intro a ha; simp [p8985] at ha; subst a; trivial
  · exact checked8985
theorem derived8985 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8985 := by
  apply localUnsat_implies_entails f8985 [c1129, c4438, c747] c8985 unsat8985 (by rfl) a
  have h0 : Entails.eval a c1129 := h 1128 (by decide)
  have h1 : Entails.eval a c4438 := h 4437 (by decide)
  have h2 : Entails.eval a c747 := h 746 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8986 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨23, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8986 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6155, some c6149, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p8986 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8986 : lratChecker f8986 p8986 = .success := by decide +kernel
theorem unsat8986 : Unsatisfiable (PosFin 65) f8986 := by
  apply lratCheckerSound f8986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8986
  · intro a ha; simp [p8986] at ha; subst a; trivial
  · exact checked8986
theorem derived8986 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8986 := by
  apply localUnsat_implies_entails f8986 [c6155, c6149] c8986 unsat8986 (by rfl) a
  have h0 : Entails.eval a c6155 := h 6154 (by decide)
  have h1 : Entails.eval a c6149 := h 6148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8987 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8987 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8604, some c4906, some c4908, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8987 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8987 : lratChecker f8987 p8987 = .success := by decide +kernel
theorem unsat8987 : Unsatisfiable (PosFin 65) f8987 := by
  apply lratCheckerSound f8987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8987
  · intro a ha; simp [p8987] at ha; subst a; trivial
  · exact checked8987
theorem derived8987 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8987 := by
  apply localUnsat_implies_entails f8987 [c8604, c4906, c4908] c8987 unsat8987 (by rfl) a
  have h0 : Entails.eval a c8604 := derived8604 a h
  have h1 : Entails.eval a c4906 := h 4905 (by decide)
  have h2 : Entails.eval a c4908 := h 4907 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8988 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨23, by decide⟩, true), (⟨54, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8988 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8957, some c8964, some c8986, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8988 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8988 : lratChecker f8988 p8988 = .success := by decide +kernel
theorem unsat8988 : Unsatisfiable (PosFin 65) f8988 := by
  apply lratCheckerSound f8988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8988
  · intro a ha; simp [p8988] at ha; subst a; trivial
  · exact checked8988
theorem derived8988 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8988 := by
  apply localUnsat_implies_entails f8988 [c8957, c8964, c8986] c8988 unsat8988 (by rfl) a
  have h0 : Entails.eval a c8957 := derived8957 a h
  have h1 : Entails.eval a c8964 := derived8964 a h
  have h2 : Entails.eval a c8986 := derived8986 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8989 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨54, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8989 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8988, some c5430, some c171, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8989 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8989 : lratChecker f8989 p8989 = .success := by decide +kernel
theorem unsat8989 : Unsatisfiable (PosFin 65) f8989 := by
  apply lratCheckerSound f8989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8989
  · intro a ha; simp [p8989] at ha; subst a; trivial
  · exact checked8989
theorem derived8989 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8989 := by
  apply localUnsat_implies_entails f8989 [c8988, c5430, c171] c8989 unsat8989 (by rfl) a
  have h0 : Entails.eval a c8988 := derived8988 a h
  have h1 : Entails.eval a c5430 := h 5429 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8990 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8990 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8987, some c8985, some c8989, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8990 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8990 : lratChecker f8990 p8990 = .success := by decide +kernel
theorem unsat8990 : Unsatisfiable (PosFin 65) f8990 := by
  apply lratCheckerSound f8990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8990
  · intro a ha; simp [p8990] at ha; subst a; trivial
  · exact checked8990
theorem derived8990 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8990 := by
  apply localUnsat_implies_entails f8990 [c8987, c8985, c8989] c8990 unsat8990 (by rfl) a
  have h0 : Entails.eval a c8987 := derived8987 a h
  have h1 : Entails.eval a c8985 := derived8985 a h
  have h2 : Entails.eval a c8989 := derived8989 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8991 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨54, by decide⟩, true), (⟨8, by decide⟩, false), (⟨20, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8991 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c790, some c5877, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8991 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8991 : lratChecker f8991 p8991 = .success := by decide +kernel
theorem unsat8991 : Unsatisfiable (PosFin 65) f8991 := by
  apply lratCheckerSound f8991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8991
  · intro a ha; simp [p8991] at ha; subst a; trivial
  · exact checked8991
theorem derived8991 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8991 := by
  apply localUnsat_implies_entails f8991 [c790, c5877] c8991 unsat8991 (by rfl) a
  have h0 : Entails.eval a c790 := h 789 (by decide)
  have h1 : Entails.eval a c5877 := h 5876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8992 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8992 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8987, some c8990, some c8991, some c6152, some c5628, some c5654, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8992 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8992 : lratChecker f8992 p8992 = .success := by decide +kernel
theorem unsat8992 : Unsatisfiable (PosFin 65) f8992 := by
  apply lratCheckerSound f8992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8992
  · intro a ha; simp [p8992] at ha; subst a; trivial
  · exact checked8992
theorem derived8992 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8992 := by
  apply localUnsat_implies_entails f8992 [c8987, c8990, c8991, c6152, c5628, c5654] c8992 unsat8992 (by rfl) a
  have h0 : Entails.eval a c8987 := derived8987 a h
  have h1 : Entails.eval a c8990 := derived8990 a h
  have h2 : Entails.eval a c8991 := derived8991 a h
  have h3 : Entails.eval a c6152 := h 6151 (by decide)
  have h4 : Entails.eval a c5628 := h 5627 (by decide)
  have h5 : Entails.eval a c5654 := h 5653 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8993 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨23, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8993 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4909, some c301, some c6144, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8993 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8993 : lratChecker f8993 p8993 = .success := by decide +kernel
theorem unsat8993 : Unsatisfiable (PosFin 65) f8993 := by
  apply lratCheckerSound f8993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8993
  · intro a ha; simp [p8993] at ha; subst a; trivial
  · exact checked8993
theorem derived8993 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8993 := by
  apply localUnsat_implies_entails f8993 [c4909, c301, c6144] c8993 unsat8993 (by rfl) a
  have h0 : Entails.eval a c4909 := h 4908 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c6144 := h 6143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8994 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8994 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8985, some c8993, some c8957, some c5430, some c171, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8994 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8994 : lratChecker f8994 p8994 = .success := by decide +kernel
theorem unsat8994 : Unsatisfiable (PosFin 65) f8994 := by
  apply lratCheckerSound f8994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8994
  · intro a ha; simp [p8994] at ha; subst a; trivial
  · exact checked8994
theorem derived8994 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8994 := by
  apply localUnsat_implies_entails f8994 [c8985, c8993, c8957, c5430, c171] c8994 unsat8994 (by rfl) a
  have h0 : Entails.eval a c8985 := derived8985 a h
  have h1 : Entails.eval a c8993 := derived8993 a h
  have h2 : Entails.eval a c8957 := derived8957 a h
  have h3 : Entails.eval a c5430 := h 5429 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8995 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨54, by decide⟩, true), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8995 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4884, some c790, some c5877, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8995 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8995 : lratChecker f8995 p8995 = .success := by decide +kernel
theorem unsat8995 : Unsatisfiable (PosFin 65) f8995 := by
  apply lratCheckerSound f8995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8995
  · intro a ha; simp [p8995] at ha; subst a; trivial
  · exact checked8995
theorem derived8995 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8995 := by
  apply localUnsat_implies_entails f8995 [c4884, c790, c5877] c8995 unsat8995 (by rfl) a
  have h0 : Entails.eval a c4884 := h 4883 (by decide)
  have h1 : Entails.eval a c790 := h 789 (by decide)
  have h2 : Entails.eval a c5877 := h 5876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8996 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8996 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8994, some c8995, some c8993, some c6154, some c5652, some c5637, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8996 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8996 : lratChecker f8996 p8996 = .success := by decide +kernel
theorem unsat8996 : Unsatisfiable (PosFin 65) f8996 := by
  apply lratCheckerSound f8996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8996
  · intro a ha; simp [p8996] at ha; subst a; trivial
  · exact checked8996
theorem derived8996 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8996 := by
  apply localUnsat_implies_entails f8996 [c8994, c8995, c8993, c6154, c5652, c5637] c8996 unsat8996 (by rfl) a
  have h0 : Entails.eval a c8994 := derived8994 a h
  have h1 : Entails.eval a c8995 := derived8995 a h
  have h2 : Entails.eval a c8993 := derived8993 a h
  have h3 : Entails.eval a c6154 := h 6153 (by decide)
  have h4 : Entails.eval a c5652 := h 5651 (by decide)
  have h5 : Entails.eval a c5637 := h 5636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8997 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨1, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8997 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8992, some c8996, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8997 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8997 : lratChecker f8997 p8997 = .success := by decide +kernel
theorem unsat8997 : Unsatisfiable (PosFin 65) f8997 := by
  apply lratCheckerSound f8997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8997
  · intro a ha; simp [p8997] at ha; subst a; trivial
  · exact checked8997
theorem derived8997 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8997 := by
  apply localUnsat_implies_entails f8997 [c8992, c8996] c8997 unsat8997 (by rfl) a
  have h0 : Entails.eval a c8992 := derived8992 a h
  have h1 : Entails.eval a c8996 := derived8996 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8998 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8998 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8847, some c8905, some c8983, some c8920, some c8979, some c8421, some c8984, some c8997, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8998 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8998 : lratChecker f8998 p8998 = .success := by decide +kernel
theorem unsat8998 : Unsatisfiable (PosFin 65) f8998 := by
  apply lratCheckerSound f8998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8998
  · intro a ha; simp [p8998] at ha; subst a; trivial
  · exact checked8998
theorem derived8998 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8998 := by
  apply localUnsat_implies_entails f8998 [c8686, c8847, c8905, c8983, c8920, c8979, c8421, c8984, c8997] c8998 unsat8998 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8983 := derived8983 a h
  have h4 : Entails.eval a c8920 := derived8920 a h
  have h5 : Entails.eval a c8979 := derived8979 a h
  have h6 : Entails.eval a c8421 := derived8421 a h
  have h7 : Entails.eval a c8984 := derived8984 a h
  have h8 : Entails.eval a c8997 := derived8997 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8999 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8999 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8998, some c8907, some c8686, some c8847, some c8905, some c8983, some c8920, some c8421, some c8967, some c8963, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8999 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8999 : lratChecker f8999 p8999 = .success := by decide +kernel
theorem unsat8999 : Unsatisfiable (PosFin 65) f8999 := by
  apply lratCheckerSound f8999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8999
  · intro a ha; simp [p8999] at ha; subst a; trivial
  · exact checked8999
theorem derived8999 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8999 := by
  apply localUnsat_implies_entails f8999 [c8998, c8907, c8686, c8847, c8905, c8983, c8920, c8421, c8967, c8963] c8999 unsat8999 (by rfl) a
  have h0 : Entails.eval a c8998 := derived8998 a h
  have h1 : Entails.eval a c8907 := derived8907 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8905 := derived8905 a h
  have h5 : Entails.eval a c8983 := derived8983 a h
  have h6 : Entails.eval a c8920 := derived8920 a h
  have h7 : Entails.eval a c8421 := derived8421 a h
  have h8 : Entails.eval a c8967 := derived8967 a h
  have h9 : Entails.eval a c8963 := derived8963 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9000 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨23, by decide⟩, false), (⟨54, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9000 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8983, some c8686, some c8847, some c8905, some c8920, some c8979, some c8998, some c8999, some c8885, some c8907, some c4900, some c1284, some c3679, some c4453, some c4227, some c752, some c964, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9000 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9000 : lratChecker f9000 p9000 = .success := by decide +kernel
theorem unsat9000 : Unsatisfiable (PosFin 65) f9000 := by
  apply lratCheckerSound f9000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9000
  · intro a ha; simp [p9000] at ha; subst a; trivial
  · exact checked9000
theorem derived9000 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9000 := by
  apply localUnsat_implies_entails f9000 [c8421, c8983, c8686, c8847, c8905, c8920, c8979, c8998, c8999, c8885, c8907, c4900, c1284, c3679, c4453, c4227, c752, c964] c9000 unsat9000 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8983 := derived8983 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8905 := derived8905 a h
  have h5 : Entails.eval a c8920 := derived8920 a h
  have h6 : Entails.eval a c8979 := derived8979 a h
  have h7 : Entails.eval a c8998 := derived8998 a h
  have h8 : Entails.eval a c8999 := derived8999 a h
  have h9 : Entails.eval a c8885 := derived8885 a h
  have h10 : Entails.eval a c8907 := derived8907 a h
  have h11 : Entails.eval a c4900 := h 4899 (by decide)
  have h12 : Entails.eval a c1284 := h 1283 (by decide)
  have h13 : Entails.eval a c3679 := h 3678 (by decide)
  have h14 : Entails.eval a c4453 := h 4452 (by decide)
  have h15 : Entails.eval a c4227 := h 4226 (by decide)
  have h16 : Entails.eval a c752 := h 751 (by decide)
  have h17 : Entails.eval a c964 := h 963 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9001 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨54, by decide⟩, false), (⟨25, by decide⟩, false), (⟨51, by decide⟩, false), (⟨20, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9001 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8907, some c4905, some c1272, some c3681, some c6233, some c4256, some c835, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9001 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9001 : lratChecker f9001 p9001 = .success := by decide +kernel
theorem unsat9001 : Unsatisfiable (PosFin 65) f9001 := by
  apply lratCheckerSound f9001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9001
  · intro a ha; simp [p9001] at ha; subst a; trivial
  · exact checked9001
theorem derived9001 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9001 := by
  apply localUnsat_implies_entails f9001 [c8907, c4905, c1272, c3681, c6233, c4256, c835] c9001 unsat9001 (by rfl) a
  have h0 : Entails.eval a c8907 := derived8907 a h
  have h1 : Entails.eval a c4905 := h 4904 (by decide)
  have h2 : Entails.eval a c1272 := h 1271 (by decide)
  have h3 : Entails.eval a c3681 := h 3680 (by decide)
  have h4 : Entails.eval a c6233 := h 6232 (by decide)
  have h5 : Entails.eval a c4256 := h 4255 (by decide)
  have h6 : Entails.eval a c835 := h 834 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9002 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9002 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8847, some c8983, some c8998, some c8421, some c8686, some c8905, some c8920, some c8979, some c8999, some c8885, some c8918, some c8907, some c9001, some c4900, some c1284, some c3679, some c4453, some c9000, some c4227, some c752, some c756, some c966, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9002 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9002 : lratChecker f9002 p9002 = .success := by decide +kernel
theorem unsat9002 : Unsatisfiable (PosFin 65) f9002 := by
  apply lratCheckerSound f9002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9002
  · intro a ha; simp [p9002] at ha; subst a; trivial
  · exact checked9002
theorem derived9002 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9002 := by
  apply localUnsat_implies_entails f9002 [c8847, c8983, c8998, c8421, c8686, c8905, c8920, c8979, c8999, c8885, c8918, c8907, c9001, c4900, c1284, c3679, c4453, c9000, c4227, c752, c756, c966] c9002 unsat9002 (by rfl) a
  have h0 : Entails.eval a c8847 := derived8847 a h
  have h1 : Entails.eval a c8983 := derived8983 a h
  have h2 : Entails.eval a c8998 := derived8998 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8905 := derived8905 a h
  have h6 : Entails.eval a c8920 := derived8920 a h
  have h7 : Entails.eval a c8979 := derived8979 a h
  have h8 : Entails.eval a c8999 := derived8999 a h
  have h9 : Entails.eval a c8885 := derived8885 a h
  have h10 : Entails.eval a c8918 := derived8918 a h
  have h11 : Entails.eval a c8907 := derived8907 a h
  have h12 : Entails.eval a c9001 := derived9001 a h
  have h13 : Entails.eval a c4900 := h 4899 (by decide)
  have h14 : Entails.eval a c1284 := h 1283 (by decide)
  have h15 : Entails.eval a c3679 := h 3678 (by decide)
  have h16 : Entails.eval a c4453 := h 4452 (by decide)
  have h17 : Entails.eval a c9000 := derived9000 a h
  have h18 : Entails.eval a c4227 := h 4226 (by decide)
  have h19 : Entails.eval a c752 := h 751 (by decide)
  have h20 : Entails.eval a c756 := h 755 (by decide)
  have h21 : Entails.eval a c966 := h 965 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9003 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9003 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8979, some c8905, some c8847, some c8686, some c8421, some c8983, some c8920, some c8998, some c8907, some c8999, some c8885, some c8918, some c9002, some c5652, some c1280, some c5637, some c5558, some c8923, some c273, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9003 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9003 : lratChecker f9003 p9003 = .success := by decide +kernel
theorem unsat9003 : Unsatisfiable (PosFin 65) f9003 := by
  apply lratCheckerSound f9003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9003
  · intro a ha; simp [p9003] at ha; subst a; trivial
  · exact checked9003
theorem derived9003 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9003 := by
  apply localUnsat_implies_entails f9003 [c8979, c8905, c8847, c8686, c8421, c8983, c8920, c8998, c8907, c8999, c8885, c8918, c9002, c5652, c1280, c5637, c5558, c8923, c273] c9003 unsat9003 (by rfl) a
  have h0 : Entails.eval a c8979 := derived8979 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c8983 := derived8983 a h
  have h6 : Entails.eval a c8920 := derived8920 a h
  have h7 : Entails.eval a c8998 := derived8998 a h
  have h8 : Entails.eval a c8907 := derived8907 a h
  have h9 : Entails.eval a c8999 := derived8999 a h
  have h10 : Entails.eval a c8885 := derived8885 a h
  have h11 : Entails.eval a c8918 := derived8918 a h
  have h12 : Entails.eval a c9002 := derived9002 a h
  have h13 : Entails.eval a c5652 := h 5651 (by decide)
  have h14 : Entails.eval a c1280 := h 1279 (by decide)
  have h15 : Entails.eval a c5637 := h 5636 (by decide)
  have h16 : Entails.eval a c5558 := h 5557 (by decide)
  have h17 : Entails.eval a c8923 := derived8923 a h
  have h18 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9004 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨31, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9004 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8980, some c8982, some c7994, some c295, some c6139, some c6085, some c6089, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9004 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9004 : lratChecker f9004 p9004 = .success := by decide +kernel
theorem unsat9004 : Unsatisfiable (PosFin 65) f9004 := by
  apply lratCheckerSound f9004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9004
  · intro a ha; simp [p9004] at ha; subst a; trivial
  · exact checked9004
theorem derived9004 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9004 := by
  apply localUnsat_implies_entails f9004 [c8980, c8982, c7994, c295, c6139, c6085, c6089] c9004 unsat9004 (by rfl) a
  have h0 : Entails.eval a c8980 := derived8980 a h
  have h1 : Entails.eval a c8982 := derived8982 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c295 := h 294 (by decide)
  have h4 : Entails.eval a c6139 := h 6138 (by decide)
  have h5 : Entails.eval a c6085 := h 6084 (by decide)
  have h6 : Entails.eval a c6089 := h 6088 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9005 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9005 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8421, some c8905, some c8930, some c8689, some c9003, some c8847, some c809, some c6254, some c1083, some c1135, some c6255, some c6267, some c4606, some c6264, some c869, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9005 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9005 : lratChecker f9005 p9005 = .success := by decide +kernel
theorem unsat9005 : Unsatisfiable (PosFin 65) f9005 := by
  apply lratCheckerSound f9005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9005
  · intro a ha; simp [p9005] at ha; subst a; trivial
  · exact checked9005
theorem derived9005 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9005 := by
  apply localUnsat_implies_entails f9005 [c8686, c8421, c8905, c8930, c8689, c9003, c8847, c809, c6254, c1083, c1135, c6255, c6267, c4606, c6264, c869] c9005 unsat9005 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8930 := derived8930 a h
  have h4 : Entails.eval a c8689 := derived8689 a h
  have h5 : Entails.eval a c9003 := derived9003 a h
  have h6 : Entails.eval a c8847 := derived8847 a h
  have h7 : Entails.eval a c809 := h 808 (by decide)
  have h8 : Entails.eval a c6254 := h 6253 (by decide)
  have h9 : Entails.eval a c1083 := h 1082 (by decide)
  have h10 : Entails.eval a c1135 := h 1134 (by decide)
  have h11 : Entails.eval a c6255 := h 6254 (by decide)
  have h12 : Entails.eval a c6267 := h 6266 (by decide)
  have h13 : Entails.eval a c4606 := h 4605 (by decide)
  have h14 : Entails.eval a c6264 := h 6263 (by decide)
  have h15 : Entails.eval a c869 := h 868 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9006 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨27, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨31, by decide⟩, false), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9006 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8928, some c8931, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9006 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9006 : lratChecker f9006 p9006 = .success := by decide +kernel
theorem unsat9006 : Unsatisfiable (PosFin 65) f9006 := by
  apply lratCheckerSound f9006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9006
  · intro a ha; simp [p9006] at ha; subst a; trivial
  · exact checked9006
theorem derived9006 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9006 := by
  apply localUnsat_implies_entails f9006 [c8928, c8931] c9006 unsat9006 (by rfl) a
  have h0 : Entails.eval a c8928 := derived8928 a h
  have h1 : Entails.eval a c8931 := derived8931 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9007 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨27, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨31, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9007 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8933, some c8974, some c9006, some c7994, some c6143, some c6168, some c5636, some c5644, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9007 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9007 : lratChecker f9007 p9007 = .success := by decide +kernel
theorem unsat9007 : Unsatisfiable (PosFin 65) f9007 := by
  apply lratCheckerSound f9007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9007
  · intro a ha; simp [p9007] at ha; subst a; trivial
  · exact checked9007
theorem derived9007 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9007 := by
  apply localUnsat_implies_entails f9007 [c8933, c8974, c9006, c7994, c6143, c6168, c5636, c5644] c9007 unsat9007 (by rfl) a
  have h0 : Entails.eval a c8933 := derived8933 a h
  have h1 : Entails.eval a c8974 := derived8974 a h
  have h2 : Entails.eval a c9006 := derived9006 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c6143 := h 6142 (by decide)
  have h5 : Entails.eval a c6168 := h 6167 (by decide)
  have h6 : Entails.eval a c5636 := h 5635 (by decide)
  have h7 : Entails.eval a c5644 := h 5643 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9008 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9008 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9005, some c8686, some c8847, some c8905, some c9003, some c8421, some c8930, some c8689, some c9004, some c8979, some c9006, some c7994, some c1272, some c4450, some c758, some c756, some c757, some c5636, some c5644, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9008 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9008 : lratChecker f9008 p9008 = .success := by decide +kernel
theorem unsat9008 : Unsatisfiable (PosFin 65) f9008 := by
  apply lratCheckerSound f9008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9008
  · intro a ha; simp [p9008] at ha; subst a; trivial
  · exact checked9008
theorem derived9008 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9008 := by
  apply localUnsat_implies_entails f9008 [c9005, c8686, c8847, c8905, c9003, c8421, c8930, c8689, c9004, c8979, c9006, c7994, c1272, c4450, c758, c756, c757, c5636, c5644] c9008 unsat9008 (by rfl) a
  have h0 : Entails.eval a c9005 := derived9005 a h
  have h1 : Entails.eval a c8686 := derived8686 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8905 := derived8905 a h
  have h4 : Entails.eval a c9003 := derived9003 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8930 := derived8930 a h
  have h7 : Entails.eval a c8689 := derived8689 a h
  have h8 : Entails.eval a c9004 := derived9004 a h
  have h9 : Entails.eval a c8979 := derived8979 a h
  have h10 : Entails.eval a c9006 := derived9006 a h
  have h11 : Entails.eval a c7994 := derived7994 a h
  have h12 : Entails.eval a c1272 := h 1271 (by decide)
  have h13 : Entails.eval a c4450 := h 4449 (by decide)
  have h14 : Entails.eval a c758 := h 757 (by decide)
  have h15 : Entails.eval a c756 := h 755 (by decide)
  have h16 : Entails.eval a c757 := h 756 (by decide)
  have h17 : Entails.eval a c5636 := h 5635 (by decide)
  have h18 : Entails.eval a c5644 := h 5643 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9009 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨31, by decide⟩, false), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9009 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6181, some c6173, some c6180, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p9009 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9009 : lratChecker f9009 p9009 = .success := by decide +kernel
theorem unsat9009 : Unsatisfiable (PosFin 65) f9009 := by
  apply lratCheckerSound f9009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9009
  · intro a ha; simp [p9009] at ha; subst a; trivial
  · exact checked9009
theorem derived9009 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9009 := by
  apply localUnsat_implies_entails f9009 [c6181, c6173, c6180] c9009 unsat9009 (by rfl) a
  have h0 : Entails.eval a c6181 := h 6180 (by decide)
  have h1 : Entails.eval a c6173 := h 6172 (by decide)
  have h2 : Entails.eval a c6180 := h 6179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9010 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9010 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8928, some c6153, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p9010 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9010 : lratChecker f9010 p9010 = .success := by decide +kernel
theorem unsat9010 : Unsatisfiable (PosFin 65) f9010 := by
  apply lratCheckerSound f9010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9010
  · intro a ha; simp [p9010] at ha; subst a; trivial
  · exact checked9010
theorem derived9010 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9010 := by
  apply localUnsat_implies_entails f9010 [c8928, c6153] c9010 unsat9010 (by rfl) a
  have h0 : Entails.eval a c8928 := derived8928 a h
  have h1 : Entails.eval a c6153 := h 6152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9011 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9011 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9003, some c8979, some c8905, some c8847, some c8686, some c8421, some c8930, some c8689, some c9004, some c9005, some c9007, some c9008, some c9009, some c9010, some c7994, some c6139, some c5636, some c6163, some c5644, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9011 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9011 : lratChecker f9011 p9011 = .success := by decide +kernel
theorem unsat9011 : Unsatisfiable (PosFin 65) f9011 := by
  apply lratCheckerSound f9011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9011
  · intro a ha; simp [p9011] at ha; subst a; trivial
  · exact checked9011
theorem derived9011 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9011 := by
  apply localUnsat_implies_entails f9011 [c9003, c8979, c8905, c8847, c8686, c8421, c8930, c8689, c9004, c9005, c9007, c9008, c9009, c9010, c7994, c6139, c5636, c6163, c5644] c9011 unsat9011 (by rfl) a
  have h0 : Entails.eval a c9003 := derived9003 a h
  have h1 : Entails.eval a c8979 := derived8979 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c8930 := derived8930 a h
  have h7 : Entails.eval a c8689 := derived8689 a h
  have h8 : Entails.eval a c9004 := derived9004 a h
  have h9 : Entails.eval a c9005 := derived9005 a h
  have h10 : Entails.eval a c9007 := derived9007 a h
  have h11 : Entails.eval a c9008 := derived9008 a h
  have h12 : Entails.eval a c9009 := derived9009 a h
  have h13 : Entails.eval a c9010 := derived9010 a h
  have h14 : Entails.eval a c7994 := derived7994 a h
  have h15 : Entails.eval a c6139 := h 6138 (by decide)
  have h16 : Entails.eval a c5636 := h 5635 (by decide)
  have h17 : Entails.eval a c6163 := h 6162 (by decide)
  have h18 : Entails.eval a c5644 := h 5643 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9012 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨31, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9012 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1188, some c1202, some c1185, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9012 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9012 : lratChecker f9012 p9012 = .success := by decide +kernel
theorem unsat9012 : Unsatisfiable (PosFin 65) f9012 := by
  apply lratCheckerSound f9012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9012
  · intro a ha; simp [p9012] at ha; subst a; trivial
  · exact checked9012
theorem derived9012 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9012 := by
  apply localUnsat_implies_entails f9012 [c1188, c1202, c1185] c9012 unsat9012 (by rfl) a
  have h0 : Entails.eval a c1188 := h 1187 (by decide)
  have h1 : Entails.eval a c1202 := h 1201 (by decide)
  have h2 : Entails.eval a c1185 := h 1184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9013 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9013 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c763, some c6259, some c6266, some c4434, some c4443, some c6262, some c5642, some c6256, some c5641, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9013 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9013 : lratChecker f9013 p9013 = .success := by decide +kernel
theorem unsat9013 : Unsatisfiable (PosFin 65) f9013 := by
  apply lratCheckerSound f9013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9013
  · intro a ha; simp [p9013] at ha; subst a; trivial
  · exact checked9013
theorem derived9013 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9013 := by
  apply localUnsat_implies_entails f9013 [c763, c6259, c6266, c4434, c4443, c6262, c5642, c6256, c5641] c9013 unsat9013 (by rfl) a
  have h0 : Entails.eval a c763 := h 762 (by decide)
  have h1 : Entails.eval a c6259 := h 6258 (by decide)
  have h2 : Entails.eval a c6266 := h 6265 (by decide)
  have h3 : Entails.eval a c4434 := h 4433 (by decide)
  have h4 : Entails.eval a c4443 := h 4442 (by decide)
  have h5 : Entails.eval a c6262 := h 6261 (by decide)
  have h6 : Entails.eval a c5642 := h 5641 (by decide)
  have h7 : Entails.eval a c6256 := h 6255 (by decide)
  have h8 : Entails.eval a c5641 := h 5640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9014 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨27, by decide⟩, false), (⟨2, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9014 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9013, some c6255, some c6265, some c6260, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p9014 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9014 : lratChecker f9014 p9014 = .success := by decide +kernel
theorem unsat9014 : Unsatisfiable (PosFin 65) f9014 := by
  apply lratCheckerSound f9014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9014
  · intro a ha; simp [p9014] at ha; subst a; trivial
  · exact checked9014
theorem derived9014 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9014 := by
  apply localUnsat_implies_entails f9014 [c9013, c6255, c6265, c6260] c9014 unsat9014 (by rfl) a
  have h0 : Entails.eval a c9013 := derived9013 a h
  have h1 : Entails.eval a c6255 := h 6254 (by decide)
  have h2 : Entails.eval a c6265 := h 6264 (by decide)
  have h3 : Entails.eval a c6260 := h 6259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9015 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9015 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1135, some c9014, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9015 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9015 : lratChecker f9015 p9015 = .success := by decide +kernel
theorem unsat9015 : Unsatisfiable (PosFin 65) f9015 := by
  apply lratCheckerSound f9015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9015
  · intro a ha; simp [p9015] at ha; subst a; trivial
  · exact checked9015
theorem derived9015 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9015 := by
  apply localUnsat_implies_entails f9015 [c1135, c9014] c9015 unsat9015 (by rfl) a
  have h0 : Entails.eval a c1135 := h 1134 (by decide)
  have h1 : Entails.eval a c9014 := derived9014 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9016 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨5, by decide⟩, true), (⟨62, by decide⟩, true), (⟨11, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9016 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4900, some c1284, some c3679, some c4260, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9016 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9016 : lratChecker f9016 p9016 = .success := by decide +kernel
theorem unsat9016 : Unsatisfiable (PosFin 65) f9016 := by
  apply lratCheckerSound f9016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9016
  · intro a ha; simp [p9016] at ha; subst a; trivial
  · exact checked9016
theorem derived9016 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9016 := by
  apply localUnsat_implies_entails f9016 [c4900, c1284, c3679, c4260] c9016 unsat9016 (by rfl) a
  have h0 : Entails.eval a c4900 := h 4899 (by decide)
  have h1 : Entails.eval a c1284 := h 1283 (by decide)
  have h2 : Entails.eval a c3679 := h 3678 (by decide)
  have h3 : Entails.eval a c4260 := h 4259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9017 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨63, by decide⟩, false), (⟨5, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9017 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4905, some c3681, some c4221, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9017 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9017 : lratChecker f9017 p9017 = .success := by decide +kernel
theorem unsat9017 : Unsatisfiable (PosFin 65) f9017 := by
  apply lratCheckerSound f9017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9017
  · intro a ha; simp [p9017] at ha; subst a; trivial
  · exact checked9017
theorem derived9017 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9017 := by
  apply localUnsat_implies_entails f9017 [c4905, c3681, c4221] c9017 unsat9017 (by rfl) a
  have h0 : Entails.eval a c4905 := h 4904 (by decide)
  have h1 : Entails.eval a c3681 := h 3680 (by decide)
  have h2 : Entails.eval a c4221 := h 4220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9018 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9018 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8905, some c8847, some c8686, some c8421, some c8979, some c9003, some c9011, some c9012, some c9015, some c8975, some c8882, some c8977, some c9016, some c7994, some c9017, some c8604, some c2735, some c4722, some c3193, some c4182, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9018 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9018 : lratChecker f9018 p9018 = .success := by decide +kernel
theorem unsat9018 : Unsatisfiable (PosFin 65) f9018 := by
  apply lratCheckerSound f9018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9018
  · intro a ha; simp [p9018] at ha; subst a; trivial
  · exact checked9018
theorem derived9018 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9018 := by
  apply localUnsat_implies_entails f9018 [c8905, c8847, c8686, c8421, c8979, c9003, c9011, c9012, c9015, c8975, c8882, c8977, c9016, c7994, c9017, c8604, c2735, c4722, c3193, c4182] c9018 unsat9018 (by rfl) a
  have h0 : Entails.eval a c8905 := derived8905 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8686 := derived8686 a h
  have h3 : Entails.eval a c8421 := derived8421 a h
  have h4 : Entails.eval a c8979 := derived8979 a h
  have h5 : Entails.eval a c9003 := derived9003 a h
  have h6 : Entails.eval a c9011 := derived9011 a h
  have h7 : Entails.eval a c9012 := derived9012 a h
  have h8 : Entails.eval a c9015 := derived9015 a h
  have h9 : Entails.eval a c8975 := derived8975 a h
  have h10 : Entails.eval a c8882 := derived8882 a h
  have h11 : Entails.eval a c8977 := derived8977 a h
  have h12 : Entails.eval a c9016 := derived9016 a h
  have h13 : Entails.eval a c7994 := derived7994 a h
  have h14 : Entails.eval a c9017 := derived9017 a h
  have h15 : Entails.eval a c8604 := derived8604 a h
  have h16 : Entails.eval a c2735 := h 2734 (by decide)
  have h17 : Entails.eval a c4722 := h 4721 (by decide)
  have h18 : Entails.eval a c3193 := h 3192 (by decide)
  have h19 : Entails.eval a c4182 := h 4181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9019 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9019 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5966, some c5975, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9019 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9019 : lratChecker f9019 p9019 = .success := by decide +kernel
theorem unsat9019 : Unsatisfiable (PosFin 65) f9019 := by
  apply lratCheckerSound f9019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9019
  · intro a ha; simp [p9019] at ha; subst a; trivial
  · exact checked9019
theorem derived9019 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9019 := by
  apply localUnsat_implies_entails f9019 [c5966, c5975] c9019 unsat9019 (by rfl) a
  have h0 : Entails.eval a c5966 := h 5965 (by decide)
  have h1 : Entails.eval a c5975 := h 5974 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9020 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨54, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9020 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c749, some c745, some c754, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9020 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9020 : lratChecker f9020 p9020 = .success := by decide +kernel
theorem unsat9020 : Unsatisfiable (PosFin 65) f9020 := by
  apply lratCheckerSound f9020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9020
  · intro a ha; simp [p9020] at ha; subst a; trivial
  · exact checked9020
theorem derived9020 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9020 := by
  apply localUnsat_implies_entails f9020 [c749, c745, c754] c9020 unsat9020 (by rfl) a
  have h0 : Entails.eval a c749 := h 748 (by decide)
  have h1 : Entails.eval a c745 := h 744 (by decide)
  have h2 : Entails.eval a c754 := h 753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9021 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9021 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1151, some c4465, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9021 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9021 : lratChecker f9021 p9021 = .success := by decide +kernel
theorem unsat9021 : Unsatisfiable (PosFin 65) f9021 := by
  apply lratCheckerSound f9021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9021
  · intro a ha; simp [p9021] at ha; subst a; trivial
  · exact checked9021
theorem derived9021 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9021 := by
  apply localUnsat_implies_entails f9021 [c1151, c4465] c9021 unsat9021 (by rfl) a
  have h0 : Entails.eval a c1151 := h 1150 (by decide)
  have h1 : Entails.eval a c4465 := h 4464 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9022 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9022 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8905, some c8930, some c8847, some c9019, some c9020, some c9021, some c7994, some c1272, some c4450, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9022 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9022 : lratChecker f9022 p9022 = .success := by decide +kernel
theorem unsat9022 : Unsatisfiable (PosFin 65) f9022 := by
  apply lratCheckerSound f9022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9022
  · intro a ha; simp [p9022] at ha; subst a; trivial
  · exact checked9022
theorem derived9022 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9022 := by
  apply localUnsat_implies_entails f9022 [c8686, c8905, c8930, c8847, c9019, c9020, c9021, c7994, c1272, c4450] c9022 unsat9022 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8930 := derived8930 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c9019 := derived9019 a h
  have h5 : Entails.eval a c9020 := derived9020 a h
  have h6 : Entails.eval a c9021 := derived9021 a h
  have h7 : Entails.eval a c7994 := derived7994 a h
  have h8 : Entails.eval a c1272 := h 1271 (by decide)
  have h9 : Entails.eval a c4450 := h 4449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9023 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨54, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9023 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c793, some c5968, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9023 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9023 : lratChecker f9023 p9023 = .success := by decide +kernel
theorem unsat9023 : Unsatisfiable (PosFin 65) f9023 := by
  apply lratCheckerSound f9023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9023
  · intro a ha; simp [p9023] at ha; subst a; trivial
  · exact checked9023
theorem derived9023 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9023 := by
  apply localUnsat_implies_entails f9023 [c793, c5968] c9023 unsat9023 (by rfl) a
  have h0 : Entails.eval a c793 := h 792 (by decide)
  have h1 : Entails.eval a c5968 := h 5967 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9024 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨20, by decide⟩, true), (⟨54, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9024 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6072, some c5842, some c5847, some c5841, some c5853, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p9024 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9024 : lratChecker f9024 p9024 = .success := by decide +kernel
theorem unsat9024 : Unsatisfiable (PosFin 65) f9024 := by
  apply lratCheckerSound f9024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9024
  · intro a ha; simp [p9024] at ha; subst a; trivial
  · exact checked9024
theorem derived9024 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9024 := by
  apply localUnsat_implies_entails f9024 [c6072, c5842, c5847, c5841, c5853] c9024 unsat9024 (by rfl) a
  have h0 : Entails.eval a c6072 := h 6071 (by decide)
  have h1 : Entails.eval a c5842 := h 5841 (by decide)
  have h2 : Entails.eval a c5847 := h 5846 (by decide)
  have h3 : Entails.eval a c5841 := h 5840 (by decide)
  have h4 : Entails.eval a c5853 := h 5852 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9025 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨25, by decide⟩, false), (⟨20, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨8, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9025 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1097, some c3634, some c4666, some c9021, some c5452, some c5400, some c351, some c5614, some c6098, some c5416, some c5510, some c5592, some c6201, some c8441, some c783, some c796, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9025 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9025 : lratChecker f9025 p9025 = .success := by decide +kernel
theorem unsat9025 : Unsatisfiable (PosFin 65) f9025 := by
  apply lratCheckerSound f9025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9025
  · intro a ha; simp [p9025] at ha; subst a; trivial
  · exact checked9025
theorem derived9025 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9025 := by
  apply localUnsat_implies_entails f9025 [c1097, c3634, c4666, c9021, c5452, c5400, c351, c5614, c6098, c5416, c5510, c5592, c6201, c8441, c783, c796] c9025 unsat9025 (by rfl) a
  have h0 : Entails.eval a c1097 := h 1096 (by decide)
  have h1 : Entails.eval a c3634 := h 3633 (by decide)
  have h2 : Entails.eval a c4666 := h 4665 (by decide)
  have h3 : Entails.eval a c9021 := derived9021 a h
  have h4 : Entails.eval a c5452 := h 5451 (by decide)
  have h5 : Entails.eval a c5400 := h 5399 (by decide)
  have h6 : Entails.eval a c351 := h 350 (by decide)
  have h7 : Entails.eval a c5614 := h 5613 (by decide)
  have h8 : Entails.eval a c6098 := h 6097 (by decide)
  have h9 : Entails.eval a c5416 := h 5415 (by decide)
  have h10 : Entails.eval a c5510 := h 5509 (by decide)
  have h11 : Entails.eval a c5592 := h 5591 (by decide)
  have h12 : Entails.eval a c6201 := h 6200 (by decide)
  have h13 : Entails.eval a c8441 := derived8441 a h
  have h14 : Entails.eval a c783 := h 782 (by decide)
  have h15 : Entails.eval a c796 := h 795 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9026 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9026 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8421, some c8905, some c8930, some c8689, some c9018, some c8847, some c9022, some c9023, some c9024, some c8913, some c9025, some c7994, some c6066, some c5842, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9026 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9026 : lratChecker f9026 p9026 = .success := by decide +kernel
theorem unsat9026 : Unsatisfiable (PosFin 65) f9026 := by
  apply lratCheckerSound f9026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9026
  · intro a ha; simp [p9026] at ha; subst a; trivial
  · exact checked9026
theorem derived9026 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9026 := by
  apply localUnsat_implies_entails f9026 [c8686, c8421, c8905, c8930, c8689, c9018, c8847, c9022, c9023, c9024, c8913, c9025, c7994, c6066, c5842] c9026 unsat9026 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8930 := derived8930 a h
  have h4 : Entails.eval a c8689 := derived8689 a h
  have h5 : Entails.eval a c9018 := derived9018 a h
  have h6 : Entails.eval a c8847 := derived8847 a h
  have h7 : Entails.eval a c9022 := derived9022 a h
  have h8 : Entails.eval a c9023 := derived9023 a h
  have h9 : Entails.eval a c9024 := derived9024 a h
  have h10 : Entails.eval a c8913 := derived8913 a h
  have h11 : Entails.eval a c9025 := derived9025 a h
  have h12 : Entails.eval a c7994 := derived7994 a h
  have h13 : Entails.eval a c6066 := h 6065 (by decide)
  have h14 : Entails.eval a c5842 := h 5841 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9027 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9027 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8763, some c5812, some c5825, some c5824, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9027 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9027 : lratChecker f9027 p9027 = .success := by decide +kernel
theorem unsat9027 : Unsatisfiable (PosFin 65) f9027 := by
  apply lratCheckerSound f9027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9027
  · intro a ha; simp [p9027] at ha; subst a; trivial
  · exact checked9027
theorem derived9027 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9027 := by
  apply localUnsat_implies_entails f9027 [c8763, c5812, c5825, c5824] c9027 unsat9027 (by rfl) a
  have h0 : Entails.eval a c8763 := derived8763 a h
  have h1 : Entails.eval a c5812 := h 5811 (by decide)
  have h2 : Entails.eval a c5825 := h 5824 (by decide)
  have h3 : Entails.eval a c5824 := h 5823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9028 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨54, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9028 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8956, some c5943, some c5887, some c6191, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9028 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9028 : lratChecker f9028 p9028 = .success := by decide +kernel
theorem unsat9028 : Unsatisfiable (PosFin 65) f9028 := by
  apply lratCheckerSound f9028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9028
  · intro a ha; simp [p9028] at ha; subst a; trivial
  · exact checked9028
theorem derived9028 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9028 := by
  apply localUnsat_implies_entails f9028 [c8956, c5943, c5887, c6191] c9028 unsat9028 (by rfl) a
  have h0 : Entails.eval a c8956 := derived8956 a h
  have h1 : Entails.eval a c5943 := h 5942 (by decide)
  have h2 : Entails.eval a c5887 := h 5886 (by decide)
  have h3 : Entails.eval a c6191 := h 6190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9029 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9029 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c749, some c745, some c752, some c755, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9029 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9029 : lratChecker f9029 p9029 = .success := by decide +kernel
theorem unsat9029 : Unsatisfiable (PosFin 65) f9029 := by
  apply lratCheckerSound f9029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9029
  · intro a ha; simp [p9029] at ha; subst a; trivial
  · exact checked9029
theorem derived9029 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9029 := by
  apply localUnsat_implies_entails f9029 [c749, c745, c752, c755] c9029 unsat9029 (by rfl) a
  have h0 : Entails.eval a c749 := h 748 (by decide)
  have h1 : Entails.eval a c745 := h 744 (by decide)
  have h2 : Entails.eval a c752 := h 751 (by decide)
  have h3 : Entails.eval a c755 := h 754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9030 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨53, by decide⟩, true), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9030 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8847, some c8905, some c9018, some c9027, some c9026, some c8930, some c8421, some c9028, some c9029, some c9021, some c7994, some c1272, some c4450, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9030 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9030 : lratChecker f9030 p9030 = .success := by decide +kernel
theorem unsat9030 : Unsatisfiable (PosFin 65) f9030 := by
  apply lratCheckerSound f9030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9030
  · intro a ha; simp [p9030] at ha; subst a; trivial
  · exact checked9030
theorem derived9030 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9030 := by
  apply localUnsat_implies_entails f9030 [c8686, c8847, c8905, c9018, c9027, c9026, c8930, c8421, c9028, c9029, c9021, c7994, c1272, c4450] c9030 unsat9030 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c9018 := derived9018 a h
  have h4 : Entails.eval a c9027 := derived9027 a h
  have h5 : Entails.eval a c9026 := derived9026 a h
  have h6 : Entails.eval a c8930 := derived8930 a h
  have h7 : Entails.eval a c8421 := derived8421 a h
  have h8 : Entails.eval a c9028 := derived9028 a h
  have h9 : Entails.eval a c9029 := derived9029 a h
  have h10 : Entails.eval a c9021 := derived9021 a h
  have h11 : Entails.eval a c7994 := derived7994 a h
  have h12 : Entails.eval a c1272 := h 1271 (by decide)
  have h13 : Entails.eval a c4450 := h 4449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9031 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨49, by decide⟩, true), (⟨29, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9031 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8849, some c7994, some c5943, some c5887, some c6191, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9031 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9031 : lratChecker f9031 p9031 = .success := by decide +kernel
theorem unsat9031 : Unsatisfiable (PosFin 65) f9031 := by
  apply lratCheckerSound f9031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9031
  · intro a ha; simp [p9031] at ha; subst a; trivial
  · exact checked9031
theorem derived9031 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9031 := by
  apply localUnsat_implies_entails f9031 [c8849, c7994, c5943, c5887, c6191] c9031 unsat9031 (by rfl) a
  have h0 : Entails.eval a c8849 := derived8849 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c5943 := h 5942 (by decide)
  have h3 : Entails.eval a c5887 := h 5886 (by decide)
  have h4 : Entails.eval a c6191 := h 6190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9032 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9032 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c266, some c351, some c5751, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p9032 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9032 : lratChecker f9032 p9032 = .success := by decide +kernel
theorem unsat9032 : Unsatisfiable (PosFin 65) f9032 := by
  apply lratCheckerSound f9032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9032
  · intro a ha; simp [p9032] at ha; subst a; trivial
  · exact checked9032
theorem derived9032 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9032 := by
  apply localUnsat_implies_entails f9032 [c266, c351, c5751] c9032 unsat9032 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c351 := h 350 (by decide)
  have h2 : Entails.eval a c5751 := h 5750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9033 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨27, by decide⟩, true), (⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9033 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8421, some c8905, some c8930, some c8689, some c9018, some c8847, some c1097, some c3634, some c4666, some c9021, some c9032, some c6138, some c5626, some c227, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9033 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9033 : lratChecker f9033 p9033 = .success := by decide +kernel
theorem unsat9033 : Unsatisfiable (PosFin 65) f9033 := by
  apply lratCheckerSound f9033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9033
  · intro a ha; simp [p9033] at ha; subst a; trivial
  · exact checked9033
theorem derived9033 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9033 := by
  apply localUnsat_implies_entails f9033 [c8686, c8421, c8905, c8930, c8689, c9018, c8847, c1097, c3634, c4666, c9021, c9032, c6138, c5626, c227] c9033 unsat9033 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8421 := derived8421 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8930 := derived8930 a h
  have h4 : Entails.eval a c8689 := derived8689 a h
  have h5 : Entails.eval a c9018 := derived9018 a h
  have h6 : Entails.eval a c8847 := derived8847 a h
  have h7 : Entails.eval a c1097 := h 1096 (by decide)
  have h8 : Entails.eval a c3634 := h 3633 (by decide)
  have h9 : Entails.eval a c4666 := h 4665 (by decide)
  have h10 : Entails.eval a c9021 := derived9021 a h
  have h11 : Entails.eval a c9032 := derived9032 a h
  have h12 : Entails.eval a c6138 := h 6137 (by decide)
  have h13 : Entails.eval a c5626 := h 5625 (by decide)
  have h14 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9034 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9034 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9018, some c8905, some c8847, some c8686, some c9027, some c9026, some c9030, some c9031, some c9033, some c7994, some c6011, some c5920, some c5842, some c6048, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9034 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9034 : lratChecker f9034 p9034 = .success := by decide +kernel
theorem unsat9034 : Unsatisfiable (PosFin 65) f9034 := by
  apply lratCheckerSound f9034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9034
  · intro a ha; simp [p9034] at ha; subst a; trivial
  · exact checked9034
theorem derived9034 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9034 := by
  apply localUnsat_implies_entails f9034 [c9018, c8905, c8847, c8686, c9027, c9026, c9030, c9031, c9033, c7994, c6011, c5920, c5842, c6048] c9034 unsat9034 (by rfl) a
  have h0 : Entails.eval a c9018 := derived9018 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c9027 := derived9027 a h
  have h5 : Entails.eval a c9026 := derived9026 a h
  have h6 : Entails.eval a c9030 := derived9030 a h
  have h7 : Entails.eval a c9031 := derived9031 a h
  have h8 : Entails.eval a c9033 := derived9033 a h
  have h9 : Entails.eval a c7994 := derived7994 a h
  have h10 : Entails.eval a c6011 := h 6010 (by decide)
  have h11 : Entails.eval a c5920 := h 5919 (by decide)
  have h12 : Entails.eval a c5842 := h 5841 (by decide)
  have h13 : Entails.eval a c6048 := h 6047 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9035 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9035 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1214, some c1213, some c1226, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9035 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9035 : lratChecker f9035 p9035 = .success := by decide +kernel
theorem unsat9035 : Unsatisfiable (PosFin 65) f9035 := by
  apply lratCheckerSound f9035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9035
  · intro a ha; simp [p9035] at ha; subst a; trivial
  · exact checked9035
theorem derived9035 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9035 := by
  apply localUnsat_implies_entails f9035 [c1214, c1213, c1226] c9035 unsat9035 (by rfl) a
  have h0 : Entails.eval a c1214 := h 1213 (by decide)
  have h1 : Entails.eval a c1213 := h 1212 (by decide)
  have h2 : Entails.eval a c1226 := h 1225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9036 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9036 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9035, some c1221, some c1428, some c1231, some c9024, some c5977, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9036 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9036 : lratChecker f9036 p9036 = .success := by decide +kernel
theorem unsat9036 : Unsatisfiable (PosFin 65) f9036 := by
  apply lratCheckerSound f9036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9036
  · intro a ha; simp [p9036] at ha; subst a; trivial
  · exact checked9036
theorem derived9036 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9036 := by
  apply localUnsat_implies_entails f9036 [c9035, c1221, c1428, c1231, c9024, c5977] c9036 unsat9036 (by rfl) a
  have h0 : Entails.eval a c9035 := derived9035 a h
  have h1 : Entails.eval a c1221 := h 1220 (by decide)
  have h2 : Entails.eval a c1428 := h 1427 (by decide)
  have h3 : Entails.eval a c1231 := h 1230 (by decide)
  have h4 : Entails.eval a c9024 := derived9024 a h
  have h5 : Entails.eval a c5977 := h 5976 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9037 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9037 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8531, some c5971, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9037 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9037 : lratChecker f9037 p9037 = .success := by decide +kernel
theorem unsat9037 : Unsatisfiable (PosFin 65) f9037 := by
  apply lratCheckerSound f9037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9037
  · intro a ha; simp [p9037] at ha; subst a; trivial
  · exact checked9037
theorem derived9037 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9037 := by
  apply localUnsat_implies_entails f9037 [c8531, c5971] c9037 unsat9037 (by rfl) a
  have h0 : Entails.eval a c8531 := derived8531 a h
  have h1 : Entails.eval a c5971 := h 5970 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9038 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨8, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9038 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2750, some c1155, some c2753, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9038 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9038 : lratChecker f9038 p9038 = .success := by decide +kernel
theorem unsat9038 : Unsatisfiable (PosFin 65) f9038 := by
  apply lratCheckerSound f9038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9038
  · intro a ha; simp [p9038] at ha; subst a; trivial
  · exact checked9038
theorem derived9038 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9038 := by
  apply localUnsat_implies_entails f9038 [c2750, c1155, c2753] c9038 unsat9038 (by rfl) a
  have h0 : Entails.eval a c2750 := h 2749 (by decide)
  have h1 : Entails.eval a c1155 := h 1154 (by decide)
  have h2 : Entails.eval a c2753 := h 2752 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9039 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨6, by decide⟩, true), (⟨20, by decide⟩, true), (⟨63, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9039 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9034, some c8905, some c8847, some c8686, some c8421, some c8987, some c8963, some c9038, some c4441, some c4437, some c4451, some c797, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9039 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9039 : lratChecker f9039 p9039 = .success := by decide +kernel
theorem unsat9039 : Unsatisfiable (PosFin 65) f9039 := by
  apply lratCheckerSound f9039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9039
  · intro a ha; simp [p9039] at ha; subst a; trivial
  · exact checked9039
theorem derived9039 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9039 := by
  apply localUnsat_implies_entails f9039 [c9034, c8905, c8847, c8686, c8421, c8987, c8963, c9038, c4441, c4437, c4451, c797] c9039 unsat9039 (by rfl) a
  have h0 : Entails.eval a c9034 := derived9034 a h
  have h1 : Entails.eval a c8905 := derived8905 a h
  have h2 : Entails.eval a c8847 := derived8847 a h
  have h3 : Entails.eval a c8686 := derived8686 a h
  have h4 : Entails.eval a c8421 := derived8421 a h
  have h5 : Entails.eval a c8987 := derived8987 a h
  have h6 : Entails.eval a c8963 := derived8963 a h
  have h7 : Entails.eval a c9038 := derived9038 a h
  have h8 : Entails.eval a c4441 := h 4440 (by decide)
  have h9 : Entails.eval a c4437 := h 4436 (by decide)
  have h10 : Entails.eval a c4451 := h 4450 (by decide)
  have h11 : Entails.eval a c797 := h 796 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9040 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨63, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9040 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4909, some c4918, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p9040 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9040 : lratChecker f9040 p9040 = .success := by decide +kernel
theorem unsat9040 : Unsatisfiable (PosFin 65) f9040 := by
  apply lratCheckerSound f9040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9040
  · intro a ha; simp [p9040] at ha; subst a; trivial
  · exact checked9040
theorem derived9040 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9040 := by
  apply localUnsat_implies_entails f9040 [c4909, c4918] c9040 unsat9040 (by rfl) a
  have h0 : Entails.eval a c4909 := h 4908 (by decide)
  have h1 : Entails.eval a c4918 := h 4917 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9041 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9041 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8847, some c8905, some c9034, some c9036, some c8421, some c9037, some c9020, some c9039, some c9040, some c9038, some c4453, some c4462, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9041 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9041 : lratChecker f9041 p9041 = .success := by decide +kernel
theorem unsat9041 : Unsatisfiable (PosFin 65) f9041 := by
  apply lratCheckerSound f9041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9041
  · intro a ha; simp [p9041] at ha; subst a; trivial
  · exact checked9041
theorem derived9041 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9041 := by
  apply localUnsat_implies_entails f9041 [c8686, c8847, c8905, c9034, c9036, c8421, c9037, c9020, c9039, c9040, c9038, c4453, c4462] c9041 unsat9041 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c9034 := derived9034 a h
  have h4 : Entails.eval a c9036 := derived9036 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c9037 := derived9037 a h
  have h7 : Entails.eval a c9020 := derived9020 a h
  have h8 : Entails.eval a c9039 := derived9039 a h
  have h9 : Entails.eval a c9040 := derived9040 a h
  have h10 : Entails.eval a c9038 := derived9038 a h
  have h11 : Entails.eval a c4453 := h 4452 (by decide)
  have h12 : Entails.eval a c4462 := h 4461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9042 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9042 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8847, some c8905, some c9034, some c9036, some c9041, some c5975, some c6070, some c1272, some c9020, some c4437, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9042 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9042 : lratChecker f9042 p9042 = .success := by decide +kernel
theorem unsat9042 : Unsatisfiable (PosFin 65) f9042 := by
  apply lratCheckerSound f9042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9042
  · intro a ha; simp [p9042] at ha; subst a; trivial
  · exact checked9042
theorem derived9042 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9042 := by
  apply localUnsat_implies_entails f9042 [c8686, c8847, c8905, c9034, c9036, c9041, c5975, c6070, c1272, c9020, c4437] c9042 unsat9042 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8847 := derived8847 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c9034 := derived9034 a h
  have h4 : Entails.eval a c9036 := derived9036 a h
  have h5 : Entails.eval a c9041 := derived9041 a h
  have h6 : Entails.eval a c5975 := h 5974 (by decide)
  have h7 : Entails.eval a c6070 := h 6069 (by decide)
  have h8 : Entails.eval a c1272 := h 1271 (by decide)
  have h9 : Entails.eval a c9020 := derived9020 a h
  have h10 : Entails.eval a c4437 := h 4436 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9043 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨51, by decide⟩, false), (⟨63, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9043 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4453, some c4462, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9043 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9043 : lratChecker f9043 p9043 = .success := by decide +kernel
theorem unsat9043 : Unsatisfiable (PosFin 65) f9043 := by
  apply lratCheckerSound f9043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9043
  · intro a ha; simp [p9043] at ha; subst a; trivial
  · exact checked9043
theorem derived9043 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9043 := by
  apply localUnsat_implies_entails f9043 [c4453, c4462] c9043 unsat9043 (by rfl) a
  have h0 : Entails.eval a c4453 := h 4452 (by decide)
  have h1 : Entails.eval a c4462 := h 4461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9044 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨63, by decide⟩, true), (⟨11, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9044 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9040, some c9038, some c9043, some c9037, some c8889, some c4731, some c5931, some c5449, some c5441, some c5399, some c86, some c65, some c8884, some c6407, some c7286, some c496, some c6980, some c6505, some c8166, some c5846, some c6071, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9044 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked9044 : lratChecker f9044 p9044 = .success := by decide +kernel
theorem unsat9044 : Unsatisfiable (PosFin 65) f9044 := by
  apply lratCheckerSound f9044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9044
  · intro a ha; simp [p9044] at ha; subst a; trivial
  · exact checked9044
theorem derived9044 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9044 := by
  apply localUnsat_implies_entails f9044 [c9040, c9038, c9043, c9037, c8889, c4731, c5931, c5449, c5441, c5399, c86, c65, c8884, c6407, c7286, c496, c6980, c6505, c8166, c5846, c6071] c9044 unsat9044 (by rfl) a
  have h0 : Entails.eval a c9040 := derived9040 a h
  have h1 : Entails.eval a c9038 := derived9038 a h
  have h2 : Entails.eval a c9043 := derived9043 a h
  have h3 : Entails.eval a c9037 := derived9037 a h
  have h4 : Entails.eval a c8889 := derived8889 a h
  have h5 : Entails.eval a c4731 := h 4730 (by decide)
  have h6 : Entails.eval a c5931 := h 5930 (by decide)
  have h7 : Entails.eval a c5449 := h 5448 (by decide)
  have h8 : Entails.eval a c5441 := h 5440 (by decide)
  have h9 : Entails.eval a c5399 := h 5398 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c8884 := derived8884 a h
  have h13 : Entails.eval a c6407 := h 6406 (by decide)
  have h14 : Entails.eval a c7286 := h 7285 (by decide)
  have h15 : Entails.eval a c496 := h 495 (by decide)
  have h16 : Entails.eval a c6980 := h 6979 (by decide)
  have h17 : Entails.eval a c6505 := h 6504 (by decide)
  have h18 : Entails.eval a c8166 := derived8166 a h
  have h19 : Entails.eval a c5846 := h 5845 (by decide)
  have h20 : Entails.eval a c6071 := h 6070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9045 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, true), (⟨11, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9045 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9037, some c9024, some c9044, some c6067, some c5841, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9045 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9045 : lratChecker f9045 p9045 = .success := by decide +kernel
theorem unsat9045 : Unsatisfiable (PosFin 65) f9045 := by
  apply lratCheckerSound f9045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9045
  · intro a ha; simp [p9045] at ha; subst a; trivial
  · exact checked9045
theorem derived9045 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9045 := by
  apply localUnsat_implies_entails f9045 [c9037, c9024, c9044, c6067, c5841] c9045 unsat9045 (by rfl) a
  have h0 : Entails.eval a c9037 := derived9037 a h
  have h1 : Entails.eval a c9024 := derived9024 a h
  have h2 : Entails.eval a c9044 := derived9044 a h
  have h3 : Entails.eval a c6067 := h 6066 (by decide)
  have h4 : Entails.eval a c5841 := h 5840 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9046 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9046 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9034, some c9018, some c8905, some c8847, some c8686, some c8421, some c9036, some c9042, some c9045, some c7994, some c8859, some c6066, some c5842, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9046 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9046 : lratChecker f9046 p9046 = .success := by decide +kernel
theorem unsat9046 : Unsatisfiable (PosFin 65) f9046 := by
  apply lratCheckerSound f9046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9046
  · intro a ha; simp [p9046] at ha; subst a; trivial
  · exact checked9046
theorem derived9046 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9046 := by
  apply localUnsat_implies_entails f9046 [c9034, c9018, c8905, c8847, c8686, c8421, c9036, c9042, c9045, c7994, c8859, c6066, c5842] c9046 unsat9046 (by rfl) a
  have h0 : Entails.eval a c9034 := derived9034 a h
  have h1 : Entails.eval a c9018 := derived9018 a h
  have h2 : Entails.eval a c8905 := derived8905 a h
  have h3 : Entails.eval a c8847 := derived8847 a h
  have h4 : Entails.eval a c8686 := derived8686 a h
  have h5 : Entails.eval a c8421 := derived8421 a h
  have h6 : Entails.eval a c9036 := derived9036 a h
  have h7 : Entails.eval a c9042 := derived9042 a h
  have h8 : Entails.eval a c9045 := derived9045 a h
  have h9 : Entails.eval a c7994 := derived7994 a h
  have h10 : Entails.eval a c8859 := derived8859 a h
  have h11 : Entails.eval a c6066 := h 6065 (by decide)
  have h12 : Entails.eval a c5842 := h 5841 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9047 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9047 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1412, some c9035, some c279, some c280, some c282, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9047 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9047 : lratChecker f9047 p9047 = .success := by decide +kernel
theorem unsat9047 : Unsatisfiable (PosFin 65) f9047 := by
  apply lratCheckerSound f9047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9047
  · intro a ha; simp [p9047] at ha; subst a; trivial
  · exact checked9047
theorem derived9047 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9047 := by
  apply localUnsat_implies_entails f9047 [c1412, c9035, c279, c280, c282] c9047 unsat9047 (by rfl) a
  have h0 : Entails.eval a c1412 := h 1411 (by decide)
  have h1 : Entails.eval a c9035 := derived9035 a h
  have h2 : Entails.eval a c279 := h 278 (by decide)
  have h3 : Entails.eval a c280 := h 279 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9048 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨63, by decide⟩, true), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9048 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4453, some c4451, some c4469, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9048 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9048 : lratChecker f9048 p9048 = .success := by decide +kernel
theorem unsat9048 : Unsatisfiable (PosFin 65) f9048 := by
  apply lratCheckerSound f9048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9048
  · intro a ha; simp [p9048] at ha; subst a; trivial
  · exact checked9048
theorem derived9048 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9048 := by
  apply localUnsat_implies_entails f9048 [c4453, c4451, c4469] c9048 unsat9048 (by rfl) a
  have h0 : Entails.eval a c4453 := h 4452 (by decide)
  have h1 : Entails.eval a c4451 := h 4450 (by decide)
  have h2 : Entails.eval a c4469 := h 4468 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9049 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9049 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1156, some c1155, some c1160, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9049 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9049 : lratChecker f9049 p9049 = .success := by decide +kernel
theorem unsat9049 : Unsatisfiable (PosFin 65) f9049 := by
  apply lratCheckerSound f9049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9049
  · intro a ha; simp [p9049] at ha; subst a; trivial
  · exact checked9049
theorem derived9049 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9049 := by
  apply localUnsat_implies_entails f9049 [c1156, c1155, c1160] c9049 unsat9049 (by rfl) a
  have h0 : Entails.eval a c1156 := h 1155 (by decide)
  have h1 : Entails.eval a c1155 := h 1154 (by decide)
  have h2 : Entails.eval a c1160 := h 1159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9050 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9050 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c738, some c9029, some c732, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9050 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9050 : lratChecker f9050 p9050 = .success := by decide +kernel
theorem unsat9050 : Unsatisfiable (PosFin 65) f9050 := by
  apply lratCheckerSound f9050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9050
  · intro a ha; simp [p9050] at ha; subst a; trivial
  · exact checked9050
theorem derived9050 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9050 := by
  apply localUnsat_implies_entails f9050 [c738, c9029, c732] c9050 unsat9050 (by rfl) a
  have h0 : Entails.eval a c738 := h 737 (by decide)
  have h1 : Entails.eval a c9029 := derived9029 a h
  have h2 : Entails.eval a c732 := h 731 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived9050

end CochromaticTwenty.Certificates.FixedCore0
