import MerLeanExperiment.Certificates.FixedCore0.Steps1500_1599

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9151 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9151 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9149, some c9135, some c9150, some c9138, some c1143, some c1142, some c8007, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9151 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9151 : lratChecker f9151 p9151 = .success := by decide +kernel
theorem unsat9151 : Unsatisfiable (PosFin 65) f9151 := by
  apply lratCheckerSound f9151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9151
  · intro a ha; simp [p9151] at ha; subst a; trivial
  · exact checked9151
theorem derived9151 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9151 := by
  apply localUnsat_implies_entails f9151 [c8269, c9149, c9135, c9150, c9138, c1143, c1142, c8007] c9151 unsat9151 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9149 := derived9149 a h
  have h2 : Entails.eval a c9135 := derived9135 a h
  have h3 : Entails.eval a c9150 := derived9150 a h
  have h4 : Entails.eval a c9138 := derived9138 a h
  have h5 : Entails.eval a c1143 := h 1142 (by decide)
  have h6 : Entails.eval a c1142 := h 1141 (by decide)
  have h7 : Entails.eval a c8007 := derived8007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9152 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9152 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3038, some c3401, some c3500, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p9152 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9152 : lratChecker f9152 p9152 = .success := by decide +kernel
theorem unsat9152 : Unsatisfiable (PosFin 65) f9152 := by
  apply lratCheckerSound f9152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9152
  · intro a ha; simp [p9152] at ha; subst a; trivial
  · exact checked9152
theorem derived9152 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9152 := by
  apply localUnsat_implies_entails f9152 [c3038, c3401, c3500] c9152 unsat9152 (by rfl) a
  have h0 : Entails.eval a c3038 := h 3037 (by decide)
  have h1 : Entails.eval a c3401 := h 3400 (by decide)
  have h2 : Entails.eval a c3500 := h 3499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9153 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9153 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1219, some c1230, some c8486, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9153 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9153 : lratChecker f9153 p9153 = .success := by decide +kernel
theorem unsat9153 : Unsatisfiable (PosFin 65) f9153 := by
  apply lratCheckerSound f9153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9153
  · intro a ha; simp [p9153] at ha; subst a; trivial
  · exact checked9153
theorem derived9153 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9153 := by
  apply localUnsat_implies_entails f9153 [c1219, c1230, c8486] c9153 unsat9153 (by rfl) a
  have h0 : Entails.eval a c1219 := h 1218 (by decide)
  have h1 : Entails.eval a c1230 := h 1229 (by decide)
  have h2 : Entails.eval a c8486 := derived8486 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9154 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9154 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9152, some c9153, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9154 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9154 : lratChecker f9154 p9154 = .success := by decide +kernel
theorem unsat9154 : Unsatisfiable (PosFin 65) f9154 := by
  apply lratCheckerSound f9154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9154
  · intro a ha; simp [p9154] at ha; subst a; trivial
  · exact checked9154
theorem derived9154 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9154 := by
  apply localUnsat_implies_entails f9154 [c9152, c9153] c9154 unsat9154 (by rfl) a
  have h0 : Entails.eval a c9152 := derived9152 a h
  have h1 : Entails.eval a c9153 := derived9153 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9155 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9155 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9151, some c9154, some c9140, some c9102, some c9111, some c2613, some c2642, some c8300, some c8380, some c3763, some c3775, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9155 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9155 : lratChecker f9155 p9155 = .success := by decide +kernel
theorem unsat9155 : Unsatisfiable (PosFin 65) f9155 := by
  apply lratCheckerSound f9155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9155
  · intro a ha; simp [p9155] at ha; subst a; trivial
  · exact checked9155
theorem derived9155 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9155 := by
  apply localUnsat_implies_entails f9155 [c9098, c9151, c9154, c9140, c9102, c9111, c2613, c2642, c8300, c8380, c3763, c3775] c9155 unsat9155 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9151 := derived9151 a h
  have h2 : Entails.eval a c9154 := derived9154 a h
  have h3 : Entails.eval a c9140 := derived9140 a h
  have h4 : Entails.eval a c9102 := derived9102 a h
  have h5 : Entails.eval a c9111 := derived9111 a h
  have h6 : Entails.eval a c2613 := h 2612 (by decide)
  have h7 : Entails.eval a c2642 := h 2641 (by decide)
  have h8 : Entails.eval a c8300 := derived8300 a h
  have h9 : Entails.eval a c8380 := derived8380 a h
  have h10 : Entails.eval a c3763 := h 3762 (by decide)
  have h11 : Entails.eval a c3775 := h 3774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9156 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9156 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9151, some c9098, some c9155, some c7994, some c3726, some c1096, some c1110, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9156 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9156 : lratChecker f9156 p9156 = .success := by decide +kernel
theorem unsat9156 : Unsatisfiable (PosFin 65) f9156 := by
  apply lratCheckerSound f9156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9156
  · intro a ha; simp [p9156] at ha; subst a; trivial
  · exact checked9156
theorem derived9156 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9156 := by
  apply localUnsat_implies_entails f9156 [c9151, c9098, c9155, c7994, c3726, c1096, c1110] c9156 unsat9156 (by rfl) a
  have h0 : Entails.eval a c9151 := derived9151 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9155 := derived9155 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c3726 := h 3725 (by decide)
  have h5 : Entails.eval a c1096 := h 1095 (by decide)
  have h6 : Entails.eval a c1110 := h 1109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9157 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9157 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9151, some c9154, some c7994, some c8380, some c9140, some c4717, some c3190, some c3146, some c3840, some c3835, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9157 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9157 : lratChecker f9157 p9157 = .success := by decide +kernel
theorem unsat9157 : Unsatisfiable (PosFin 65) f9157 := by
  apply lratCheckerSound f9157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9157
  · intro a ha; simp [p9157] at ha; subst a; trivial
  · exact checked9157
theorem derived9157 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9157 := by
  apply localUnsat_implies_entails f9157 [c9098, c9151, c9154, c7994, c8380, c9140, c4717, c3190, c3146, c3840, c3835] c9157 unsat9157 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9151 := derived9151 a h
  have h2 : Entails.eval a c9154 := derived9154 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8380 := derived8380 a h
  have h5 : Entails.eval a c9140 := derived9140 a h
  have h6 : Entails.eval a c4717 := h 4716 (by decide)
  have h7 : Entails.eval a c3190 := h 3189 (by decide)
  have h8 : Entails.eval a c3146 := h 3145 (by decide)
  have h9 : Entails.eval a c3840 := h 3839 (by decide)
  have h10 : Entails.eval a c3835 := h 3834 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9158 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9158 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9157, some c9098, some c9156, some c9124, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9158 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9158 : lratChecker f9158 p9158 = .success := by decide +kernel
theorem unsat9158 : Unsatisfiable (PosFin 65) f9158 := by
  apply lratCheckerSound f9158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9158
  · intro a ha; simp [p9158] at ha; subst a; trivial
  · exact checked9158
theorem derived9158 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9158 := by
  apply localUnsat_implies_entails f9158 [c9157, c9098, c9156, c9124] c9158 unsat9158 (by rfl) a
  have h0 : Entails.eval a c9157 := derived9157 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9156 := derived9156 a h
  have h3 : Entails.eval a c9124 := derived9124 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9159 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9159 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9157, some c9098, some c9151, some c9154, some c9140, some c9102, some c4717, some c9105, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9159 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9159 : lratChecker f9159 p9159 = .success := by decide +kernel
theorem unsat9159 : Unsatisfiable (PosFin 65) f9159 := by
  apply lratCheckerSound f9159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9159
  · intro a ha; simp [p9159] at ha; subst a; trivial
  · exact checked9159
theorem derived9159 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9159 := by
  apply localUnsat_implies_entails f9159 [c9157, c9098, c9151, c9154, c9140, c9102, c4717, c9105] c9159 unsat9159 (by rfl) a
  have h0 : Entails.eval a c9157 := derived9157 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9151 := derived9151 a h
  have h3 : Entails.eval a c9154 := derived9154 a h
  have h4 : Entails.eval a c9140 := derived9140 a h
  have h5 : Entails.eval a c9102 := derived9102 a h
  have h6 : Entails.eval a c4717 := h 4716 (by decide)
  have h7 : Entails.eval a c9105 := derived9105 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9160 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨63, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9160 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1106, some c1095, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9160 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9160 : lratChecker f9160 p9160 = .success := by decide +kernel
theorem unsat9160 : Unsatisfiable (PosFin 65) f9160 := by
  apply lratCheckerSound f9160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9160
  · intro a ha; simp [p9160] at ha; subst a; trivial
  · exact checked9160
theorem derived9160 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9160 := by
  apply localUnsat_implies_entails f9160 [c1106, c1095] c9160 unsat9160 (by rfl) a
  have h0 : Entails.eval a c1106 := h 1105 (by decide)
  have h1 : Entails.eval a c1095 := h 1094 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9161 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9161 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9151, some c9154, some c9157, some c9158, some c9159, some c9160, some c3740, some c4448, some c4717, some c9105, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9161 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9161 : lratChecker f9161 p9161 = .success := by decide +kernel
theorem unsat9161 : Unsatisfiable (PosFin 65) f9161 := by
  apply lratCheckerSound f9161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9161
  · intro a ha; simp [p9161] at ha; subst a; trivial
  · exact checked9161
theorem derived9161 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9161 := by
  apply localUnsat_implies_entails f9161 [c9098, c9151, c9154, c9157, c9158, c9159, c9160, c3740, c4448, c4717, c9105] c9161 unsat9161 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9151 := derived9151 a h
  have h2 : Entails.eval a c9154 := derived9154 a h
  have h3 : Entails.eval a c9157 := derived9157 a h
  have h4 : Entails.eval a c9158 := derived9158 a h
  have h5 : Entails.eval a c9159 := derived9159 a h
  have h6 : Entails.eval a c9160 := derived9160 a h
  have h7 : Entails.eval a c3740 := h 3739 (by decide)
  have h8 : Entails.eval a c4448 := h 4447 (by decide)
  have h9 : Entails.eval a c4717 := h 4716 (by decide)
  have h10 : Entails.eval a c9105 := derived9105 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9162 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨64, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9162 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9124, some c9140, some c1097, some c3737, some c3744, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9162 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9162 : lratChecker f9162 p9162 = .success := by decide +kernel
theorem unsat9162 : Unsatisfiable (PosFin 65) f9162 := by
  apply lratCheckerSound f9162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9162
  · intro a ha; simp [p9162] at ha; subst a; trivial
  · exact checked9162
theorem derived9162 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9162 := by
  apply localUnsat_implies_entails f9162 [c9124, c9140, c1097, c3737, c3744] c9162 unsat9162 (by rfl) a
  have h0 : Entails.eval a c9124 := derived9124 a h
  have h1 : Entails.eval a c9140 := derived9140 a h
  have h2 : Entails.eval a c1097 := h 1096 (by decide)
  have h3 : Entails.eval a c3737 := h 3736 (by decide)
  have h4 : Entails.eval a c3744 := h 3743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9163 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9163 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9151, some c9098, some c9124, some c9162, some c3726, some c1096, some c1110, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9163 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9163 : lratChecker f9163 p9163 = .success := by decide +kernel
theorem unsat9163 : Unsatisfiable (PosFin 65) f9163 := by
  apply lratCheckerSound f9163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9163
  · intro a ha; simp [p9163] at ha; subst a; trivial
  · exact checked9163
theorem derived9163 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9163 := by
  apply localUnsat_implies_entails f9163 [c9151, c9098, c9124, c9162, c3726, c1096, c1110] c9163 unsat9163 (by rfl) a
  have h0 : Entails.eval a c9151 := derived9151 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9124 := derived9124 a h
  have h3 : Entails.eval a c9162 := derived9162 a h
  have h4 : Entails.eval a c3726 := h 3725 (by decide)
  have h5 : Entails.eval a c1096 := h 1095 (by decide)
  have h6 : Entails.eval a c1110 := h 1109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9164 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9164 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4331, some c3763, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p9164 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9164 : lratChecker f9164 p9164 = .success := by decide +kernel
theorem unsat9164 : Unsatisfiable (PosFin 65) f9164 := by
  apply lratCheckerSound f9164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9164
  · intro a ha; simp [p9164] at ha; subst a; trivial
  · exact checked9164
theorem derived9164 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9164 := by
  apply localUnsat_implies_entails f9164 [c4331, c3763] c9164 unsat9164 (by rfl) a
  have h0 : Entails.eval a c4331 := h 4330 (by decide)
  have h1 : Entails.eval a c3763 := h 3762 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9165 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9165 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9161, some c9098, some c9151, some c9154, some c9163, some c7994, some c9140, some c1097, some c9021, some c4733, some c3728, some c3733, some c3741, some c9164, some c3201, some c3771, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9165 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9165 : lratChecker f9165 p9165 = .success := by decide +kernel
theorem unsat9165 : Unsatisfiable (PosFin 65) f9165 := by
  apply lratCheckerSound f9165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9165
  · intro a ha; simp [p9165] at ha; subst a; trivial
  · exact checked9165
theorem derived9165 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9165 := by
  apply localUnsat_implies_entails f9165 [c9161, c9098, c9151, c9154, c9163, c7994, c9140, c1097, c9021, c4733, c3728, c3733, c3741, c9164, c3201, c3771] c9165 unsat9165 (by rfl) a
  have h0 : Entails.eval a c9161 := derived9161 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9151 := derived9151 a h
  have h3 : Entails.eval a c9154 := derived9154 a h
  have h4 : Entails.eval a c9163 := derived9163 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c9140 := derived9140 a h
  have h7 : Entails.eval a c1097 := h 1096 (by decide)
  have h8 : Entails.eval a c9021 := derived9021 a h
  have h9 : Entails.eval a c4733 := h 4732 (by decide)
  have h10 : Entails.eval a c3728 := h 3727 (by decide)
  have h11 : Entails.eval a c3733 := h 3732 (by decide)
  have h12 : Entails.eval a c3741 := h 3740 (by decide)
  have h13 : Entails.eval a c9164 := derived9164 a h
  have h14 : Entails.eval a c3201 := h 3200 (by decide)
  have h15 : Entails.eval a c3771 := h 3770 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9166 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, true), (⟨52, by decide⟩, true), (⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9166 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3708, some c8763, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9166 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9166 : lratChecker f9166 p9166 = .success := by decide +kernel
theorem unsat9166 : Unsatisfiable (PosFin 65) f9166 := by
  apply lratCheckerSound f9166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9166
  · intro a ha; simp [p9166] at ha; subst a; trivial
  · exact checked9166
theorem derived9166 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9166 := by
  apply localUnsat_implies_entails f9166 [c3708, c8763] c9166 unsat9166 (by rfl) a
  have h0 : Entails.eval a c3708 := h 3707 (by decide)
  have h1 : Entails.eval a c8763 := derived8763 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9167 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9167 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9151, some c8801, some c8715, some c8818, some c8812, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9167 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9167 : lratChecker f9167 p9167 = .success := by decide +kernel
theorem unsat9167 : Unsatisfiable (PosFin 65) f9167 := by
  apply lratCheckerSound f9167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9167
  · intro a ha; simp [p9167] at ha; subst a; trivial
  · exact checked9167
theorem derived9167 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9167 := by
  apply localUnsat_implies_entails f9167 [c9151, c8801, c8715, c8818, c8812] c9167 unsat9167 (by rfl) a
  have h0 : Entails.eval a c9151 := derived9151 a h
  have h1 : Entails.eval a c8801 := derived8801 a h
  have h2 : Entails.eval a c8715 := derived8715 a h
  have h3 : Entails.eval a c8818 := derived8818 a h
  have h4 : Entails.eval a c8812 := derived8812 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9168 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9168 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9151, some c9161, some c9165, some c9115, some c9167, some c8731, some c8763, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9168 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9168 : lratChecker f9168 p9168 = .success := by decide +kernel
theorem unsat9168 : Unsatisfiable (PosFin 65) f9168 := by
  apply lratCheckerSound f9168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9168
  · intro a ha; simp [p9168] at ha; subst a; trivial
  · exact checked9168
theorem derived9168 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9168 := by
  apply localUnsat_implies_entails f9168 [c9151, c9161, c9165, c9115, c9167, c8731, c8763] c9168 unsat9168 (by rfl) a
  have h0 : Entails.eval a c9151 := derived9151 a h
  have h1 : Entails.eval a c9161 := derived9161 a h
  have h2 : Entails.eval a c9165 := derived9165 a h
  have h3 : Entails.eval a c9115 := derived9115 a h
  have h4 : Entails.eval a c9167 := derived9167 a h
  have h5 : Entails.eval a c8731 := derived8731 a h
  have h6 : Entails.eval a c8763 := derived8763 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9169 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9169 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9168, some c9098, some c1152, some c2897, some c3418, some c3840, some c3835, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9169 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9169 : lratChecker f9169 p9169 = .success := by decide +kernel
theorem unsat9169 : Unsatisfiable (PosFin 65) f9169 := by
  apply lratCheckerSound f9169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9169
  · intro a ha; simp [p9169] at ha; subst a; trivial
  · exact checked9169
theorem derived9169 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9169 := by
  apply localUnsat_implies_entails f9169 [c9168, c9098, c1152, c2897, c3418, c3840, c3835] c9169 unsat9169 (by rfl) a
  have h0 : Entails.eval a c9168 := derived9168 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c1152 := h 1151 (by decide)
  have h3 : Entails.eval a c2897 := h 2896 (by decide)
  have h4 : Entails.eval a c3418 := h 3417 (by decide)
  have h5 : Entails.eval a c3840 := h 3839 (by decide)
  have h6 : Entails.eval a c3835 := h 3834 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9170 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨12, by decide⟩, false), (⟨53, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9170 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1292, some c1161, some c7994, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9170 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9170 : lratChecker f9170 p9170 = .success := by decide +kernel
theorem unsat9170 : Unsatisfiable (PosFin 65) f9170 := by
  apply lratCheckerSound f9170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9170
  · intro a ha; simp [p9170] at ha; subst a; trivial
  · exact checked9170
theorem derived9170 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9170 := by
  apply localUnsat_implies_entails f9170 [c1292, c1161, c7994] c9170 unsat9170 (by rfl) a
  have h0 : Entails.eval a c1292 := h 1291 (by decide)
  have h1 : Entails.eval a c1161 := h 1160 (by decide)
  have h2 : Entails.eval a c7994 := derived7994 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9171 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9171 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9151, some c9098, some c9168, some c9170, some c9169, some c1151, some c7994, some c1272, some c9124, some c9115, some c9167, some c8731, some c8763, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9171 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9171 : lratChecker f9171 p9171 = .success := by decide +kernel
theorem unsat9171 : Unsatisfiable (PosFin 65) f9171 := by
  apply lratCheckerSound f9171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9171
  · intro a ha; simp [p9171] at ha; subst a; trivial
  · exact checked9171
theorem derived9171 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9171 := by
  apply localUnsat_implies_entails f9171 [c9151, c9098, c9168, c9170, c9169, c1151, c7994, c1272, c9124, c9115, c9167, c8731, c8763] c9171 unsat9171 (by rfl) a
  have h0 : Entails.eval a c9151 := derived9151 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9168 := derived9168 a h
  have h3 : Entails.eval a c9170 := derived9170 a h
  have h4 : Entails.eval a c9169 := derived9169 a h
  have h5 : Entails.eval a c1151 := h 1150 (by decide)
  have h6 : Entails.eval a c7994 := derived7994 a h
  have h7 : Entails.eval a c1272 := h 1271 (by decide)
  have h8 : Entails.eval a c9124 := derived9124 a h
  have h9 : Entails.eval a c9115 := derived9115 a h
  have h10 : Entails.eval a c9167 := derived9167 a h
  have h11 : Entails.eval a c8731 := derived8731 a h
  have h12 : Entails.eval a c8763 := derived8763 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9172 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9172 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9124, some c9119, some c3528, some c3737, some c2624, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9172 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9172 : lratChecker f9172 p9172 = .success := by decide +kernel
theorem unsat9172 : Unsatisfiable (PosFin 65) f9172 := by
  apply lratCheckerSound f9172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9172
  · intro a ha; simp [p9172] at ha; subst a; trivial
  · exact checked9172
theorem derived9172 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9172 := by
  apply localUnsat_implies_entails f9172 [c9124, c9119, c3528, c3737, c2624] c9172 unsat9172 (by rfl) a
  have h0 : Entails.eval a c9124 := derived9124 a h
  have h1 : Entails.eval a c9119 := derived9119 a h
  have h2 : Entails.eval a c3528 := h 3527 (by decide)
  have h3 : Entails.eval a c3737 := h 3736 (by decide)
  have h4 : Entails.eval a c2624 := h 2623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9173 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨19, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9173 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3703, some c3696, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p9173 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9173 : lratChecker f9173 p9173 = .success := by decide +kernel
theorem unsat9173 : Unsatisfiable (PosFin 65) f9173 := by
  apply lratCheckerSound f9173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9173
  · intro a ha; simp [p9173] at ha; subst a; trivial
  · exact checked9173
theorem derived9173 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9173 := by
  apply localUnsat_implies_entails f9173 [c3703, c3696] c9173 unsat9173 (by rfl) a
  have h0 : Entails.eval a c3703 := h 3702 (by decide)
  have h1 : Entails.eval a c3696 := h 3695 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9174 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9174 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9151, some c9098, some c9115, some c9167, some c8731, some c8846, some c8840, some c9173, some c1062, some c1063, some c602, some c601, some c604, some c651, some c99, some c648, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9174 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9174 : lratChecker f9174 p9174 = .success := by decide +kernel
theorem unsat9174 : Unsatisfiable (PosFin 65) f9174 := by
  apply lratCheckerSound f9174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9174
  · intro a ha; simp [p9174] at ha; subst a; trivial
  · exact checked9174
theorem derived9174 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9174 := by
  apply localUnsat_implies_entails f9174 [c9151, c9098, c9115, c9167, c8731, c8846, c8840, c9173, c1062, c1063, c602, c601, c604, c651, c99, c648] c9174 unsat9174 (by rfl) a
  have h0 : Entails.eval a c9151 := derived9151 a h
  have h1 : Entails.eval a c9098 := derived9098 a h
  have h2 : Entails.eval a c9115 := derived9115 a h
  have h3 : Entails.eval a c9167 := derived9167 a h
  have h4 : Entails.eval a c8731 := derived8731 a h
  have h5 : Entails.eval a c8846 := derived8846 a h
  have h6 : Entails.eval a c8840 := derived8840 a h
  have h7 : Entails.eval a c9173 := derived9173 a h
  have h8 : Entails.eval a c1062 := h 1061 (by decide)
  have h9 : Entails.eval a c1063 := h 1062 (by decide)
  have h10 : Entails.eval a c602 := h 601 (by decide)
  have h11 : Entails.eval a c601 := h 600 (by decide)
  have h12 : Entails.eval a c604 := h 603 (by decide)
  have h13 : Entails.eval a c651 := h 650 (by decide)
  have h14 : Entails.eval a c99 := h 98 (by decide)
  have h15 : Entails.eval a c648 := h 647 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9175 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨64, by decide⟩, false), (⟨12, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9175 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3728, some c3745, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p9175 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9175 : lratChecker f9175 p9175 = .success := by decide +kernel
theorem unsat9175 : Unsatisfiable (PosFin 65) f9175 := by
  apply lratCheckerSound f9175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9175
  · intro a ha; simp [p9175] at ha; subst a; trivial
  · exact checked9175
theorem derived9175 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9175 := by
  apply localUnsat_implies_entails f9175 [c3728, c3745] c9175 unsat9175 (by rfl) a
  have h0 : Entails.eval a c3728 := h 3727 (by decide)
  have h1 : Entails.eval a c3745 := h 3744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9176 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9176 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9171, some c9151, some c9098, some c9174, some c9172, some c8300, some c8380, some c9175, some c1100, some c1111, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9176 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9176 : lratChecker f9176 p9176 = .success := by decide +kernel
theorem unsat9176 : Unsatisfiable (PosFin 65) f9176 := by
  apply lratCheckerSound f9176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9176
  · intro a ha; simp [p9176] at ha; subst a; trivial
  · exact checked9176
theorem derived9176 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9176 := by
  apply localUnsat_implies_entails f9176 [c9171, c9151, c9098, c9174, c9172, c8300, c8380, c9175, c1100, c1111] c9176 unsat9176 (by rfl) a
  have h0 : Entails.eval a c9171 := derived9171 a h
  have h1 : Entails.eval a c9151 := derived9151 a h
  have h2 : Entails.eval a c9098 := derived9098 a h
  have h3 : Entails.eval a c9174 := derived9174 a h
  have h4 : Entails.eval a c9172 := derived9172 a h
  have h5 : Entails.eval a c8300 := derived8300 a h
  have h6 : Entails.eval a c8380 := derived8380 a h
  have h7 : Entails.eval a c9175 := derived9175 a h
  have h8 : Entails.eval a c1100 := h 1099 (by decide)
  have h9 : Entails.eval a c1111 := h 1110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9177 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9177 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9176, some c9171, some c9151, some c9098, some c9115, some c9167, some c8731, some c9173, some c1066, some c1091, some c585, some c1098, some c1101, some c5309, some c5477, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9177 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9177 : lratChecker f9177 p9177 = .success := by decide +kernel
theorem unsat9177 : Unsatisfiable (PosFin 65) f9177 := by
  apply lratCheckerSound f9177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9177
  · intro a ha; simp [p9177] at ha; subst a; trivial
  · exact checked9177
theorem derived9177 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9177 := by
  apply localUnsat_implies_entails f9177 [c9176, c9171, c9151, c9098, c9115, c9167, c8731, c9173, c1066, c1091, c585, c1098, c1101, c5309, c5477] c9177 unsat9177 (by rfl) a
  have h0 : Entails.eval a c9176 := derived9176 a h
  have h1 : Entails.eval a c9171 := derived9171 a h
  have h2 : Entails.eval a c9151 := derived9151 a h
  have h3 : Entails.eval a c9098 := derived9098 a h
  have h4 : Entails.eval a c9115 := derived9115 a h
  have h5 : Entails.eval a c9167 := derived9167 a h
  have h6 : Entails.eval a c8731 := derived8731 a h
  have h7 : Entails.eval a c9173 := derived9173 a h
  have h8 : Entails.eval a c1066 := h 1065 (by decide)
  have h9 : Entails.eval a c1091 := h 1090 (by decide)
  have h10 : Entails.eval a c585 := h 584 (by decide)
  have h11 : Entails.eval a c1098 := h 1097 (by decide)
  have h12 : Entails.eval a c1101 := h 1100 (by decide)
  have h13 : Entails.eval a c5309 := h 5308 (by decide)
  have h14 : Entails.eval a c5477 := h 5476 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9178 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9178 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8777, some c8841, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9178 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9178 : lratChecker f9178 p9178 = .success := by decide +kernel
theorem unsat9178 : Unsatisfiable (PosFin 65) f9178 := by
  apply lratCheckerSound f9178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9178
  · intro a ha; simp [p9178] at ha; subst a; trivial
  · exact checked9178
theorem derived9178 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9178 := by
  apply localUnsat_implies_entails f9178 [c8777, c8841] c9178 unsat9178 (by rfl) a
  have h0 : Entails.eval a c8777 := derived8777 a h
  have h1 : Entails.eval a c8841 := derived8841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9179 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9179 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9151, some c9171, some c9177, some c9172, some c3728, some c3735, some c3733, some c3741, some c9175, some c9176, some c8801, some c3699, some c8837, some c8975, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9179 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9179 : lratChecker f9179 p9179 = .success := by decide +kernel
theorem unsat9179 : Unsatisfiable (PosFin 65) f9179 := by
  apply lratCheckerSound f9179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9179
  · intro a ha; simp [p9179] at ha; subst a; trivial
  · exact checked9179
theorem derived9179 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9179 := by
  apply localUnsat_implies_entails f9179 [c9098, c9151, c9171, c9177, c9172, c3728, c3735, c3733, c3741, c9175, c9176, c8801, c3699, c8837, c8975] c9179 unsat9179 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9151 := derived9151 a h
  have h2 : Entails.eval a c9171 := derived9171 a h
  have h3 : Entails.eval a c9177 := derived9177 a h
  have h4 : Entails.eval a c9172 := derived9172 a h
  have h5 : Entails.eval a c3728 := h 3727 (by decide)
  have h6 : Entails.eval a c3735 := h 3734 (by decide)
  have h7 : Entails.eval a c3733 := h 3732 (by decide)
  have h8 : Entails.eval a c3741 := h 3740 (by decide)
  have h9 : Entails.eval a c9175 := derived9175 a h
  have h10 : Entails.eval a c9176 := derived9176 a h
  have h11 : Entails.eval a c8801 := derived8801 a h
  have h12 : Entails.eval a c3699 := h 3698 (by decide)
  have h13 : Entails.eval a c8837 := derived8837 a h
  have h14 : Entails.eval a c8975 := derived8975 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9180 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9180 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9171, some c9177, some c9172, some c7994, some c9176, some c9151, some c9178, some c9179, some c8731, some c3703, some c148, some c155, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9180 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9180 : lratChecker f9180 p9180 = .success := by decide +kernel
theorem unsat9180 : Unsatisfiable (PosFin 65) f9180 := by
  apply lratCheckerSound f9180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9180
  · intro a ha; simp [p9180] at ha; subst a; trivial
  · exact checked9180
theorem derived9180 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9180 := by
  apply localUnsat_implies_entails f9180 [c9098, c9171, c9177, c9172, c7994, c9176, c9151, c9178, c9179, c8731, c3703, c148, c155] c9180 unsat9180 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9171 := derived9171 a h
  have h2 : Entails.eval a c9177 := derived9177 a h
  have h3 : Entails.eval a c9172 := derived9172 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c9176 := derived9176 a h
  have h6 : Entails.eval a c9151 := derived9151 a h
  have h7 : Entails.eval a c9178 := derived9178 a h
  have h8 : Entails.eval a c9179 := derived9179 a h
  have h9 : Entails.eval a c8731 := derived8731 a h
  have h10 : Entails.eval a c3703 := h 3702 (by decide)
  have h11 : Entails.eval a c148 := h 147 (by decide)
  have h12 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9181 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨9, by decide⟩, false), (⟨64, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9181 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c1101, some c1103, some c1114, some c1111, some c8801, some c1070, some c8837, some c8975, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9181 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9181 : lratChecker f9181 p9181 = .success := by decide +kernel
theorem unsat9181 : Unsatisfiable (PosFin 65) f9181 := by
  apply lratCheckerSound f9181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9181
  · intro a ha; simp [p9181] at ha; subst a; trivial
  · exact checked9181
theorem derived9181 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9181 := by
  apply localUnsat_implies_entails f9181 [c7994, c1101, c1103, c1114, c1111, c8801, c1070, c8837, c8975] c9181 unsat9181 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c1101 := h 1100 (by decide)
  have h2 : Entails.eval a c1103 := h 1102 (by decide)
  have h3 : Entails.eval a c1114 := h 1113 (by decide)
  have h4 : Entails.eval a c1111 := h 1110 (by decide)
  have h5 : Entails.eval a c8801 := derived8801 a h
  have h6 : Entails.eval a c1070 := h 1069 (by decide)
  have h7 : Entails.eval a c8837 := derived8837 a h
  have h8 : Entails.eval a c8975 := derived8975 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9182 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9182 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9151, some c9178, some c9171, some c9098, some c9176, some c9177, some c9172, some c7994, some c9180, some c1101, some c1103, some c9181, some c8731, some c8764, some c9095, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9182 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9182 : lratChecker f9182 p9182 = .success := by decide +kernel
theorem unsat9182 : Unsatisfiable (PosFin 65) f9182 := by
  apply lratCheckerSound f9182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9182
  · intro a ha; simp [p9182] at ha; subst a; trivial
  · exact checked9182
theorem derived9182 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9182 := by
  apply localUnsat_implies_entails f9182 [c9151, c9178, c9171, c9098, c9176, c9177, c9172, c7994, c9180, c1101, c1103, c9181, c8731, c8764, c9095] c9182 unsat9182 (by rfl) a
  have h0 : Entails.eval a c9151 := derived9151 a h
  have h1 : Entails.eval a c9178 := derived9178 a h
  have h2 : Entails.eval a c9171 := derived9171 a h
  have h3 : Entails.eval a c9098 := derived9098 a h
  have h4 : Entails.eval a c9176 := derived9176 a h
  have h5 : Entails.eval a c9177 := derived9177 a h
  have h6 : Entails.eval a c9172 := derived9172 a h
  have h7 : Entails.eval a c7994 := derived7994 a h
  have h8 : Entails.eval a c9180 := derived9180 a h
  have h9 : Entails.eval a c1101 := h 1100 (by decide)
  have h10 : Entails.eval a c1103 := h 1102 (by decide)
  have h11 : Entails.eval a c9181 := derived9181 a h
  have h12 : Entails.eval a c8731 := derived8731 a h
  have h13 : Entails.eval a c8764 := derived8764 a h
  have h14 : Entails.eval a c9095 := derived9095 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9183 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9183 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9182, some c9151, some c9178, some c9171, some c1143, some c1142, some c9167, some c1166, some c8731, some c1272, some c1285, some c1286, some c8846, some c1119, some c1122, some c9049, some c1303, some c1168, some c8840, some c583, some c1125, some c1249, some c1242, some c594, some c589, some c610, some c1137, some c1120, some c1121, some c605, some c649, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9183 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked9183 : lratChecker f9183 p9183 = .success := by decide +kernel
theorem unsat9183 : Unsatisfiable (PosFin 65) f9183 := by
  apply lratCheckerSound f9183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9183
  · intro a ha; simp [p9183] at ha; subst a; trivial
  · exact checked9183
theorem derived9183 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9183 := by
  apply localUnsat_implies_entails f9183 [c9182, c9151, c9178, c9171, c1143, c1142, c9167, c1166, c8731, c1272, c1285, c1286, c8846, c1119, c1122, c9049, c1303, c1168, c8840, c583, c1125, c1249, c1242, c594, c589, c610, c1137, c1120, c1121, c605, c649] c9183 unsat9183 (by rfl) a
  have h0 : Entails.eval a c9182 := derived9182 a h
  have h1 : Entails.eval a c9151 := derived9151 a h
  have h2 : Entails.eval a c9178 := derived9178 a h
  have h3 : Entails.eval a c9171 := derived9171 a h
  have h4 : Entails.eval a c1143 := h 1142 (by decide)
  have h5 : Entails.eval a c1142 := h 1141 (by decide)
  have h6 : Entails.eval a c9167 := derived9167 a h
  have h7 : Entails.eval a c1166 := h 1165 (by decide)
  have h8 : Entails.eval a c8731 := derived8731 a h
  have h9 : Entails.eval a c1272 := h 1271 (by decide)
  have h10 : Entails.eval a c1285 := h 1284 (by decide)
  have h11 : Entails.eval a c1286 := h 1285 (by decide)
  have h12 : Entails.eval a c8846 := derived8846 a h
  have h13 : Entails.eval a c1119 := h 1118 (by decide)
  have h14 : Entails.eval a c1122 := h 1121 (by decide)
  have h15 : Entails.eval a c9049 := derived9049 a h
  have h16 : Entails.eval a c1303 := h 1302 (by decide)
  have h17 : Entails.eval a c1168 := h 1167 (by decide)
  have h18 : Entails.eval a c8840 := derived8840 a h
  have h19 : Entails.eval a c583 := h 582 (by decide)
  have h20 : Entails.eval a c1125 := h 1124 (by decide)
  have h21 : Entails.eval a c1249 := h 1248 (by decide)
  have h22 : Entails.eval a c1242 := h 1241 (by decide)
  have h23 : Entails.eval a c594 := h 593 (by decide)
  have h24 : Entails.eval a c589 := h 588 (by decide)
  have h25 : Entails.eval a c610 := h 609 (by decide)
  have h26 : Entails.eval a c1137 := h 1136 (by decide)
  have h27 : Entails.eval a c1120 := h 1119 (by decide)
  have h28 : Entails.eval a c1121 := h 1120 (by decide)
  have h29 : Entails.eval a c605 := h 604 (by decide)
  have h30 : Entails.eval a c649 := h 648 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9184 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9184 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9151, some c9171, some c9182, some c9183, some c9138, some c7994, some c1275, some c1274, some c1303, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9184 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9184 : lratChecker f9184 p9184 = .success := by decide +kernel
theorem unsat9184 : Unsatisfiable (PosFin 65) f9184 := by
  apply lratCheckerSound f9184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9184
  · intro a ha; simp [p9184] at ha; subst a; trivial
  · exact checked9184
theorem derived9184 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9184 := by
  apply localUnsat_implies_entails f9184 [c9151, c9171, c9182, c9183, c9138, c7994, c1275, c1274, c1303] c9184 unsat9184 (by rfl) a
  have h0 : Entails.eval a c9151 := derived9151 a h
  have h1 : Entails.eval a c9171 := derived9171 a h
  have h2 : Entails.eval a c9182 := derived9182 a h
  have h3 : Entails.eval a c9183 := derived9183 a h
  have h4 : Entails.eval a c9138 := derived9138 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c1275 := h 1274 (by decide)
  have h7 : Entails.eval a c1274 := h 1273 (by decide)
  have h8 : Entails.eval a c1303 := h 1302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9185 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨12, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9185 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9134, some c7994, some c3518, some c3719, some c2614, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p9185 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9185 : lratChecker f9185 p9185 = .success := by decide +kernel
theorem unsat9185 : Unsatisfiable (PosFin 65) f9185 := by
  apply lratCheckerSound f9185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9185
  · intro a ha; simp [p9185] at ha; subst a; trivial
  · exact checked9185
theorem derived9185 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9185 := by
  apply localUnsat_implies_entails f9185 [c9134, c7994, c3518, c3719, c2614] c9185 unsat9185 (by rfl) a
  have h0 : Entails.eval a c9134 := derived9134 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c3518 := h 3517 (by decide)
  have h3 : Entails.eval a c3719 := h 3718 (by decide)
  have h4 : Entails.eval a c2614 := h 2613 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9186 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9186 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9184, some c9185, some c3721, some c3723, some c9119, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9186 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9186 : lratChecker f9186 p9186 = .success := by decide +kernel
theorem unsat9186 : Unsatisfiable (PosFin 65) f9186 := by
  apply lratCheckerSound f9186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9186
  · intro a ha; simp [p9186] at ha; subst a; trivial
  · exact checked9186
theorem derived9186 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9186 := by
  apply localUnsat_implies_entails f9186 [c9098, c9184, c9185, c3721, c3723, c9119] c9186 unsat9186 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9184 := derived9184 a h
  have h2 : Entails.eval a c9185 := derived9185 a h
  have h3 : Entails.eval a c3721 := h 3720 (by decide)
  have h4 : Entails.eval a c3723 := h 3722 (by decide)
  have h5 : Entails.eval a c9119 := derived9119 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9187 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9187 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9098, some c9184, some c9185, some c9172, some c9186, some c1091, some c1090, some c1108, some c9119, some c3521, some c2619, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9187 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9187 : lratChecker f9187 p9187 = .success := by decide +kernel
theorem unsat9187 : Unsatisfiable (PosFin 65) f9187 := by
  apply lratCheckerSound f9187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9187
  · intro a ha; simp [p9187] at ha; subst a; trivial
  · exact checked9187
theorem derived9187 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9187 := by
  apply localUnsat_implies_entails f9187 [c9098, c9184, c9185, c9172, c9186, c1091, c1090, c1108, c9119, c3521, c2619] c9187 unsat9187 (by rfl) a
  have h0 : Entails.eval a c9098 := derived9098 a h
  have h1 : Entails.eval a c9184 := derived9184 a h
  have h2 : Entails.eval a c9185 := derived9185 a h
  have h3 : Entails.eval a c9172 := derived9172 a h
  have h4 : Entails.eval a c9186 := derived9186 a h
  have h5 : Entails.eval a c1091 := h 1090 (by decide)
  have h6 : Entails.eval a c1090 := h 1089 (by decide)
  have h7 : Entails.eval a c1108 := h 1107 (by decide)
  have h8 : Entails.eval a c9119 := derived9119 a h
  have h9 : Entails.eval a c3521 := h 3520 (by decide)
  have h10 : Entails.eval a c2619 := h 2618 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9188 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9188 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9187, some c9151, some c9098, some c8300, some c8380, some c9175, some c1111, some c1100, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9188 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9188 : lratChecker f9188 p9188 = .success := by decide +kernel
theorem unsat9188 : Unsatisfiable (PosFin 65) f9188 := by
  apply lratCheckerSound f9188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9188
  · intro a ha; simp [p9188] at ha; subst a; trivial
  · exact checked9188
theorem derived9188 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9188 := by
  apply localUnsat_implies_entails f9188 [c9187, c9151, c9098, c8300, c8380, c9175, c1111, c1100] c9188 unsat9188 (by rfl) a
  have h0 : Entails.eval a c9187 := derived9187 a h
  have h1 : Entails.eval a c9151 := derived9151 a h
  have h2 : Entails.eval a c9098 := derived9098 a h
  have h3 : Entails.eval a c8300 := derived8300 a h
  have h4 : Entails.eval a c8380 := derived8380 a h
  have h5 : Entails.eval a c9175 := derived9175 a h
  have h6 : Entails.eval a c1111 := h 1110 (by decide)
  have h7 : Entails.eval a c1100 := h 1099 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9189 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨64, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9189 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c3728, some c3722, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p9189 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9189 : lratChecker f9189 p9189 = .success := by decide +kernel
theorem unsat9189 : Unsatisfiable (PosFin 65) f9189 := by
  apply lratCheckerSound f9189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9189
  · intro a ha; simp [p9189] at ha; subst a; trivial
  · exact checked9189
theorem derived9189 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9189 := by
  apply localUnsat_implies_entails f9189 [c7994, c3728, c3722] c9189 unsat9189 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c3728 := h 3727 (by decide)
  have h2 : Entails.eval a c3722 := h 3721 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9190 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9190 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9184, some c9151, some c9098, some c9185, some c9187, some c7994, some c9188, some c9189, some c1101, some c1103, some c2617, some c3520, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9190 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9190 : lratChecker f9190 p9190 = .success := by decide +kernel
theorem unsat9190 : Unsatisfiable (PosFin 65) f9190 := by
  apply lratCheckerSound f9190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9190
  · intro a ha; simp [p9190] at ha; subst a; trivial
  · exact checked9190
theorem derived9190 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9190 := by
  apply localUnsat_implies_entails f9190 [c9184, c9151, c9098, c9185, c9187, c7994, c9188, c9189, c1101, c1103, c2617, c3520] c9190 unsat9190 (by rfl) a
  have h0 : Entails.eval a c9184 := derived9184 a h
  have h1 : Entails.eval a c9151 := derived9151 a h
  have h2 : Entails.eval a c9098 := derived9098 a h
  have h3 : Entails.eval a c9185 := derived9185 a h
  have h4 : Entails.eval a c9187 := derived9187 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c9188 := derived9188 a h
  have h7 : Entails.eval a c9189 := derived9189 a h
  have h8 : Entails.eval a c1101 := h 1100 (by decide)
  have h9 : Entails.eval a c1103 := h 1102 (by decide)
  have h10 : Entails.eval a c2617 := h 2616 (by decide)
  have h11 : Entails.eval a c3520 := h 3519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9191 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨12, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9191 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2898, some c3419, some c3833, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9191 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9191 : lratChecker f9191 p9191 = .success := by decide +kernel
theorem unsat9191 : Unsatisfiable (PosFin 65) f9191 := by
  apply lratCheckerSound f9191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9191
  · intro a ha; simp [p9191] at ha; subst a; trivial
  · exact checked9191
theorem derived9191 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9191 := by
  apply localUnsat_implies_entails f9191 [c2898, c3419, c3833] c9191 unsat9191 (by rfl) a
  have h0 : Entails.eval a c2898 := h 2897 (by decide)
  have h1 : Entails.eval a c3419 := h 3418 (by decide)
  have h2 : Entails.eval a c3833 := h 3832 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9192 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9192 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9190, some c9184, some c9098, some c9191, some c9138, some c1143, some c1142, some c1298, some c1286, some c2900, some c3421, some c3836, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9192 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9192 : lratChecker f9192 p9192 = .success := by decide +kernel
theorem unsat9192 : Unsatisfiable (PosFin 65) f9192 := by
  apply lratCheckerSound f9192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9192
  · intro a ha; simp [p9192] at ha; subst a; trivial
  · exact checked9192
theorem derived9192 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9192 := by
  apply localUnsat_implies_entails f9192 [c9190, c9184, c9098, c9191, c9138, c1143, c1142, c1298, c1286, c2900, c3421, c3836] c9192 unsat9192 (by rfl) a
  have h0 : Entails.eval a c9190 := derived9190 a h
  have h1 : Entails.eval a c9184 := derived9184 a h
  have h2 : Entails.eval a c9098 := derived9098 a h
  have h3 : Entails.eval a c9191 := derived9191 a h
  have h4 : Entails.eval a c9138 := derived9138 a h
  have h5 : Entails.eval a c1143 := h 1142 (by decide)
  have h6 : Entails.eval a c1142 := h 1141 (by decide)
  have h7 : Entails.eval a c1298 := h 1297 (by decide)
  have h8 : Entails.eval a c1286 := h 1285 (by decide)
  have h9 : Entails.eval a c2900 := h 2899 (by decide)
  have h10 : Entails.eval a c3421 := h 3420 (by decide)
  have h11 : Entails.eval a c3836 := h 3835 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9193 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9193 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9151, some c9190, some c9192, some c7994, some c1275, some c1274, some c1303, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9193 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9193 : lratChecker f9193 p9193 = .success := by decide +kernel
theorem unsat9193 : Unsatisfiable (PosFin 65) f9193 := by
  apply lratCheckerSound f9193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9193
  · intro a ha; simp [p9193] at ha; subst a; trivial
  · exact checked9193
theorem derived9193 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9193 := by
  apply localUnsat_implies_entails f9193 [c9151, c9190, c9192, c7994, c1275, c1274, c1303] c9193 unsat9193 (by rfl) a
  have h0 : Entails.eval a c9151 := derived9151 a h
  have h1 : Entails.eval a c9190 := derived9190 a h
  have h2 : Entails.eval a c9192 := derived9192 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c1275 := h 1274 (by decide)
  have h5 : Entails.eval a c1274 := h 1273 (by decide)
  have h6 : Entails.eval a c1303 := h 1302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9194 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨55, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9194 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8435, some c8445, some c692, some c8580, some c8423, some c8434, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9194 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9194 : lratChecker f9194 p9194 = .success := by decide +kernel
theorem unsat9194 : Unsatisfiable (PosFin 65) f9194 := by
  apply lratCheckerSound f9194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9194
  · intro a ha; simp [p9194] at ha; subst a; trivial
  · exact checked9194
theorem derived9194 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9194 := by
  apply localUnsat_implies_entails f9194 [c8435, c8445, c692, c8580, c8423, c8434] c9194 unsat9194 (by rfl) a
  have h0 : Entails.eval a c8435 := derived8435 a h
  have h1 : Entails.eval a c8445 := derived8445 a h
  have h2 : Entails.eval a c692 := h 691 (by decide)
  have h3 : Entails.eval a c8580 := derived8580 a h
  have h4 : Entails.eval a c8423 := derived8423 a h
  have h5 : Entails.eval a c8434 := derived8434 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9195 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9195 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8438, some c654, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9195 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9195 : lratChecker f9195 p9195 = .success := by decide +kernel
theorem unsat9195 : Unsatisfiable (PosFin 65) f9195 := by
  apply lratCheckerSound f9195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9195
  · intro a ha; simp [p9195] at ha; subst a; trivial
  · exact checked9195
theorem derived9195 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9195 := by
  apply localUnsat_implies_entails f9195 [c8438, c654] c9195 unsat9195 (by rfl) a
  have h0 : Entails.eval a c8438 := derived8438 a h
  have h1 : Entails.eval a c654 := h 653 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9196 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9196 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1444, some c1420, some c1453, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9196 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9196 : lratChecker f9196 p9196 = .success := by decide +kernel
theorem unsat9196 : Unsatisfiable (PosFin 65) f9196 := by
  apply lratCheckerSound f9196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9196
  · intro a ha; simp [p9196] at ha; subst a; trivial
  · exact checked9196
theorem derived9196 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9196 := by
  apply localUnsat_implies_entails f9196 [c1444, c1420, c1453] c9196 unsat9196 (by rfl) a
  have h0 : Entails.eval a c1444 := h 1443 (by decide)
  have h1 : Entails.eval a c1420 := h 1419 (by decide)
  have h2 : Entails.eval a c1453 := h 1452 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9197 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨7, by decide⟩, false), (⟨62, by decide⟩, false), (⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9197 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c8029, some c9194, some c9195, some c8580, some c881, some c130, some c135, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9197 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9197 : lratChecker f9197 p9197 = .success := by decide +kernel
theorem unsat9197 : Unsatisfiable (PosFin 65) f9197 := by
  apply lratCheckerSound f9197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9197
  · intro a ha; simp [p9197] at ha; subst a; trivial
  · exact checked9197
theorem derived9197 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9197 := by
  apply localUnsat_implies_entails f9197 [c9193, c8029, c9194, c9195, c8580, c881, c130, c135] c9197 unsat9197 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c8029 := derived8029 a h
  have h2 : Entails.eval a c9194 := derived9194 a h
  have h3 : Entails.eval a c9195 := derived9195 a h
  have h4 : Entails.eval a c8580 := derived8580 a h
  have h5 : Entails.eval a c881 := h 880 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9198 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨54, by decide⟩, false), (⟨63, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9198 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9196, some c9142, some c9103, some c9197, some c4292, some c2643, some c4180, some c3328, some c3942, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9198 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9198 : lratChecker f9198 p9198 = .success := by decide +kernel
theorem unsat9198 : Unsatisfiable (PosFin 65) f9198 := by
  apply lratCheckerSound f9198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9198
  · intro a ha; simp [p9198] at ha; subst a; trivial
  · exact checked9198
theorem derived9198 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9198 := by
  apply localUnsat_implies_entails f9198 [c9193, c9196, c9142, c9103, c9197, c4292, c2643, c4180, c3328, c3942] c9198 unsat9198 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9196 := derived9196 a h
  have h2 : Entails.eval a c9142 := derived9142 a h
  have h3 : Entails.eval a c9103 := derived9103 a h
  have h4 : Entails.eval a c9197 := derived9197 a h
  have h5 : Entails.eval a c4292 := h 4291 (by decide)
  have h6 : Entails.eval a c2643 := h 2642 (by decide)
  have h7 : Entails.eval a c4180 := h 4179 (by decide)
  have h8 : Entails.eval a c3328 := h 3327 (by decide)
  have h9 : Entails.eval a c3942 := h 3941 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9199 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9199 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3237, some c3328, some c3641, some c3659, some c3639, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9199 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9199 : lratChecker f9199 p9199 = .success := by decide +kernel
theorem unsat9199 : Unsatisfiable (PosFin 65) f9199 := by
  apply lratCheckerSound f9199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9199
  · intro a ha; simp [p9199] at ha; subst a; trivial
  · exact checked9199
theorem derived9199 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9199 := by
  apply localUnsat_implies_entails f9199 [c3237, c3328, c3641, c3659, c3639] c9199 unsat9199 (by rfl) a
  have h0 : Entails.eval a c3237 := h 3236 (by decide)
  have h1 : Entails.eval a c3328 := h 3327 (by decide)
  have h2 : Entails.eval a c3641 := h 3640 (by decide)
  have h3 : Entails.eval a c3659 := h 3658 (by decide)
  have h4 : Entails.eval a c3639 := h 3638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9200 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9200 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3348, some c3353, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9200 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9200 : lratChecker f9200 p9200 = .success := by decide +kernel
theorem unsat9200 : Unsatisfiable (PosFin 65) f9200 := by
  apply lratCheckerSound f9200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9200
  · intro a ha; simp [p9200] at ha; subst a; trivial
  · exact checked9200
theorem derived9200 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9200 := by
  apply localUnsat_implies_entails f9200 [c3348, c3353] c9200 unsat9200 (by rfl) a
  have h0 : Entails.eval a c3348 := h 3347 (by decide)
  have h1 : Entails.eval a c3353 := h 3352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9201 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨51, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9201 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1374, some c3650, some c4910, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9201 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9201 : lratChecker f9201 p9201 = .success := by decide +kernel
theorem unsat9201 : Unsatisfiable (PosFin 65) f9201 := by
  apply lratCheckerSound f9201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9201
  · intro a ha; simp [p9201] at ha; subst a; trivial
  · exact checked9201
theorem derived9201 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9201 := by
  apply localUnsat_implies_entails f9201 [c1374, c3650, c4910] c9201 unsat9201 (by rfl) a
  have h0 : Entails.eval a c1374 := h 1373 (by decide)
  have h1 : Entails.eval a c3650 := h 3649 (by decide)
  have h2 : Entails.eval a c4910 := h 4909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9202 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9202 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9199, some c8001, some c8029, some c9196, some c9200, some c9201, some c9198, some c3798, some c3291, some c3661, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9202 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9202 : lratChecker f9202 p9202 = .success := by decide +kernel
theorem unsat9202 : Unsatisfiable (PosFin 65) f9202 := by
  apply lratCheckerSound f9202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9202
  · intro a ha; simp [p9202] at ha; subst a; trivial
  · exact checked9202
theorem derived9202 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9202 := by
  apply localUnsat_implies_entails f9202 [c9193, c9199, c8001, c8029, c9196, c9200, c9201, c9198, c3798, c3291, c3661] c9202 unsat9202 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9199 := derived9199 a h
  have h2 : Entails.eval a c8001 := derived8001 a h
  have h3 : Entails.eval a c8029 := derived8029 a h
  have h4 : Entails.eval a c9196 := derived9196 a h
  have h5 : Entails.eval a c9200 := derived9200 a h
  have h6 : Entails.eval a c9201 := derived9201 a h
  have h7 : Entails.eval a c9198 := derived9198 a h
  have h8 : Entails.eval a c3798 := h 3797 (by decide)
  have h9 : Entails.eval a c3291 := h 3290 (by decide)
  have h10 : Entails.eval a c3661 := h 3660 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9203 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨11, by decide⟩, true), (⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9203 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1375, some c9200, some c4911, some c3651, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9203 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9203 : lratChecker f9203 p9203 = .success := by decide +kernel
theorem unsat9203 : Unsatisfiable (PosFin 65) f9203 := by
  apply lratCheckerSound f9203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9203
  · intro a ha; simp [p9203] at ha; subst a; trivial
  · exact checked9203
theorem derived9203 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9203 := by
  apply localUnsat_implies_entails f9203 [c1375, c9200, c4911, c3651] c9203 unsat9203 (by rfl) a
  have h0 : Entails.eval a c1375 := h 1374 (by decide)
  have h1 : Entails.eval a c9200 := derived9200 a h
  have h2 : Entails.eval a c4911 := h 4910 (by decide)
  have h3 : Entails.eval a c3651 := h 3650 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9204 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨9, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9204 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1360, some c3285, some c3338, some c3642, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9204 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9204 : lratChecker f9204 p9204 = .success := by decide +kernel
theorem unsat9204 : Unsatisfiable (PosFin 65) f9204 := by
  apply lratCheckerSound f9204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9204
  · intro a ha; simp [p9204] at ha; subst a; trivial
  · exact checked9204
theorem derived9204 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9204 := by
  apply localUnsat_implies_entails f9204 [c1360, c3285, c3338, c3642] c9204 unsat9204 (by rfl) a
  have h0 : Entails.eval a c1360 := h 1359 (by decide)
  have h1 : Entails.eval a c3285 := h 3284 (by decide)
  have h2 : Entails.eval a c3338 := h 3337 (by decide)
  have h3 : Entails.eval a c3642 := h 3641 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9205 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9205 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9204, some c9196, some c9203, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9205 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9205 : lratChecker f9205 p9205 = .success := by decide +kernel
theorem unsat9205 : Unsatisfiable (PosFin 65) f9205 := by
  apply lratCheckerSound f9205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9205
  · intro a ha; simp [p9205] at ha; subst a; trivial
  · exact checked9205
theorem derived9205 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9205 := by
  apply localUnsat_implies_entails f9205 [c9204, c9196, c9203] c9205 unsat9205 (by rfl) a
  have h0 : Entails.eval a c9204 := derived9204 a h
  have h1 : Entails.eval a c9196 := derived9196 a h
  have h2 : Entails.eval a c9203 := derived9203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9206 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9206 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9202, some c9205, some c8007, some c3237, some c3328, some c3632, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9206 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9206 : lratChecker f9206 p9206 = .success := by decide +kernel
theorem unsat9206 : Unsatisfiable (PosFin 65) f9206 := by
  apply lratCheckerSound f9206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9206
  · intro a ha; simp [p9206] at ha; subst a; trivial
  · exact checked9206
theorem derived9206 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9206 := by
  apply localUnsat_implies_entails f9206 [c9193, c9202, c9205, c8007, c3237, c3328, c3632] c9206 unsat9206 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9202 := derived9202 a h
  have h2 : Entails.eval a c9205 := derived9205 a h
  have h3 : Entails.eval a c8007 := derived8007 a h
  have h4 : Entails.eval a c3237 := h 3236 (by decide)
  have h5 : Entails.eval a c3328 := h 3327 (by decide)
  have h6 : Entails.eval a c3632 := h 3631 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9207 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9207 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9206, some c3336, some c3245, some c3643, some c3659, some c3639, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9207 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9207 : lratChecker f9207 p9207 = .success := by decide +kernel
theorem unsat9207 : Unsatisfiable (PosFin 65) f9207 := by
  apply lratCheckerSound f9207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9207
  · intro a ha; simp [p9207] at ha; subst a; trivial
  · exact checked9207
theorem derived9207 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9207 := by
  apply localUnsat_implies_entails f9207 [c9193, c9206, c3336, c3245, c3643, c3659, c3639] c9207 unsat9207 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9206 := derived9206 a h
  have h2 : Entails.eval a c3336 := h 3335 (by decide)
  have h3 : Entails.eval a c3245 := h 3244 (by decide)
  have h4 : Entails.eval a c3643 := h 3642 (by decide)
  have h5 : Entails.eval a c3659 := h 3658 (by decide)
  have h6 : Entails.eval a c3639 := h 3638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9208 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9208 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9207, some c1105, some c1106, some c1117, some c1118, some c2813, some c3382, some c1370, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9208 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9208 : lratChecker f9208 p9208 = .success := by decide +kernel
theorem unsat9208 : Unsatisfiable (PosFin 65) f9208 := by
  apply lratCheckerSound f9208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9208
  · intro a ha; simp [p9208] at ha; subst a; trivial
  · exact checked9208
theorem derived9208 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9208 := by
  apply localUnsat_implies_entails f9208 [c9193, c9207, c1105, c1106, c1117, c1118, c2813, c3382, c1370] c9208 unsat9208 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9207 := derived9207 a h
  have h2 : Entails.eval a c1105 := h 1104 (by decide)
  have h3 : Entails.eval a c1106 := h 1105 (by decide)
  have h4 : Entails.eval a c1117 := h 1116 (by decide)
  have h5 : Entails.eval a c1118 := h 1117 (by decide)
  have h6 : Entails.eval a c2813 := h 2812 (by decide)
  have h7 : Entails.eval a c3382 := h 3381 (by decide)
  have h8 : Entails.eval a c1370 := h 1369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9209 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨9, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9209 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3236, some c3327, some c3659, some c3639, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9209 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9209 : lratChecker f9209 p9209 = .success := by decide +kernel
theorem unsat9209 : Unsatisfiable (PosFin 65) f9209 := by
  apply lratCheckerSound f9209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9209
  · intro a ha; simp [p9209] at ha; subst a; trivial
  · exact checked9209
theorem derived9209 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9209 := by
  apply localUnsat_implies_entails f9209 [c3236, c3327, c3659, c3639] c9209 unsat9209 (by rfl) a
  have h0 : Entails.eval a c3236 := h 3235 (by decide)
  have h1 : Entails.eval a c3327 := h 3326 (by decide)
  have h2 : Entails.eval a c3659 := h 3658 (by decide)
  have h3 : Entails.eval a c3639 := h 3638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9210 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9210 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9209, some c3258, some c3348, some c3658, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9210 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9210 : lratChecker f9210 p9210 = .success := by decide +kernel
theorem unsat9210 : Unsatisfiable (PosFin 65) f9210 := by
  apply lratCheckerSound f9210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9210
  · intro a ha; simp [p9210] at ha; subst a; trivial
  · exact checked9210
theorem derived9210 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9210 := by
  apply localUnsat_implies_entails f9210 [c9209, c3258, c3348, c3658] c9210 unsat9210 (by rfl) a
  have h0 : Entails.eval a c9209 := derived9209 a h
  have h1 : Entails.eval a c3258 := h 3257 (by decide)
  have h2 : Entails.eval a c3348 := h 3347 (by decide)
  have h3 : Entails.eval a c3658 := h 3657 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9211 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9211 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9210, some c1105, some c1106, some c2810, some c2613, some c3124, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9211 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9211 : lratChecker f9211 p9211 = .success := by decide +kernel
theorem unsat9211 : Unsatisfiable (PosFin 65) f9211 := by
  apply lratCheckerSound f9211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9211
  · intro a ha; simp [p9211] at ha; subst a; trivial
  · exact checked9211
theorem derived9211 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9211 := by
  apply localUnsat_implies_entails f9211 [c9193, c9210, c1105, c1106, c2810, c2613, c3124] c9211 unsat9211 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9210 := derived9210 a h
  have h2 : Entails.eval a c1105 := h 1104 (by decide)
  have h3 : Entails.eval a c1106 := h 1105 (by decide)
  have h4 : Entails.eval a c2810 := h 2809 (by decide)
  have h5 : Entails.eval a c2613 := h 2612 (by decide)
  have h6 : Entails.eval a c3124 := h 3123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9212 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9212 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3258, some c3348, some c3658, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9212 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9212 : lratChecker f9212 p9212 = .success := by decide +kernel
theorem unsat9212 : Unsatisfiable (PosFin 65) f9212 := by
  apply lratCheckerSound f9212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9212
  · intro a ha; simp [p9212] at ha; subst a; trivial
  · exact checked9212
theorem derived9212 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9212 := by
  apply localUnsat_implies_entails f9212 [c3258, c3348, c3658] c9212 unsat9212 (by rfl) a
  have h0 : Entails.eval a c3258 := h 3257 (by decide)
  have h1 : Entails.eval a c3348 := h 3347 (by decide)
  have h2 : Entails.eval a c3658 := h 3657 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9213 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨58, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9213 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3659, some c3639, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9213 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9213 : lratChecker f9213 p9213 = .success := by decide +kernel
theorem unsat9213 : Unsatisfiable (PosFin 65) f9213 := by
  apply lratCheckerSound f9213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9213
  · intro a ha; simp [p9213] at ha; subst a; trivial
  · exact checked9213
theorem derived9213 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9213 := by
  apply localUnsat_implies_entails f9213 [c3659, c3639] c9213 unsat9213 (by rfl) a
  have h0 : Entails.eval a c3659 := h 3658 (by decide)
  have h1 : Entails.eval a c3639 := h 3638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9214 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9214 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3260, some c3235, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9214 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9214 : lratChecker f9214 p9214 = .success := by decide +kernel
theorem unsat9214 : Unsatisfiable (PosFin 65) f9214 := by
  apply lratCheckerSound f9214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9214
  · intro a ha; simp [p9214] at ha; subst a; trivial
  · exact checked9214
theorem derived9214 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9214 := by
  apply localUnsat_implies_entails f9214 [c3260, c3235] c9214 unsat9214 (by rfl) a
  have h0 : Entails.eval a c3260 := h 3259 (by decide)
  have h1 : Entails.eval a c3235 := h 3234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9215 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9215 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9212, some c9214, some c9213, some c3349, some c3334, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9215 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9215 : lratChecker f9215 p9215 = .success := by decide +kernel
theorem unsat9215 : Unsatisfiable (PosFin 65) f9215 := by
  apply lratCheckerSound f9215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9215
  · intro a ha; simp [p9215] at ha; subst a; trivial
  · exact checked9215
theorem derived9215 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9215 := by
  apply localUnsat_implies_entails f9215 [c9212, c9214, c9213, c3349, c3334] c9215 unsat9215 (by rfl) a
  have h0 : Entails.eval a c9212 := derived9212 a h
  have h1 : Entails.eval a c9214 := derived9214 a h
  have h2 : Entails.eval a c9213 := derived9213 a h
  have h3 : Entails.eval a c3349 := h 3348 (by decide)
  have h4 : Entails.eval a c3334 := h 3333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9216 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9216 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9208, some c9211, some c9215, some c1105, some c1106, some c1117, some c1097, some c1096, some c9160, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9216 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9216 : lratChecker f9216 p9216 = .success := by decide +kernel
theorem unsat9216 : Unsatisfiable (PosFin 65) f9216 := by
  apply lratCheckerSound f9216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9216
  · intro a ha; simp [p9216] at ha; subst a; trivial
  · exact checked9216
theorem derived9216 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9216 := by
  apply localUnsat_implies_entails f9216 [c9193, c9208, c9211, c9215, c1105, c1106, c1117, c1097, c1096, c9160] c9216 unsat9216 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9208 := derived9208 a h
  have h2 : Entails.eval a c9211 := derived9211 a h
  have h3 : Entails.eval a c9215 := derived9215 a h
  have h4 : Entails.eval a c1105 := h 1104 (by decide)
  have h5 : Entails.eval a c1106 := h 1105 (by decide)
  have h6 : Entails.eval a c1117 := h 1116 (by decide)
  have h7 : Entails.eval a c1097 := h 1096 (by decide)
  have h8 : Entails.eval a c1096 := h 1095 (by decide)
  have h9 : Entails.eval a c9160 := derived9160 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9217 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨4, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9217 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3015, some c3017, some c3004, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9217 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9217 : lratChecker f9217 p9217 = .success := by decide +kernel
theorem unsat9217 : Unsatisfiable (PosFin 65) f9217 := by
  apply lratCheckerSound f9217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9217
  · intro a ha; simp [p9217] at ha; subst a; trivial
  · exact checked9217
theorem derived9217 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9217 := by
  apply localUnsat_implies_entails f9217 [c3015, c3017, c3004] c9217 unsat9217 (by rfl) a
  have h0 : Entails.eval a c3015 := h 3014 (by decide)
  have h1 : Entails.eval a c3017 := h 3016 (by decide)
  have h2 : Entails.eval a c3004 := h 3003 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9218 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9218 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9216, some c9217, some c1105, some c1106, some c2618, some c2945, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9218 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9218 : lratChecker f9218 p9218 = .success := by decide +kernel
theorem unsat9218 : Unsatisfiable (PosFin 65) f9218 := by
  apply lratCheckerSound f9218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9218
  · intro a ha; simp [p9218] at ha; subst a; trivial
  · exact checked9218
theorem derived9218 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9218 := by
  apply localUnsat_implies_entails f9218 [c9193, c9216, c9217, c1105, c1106, c2618, c2945] c9218 unsat9218 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9216 := derived9216 a h
  have h2 : Entails.eval a c9217 := derived9217 a h
  have h3 : Entails.eval a c1105 := h 1104 (by decide)
  have h4 : Entails.eval a c1106 := h 1105 (by decide)
  have h5 : Entails.eval a c2618 := h 2617 (by decide)
  have h6 : Entails.eval a c2945 := h 2944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9219 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9219 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3236, some c3327, some c2778, some c4027, some c4253, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9219 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9219 : lratChecker f9219 p9219 = .success := by decide +kernel
theorem unsat9219 : Unsatisfiable (PosFin 65) f9219 := by
  apply lratCheckerSound f9219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9219
  · intro a ha; simp [p9219] at ha; subst a; trivial
  · exact checked9219
theorem derived9219 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9219 := by
  apply localUnsat_implies_entails f9219 [c3236, c3327, c2778, c4027, c4253] c9219 unsat9219 (by rfl) a
  have h0 : Entails.eval a c3236 := h 3235 (by decide)
  have h1 : Entails.eval a c3327 := h 3326 (by decide)
  have h2 : Entails.eval a c2778 := h 2777 (by decide)
  have h3 : Entails.eval a c4027 := h 4026 (by decide)
  have h4 : Entails.eval a c4253 := h 4252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9220 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨62, by decide⟩, false), (⟨58, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9220 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3269, some c3334, some c3639, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9220 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9220 : lratChecker f9220 p9220 = .success := by decide +kernel
theorem unsat9220 : Unsatisfiable (PosFin 65) f9220 := by
  apply lratCheckerSound f9220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9220
  · intro a ha; simp [p9220] at ha; subst a; trivial
  · exact checked9220
theorem derived9220 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9220 := by
  apply localUnsat_implies_entails f9220 [c3269, c3334, c3639] c9220 unsat9220 (by rfl) a
  have h0 : Entails.eval a c3269 := h 3268 (by decide)
  have h1 : Entails.eval a c3334 := h 3333 (by decide)
  have h2 : Entails.eval a c3639 := h 3638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9221 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨59, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9221 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3290, some c3292, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9221 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9221 : lratChecker f9221 p9221 = .success := by decide +kernel
theorem unsat9221 : Unsatisfiable (PosFin 65) f9221 := by
  apply lratCheckerSound f9221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9221
  · intro a ha; simp [p9221] at ha; subst a; trivial
  · exact checked9221
theorem derived9221 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9221 := by
  apply localUnsat_implies_entails f9221 [c3290, c3292] c9221 unsat9221 (by rfl) a
  have h0 : Entails.eval a c3290 := h 3289 (by decide)
  have h1 : Entails.eval a c3292 := h 3291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9222 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9222 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3386, some c3617, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9222 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9222 : lratChecker f9222 p9222 = .success := by decide +kernel
theorem unsat9222 : Unsatisfiable (PosFin 65) f9222 := by
  apply lratCheckerSound f9222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9222
  · intro a ha; simp [p9222] at ha; subst a; trivial
  · exact checked9222
theorem derived9222 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9222 := by
  apply localUnsat_implies_entails f9222 [c3386, c3617] c9222 unsat9222 (by rfl) a
  have h0 : Entails.eval a c3386 := h 3385 (by decide)
  have h1 : Entails.eval a c3617 := h 3616 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9223 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9223 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4617, some c9222, some c3680, some c3379, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9223 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9223 : lratChecker f9223 p9223 = .success := by decide +kernel
theorem unsat9223 : Unsatisfiable (PosFin 65) f9223 := by
  apply lratCheckerSound f9223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9223
  · intro a ha; simp [p9223] at ha; subst a; trivial
  · exact checked9223
theorem derived9223 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9223 := by
  apply localUnsat_implies_entails f9223 [c4617, c9222, c3680, c3379] c9223 unsat9223 (by rfl) a
  have h0 : Entails.eval a c4617 := h 4616 (by decide)
  have h1 : Entails.eval a c9222 := derived9222 a h
  have h2 : Entails.eval a c3680 := h 3679 (by decide)
  have h3 : Entails.eval a c3379 := h 3378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9224 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9224 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c3344, some c3346, some c3353, some c8419, some c8029, some c9221, some c9223, some c2782, some c3460, some c3384, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9224 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9224 : lratChecker f9224 p9224 = .success := by decide +kernel
theorem unsat9224 : Unsatisfiable (PosFin 65) f9224 := by
  apply lratCheckerSound f9224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9224
  · intro a ha; simp [p9224] at ha; subst a; trivial
  · exact checked9224
theorem derived9224 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9224 := by
  apply localUnsat_implies_entails f9224 [c9193, c3344, c3346, c3353, c8419, c8029, c9221, c9223, c2782, c3460, c3384] c9224 unsat9224 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c3344 := h 3343 (by decide)
  have h2 : Entails.eval a c3346 := h 3345 (by decide)
  have h3 : Entails.eval a c3353 := h 3352 (by decide)
  have h4 : Entails.eval a c8419 := derived8419 a h
  have h5 : Entails.eval a c8029 := derived8029 a h
  have h6 : Entails.eval a c9221 := derived9221 a h
  have h7 : Entails.eval a c9223 := derived9223 a h
  have h8 : Entails.eval a c2782 := h 2781 (by decide)
  have h9 : Entails.eval a c3460 := h 3459 (by decide)
  have h10 : Entails.eval a c3384 := h 3383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9225 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9225 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3251, some c3255, some c3265, some c3248, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9225 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9225 : lratChecker f9225 p9225 = .success := by decide +kernel
theorem unsat9225 : Unsatisfiable (PosFin 65) f9225 := by
  apply lratCheckerSound f9225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9225
  · intro a ha; simp [p9225] at ha; subst a; trivial
  · exact checked9225
theorem derived9225 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9225 := by
  apply localUnsat_implies_entails f9225 [c3251, c3255, c3265, c3248] c9225 unsat9225 (by rfl) a
  have h0 : Entails.eval a c3251 := h 3250 (by decide)
  have h1 : Entails.eval a c3255 := h 3254 (by decide)
  have h2 : Entails.eval a c3265 := h 3264 (by decide)
  have h3 : Entails.eval a c3248 := h 3247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9226 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9226 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9219, some c9220, some c9224, some c9225, some c3665, some c3637, some c3664, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9226 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9226 : lratChecker f9226 p9226 = .success := by decide +kernel
theorem unsat9226 : Unsatisfiable (PosFin 65) f9226 := by
  apply lratCheckerSound f9226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9226
  · intro a ha; simp [p9226] at ha; subst a; trivial
  · exact checked9226
theorem derived9226 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9226 := by
  apply localUnsat_implies_entails f9226 [c9193, c9219, c9220, c9224, c9225, c3665, c3637, c3664] c9226 unsat9226 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9219 := derived9219 a h
  have h2 : Entails.eval a c9220 := derived9220 a h
  have h3 : Entails.eval a c9224 := derived9224 a h
  have h4 : Entails.eval a c9225 := derived9225 a h
  have h5 : Entails.eval a c3665 := h 3664 (by decide)
  have h6 : Entails.eval a c3637 := h 3636 (by decide)
  have h7 : Entails.eval a c3664 := h 3663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9227 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9227 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9219, some c9226, some c8007, some c3246, some c3337, some c3648, some c3638, some c4031, some c2781, some c4255, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9227 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9227 : lratChecker f9227 p9227 = .success := by decide +kernel
theorem unsat9227 : Unsatisfiable (PosFin 65) f9227 := by
  apply lratCheckerSound f9227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9227
  · intro a ha; simp [p9227] at ha; subst a; trivial
  · exact checked9227
theorem derived9227 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9227 := by
  apply localUnsat_implies_entails f9227 [c9193, c9219, c9226, c8007, c3246, c3337, c3648, c3638, c4031, c2781, c4255] c9227 unsat9227 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9219 := derived9219 a h
  have h2 : Entails.eval a c9226 := derived9226 a h
  have h3 : Entails.eval a c8007 := derived8007 a h
  have h4 : Entails.eval a c3246 := h 3245 (by decide)
  have h5 : Entails.eval a c3337 := h 3336 (by decide)
  have h6 : Entails.eval a c3648 := h 3647 (by decide)
  have h7 : Entails.eval a c3638 := h 3637 (by decide)
  have h8 : Entails.eval a c4031 := h 4030 (by decide)
  have h9 : Entails.eval a c2781 := h 2780 (by decide)
  have h10 : Entails.eval a c4255 := h 4254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9228 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨52, by decide⟩, false), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9228 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3328, some c3342, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9228 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9228 : lratChecker f9228 p9228 = .success := by decide +kernel
theorem unsat9228 : Unsatisfiable (PosFin 65) f9228 := by
  apply lratCheckerSound f9228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9228
  · intro a ha; simp [p9228] at ha; subst a; trivial
  · exact checked9228
theorem derived9228 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9228 := by
  apply localUnsat_implies_entails f9228 [c3328, c3342] c9228 unsat9228 (by rfl) a
  have h0 : Entails.eval a c3328 := h 3327 (by decide)
  have h1 : Entails.eval a c3342 := h 3341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9229 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9229 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3237, some c3249, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9229 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9229 : lratChecker f9229 p9229 = .success := by decide +kernel
theorem unsat9229 : Unsatisfiable (PosFin 65) f9229 := by
  apply lratCheckerSound f9229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9229
  · intro a ha; simp [p9229] at ha; subst a; trivial
  · exact checked9229
theorem derived9229 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9229 := by
  apply localUnsat_implies_entails f9229 [c3237, c3249] c9229 unsat9229 (by rfl) a
  have h0 : Entails.eval a c3237 := h 3236 (by decide)
  have h1 : Entails.eval a c3249 := h 3248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9230 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9230 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c3653, some c3646, some c3632, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9230 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9230 : lratChecker f9230 p9230 = .success := by decide +kernel
theorem unsat9230 : Unsatisfiable (PosFin 65) f9230 := by
  apply lratCheckerSound f9230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9230
  · intro a ha; simp [p9230] at ha; subst a; trivial
  · exact checked9230
theorem derived9230 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9230 := by
  apply localUnsat_implies_entails f9230 [c9228, c9229, c3653, c3646, c3632] c9230 unsat9230 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c3653 := h 3652 (by decide)
  have h3 : Entails.eval a c3646 := h 3645 (by decide)
  have h4 : Entails.eval a c3632 := h 3631 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9231 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨61, by decide⟩, true), (⟨8, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9231 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1418, some c1359, some c4910, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9231 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9231 : lratChecker f9231 p9231 = .success := by decide +kernel
theorem unsat9231 : Unsatisfiable (PosFin 65) f9231 := by
  apply lratCheckerSound f9231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9231
  · intro a ha; simp [p9231] at ha; subst a; trivial
  · exact checked9231
theorem derived9231 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9231 := by
  apply localUnsat_implies_entails f9231 [c1418, c1359, c4910] c9231 unsat9231 (by rfl) a
  have h0 : Entails.eval a c1418 := h 1417 (by decide)
  have h1 : Entails.eval a c1359 := h 1358 (by decide)
  have h2 : Entails.eval a c4910 := h 4909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9232 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9232 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3337, some c3346, some c3357, some c3342, some c3259, some c3248, some c3262, some c3344, some c9231, some c1371, some c1435, some c4911, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9232 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9232 : lratChecker f9232 p9232 = .success := by decide +kernel
theorem unsat9232 : Unsatisfiable (PosFin 65) f9232 := by
  apply lratCheckerSound f9232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9232
  · intro a ha; simp [p9232] at ha; subst a; trivial
  · exact checked9232
theorem derived9232 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9232 := by
  apply localUnsat_implies_entails f9232 [c3337, c3346, c3357, c3342, c3259, c3248, c3262, c3344, c9231, c1371, c1435, c4911] c9232 unsat9232 (by rfl) a
  have h0 : Entails.eval a c3337 := h 3336 (by decide)
  have h1 : Entails.eval a c3346 := h 3345 (by decide)
  have h2 : Entails.eval a c3357 := h 3356 (by decide)
  have h3 : Entails.eval a c3342 := h 3341 (by decide)
  have h4 : Entails.eval a c3259 := h 3258 (by decide)
  have h5 : Entails.eval a c3248 := h 3247 (by decide)
  have h6 : Entails.eval a c3262 := h 3261 (by decide)
  have h7 : Entails.eval a c3344 := h 3343 (by decide)
  have h8 : Entails.eval a c9231 := derived9231 a h
  have h9 : Entails.eval a c1371 := h 1370 (by decide)
  have h10 : Entails.eval a c1435 := h 1434 (by decide)
  have h11 : Entails.eval a c4911 := h 4910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9233 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨51, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9233 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5957, some c3366, some c303, some c3323, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9233 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9233 : lratChecker f9233 p9233 = .success := by decide +kernel
theorem unsat9233 : Unsatisfiable (PosFin 65) f9233 := by
  apply lratCheckerSound f9233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9233
  · intro a ha; simp [p9233] at ha; subst a; trivial
  · exact checked9233
theorem derived9233 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9233 := by
  apply localUnsat_implies_entails f9233 [c5957, c3366, c303, c3323] c9233 unsat9233 (by rfl) a
  have h0 : Entails.eval a c5957 := h 5956 (by decide)
  have h1 : Entails.eval a c3366 := h 3365 (by decide)
  have h2 : Entails.eval a c303 := h 302 (by decide)
  have h3 : Entails.eval a c3323 := h 3322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9234 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨51, by decide⟩, true), (⟨60, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9234 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3337, some c8713, some c9233, some c3365, some c3311, some c3300, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9234 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9234 : lratChecker f9234 p9234 = .success := by decide +kernel
theorem unsat9234 : Unsatisfiable (PosFin 65) f9234 := by
  apply lratCheckerSound f9234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9234
  · intro a ha; simp [p9234] at ha; subst a; trivial
  · exact checked9234
theorem derived9234 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9234 := by
  apply localUnsat_implies_entails f9234 [c3337, c8713, c9233, c3365, c3311, c3300] c9234 unsat9234 (by rfl) a
  have h0 : Entails.eval a c3337 := h 3336 (by decide)
  have h1 : Entails.eval a c8713 := derived8713 a h
  have h2 : Entails.eval a c9233 := derived9233 a h
  have h3 : Entails.eval a c3365 := h 3364 (by decide)
  have h4 : Entails.eval a c3311 := h 3310 (by decide)
  have h5 : Entails.eval a c3300 := h 3299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9235 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9235 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8860, some c181, some c8820, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9235 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9235 : lratChecker f9235 p9235 = .success := by decide +kernel
theorem unsat9235 : Unsatisfiable (PosFin 65) f9235 := by
  apply lratCheckerSound f9235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9235
  · intro a ha; simp [p9235] at ha; subst a; trivial
  · exact checked9235
theorem derived9235 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9235 := by
  apply localUnsat_implies_entails f9235 [c8860, c181, c8820] c9235 unsat9235 (by rfl) a
  have h0 : Entails.eval a c8860 := derived8860 a h
  have h1 : Entails.eval a c181 := h 180 (by decide)
  have h2 : Entails.eval a c8820 := derived8820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9236 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨51, by decide⟩, true), (⟨59, by decide⟩, false), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9236 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c8820, some c8821, some c3359, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9236 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9236 : lratChecker f9236 p9236 = .success := by decide +kernel
theorem unsat9236 : Unsatisfiable (PosFin 65) f9236 := by
  apply lratCheckerSound f9236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9236
  · intro a ha; simp [p9236] at ha; subst a; trivial
  · exact checked9236
theorem derived9236 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9236 := by
  apply localUnsat_implies_entails f9236 [c9193, c8820, c8821, c3359] c9236 unsat9236 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c8820 := derived8820 a h
  have h2 : Entails.eval a c8821 := derived8821 a h
  have h3 : Entails.eval a c3359 := h 3358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9237 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨60, by decide⟩, false), (⟨13, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9237 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9218, some c9227, some c9230, some c9232, some c3337, some c3346, some c3357, some c3342, some c4617, some c1418, some c3613, some c4454, some c3453, some c4295, some c3457, some c3389, some c3351, some c9234, some c9235, some c9236, some c5474, some c8898, some c121, some c3297, some c3321, some c3308, some c3299, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9237 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked9237 : lratChecker f9237 p9237 = .success := by decide +kernel
theorem unsat9237 : Unsatisfiable (PosFin 65) f9237 := by
  apply lratCheckerSound f9237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9237
  · intro a ha; simp [p9237] at ha; subst a; trivial
  · exact checked9237
theorem derived9237 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9237 := by
  apply localUnsat_implies_entails f9237 [c9193, c9218, c9227, c9230, c9232, c3337, c3346, c3357, c3342, c4617, c1418, c3613, c4454, c3453, c4295, c3457, c3389, c3351, c9234, c9235, c9236, c5474, c8898, c121, c3297, c3321, c3308, c3299] c9237 unsat9237 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9218 := derived9218 a h
  have h2 : Entails.eval a c9227 := derived9227 a h
  have h3 : Entails.eval a c9230 := derived9230 a h
  have h4 : Entails.eval a c9232 := derived9232 a h
  have h5 : Entails.eval a c3337 := h 3336 (by decide)
  have h6 : Entails.eval a c3346 := h 3345 (by decide)
  have h7 : Entails.eval a c3357 := h 3356 (by decide)
  have h8 : Entails.eval a c3342 := h 3341 (by decide)
  have h9 : Entails.eval a c4617 := h 4616 (by decide)
  have h10 : Entails.eval a c1418 := h 1417 (by decide)
  have h11 : Entails.eval a c3613 := h 3612 (by decide)
  have h12 : Entails.eval a c4454 := h 4453 (by decide)
  have h13 : Entails.eval a c3453 := h 3452 (by decide)
  have h14 : Entails.eval a c4295 := h 4294 (by decide)
  have h15 : Entails.eval a c3457 := h 3456 (by decide)
  have h16 : Entails.eval a c3389 := h 3388 (by decide)
  have h17 : Entails.eval a c3351 := h 3350 (by decide)
  have h18 : Entails.eval a c9234 := derived9234 a h
  have h19 : Entails.eval a c9235 := derived9235 a h
  have h20 : Entails.eval a c9236 := derived9236 a h
  have h21 : Entails.eval a c5474 := h 5473 (by decide)
  have h22 : Entails.eval a c8898 := derived8898 a h
  have h23 : Entails.eval a c121 := h 120 (by decide)
  have h24 : Entails.eval a c3297 := h 3296 (by decide)
  have h25 : Entails.eval a c3321 := h 3320 (by decide)
  have h26 : Entails.eval a c3308 := h 3307 (by decide)
  have h27 : Entails.eval a c3299 := h 3298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9238 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨63, by decide⟩, false), (⟨62, by decide⟩, false), (⟨59, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9238 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c8893, some c3296, some c6252, some c6073, some c3302, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9238 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9238 : lratChecker f9238 p9238 = .success := by decide +kernel
theorem unsat9238 : Unsatisfiable (PosFin 65) f9238 := by
  apply lratCheckerSound f9238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9238
  · intro a ha; simp [p9238] at ha; subst a; trivial
  · exact checked9238
theorem derived9238 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9238 := by
  apply localUnsat_implies_entails f9238 [c9193, c8893, c3296, c6252, c6073, c3302] c9238 unsat9238 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c8893 := derived8893 a h
  have h2 : Entails.eval a c3296 := h 3295 (by decide)
  have h3 : Entails.eval a c6252 := h 6251 (by decide)
  have h4 : Entails.eval a c6073 := h 6072 (by decide)
  have h5 : Entails.eval a c3302 := h 3301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9239 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨51, by decide⟩, false), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9239 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3364, some c5434, some c3361, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9239 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9239 : lratChecker f9239 p9239 = .success := by decide +kernel
theorem unsat9239 : Unsatisfiable (PosFin 65) f9239 := by
  apply lratCheckerSound f9239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9239
  · intro a ha; simp [p9239] at ha; subst a; trivial
  · exact checked9239
theorem derived9239 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9239 := by
  apply localUnsat_implies_entails f9239 [c3364, c5434, c3361] c9239 unsat9239 (by rfl) a
  have h0 : Entails.eval a c3364 := h 3363 (by decide)
  have h1 : Entails.eval a c5434 := h 5433 (by decide)
  have h2 : Entails.eval a c3361 := h 3360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9240 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨13, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9240 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9218, some c9227, some c9230, some c9232, some c3337, some c3346, some c3357, some c3342, some c9237, some c1371, some c2777, some c3389, some c3379, some c9238, some c9239, some c182, some c123, some c3297, some c5571, some c5916, some c5860, some c6029, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9240 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9240 : lratChecker f9240 p9240 = .success := by decide +kernel
theorem unsat9240 : Unsatisfiable (PosFin 65) f9240 := by
  apply lratCheckerSound f9240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9240
  · intro a ha; simp [p9240] at ha; subst a; trivial
  · exact checked9240
theorem derived9240 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9240 := by
  apply localUnsat_implies_entails f9240 [c9193, c9218, c9227, c9230, c9232, c3337, c3346, c3357, c3342, c9237, c1371, c2777, c3389, c3379, c9238, c9239, c182, c123, c3297, c5571, c5916, c5860, c6029] c9240 unsat9240 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9218 := derived9218 a h
  have h2 : Entails.eval a c9227 := derived9227 a h
  have h3 : Entails.eval a c9230 := derived9230 a h
  have h4 : Entails.eval a c9232 := derived9232 a h
  have h5 : Entails.eval a c3337 := h 3336 (by decide)
  have h6 : Entails.eval a c3346 := h 3345 (by decide)
  have h7 : Entails.eval a c3357 := h 3356 (by decide)
  have h8 : Entails.eval a c3342 := h 3341 (by decide)
  have h9 : Entails.eval a c9237 := derived9237 a h
  have h10 : Entails.eval a c1371 := h 1370 (by decide)
  have h11 : Entails.eval a c2777 := h 2776 (by decide)
  have h12 : Entails.eval a c3389 := h 3388 (by decide)
  have h13 : Entails.eval a c3379 := h 3378 (by decide)
  have h14 : Entails.eval a c9238 := derived9238 a h
  have h15 : Entails.eval a c9239 := derived9239 a h
  have h16 : Entails.eval a c182 := h 181 (by decide)
  have h17 : Entails.eval a c123 := h 122 (by decide)
  have h18 : Entails.eval a c3297 := h 3296 (by decide)
  have h19 : Entails.eval a c5571 := h 5570 (by decide)
  have h20 : Entails.eval a c5916 := h 5915 (by decide)
  have h21 : Entails.eval a c5860 := h 5859 (by decide)
  have h22 : Entails.eval a c6029 := h 6028 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9241 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9241 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9218, some c9227, some c9230, some c3342, some c3337, some c3346, some c3357, some c9232, some c9240, some c3344, some c3351, some c8419, some c9223, some c2777, some c3453, some c3384, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9241 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9241 : lratChecker f9241 p9241 = .success := by decide +kernel
theorem unsat9241 : Unsatisfiable (PosFin 65) f9241 := by
  apply lratCheckerSound f9241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9241
  · intro a ha; simp [p9241] at ha; subst a; trivial
  · exact checked9241
theorem derived9241 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9241 := by
  apply localUnsat_implies_entails f9241 [c9193, c9218, c9227, c9230, c3342, c3337, c3346, c3357, c9232, c9240, c3344, c3351, c8419, c9223, c2777, c3453, c3384] c9241 unsat9241 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9218 := derived9218 a h
  have h2 : Entails.eval a c9227 := derived9227 a h
  have h3 : Entails.eval a c9230 := derived9230 a h
  have h4 : Entails.eval a c3342 := h 3341 (by decide)
  have h5 : Entails.eval a c3337 := h 3336 (by decide)
  have h6 : Entails.eval a c3346 := h 3345 (by decide)
  have h7 : Entails.eval a c3357 := h 3356 (by decide)
  have h8 : Entails.eval a c9232 := derived9232 a h
  have h9 : Entails.eval a c9240 := derived9240 a h
  have h10 : Entails.eval a c3344 := h 3343 (by decide)
  have h11 : Entails.eval a c3351 := h 3350 (by decide)
  have h12 : Entails.eval a c8419 := derived8419 a h
  have h13 : Entails.eval a c9223 := derived9223 a h
  have h14 : Entails.eval a c2777 := h 2776 (by decide)
  have h15 : Entails.eval a c3453 := h 3452 (by decide)
  have h16 : Entails.eval a c3384 := h 3383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9242 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9242 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4617, some c1418, some c4857, some c4377, some c4337, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9242 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9242 : lratChecker f9242 p9242 = .success := by decide +kernel
theorem unsat9242 : Unsatisfiable (PosFin 65) f9242 := by
  apply lratCheckerSound f9242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9242
  · intro a ha; simp [p9242] at ha; subst a; trivial
  · exact checked9242
theorem derived9242 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9242 := by
  apply localUnsat_implies_entails f9242 [c4617, c1418, c4857, c4377, c4337] c9242 unsat9242 (by rfl) a
  have h0 : Entails.eval a c4617 := h 4616 (by decide)
  have h1 : Entails.eval a c1418 := h 1417 (by decide)
  have h2 : Entails.eval a c4857 := h 4856 (by decide)
  have h3 : Entails.eval a c4377 := h 4376 (by decide)
  have h4 : Entails.eval a c4337 := h 4336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9243 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9243 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3246, some c3249, some c3259, some c3248, some c9242, some c1371, some c3814, some c4911, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9243 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9243 : lratChecker f9243 p9243 = .success := by decide +kernel
theorem unsat9243 : Unsatisfiable (PosFin 65) f9243 := by
  apply lratCheckerSound f9243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9243
  · intro a ha; simp [p9243] at ha; subst a; trivial
  · exact checked9243
theorem derived9243 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9243 := by
  apply localUnsat_implies_entails f9243 [c3246, c3249, c3259, c3248, c9242, c1371, c3814, c4911] c9243 unsat9243 (by rfl) a
  have h0 : Entails.eval a c3246 := h 3245 (by decide)
  have h1 : Entails.eval a c3249 := h 3248 (by decide)
  have h2 : Entails.eval a c3259 := h 3258 (by decide)
  have h3 : Entails.eval a c3248 := h 3247 (by decide)
  have h4 : Entails.eval a c9242 := derived9242 a h
  have h5 : Entails.eval a c1371 := h 1370 (by decide)
  have h6 : Entails.eval a c3814 := h 3813 (by decide)
  have h7 : Entails.eval a c4911 := h 4910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9244 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9244 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9218, some c9193, some c9227, some c9230, some c9241, some c9243, some c3653, some c3646, some c3632, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9244 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9244 : lratChecker f9244 p9244 = .success := by decide +kernel
theorem unsat9244 : Unsatisfiable (PosFin 65) f9244 := by
  apply lratCheckerSound f9244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9244
  · intro a ha; simp [p9244] at ha; subst a; trivial
  · exact checked9244
theorem derived9244 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9244 := by
  apply localUnsat_implies_entails f9244 [c9218, c9193, c9227, c9230, c9241, c9243, c3653, c3646, c3632] c9244 unsat9244 (by rfl) a
  have h0 : Entails.eval a c9218 := derived9218 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9227 := derived9227 a h
  have h3 : Entails.eval a c9230 := derived9230 a h
  have h4 : Entails.eval a c9241 := derived9241 a h
  have h5 : Entails.eval a c9243 := derived9243 a h
  have h6 : Entails.eval a c3653 := h 3652 (by decide)
  have h7 : Entails.eval a c3646 := h 3645 (by decide)
  have h8 : Entails.eval a c3632 := h 3631 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9245 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9245 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3386, some c2788, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9245 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9245 : lratChecker f9245 p9245 = .success := by decide +kernel
theorem unsat9245 : Unsatisfiable (PosFin 65) f9245 := by
  apply lratCheckerSound f9245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9245
  · intro a ha; simp [p9245] at ha; subst a; trivial
  · exact checked9245
theorem derived9245 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9245 := by
  apply localUnsat_implies_entails f9245 [c3386, c2788] c9245 unsat9245 (by rfl) a
  have h0 : Entails.eval a c3386 := h 3385 (by decide)
  have h1 : Entails.eval a c2788 := h 2787 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9246 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨8, by decide⟩, false), (⟨58, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9246 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2785, some c2780, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9246 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9246 : lratChecker f9246 p9246 = .success := by decide +kernel
theorem unsat9246 : Unsatisfiable (PosFin 65) f9246 := by
  apply lratCheckerSound f9246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9246
  · intro a ha; simp [p9246] at ha; subst a; trivial
  · exact checked9246
theorem derived9246 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9246 := by
  apply localUnsat_implies_entails f9246 [c2785, c2780] c9246 unsat9246 (by rfl) a
  have h0 : Entails.eval a c2785 := h 2784 (by decide)
  have h1 : Entails.eval a c2780 := h 2779 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9247 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9247 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3460, some c3384, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9247 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9247 : lratChecker f9247 p9247 = .success := by decide +kernel
theorem unsat9247 : Unsatisfiable (PosFin 65) f9247 := by
  apply lratCheckerSound f9247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9247
  · intro a ha; simp [p9247] at ha; subst a; trivial
  · exact checked9247
theorem derived9247 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9247 := by
  apply localUnsat_implies_entails f9247 [c3460, c3384] c9247 unsat9247 (by rfl) a
  have h0 : Entails.eval a c3460 := h 3459 (by decide)
  have h1 : Entails.eval a c3384 := h 3383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9248 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9248 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c3334, some c3344, some c3339, some c3350, some c3345, some c3354, some c3346, some c8419, some c9221, some c9247, some c2780, some c2792, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9248 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9248 : lratChecker f9248 p9248 = .success := by decide +kernel
theorem unsat9248 : Unsatisfiable (PosFin 65) f9248 := by
  apply lratCheckerSound f9248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9248
  · intro a ha; simp [p9248] at ha; subst a; trivial
  · exact checked9248
theorem derived9248 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9248 := by
  apply localUnsat_implies_entails f9248 [c9193, c3334, c3344, c3339, c3350, c3345, c3354, c3346, c8419, c9221, c9247, c2780, c2792] c9248 unsat9248 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c3334 := h 3333 (by decide)
  have h2 : Entails.eval a c3344 := h 3343 (by decide)
  have h3 : Entails.eval a c3339 := h 3338 (by decide)
  have h4 : Entails.eval a c3350 := h 3349 (by decide)
  have h5 : Entails.eval a c3345 := h 3344 (by decide)
  have h6 : Entails.eval a c3354 := h 3353 (by decide)
  have h7 : Entails.eval a c3346 := h 3345 (by decide)
  have h8 : Entails.eval a c8419 := derived8419 a h
  have h9 : Entails.eval a c9221 := derived9221 a h
  have h10 : Entails.eval a c9247 := derived9247 a h
  have h11 : Entails.eval a c2780 := h 2779 (by decide)
  have h12 : Entails.eval a c2792 := h 2791 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9249 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9249 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3235, some c3251, some c3261, some c3263, some c3266, some c9221, some c8408, some c1391, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9249 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9249 : lratChecker f9249 p9249 = .success := by decide +kernel
theorem unsat9249 : Unsatisfiable (PosFin 65) f9249 := by
  apply lratCheckerSound f9249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9249
  · intro a ha; simp [p9249] at ha; subst a; trivial
  · exact checked9249
theorem derived9249 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9249 := by
  apply localUnsat_implies_entails f9249 [c3235, c3251, c3261, c3263, c3266, c9221, c8408, c1391] c9249 unsat9249 (by rfl) a
  have h0 : Entails.eval a c3235 := h 3234 (by decide)
  have h1 : Entails.eval a c3251 := h 3250 (by decide)
  have h2 : Entails.eval a c3261 := h 3260 (by decide)
  have h3 : Entails.eval a c3263 := h 3262 (by decide)
  have h4 : Entails.eval a c3266 := h 3265 (by decide)
  have h5 : Entails.eval a c9221 := derived9221 a h
  have h6 : Entails.eval a c8408 := derived8408 a h
  have h7 : Entails.eval a c1391 := h 1390 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9250 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9250 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9244, some c9218, some c9193, some c9219, some c9248, some c9249, some c3637, some c3639, some c3664, some c3663, some c3660, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9250 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9250 : lratChecker f9250 p9250 = .success := by decide +kernel
theorem unsat9250 : Unsatisfiable (PosFin 65) f9250 := by
  apply lratCheckerSound f9250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9250
  · intro a ha; simp [p9250] at ha; subst a; trivial
  · exact checked9250
theorem derived9250 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9250 := by
  apply localUnsat_implies_entails f9250 [c9244, c9218, c9193, c9219, c9248, c9249, c3637, c3639, c3664, c3663, c3660] c9250 unsat9250 (by rfl) a
  have h0 : Entails.eval a c9244 := derived9244 a h
  have h1 : Entails.eval a c9218 := derived9218 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c9219 := derived9219 a h
  have h4 : Entails.eval a c9248 := derived9248 a h
  have h5 : Entails.eval a c9249 := derived9249 a h
  have h6 : Entails.eval a c3637 := h 3636 (by decide)
  have h7 : Entails.eval a c3639 := h 3638 (by decide)
  have h8 : Entails.eval a c3664 := h 3663 (by decide)
  have h9 : Entails.eval a c3663 := h 3662 (by decide)
  have h10 : Entails.eval a c3660 := h 3659 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9250

end CochromaticTwenty.Certificates.FixedCore0
