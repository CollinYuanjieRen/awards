import MerLeanExperiment.Certificates.FixedCore0.Steps3500_3599

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c11151 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11151 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11133, some c11108, some c11085, some c10282, some c10227, some c10396, some c10228, some c10207, some c11134, some c11146, some c11150, some c10550, some c10545, some c10611, some c10561, some c10745, some c3177, some c2937, some c3555, some c3360, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11151 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked11151 : lratChecker f11151 p11151 = .success := by decide +kernel
theorem unsat11151 : Unsatisfiable (PosFin 65) f11151 := by
  apply lratCheckerSound f11151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11151
  · intro a ha; simp [p11151] at ha; subst a; trivial
  · exact checked11151
theorem derived11151 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11151 := by
  apply localUnsat_implies_entails f11151 [c11018, c11133, c11108, c11085, c10282, c10227, c10396, c10228, c10207, c11134, c11146, c11150, c10550, c10545, c10611, c10561, c10745, c3177, c2937, c3555, c3360] c11151 unsat11151 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11133 := derived11133 a h
  have h2 : Entails.eval a c11108 := derived11108 a h
  have h3 : Entails.eval a c11085 := derived11085 a h
  have h4 : Entails.eval a c10282 := derived10282 a h
  have h5 : Entails.eval a c10227 := derived10227 a h
  have h6 : Entails.eval a c10396 := derived10396 a h
  have h7 : Entails.eval a c10228 := derived10228 a h
  have h8 : Entails.eval a c10207 := derived10207 a h
  have h9 : Entails.eval a c11134 := derived11134 a h
  have h10 : Entails.eval a c11146 := derived11146 a h
  have h11 : Entails.eval a c11150 := derived11150 a h
  have h12 : Entails.eval a c10550 := derived10550 a h
  have h13 : Entails.eval a c10545 := derived10545 a h
  have h14 : Entails.eval a c10611 := derived10611 a h
  have h15 : Entails.eval a c10561 := derived10561 a h
  have h16 : Entails.eval a c10745 := derived10745 a h
  have h17 : Entails.eval a c3177 := h 3176 (by decide)
  have h18 : Entails.eval a c2937 := h 2936 (by decide)
  have h19 : Entails.eval a c3555 := h 3554 (by decide)
  have h20 : Entails.eval a c3360 := h 3359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11152 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11152 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11101, some c10526, some c11051, some c10335, some c10213, some c10214, some c10592, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11152 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11152 : lratChecker f11152 p11152 = .success := by decide +kernel
theorem unsat11152 : Unsatisfiable (PosFin 65) f11152 := by
  apply lratCheckerSound f11152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11152
  · intro a ha; simp [p11152] at ha; subst a; trivial
  · exact checked11152
theorem derived11152 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11152 := by
  apply localUnsat_implies_entails f11152 [c11133, c11101, c10526, c11051, c10335, c10213, c10214, c10592] c11152 unsat11152 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c10526 := derived10526 a h
  have h3 : Entails.eval a c11051 := derived11051 a h
  have h4 : Entails.eval a c10335 := derived10335 a h
  have h5 : Entails.eval a c10213 := derived10213 a h
  have h6 : Entails.eval a c10214 := derived10214 a h
  have h7 : Entails.eval a c10592 := derived10592 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11153 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨57, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11153 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11101, some c10686, some c10554, some c10574, some c10462, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11153 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11153 : lratChecker f11153 p11153 = .success := by decide +kernel
theorem unsat11153 : Unsatisfiable (PosFin 65) f11153 := by
  apply lratCheckerSound f11153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11153
  · intro a ha; simp [p11153] at ha; subst a; trivial
  · exact checked11153
theorem derived11153 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11153 := by
  apply localUnsat_implies_entails f11153 [c11133, c11101, c10686, c10554, c10574, c10462] c11153 unsat11153 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c10686 := derived10686 a h
  have h3 : Entails.eval a c10554 := derived10554 a h
  have h4 : Entails.eval a c10574 := derived10574 a h
  have h5 : Entails.eval a c10462 := derived10462 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11154 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨57, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11154 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11108, some c10462, some c10461, some c10563, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11154 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11154 : lratChecker f11154 p11154 = .success := by decide +kernel
theorem unsat11154 : Unsatisfiable (PosFin 65) f11154 := by
  apply lratCheckerSound f11154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11154
  · intro a ha; simp [p11154] at ha; subst a; trivial
  · exact checked11154
theorem derived11154 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11154 := by
  apply localUnsat_implies_entails f11154 [c11133, c11108, c10462, c10461, c10563] c11154 unsat11154 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c10462 := derived10462 a h
  have h3 : Entails.eval a c10461 := derived10461 a h
  have h4 : Entails.eval a c10563 := derived10563 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11155 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, true), (⟨60, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11155 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11101, some c11133, some c10583, some c11108, some c10283, some c10207, some c11154, some c10584, some c10596, some c10442, some c10622, some c10563, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11155 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11155 : lratChecker f11155 p11155 = .success := by decide +kernel
theorem unsat11155 : Unsatisfiable (PosFin 65) f11155 := by
  apply lratCheckerSound f11155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11155
  · intro a ha; simp [p11155] at ha; subst a; trivial
  · exact checked11155
theorem derived11155 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11155 := by
  apply localUnsat_implies_entails f11155 [c11101, c11133, c10583, c11108, c10283, c10207, c11154, c10584, c10596, c10442, c10622, c10563] c11155 unsat11155 (by rfl) a
  have h0 : Entails.eval a c11101 := derived11101 a h
  have h1 : Entails.eval a c11133 := derived11133 a h
  have h2 : Entails.eval a c10583 := derived10583 a h
  have h3 : Entails.eval a c11108 := derived11108 a h
  have h4 : Entails.eval a c10283 := derived10283 a h
  have h5 : Entails.eval a c10207 := derived10207 a h
  have h6 : Entails.eval a c11154 := derived11154 a h
  have h7 : Entails.eval a c10584 := derived10584 a h
  have h8 : Entails.eval a c10596 := derived10596 a h
  have h9 : Entails.eval a c10442 := derived10442 a h
  have h10 : Entails.eval a c10622 := derived10622 a h
  have h11 : Entails.eval a c10563 := derived10563 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11156 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨54, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11156 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11108, some c11152, some c10283, some c10577, some c11101, some c10583, some c10207, some c11153, some c8296, some c10576, some c11155, some c10608, some c10627, some c10805, some c10811, some c10597, some c10546, some c10537, some c10562, some c8550, some c6563, some c10585, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11156 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked11156 : lratChecker f11156 p11156 = .success := by decide +kernel
theorem unsat11156 : Unsatisfiable (PosFin 65) f11156 := by
  apply lratCheckerSound f11156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11156
  · intro a ha; simp [p11156] at ha; subst a; trivial
  · exact checked11156
theorem derived11156 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11156 := by
  apply localUnsat_implies_entails f11156 [c11133, c11108, c11152, c10283, c10577, c11101, c10583, c10207, c11153, c8296, c10576, c11155, c10608, c10627, c10805, c10811, c10597, c10546, c10537, c10562, c8550, c6563, c10585] c11156 unsat11156 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11152 := derived11152 a h
  have h3 : Entails.eval a c10283 := derived10283 a h
  have h4 : Entails.eval a c10577 := derived10577 a h
  have h5 : Entails.eval a c11101 := derived11101 a h
  have h6 : Entails.eval a c10583 := derived10583 a h
  have h7 : Entails.eval a c10207 := derived10207 a h
  have h8 : Entails.eval a c11153 := derived11153 a h
  have h9 : Entails.eval a c8296 := derived8296 a h
  have h10 : Entails.eval a c10576 := derived10576 a h
  have h11 : Entails.eval a c11155 := derived11155 a h
  have h12 : Entails.eval a c10608 := derived10608 a h
  have h13 : Entails.eval a c10627 := derived10627 a h
  have h14 : Entails.eval a c10805 := derived10805 a h
  have h15 : Entails.eval a c10811 := derived10811 a h
  have h16 : Entails.eval a c10597 := derived10597 a h
  have h17 : Entails.eval a c10546 := derived10546 a h
  have h18 : Entails.eval a c10537 := derived10537 a h
  have h19 : Entails.eval a c10562 := derived10562 a h
  have h20 : Entails.eval a c8550 := derived8550 a h
  have h21 : Entails.eval a c6563 := h 6562 (by decide)
  have h22 : Entails.eval a c10585 := derived10585 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11157 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11157 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c10401, some c10406, some c10547, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11157 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11157 : lratChecker f11157 p11157 = .success := by decide +kernel
theorem unsat11157 : Unsatisfiable (PosFin 65) f11157 := by
  apply lratCheckerSound f11157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11157
  · intro a ha; simp [p11157] at ha; subst a; trivial
  · exact checked11157
theorem derived11157 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11157 := by
  apply localUnsat_implies_entails f11157 [c11133, c10401, c10406, c10547] c11157 unsat11157 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c10401 := derived10401 a h
  have h2 : Entails.eval a c10406 := derived10406 a h
  have h3 : Entails.eval a c10547 := derived10547 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11158 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨54, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11158 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11108, some c11101, some c11152, some c10283, some c10583, some c10207, some c10576, some c11156, some c11157, some c10477, some c10465, some c10628, some c10435, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11158 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11158 : lratChecker f11158 p11158 = .success := by decide +kernel
theorem unsat11158 : Unsatisfiable (PosFin 65) f11158 := by
  apply lratCheckerSound f11158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11158
  · intro a ha; simp [p11158] at ha; subst a; trivial
  · exact checked11158
theorem derived11158 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11158 := by
  apply localUnsat_implies_entails f11158 [c11133, c11108, c11101, c11152, c10283, c10583, c10207, c10576, c11156, c11157, c10477, c10465, c10628, c10435] c11158 unsat11158 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11101 := derived11101 a h
  have h3 : Entails.eval a c11152 := derived11152 a h
  have h4 : Entails.eval a c10283 := derived10283 a h
  have h5 : Entails.eval a c10583 := derived10583 a h
  have h6 : Entails.eval a c10207 := derived10207 a h
  have h7 : Entails.eval a c10576 := derived10576 a h
  have h8 : Entails.eval a c11156 := derived11156 a h
  have h9 : Entails.eval a c11157 := derived11157 a h
  have h10 : Entails.eval a c10477 := derived10477 a h
  have h11 : Entails.eval a c10465 := derived10465 a h
  have h12 : Entails.eval a c10628 := derived10628 a h
  have h13 : Entails.eval a c10435 := derived10435 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11159 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨54, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11159 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11101, some c11158, some c10528, some c10570, some c10582, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11159 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11159 : lratChecker f11159 p11159 = .success := by decide +kernel
theorem unsat11159 : Unsatisfiable (PosFin 65) f11159 := by
  apply lratCheckerSound f11159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11159
  · intro a ha; simp [p11159] at ha; subst a; trivial
  · exact checked11159
theorem derived11159 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11159 := by
  apply localUnsat_implies_entails f11159 [c11133, c11101, c11158, c10528, c10570, c10582] c11159 unsat11159 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11101 := derived11101 a h
  have h2 : Entails.eval a c11158 := derived11158 a h
  have h3 : Entails.eval a c10528 := derived10528 a h
  have h4 : Entails.eval a c10570 := derived10570 a h
  have h5 : Entails.eval a c10582 := derived10582 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11160 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11160 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11151, some c11133, some c11101, some c11085, some c10528, some c10570, some c4346, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11160 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11160 : lratChecker f11160 p11160 = .success := by decide +kernel
theorem unsat11160 : Unsatisfiable (PosFin 65) f11160 := by
  apply lratCheckerSound f11160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11160
  · intro a ha; simp [p11160] at ha; subst a; trivial
  · exact checked11160
theorem derived11160 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11160 := by
  apply localUnsat_implies_entails f11160 [c11151, c11133, c11101, c11085, c10528, c10570, c4346] c11160 unsat11160 (by rfl) a
  have h0 : Entails.eval a c11151 := derived11151 a h
  have h1 : Entails.eval a c11133 := derived11133 a h
  have h2 : Entails.eval a c11101 := derived11101 a h
  have h3 : Entails.eval a c11085 := derived11085 a h
  have h4 : Entails.eval a c10528 := derived10528 a h
  have h5 : Entails.eval a c10570 := derived10570 a h
  have h6 : Entails.eval a c4346 := h 4345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11161 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11161 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11108, some c11101, some c11085, some c4331, some c4346, some c4334, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11161 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11161 : lratChecker f11161 p11161 = .success := by decide +kernel
theorem unsat11161 : Unsatisfiable (PosFin 65) f11161 := by
  apply lratCheckerSound f11161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11161
  · intro a ha; simp [p11161] at ha; subst a; trivial
  · exact checked11161
theorem derived11161 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11161 := by
  apply localUnsat_implies_entails f11161 [c11018, c11108, c11101, c11085, c4331, c4346, c4334] c11161 unsat11161 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11101 := derived11101 a h
  have h3 : Entails.eval a c11085 := derived11085 a h
  have h4 : Entails.eval a c4331 := h 4330 (by decide)
  have h5 : Entails.eval a c4346 := h 4345 (by decide)
  have h6 : Entails.eval a c4334 := h 4333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11162 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11162 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11151, some c11133, some c11085, some c11160, some c11161, some c10526, some c11051, some c8300, some c4353, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11162 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11162 : lratChecker f11162 p11162 = .success := by decide +kernel
theorem unsat11162 : Unsatisfiable (PosFin 65) f11162 := by
  apply lratCheckerSound f11162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11162
  · intro a ha; simp [p11162] at ha; subst a; trivial
  · exact checked11162
theorem derived11162 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11162 := by
  apply localUnsat_implies_entails f11162 [c11151, c11133, c11085, c11160, c11161, c10526, c11051, c8300, c4353] c11162 unsat11162 (by rfl) a
  have h0 : Entails.eval a c11151 := derived11151 a h
  have h1 : Entails.eval a c11133 := derived11133 a h
  have h2 : Entails.eval a c11085 := derived11085 a h
  have h3 : Entails.eval a c11160 := derived11160 a h
  have h4 : Entails.eval a c11161 := derived11161 a h
  have h5 : Entails.eval a c10526 := derived10526 a h
  have h6 : Entails.eval a c11051 := derived11051 a h
  have h7 : Entails.eval a c8300 := derived8300 a h
  have h8 : Entails.eval a c4353 := h 4352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11163 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11163 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11162, some c11151, some c11133, some c10528, some c11152, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11163 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11163 : lratChecker f11163 p11163 = .success := by decide +kernel
theorem unsat11163 : Unsatisfiable (PosFin 65) f11163 := by
  apply lratCheckerSound f11163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11163
  · intro a ha; simp [p11163] at ha; subst a; trivial
  · exact checked11163
theorem derived11163 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11163 := by
  apply localUnsat_implies_entails f11163 [c11162, c11151, c11133, c10528, c11152] c11163 unsat11163 (by rfl) a
  have h0 : Entails.eval a c11162 := derived11162 a h
  have h1 : Entails.eval a c11151 := derived11151 a h
  have h2 : Entails.eval a c11133 := derived11133 a h
  have h3 : Entails.eval a c10528 := derived10528 a h
  have h4 : Entails.eval a c11152 := derived11152 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11164 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11164 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10631, some c10543, some c10632, some c10557, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11164 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11164 : lratChecker f11164 p11164 = .success := by decide +kernel
theorem unsat11164 : Unsatisfiable (PosFin 65) f11164 := by
  apply lratCheckerSound f11164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11164
  · intro a ha; simp [p11164] at ha; subst a; trivial
  · exact checked11164
theorem derived11164 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11164 := by
  apply localUnsat_implies_entails f11164 [c10631, c10543, c10632, c10557] c11164 unsat11164 (by rfl) a
  have h0 : Entails.eval a c10631 := derived10631 a h
  have h1 : Entails.eval a c10543 := derived10543 a h
  have h2 : Entails.eval a c10632 := derived10632 a h
  have h3 : Entails.eval a c10557 := derived10557 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11165 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11165 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11133, some c11108, some c11101, some c11151, some c11162, some c11159, some c11163, some c10283, some c10583, some c10582, some c10577, some c10207, some c10590, some c11153, some c11164, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11165 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11165 : lratChecker f11165 p11165 = .success := by decide +kernel
theorem unsat11165 : Unsatisfiable (PosFin 65) f11165 := by
  apply lratCheckerSound f11165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11165
  · intro a ha; simp [p11165] at ha; subst a; trivial
  · exact checked11165
theorem derived11165 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11165 := by
  apply localUnsat_implies_entails f11165 [c11133, c11108, c11101, c11151, c11162, c11159, c11163, c10283, c10583, c10582, c10577, c10207, c10590, c11153, c11164] c11165 unsat11165 (by rfl) a
  have h0 : Entails.eval a c11133 := derived11133 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11101 := derived11101 a h
  have h3 : Entails.eval a c11151 := derived11151 a h
  have h4 : Entails.eval a c11162 := derived11162 a h
  have h5 : Entails.eval a c11159 := derived11159 a h
  have h6 : Entails.eval a c11163 := derived11163 a h
  have h7 : Entails.eval a c10283 := derived10283 a h
  have h8 : Entails.eval a c10583 := derived10583 a h
  have h9 : Entails.eval a c10582 := derived10582 a h
  have h10 : Entails.eval a c10577 := derived10577 a h
  have h11 : Entails.eval a c10207 := derived10207 a h
  have h12 : Entails.eval a c10590 := derived10590 a h
  have h13 : Entails.eval a c11153 := derived11153 a h
  have h14 : Entails.eval a c11164 := derived11164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11166 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11166 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11101, some c11165, some c11129, some c11133, some c11125, some c11164, some c11124, some c10570, some c10226, some c10708, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11166 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11166 : lratChecker f11166 p11166 = .success := by decide +kernel
theorem unsat11166 : Unsatisfiable (PosFin 65) f11166 := by
  apply lratCheckerSound f11166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11166
  · intro a ha; simp [p11166] at ha; subst a; trivial
  · exact checked11166
theorem derived11166 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11166 := by
  apply localUnsat_implies_entails f11166 [c11101, c11165, c11129, c11133, c11125, c11164, c11124, c10570, c10226, c10708] c11166 unsat11166 (by rfl) a
  have h0 : Entails.eval a c11101 := derived11101 a h
  have h1 : Entails.eval a c11165 := derived11165 a h
  have h2 : Entails.eval a c11129 := derived11129 a h
  have h3 : Entails.eval a c11133 := derived11133 a h
  have h4 : Entails.eval a c11125 := derived11125 a h
  have h5 : Entails.eval a c11164 := derived11164 a h
  have h6 : Entails.eval a c11124 := derived11124 a h
  have h7 : Entails.eval a c10570 := derived10570 a h
  have h8 : Entails.eval a c10226 := derived10226 a h
  have h9 : Entails.eval a c10708 := derived10708 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11167 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11167 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11101, some c11165, some c11129, some c11133, some c11108, some c11128, some c10570, some c10226, some c10238, some c10241, some c11153, some c10207, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11167 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11167 : lratChecker f11167 p11167 = .success := by decide +kernel
theorem unsat11167 : Unsatisfiable (PosFin 65) f11167 := by
  apply lratCheckerSound f11167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11167
  · intro a ha; simp [p11167] at ha; subst a; trivial
  · exact checked11167
theorem derived11167 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11167 := by
  apply localUnsat_implies_entails f11167 [c11101, c11165, c11129, c11133, c11108, c11128, c10570, c10226, c10238, c10241, c11153, c10207] c11167 unsat11167 (by rfl) a
  have h0 : Entails.eval a c11101 := derived11101 a h
  have h1 : Entails.eval a c11165 := derived11165 a h
  have h2 : Entails.eval a c11129 := derived11129 a h
  have h3 : Entails.eval a c11133 := derived11133 a h
  have h4 : Entails.eval a c11108 := derived11108 a h
  have h5 : Entails.eval a c11128 := derived11128 a h
  have h6 : Entails.eval a c10570 := derived10570 a h
  have h7 : Entails.eval a c10226 := derived10226 a h
  have h8 : Entails.eval a c10238 := derived10238 a h
  have h9 : Entails.eval a c10241 := derived10241 a h
  have h10 : Entails.eval a c11153 := derived11153 a h
  have h11 : Entails.eval a c10207 := derived10207 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11168 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11168 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11166, some c11165, some c11133, some c11108, some c11101, some c10240, some c10718, some c11124, some c10616, some c10826, some c9878, some c10207, some c10422, some c10644, some c9864, some c10281, some c10249, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11168 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11168 : lratChecker f11168 p11168 = .success := by decide +kernel
theorem unsat11168 : Unsatisfiable (PosFin 65) f11168 := by
  apply lratCheckerSound f11168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11168
  · intro a ha; simp [p11168] at ha; subst a; trivial
  · exact checked11168
theorem derived11168 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11168 := by
  apply localUnsat_implies_entails f11168 [c11166, c11165, c11133, c11108, c11101, c10240, c10718, c11124, c10616, c10826, c9878, c10207, c10422, c10644, c9864, c10281, c10249] c11168 unsat11168 (by rfl) a
  have h0 : Entails.eval a c11166 := derived11166 a h
  have h1 : Entails.eval a c11165 := derived11165 a h
  have h2 : Entails.eval a c11133 := derived11133 a h
  have h3 : Entails.eval a c11108 := derived11108 a h
  have h4 : Entails.eval a c11101 := derived11101 a h
  have h5 : Entails.eval a c10240 := derived10240 a h
  have h6 : Entails.eval a c10718 := derived10718 a h
  have h7 : Entails.eval a c11124 := derived11124 a h
  have h8 : Entails.eval a c10616 := derived10616 a h
  have h9 : Entails.eval a c10826 := derived10826 a h
  have h10 : Entails.eval a c9878 := derived9878 a h
  have h11 : Entails.eval a c10207 := derived10207 a h
  have h12 : Entails.eval a c10422 := derived10422 a h
  have h13 : Entails.eval a c10644 := derived10644 a h
  have h14 : Entails.eval a c9864 := derived9864 a h
  have h15 : Entails.eval a c10281 := derived10281 a h
  have h16 : Entails.eval a c10249 := derived10249 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11169 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11169 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11101, some c11165, some c11168, some c11128, some c10241, some c11133, some c11108, some c10238, some c10207, some c11167, some c11154, some c10797, some c10442, some c10544, some c10723, some c10379, some c10458, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11169 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11169 : lratChecker f11169 p11169 = .success := by decide +kernel
theorem unsat11169 : Unsatisfiable (PosFin 65) f11169 := by
  apply lratCheckerSound f11169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11169
  · intro a ha; simp [p11169] at ha; subst a; trivial
  · exact checked11169
theorem derived11169 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11169 := by
  apply localUnsat_implies_entails f11169 [c11101, c11165, c11168, c11128, c10241, c11133, c11108, c10238, c10207, c11167, c11154, c10797, c10442, c10544, c10723, c10379, c10458] c11169 unsat11169 (by rfl) a
  have h0 : Entails.eval a c11101 := derived11101 a h
  have h1 : Entails.eval a c11165 := derived11165 a h
  have h2 : Entails.eval a c11168 := derived11168 a h
  have h3 : Entails.eval a c11128 := derived11128 a h
  have h4 : Entails.eval a c10241 := derived10241 a h
  have h5 : Entails.eval a c11133 := derived11133 a h
  have h6 : Entails.eval a c11108 := derived11108 a h
  have h7 : Entails.eval a c10238 := derived10238 a h
  have h8 : Entails.eval a c10207 := derived10207 a h
  have h9 : Entails.eval a c11167 := derived11167 a h
  have h10 : Entails.eval a c11154 := derived11154 a h
  have h11 : Entails.eval a c10797 := derived10797 a h
  have h12 : Entails.eval a c10442 := derived10442 a h
  have h13 : Entails.eval a c10544 := derived10544 a h
  have h14 : Entails.eval a c10723 := derived10723 a h
  have h15 : Entails.eval a c10379 := derived10379 a h
  have h16 : Entails.eval a c10458 := derived10458 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11170 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11170 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11101, some c11108, some c11133, some c11165, some c11129, some c11168, some c11128, some c10570, some c11167, some c10238, some c10241, some c10722, some c11169, some c10603, some c10468, some c9864, some c10805, some c10644, some c10673, some c10800, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11170 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked11170 : lratChecker f11170 p11170 = .success := by decide +kernel
theorem unsat11170 : Unsatisfiable (PosFin 65) f11170 := by
  apply lratCheckerSound f11170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11170
  · intro a ha; simp [p11170] at ha; subst a; trivial
  · exact checked11170
theorem derived11170 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11170 := by
  apply localUnsat_implies_entails f11170 [c11101, c11108, c11133, c11165, c11129, c11168, c11128, c10570, c11167, c10238, c10241, c10722, c11169, c10603, c10468, c9864, c10805, c10644, c10673, c10800] c11170 unsat11170 (by rfl) a
  have h0 : Entails.eval a c11101 := derived11101 a h
  have h1 : Entails.eval a c11108 := derived11108 a h
  have h2 : Entails.eval a c11133 := derived11133 a h
  have h3 : Entails.eval a c11165 := derived11165 a h
  have h4 : Entails.eval a c11129 := derived11129 a h
  have h5 : Entails.eval a c11168 := derived11168 a h
  have h6 : Entails.eval a c11128 := derived11128 a h
  have h7 : Entails.eval a c10570 := derived10570 a h
  have h8 : Entails.eval a c11167 := derived11167 a h
  have h9 : Entails.eval a c10238 := derived10238 a h
  have h10 : Entails.eval a c10241 := derived10241 a h
  have h11 : Entails.eval a c10722 := derived10722 a h
  have h12 : Entails.eval a c11169 := derived11169 a h
  have h13 : Entails.eval a c10603 := derived10603 a h
  have h14 : Entails.eval a c10468 := derived10468 a h
  have h15 : Entails.eval a c9864 := derived9864 a h
  have h16 : Entails.eval a c10805 := derived10805 a h
  have h17 : Entails.eval a c10644 := derived10644 a h
  have h18 : Entails.eval a c10673 := derived10673 a h
  have h19 : Entails.eval a c10800 := derived10800 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11171 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11171 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10621, some c10415, some c10625, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11171 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11171 : lratChecker f11171 p11171 = .success := by decide +kernel
theorem unsat11171 : Unsatisfiable (PosFin 65) f11171 := by
  apply lratCheckerSound f11171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11171
  · intro a ha; simp [p11171] at ha; subst a; trivial
  · exact checked11171
theorem derived11171 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11171 := by
  apply localUnsat_implies_entails f11171 [c10621, c10415, c10625] c11171 unsat11171 (by rfl) a
  have h0 : Entails.eval a c10621 := derived10621 a h
  have h1 : Entails.eval a c10415 := derived10415 a h
  have h2 : Entails.eval a c10625 := derived10625 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11172 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11172 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10205, some c10605, some c10217, some c10216, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11172 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11172 : lratChecker f11172 p11172 = .success := by decide +kernel
theorem unsat11172 : Unsatisfiable (PosFin 65) f11172 := by
  apply lratCheckerSound f11172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11172
  · intro a ha; simp [p11172] at ha; subst a; trivial
  · exact checked11172
theorem derived11172 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11172 := by
  apply localUnsat_implies_entails f11172 [c10205, c10605, c10217, c10216] c11172 unsat11172 (by rfl) a
  have h0 : Entails.eval a c10205 := derived10205 a h
  have h1 : Entails.eval a c10605 := derived10605 a h
  have h2 : Entails.eval a c10217 := derived10217 a h
  have h3 : Entails.eval a c10216 := derived10216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11173 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11173 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3910, some c3906, some c3905, some c3926, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11173 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11173 : lratChecker f11173 p11173 = .success := by decide +kernel
theorem unsat11173 : Unsatisfiable (PosFin 65) f11173 := by
  apply lratCheckerSound f11173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11173
  · intro a ha; simp [p11173] at ha; subst a; trivial
  · exact checked11173
theorem derived11173 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11173 := by
  apply localUnsat_implies_entails f11173 [c11170, c3910, c3906, c3905, c3926] c11173 unsat11173 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3910 := h 3909 (by decide)
  have h2 : Entails.eval a c3906 := h 3905 (by decide)
  have h3 : Entails.eval a c3905 := h 3904 (by decide)
  have h4 : Entails.eval a c3926 := h 3925 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11174 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11174 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10745, some c10623, some c10812, some c10478, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11174 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11174 : lratChecker f11174 p11174 = .success := by decide +kernel
theorem unsat11174 : Unsatisfiable (PosFin 65) f11174 := by
  apply lratCheckerSound f11174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11174
  · intro a ha; simp [p11174] at ha; subst a; trivial
  · exact checked11174
theorem derived11174 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11174 := by
  apply localUnsat_implies_entails f11174 [c10745, c10623, c10812, c10478] c11174 unsat11174 (by rfl) a
  have h0 : Entails.eval a c10745 := derived10745 a h
  have h1 : Entails.eval a c10623 := derived10623 a h
  have h2 : Entails.eval a c10812 := derived10812 a h
  have h3 : Entails.eval a c10478 := derived10478 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11175 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11175 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3912, some c10431, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11175 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11175 : lratChecker f11175 p11175 = .success := by decide +kernel
theorem unsat11175 : Unsatisfiable (PosFin 65) f11175 := by
  apply lratCheckerSound f11175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11175
  · intro a ha; simp [p11175] at ha; subst a; trivial
  · exact checked11175
theorem derived11175 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11175 := by
  apply localUnsat_implies_entails f11175 [c11170, c3912, c10431] c11175 unsat11175 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3912 := h 3911 (by decide)
  have h2 : Entails.eval a c10431 := derived10431 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11176 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨57, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11176 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10538, some c10400, some c11172, some c10581, some c10542, some c10369, some c10218, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11176 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11176 : lratChecker f11176 p11176 = .success := by decide +kernel
theorem unsat11176 : Unsatisfiable (PosFin 65) f11176 := by
  apply lratCheckerSound f11176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11176
  · intro a ha; simp [p11176] at ha; subst a; trivial
  · exact checked11176
theorem derived11176 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11176 := by
  apply localUnsat_implies_entails f11176 [c11018, c10538, c10400, c11172, c10581, c10542, c10369, c10218] c11176 unsat11176 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10538 := derived10538 a h
  have h2 : Entails.eval a c10400 := derived10400 a h
  have h3 : Entails.eval a c11172 := derived11172 a h
  have h4 : Entails.eval a c10581 := derived10581 a h
  have h5 : Entails.eval a c10542 := derived10542 a h
  have h6 : Entails.eval a c10369 := derived10369 a h
  have h7 : Entails.eval a c10218 := derived10218 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11177 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11177 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c10795, some c3918, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11177 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11177 : lratChecker f11177 p11177 = .success := by decide +kernel
theorem unsat11177 : Unsatisfiable (PosFin 65) f11177 := by
  apply lratCheckerSound f11177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11177
  · intro a ha; simp [p11177] at ha; subst a; trivial
  · exact checked11177
theorem derived11177 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11177 := by
  apply localUnsat_implies_entails f11177 [c11170, c10795, c3918] c11177 unsat11177 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c10795 := derived10795 a h
  have h2 : Entails.eval a c3918 := h 3917 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11178 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨55, by decide⟩, false), (⟨6, by decide⟩, false), (⟨51, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11178 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3891, some c3927, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11178 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11178 : lratChecker f11178 p11178 = .success := by decide +kernel
theorem unsat11178 : Unsatisfiable (PosFin 65) f11178 := by
  apply lratCheckerSound f11178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11178
  · intro a ha; simp [p11178] at ha; subst a; trivial
  · exact checked11178
theorem derived11178 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11178 := by
  apply localUnsat_implies_entails f11178 [c11170, c3891, c3927] c11178 unsat11178 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3891 := h 3890 (by decide)
  have h2 : Entails.eval a c3927 := h 3926 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11179 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, true), (⟨28, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11179 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10633, some c10815, some c10610, some c10615, some c10618, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11179 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11179 : lratChecker f11179 p11179 = .success := by decide +kernel
theorem unsat11179 : Unsatisfiable (PosFin 65) f11179 := by
  apply lratCheckerSound f11179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11179
  · intro a ha; simp [p11179] at ha; subst a; trivial
  · exact checked11179
theorem derived11179 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11179 := by
  apply localUnsat_implies_entails f11179 [c10633, c10815, c10610, c10615, c10618] c11179 unsat11179 (by rfl) a
  have h0 : Entails.eval a c10633 := derived10633 a h
  have h1 : Entails.eval a c10815 := derived10815 a h
  have h2 : Entails.eval a c10610 := derived10610 a h
  have h3 : Entails.eval a c10615 := derived10615 a h
  have h4 : Entails.eval a c10618 := derived10618 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11180 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨30, by decide⟩, true), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11180 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11179, some c3895, some c3911, some c3903, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11180 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11180 : lratChecker f11180 p11180 = .success := by decide +kernel
theorem unsat11180 : Unsatisfiable (PosFin 65) f11180 := by
  apply lratCheckerSound f11180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11180
  · intro a ha; simp [p11180] at ha; subst a; trivial
  · exact checked11180
theorem derived11180 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11180 := by
  apply localUnsat_implies_entails f11180 [c11170, c11179, c3895, c3911, c3903] c11180 unsat11180 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11179 := derived11179 a h
  have h2 : Entails.eval a c3895 := h 3894 (by decide)
  have h3 : Entails.eval a c3911 := h 3910 (by decide)
  have h4 : Entails.eval a c3903 := h 3902 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11181 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨28, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11181 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11180, some c10624, some c3910, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11181 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11181 : lratChecker f11181 p11181 = .success := by decide +kernel
theorem unsat11181 : Unsatisfiable (PosFin 65) f11181 := by
  apply lratCheckerSound f11181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11181
  · intro a ha; simp [p11181] at ha; subst a; trivial
  · exact checked11181
theorem derived11181 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11181 := by
  apply localUnsat_implies_entails f11181 [c11170, c11180, c10624, c3910] c11181 unsat11181 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11180 := derived11180 a h
  have h2 : Entails.eval a c10624 := derived10624 a h
  have h3 : Entails.eval a c3910 := h 3909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11182 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11182 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11177, some c11181, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11182 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11182 : lratChecker f11182 p11182 = .success := by decide +kernel
theorem unsat11182 : Unsatisfiable (PosFin 65) f11182 := by
  apply lratCheckerSound f11182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11182
  · intro a ha; simp [p11182] at ha; subst a; trivial
  · exact checked11182
theorem derived11182 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11182 := by
  apply localUnsat_implies_entails f11182 [c11177, c11181] c11182 unsat11182 (by rfl) a
  have h0 : Entails.eval a c11177 := derived11177 a h
  have h1 : Entails.eval a c11181 := derived11181 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11183 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨30, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11183 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c10624, some c3910, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11183 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11183 : lratChecker f11183 p11183 = .success := by decide +kernel
theorem unsat11183 : Unsatisfiable (PosFin 65) f11183 := by
  apply lratCheckerSound f11183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11183
  · intro a ha; simp [p11183] at ha; subst a; trivial
  · exact checked11183
theorem derived11183 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11183 := by
  apply localUnsat_implies_entails f11183 [c11170, c10624, c3910] c11183 unsat11183 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c10624 := derived10624 a h
  have h2 : Entails.eval a c3910 := h 3909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11184 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨26, by decide⟩, true), (⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11184 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11018, some c3914, some c3888, some c3889, some c3943, some c3944, some c3891, some c7994, some c329, some c6060, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11184 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11184 : lratChecker f11184 p11184 = .success := by decide +kernel
theorem unsat11184 : Unsatisfiable (PosFin 65) f11184 := by
  apply lratCheckerSound f11184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11184
  · intro a ha; simp [p11184] at ha; subst a; trivial
  · exact checked11184
theorem derived11184 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11184 := by
  apply localUnsat_implies_entails f11184 [c11170, c11018, c3914, c3888, c3889, c3943, c3944, c3891, c7994, c329, c6060] c11184 unsat11184 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11018 := derived11018 a h
  have h2 : Entails.eval a c3914 := h 3913 (by decide)
  have h3 : Entails.eval a c3888 := h 3887 (by decide)
  have h4 : Entails.eval a c3889 := h 3888 (by decide)
  have h5 : Entails.eval a c3943 := h 3942 (by decide)
  have h6 : Entails.eval a c3944 := h 3943 (by decide)
  have h7 : Entails.eval a c3891 := h 3890 (by decide)
  have h8 : Entails.eval a c7994 := derived7994 a h
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c6060 := h 6059 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11185 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨64, by decide⟩, true), (⟨22, by decide⟩, false), (⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11185 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11018, some c329, some c6060, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11185 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11185 : lratChecker f11185 p11185 = .success := by decide +kernel
theorem unsat11185 : Unsatisfiable (PosFin 65) f11185 := by
  apply lratCheckerSound f11185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11185
  · intro a ha; simp [p11185] at ha; subst a; trivial
  · exact checked11185
theorem derived11185 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11185 := by
  apply localUnsat_implies_entails f11185 [c11170, c11018, c329, c6060] c11185 unsat11185 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11018 := derived11018 a h
  have h2 : Entails.eval a c329 := h 328 (by decide)
  have h3 : Entails.eval a c6060 := h 6059 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11186 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, true), (⟨17, by decide⟩, false), (⟨13, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11186 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c3930, some c3927, some c3914, some c11184, some c8269, some c11185, some c11178, some c6059, some c322, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11186 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11186 : lratChecker f11186 p11186 = .success := by decide +kernel
theorem unsat11186 : Unsatisfiable (PosFin 65) f11186 := by
  apply lratCheckerSound f11186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11186
  · intro a ha; simp [p11186] at ha; subst a; trivial
  · exact checked11186
theorem derived11186 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11186 := by
  apply localUnsat_implies_entails f11186 [c11018, c11170, c3930, c3927, c3914, c11184, c8269, c11185, c11178, c6059, c322] c11186 unsat11186 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c3930 := h 3929 (by decide)
  have h3 : Entails.eval a c3927 := h 3926 (by decide)
  have h4 : Entails.eval a c3914 := h 3913 (by decide)
  have h5 : Entails.eval a c11184 := derived11184 a h
  have h6 : Entails.eval a c8269 := derived8269 a h
  have h7 : Entails.eval a c11185 := derived11185 a h
  have h8 : Entails.eval a c11178 := derived11178 a h
  have h9 : Entails.eval a c6059 := h 6058 (by decide)
  have h10 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11187 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨22, by decide⟩, true), (⟨13, by decide⟩, false), (⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11187 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c3927, some c6110, some c6108, some c3891, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11187 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11187 : lratChecker f11187 p11187 = .success := by decide +kernel
theorem unsat11187 : Unsatisfiable (PosFin 65) f11187 := by
  apply lratCheckerSound f11187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11187
  · intro a ha; simp [p11187] at ha; subst a; trivial
  · exact checked11187
theorem derived11187 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11187 := by
  apply localUnsat_implies_entails f11187 [c11018, c11170, c3927, c6110, c6108, c3891] c11187 unsat11187 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c3927 := h 3926 (by decide)
  have h3 : Entails.eval a c6110 := h 6109 (by decide)
  have h4 : Entails.eval a c6108 := h 6107 (by decide)
  have h5 : Entails.eval a c3891 := h 3890 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11188 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, true), (⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11188 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3927, some c3914, some c3923, some c3903, some c3920, some c3919, some c3930, some c11186, some c4014, some c10502, some c4239, some c10732, some c3184, some c4887, some c3566, some c2398, some c11187, some c3888, some c3889, some c821, some c6107, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11188 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked11188 : lratChecker f11188 p11188 = .success := by decide +kernel
theorem unsat11188 : Unsatisfiable (PosFin 65) f11188 := by
  apply lratCheckerSound f11188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11188
  · intro a ha; simp [p11188] at ha; subst a; trivial
  · exact checked11188
theorem derived11188 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11188 := by
  apply localUnsat_implies_entails f11188 [c11170, c3927, c3914, c3923, c3903, c3920, c3919, c3930, c11186, c4014, c10502, c4239, c10732, c3184, c4887, c3566, c2398, c11187, c3888, c3889, c821, c6107] c11188 unsat11188 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3927 := h 3926 (by decide)
  have h2 : Entails.eval a c3914 := h 3913 (by decide)
  have h3 : Entails.eval a c3923 := h 3922 (by decide)
  have h4 : Entails.eval a c3903 := h 3902 (by decide)
  have h5 : Entails.eval a c3920 := h 3919 (by decide)
  have h6 : Entails.eval a c3919 := h 3918 (by decide)
  have h7 : Entails.eval a c3930 := h 3929 (by decide)
  have h8 : Entails.eval a c11186 := derived11186 a h
  have h9 : Entails.eval a c4014 := h 4013 (by decide)
  have h10 : Entails.eval a c10502 := derived10502 a h
  have h11 : Entails.eval a c4239 := h 4238 (by decide)
  have h12 : Entails.eval a c10732 := derived10732 a h
  have h13 : Entails.eval a c3184 := h 3183 (by decide)
  have h14 : Entails.eval a c4887 := h 4886 (by decide)
  have h15 : Entails.eval a c3566 := h 3565 (by decide)
  have h16 : Entails.eval a c2398 := h 2397 (by decide)
  have h17 : Entails.eval a c11187 := derived11187 a h
  have h18 : Entails.eval a c3888 := h 3887 (by decide)
  have h19 : Entails.eval a c3889 := h 3888 (by decide)
  have h20 : Entails.eval a c821 := h 820 (by decide)
  have h21 : Entails.eval a c6107 := h 6106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11189 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11189 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c10617, some c10615, some c10618, some c10548, some c10372, some c10578, some c10634, some c10640, some c317, some c319, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11189 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11189 : lratChecker f11189 p11189 = .success := by decide +kernel
theorem unsat11189 : Unsatisfiable (PosFin 65) f11189 := by
  apply lratCheckerSound f11189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11189
  · intro a ha; simp [p11189] at ha; subst a; trivial
  · exact checked11189
theorem derived11189 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11189 := by
  apply localUnsat_implies_entails f11189 [c11018, c11170, c10617, c10615, c10618, c10548, c10372, c10578, c10634, c10640, c317, c319] c11189 unsat11189 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c10617 := derived10617 a h
  have h3 : Entails.eval a c10615 := derived10615 a h
  have h4 : Entails.eval a c10618 := derived10618 a h
  have h5 : Entails.eval a c10548 := derived10548 a h
  have h6 : Entails.eval a c10372 := derived10372 a h
  have h7 : Entails.eval a c10578 := derived10578 a h
  have h8 : Entails.eval a c10634 := derived10634 a h
  have h9 : Entails.eval a c10640 := derived10640 a h
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11190 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨13, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11190 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11018, some c11189, some c324, some c322, some c321, some c10311, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11190 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11190 : lratChecker f11190 p11190 = .success := by decide +kernel
theorem unsat11190 : Unsatisfiable (PosFin 65) f11190 := by
  apply lratCheckerSound f11190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11190
  · intro a ha; simp [p11190] at ha; subst a; trivial
  · exact checked11190
theorem derived11190 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11190 := by
  apply localUnsat_implies_entails f11190 [c11170, c11018, c11189, c324, c322, c321, c10311] c11190 unsat11190 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11018 := derived11018 a h
  have h2 : Entails.eval a c11189 := derived11189 a h
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c322 := h 321 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c10311 := derived10311 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11191 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11191 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11182, some c11183, some c11188, some c10626, some c10617, some c10495, some c10436, some c10630, some c10407, some c11190, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11191 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11191 : lratChecker f11191 p11191 = .success := by decide +kernel
theorem unsat11191 : Unsatisfiable (PosFin 65) f11191 := by
  apply lratCheckerSound f11191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11191
  · intro a ha; simp [p11191] at ha; subst a; trivial
  · exact checked11191
theorem derived11191 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11191 := by
  apply localUnsat_implies_entails f11191 [c11182, c11183, c11188, c10626, c10617, c10495, c10436, c10630, c10407, c11190] c11191 unsat11191 (by rfl) a
  have h0 : Entails.eval a c11182 := derived11182 a h
  have h1 : Entails.eval a c11183 := derived11183 a h
  have h2 : Entails.eval a c11188 := derived11188 a h
  have h3 : Entails.eval a c10626 := derived10626 a h
  have h4 : Entails.eval a c10617 := derived10617 a h
  have h5 : Entails.eval a c10495 := derived10495 a h
  have h6 : Entails.eval a c10436 := derived10436 a h
  have h7 : Entails.eval a c10630 := derived10630 a h
  have h8 : Entails.eval a c10407 := derived10407 a h
  have h9 : Entails.eval a c11190 := derived11190 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11192 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨30, by decide⟩, false), (⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11192 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10381, some c10495, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11192 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11192 : lratChecker f11192 p11192 = .success := by decide +kernel
theorem unsat11192 : Unsatisfiable (PosFin 65) f11192 := by
  apply lratCheckerSound f11192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11192
  · intro a ha; simp [p11192] at ha; subst a; trivial
  · exact checked11192
theorem derived11192 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11192 := by
  apply localUnsat_implies_entails f11192 [c10381, c10495] c11192 unsat11192 (by rfl) a
  have h0 : Entails.eval a c10381 := derived10381 a h
  have h1 : Entails.eval a c10495 := derived10495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11193 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11193 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11182, some c11191, some c11192, some c3913, some c3927, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11193 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11193 : lratChecker f11193 p11193 = .success := by decide +kernel
theorem unsat11193 : Unsatisfiable (PosFin 65) f11193 := by
  apply lratCheckerSound f11193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11193
  · intro a ha; simp [p11193] at ha; subst a; trivial
  · exact checked11193
theorem derived11193 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11193 := by
  apply localUnsat_implies_entails f11193 [c11170, c11182, c11191, c11192, c3913, c3927] c11193 unsat11193 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11182 := derived11182 a h
  have h2 : Entails.eval a c11191 := derived11191 a h
  have h3 : Entails.eval a c11192 := derived11192 a h
  have h4 : Entails.eval a c3913 := h 3912 (by decide)
  have h5 : Entails.eval a c3927 := h 3926 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11194 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨18, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11194 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3924, some c3927, some c3907, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11194 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11194 : lratChecker f11194 p11194 = .success := by decide +kernel
theorem unsat11194 : Unsatisfiable (PosFin 65) f11194 := by
  apply lratCheckerSound f11194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11194
  · intro a ha; simp [p11194] at ha; subst a; trivial
  · exact checked11194
theorem derived11194 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11194 := by
  apply localUnsat_implies_entails f11194 [c11170, c3924, c3927, c3907] c11194 unsat11194 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3924 := h 3923 (by decide)
  have h2 : Entails.eval a c3927 := h 3926 (by decide)
  have h3 : Entails.eval a c3907 := h 3906 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11195 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11195 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3895, some c3911, some c3907, some c3901, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11195 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11195 : lratChecker f11195 p11195 = .success := by decide +kernel
theorem unsat11195 : Unsatisfiable (PosFin 65) f11195 := by
  apply lratCheckerSound f11195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11195
  · intro a ha; simp [p11195] at ha; subst a; trivial
  · exact checked11195
theorem derived11195 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11195 := by
  apply localUnsat_implies_entails f11195 [c11170, c3895, c3911, c3907, c3901] c11195 unsat11195 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3895 := h 3894 (by decide)
  have h2 : Entails.eval a c3911 := h 3910 (by decide)
  have h3 : Entails.eval a c3907 := h 3906 (by decide)
  have h4 : Entails.eval a c3901 := h 3900 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11196 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨21, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨22, by decide⟩, false), (⟨31, by decide⟩, false), (⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11196 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c6087, some c355, some c322, some c5612, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11196 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11196 : lratChecker f11196 p11196 = .success := by decide +kernel
theorem unsat11196 : Unsatisfiable (PosFin 65) f11196 := by
  apply lratCheckerSound f11196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11196
  · intro a ha; simp [p11196] at ha; subst a; trivial
  · exact checked11196
theorem derived11196 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11196 := by
  apply localUnsat_implies_entails f11196 [c11018, c11170, c6087, c355, c322, c5612] c11196 unsat11196 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c6087 := h 6086 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c322 := h 321 (by decide)
  have h5 : Entails.eval a c5612 := h 5611 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11197 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11197 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c3933, some c3894, some c3903, some c3919, some c11195, some c4001, some c4235, some c4875, some c3780, some c10787, some c10827, some c4278, some c3182, some c2393, some c11196, some c3886, some c4270, some c3890, some c352, some c2651, some c10916, some c8380, some c3887, some c5623, some c4512, some c4499, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11197 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked11197 : lratChecker f11197 p11197 = .success := by decide +kernel
theorem unsat11197 : Unsatisfiable (PosFin 65) f11197 := by
  apply lratCheckerSound f11197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11197
  · intro a ha; simp [p11197] at ha; subst a; trivial
  · exact checked11197
theorem derived11197 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11197 := by
  apply localUnsat_implies_entails f11197 [c11018, c11170, c3933, c3894, c3903, c3919, c11195, c4001, c4235, c4875, c3780, c10787, c10827, c4278, c3182, c2393, c11196, c3886, c4270, c3890, c352, c2651, c10916, c8380, c3887, c5623, c4512, c4499] c11197 unsat11197 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c3933 := h 3932 (by decide)
  have h3 : Entails.eval a c3894 := h 3893 (by decide)
  have h4 : Entails.eval a c3903 := h 3902 (by decide)
  have h5 : Entails.eval a c3919 := h 3918 (by decide)
  have h6 : Entails.eval a c11195 := derived11195 a h
  have h7 : Entails.eval a c4001 := h 4000 (by decide)
  have h8 : Entails.eval a c4235 := h 4234 (by decide)
  have h9 : Entails.eval a c4875 := h 4874 (by decide)
  have h10 : Entails.eval a c3780 := h 3779 (by decide)
  have h11 : Entails.eval a c10787 := derived10787 a h
  have h12 : Entails.eval a c10827 := derived10827 a h
  have h13 : Entails.eval a c4278 := h 4277 (by decide)
  have h14 : Entails.eval a c3182 := h 3181 (by decide)
  have h15 : Entails.eval a c2393 := h 2392 (by decide)
  have h16 : Entails.eval a c11196 := derived11196 a h
  have h17 : Entails.eval a c3886 := h 3885 (by decide)
  have h18 : Entails.eval a c4270 := h 4269 (by decide)
  have h19 : Entails.eval a c3890 := h 3889 (by decide)
  have h20 : Entails.eval a c352 := h 351 (by decide)
  have h21 : Entails.eval a c2651 := h 2650 (by decide)
  have h22 : Entails.eval a c10916 := derived10916 a h
  have h23 : Entails.eval a c8380 := derived8380 a h
  have h24 : Entails.eval a c3887 := h 3886 (by decide)
  have h25 : Entails.eval a c5623 := h 5622 (by decide)
  have h26 : Entails.eval a c4512 := h 4511 (by decide)
  have h27 : Entails.eval a c4499 := h 4498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11198 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11198 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c3915, some c3930, some c3933, some c11173, some c3894, some c11194, some c11197, some c4233, some c3919, some c3996, some c4883, some c3909, some c10419, some c3566, some c11195, some c10387, some c3184, some c2388, some c2980, some c3886, some c812, some c817, some c6113, some c6119, some c10916, some c8380, some c404, some c6118, some c4512, some c395, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11198 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked11198 : lratChecker f11198 p11198 = .success := by decide +kernel
theorem unsat11198 : Unsatisfiable (PosFin 65) f11198 := by
  apply lratCheckerSound f11198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11198
  · intro a ha; simp [p11198] at ha; subst a; trivial
  · exact checked11198
theorem derived11198 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11198 := by
  apply localUnsat_implies_entails f11198 [c11018, c11170, c3915, c3930, c3933, c11173, c3894, c11194, c11197, c4233, c3919, c3996, c4883, c3909, c10419, c3566, c11195, c10387, c3184, c2388, c2980, c3886, c812, c817, c6113, c6119, c10916, c8380, c404, c6118, c4512, c395] c11198 unsat11198 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c3915 := h 3914 (by decide)
  have h3 : Entails.eval a c3930 := h 3929 (by decide)
  have h4 : Entails.eval a c3933 := h 3932 (by decide)
  have h5 : Entails.eval a c11173 := derived11173 a h
  have h6 : Entails.eval a c3894 := h 3893 (by decide)
  have h7 : Entails.eval a c11194 := derived11194 a h
  have h8 : Entails.eval a c11197 := derived11197 a h
  have h9 : Entails.eval a c4233 := h 4232 (by decide)
  have h10 : Entails.eval a c3919 := h 3918 (by decide)
  have h11 : Entails.eval a c3996 := h 3995 (by decide)
  have h12 : Entails.eval a c4883 := h 4882 (by decide)
  have h13 : Entails.eval a c3909 := h 3908 (by decide)
  have h14 : Entails.eval a c10419 := derived10419 a h
  have h15 : Entails.eval a c3566 := h 3565 (by decide)
  have h16 : Entails.eval a c11195 := derived11195 a h
  have h17 : Entails.eval a c10387 := derived10387 a h
  have h18 : Entails.eval a c3184 := h 3183 (by decide)
  have h19 : Entails.eval a c2388 := h 2387 (by decide)
  have h20 : Entails.eval a c2980 := h 2979 (by decide)
  have h21 : Entails.eval a c3886 := h 3885 (by decide)
  have h22 : Entails.eval a c812 := h 811 (by decide)
  have h23 : Entails.eval a c817 := h 816 (by decide)
  have h24 : Entails.eval a c6113 := h 6112 (by decide)
  have h25 : Entails.eval a c6119 := h 6118 (by decide)
  have h26 : Entails.eval a c10916 := derived10916 a h
  have h27 : Entails.eval a c8380 := derived8380 a h
  have h28 : Entails.eval a c404 := h 403 (by decide)
  have h29 : Entails.eval a c6118 := h 6117 (by decide)
  have h30 : Entails.eval a c4512 := h 4511 (by decide)
  have h31 : Entails.eval a c395 := h 394 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11199 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11199 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11018, some c11173, some c11195, some c11194, some c3915, some c3930, some c3909, some c3894, some c3919, some c3933, some c3903, some c11197, some c3996, some c4233, some c10387, some c10419, some c4883, some c3184, some c3566, some c2388, some c11198, some c354, some c6094, some c6095, some c254, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p11199 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked11199 : lratChecker f11199 p11199 = .success := by decide +kernel
theorem unsat11199 : Unsatisfiable (PosFin 65) f11199 := by
  apply lratCheckerSound f11199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11199
  · intro a ha; simp [p11199] at ha; subst a; trivial
  · exact checked11199
theorem derived11199 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11199 := by
  apply localUnsat_implies_entails f11199 [c11170, c11018, c11173, c11195, c11194, c3915, c3930, c3909, c3894, c3919, c3933, c3903, c11197, c3996, c4233, c10387, c10419, c4883, c3184, c3566, c2388, c11198, c354, c6094, c6095, c254] c11199 unsat11199 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11018 := derived11018 a h
  have h2 : Entails.eval a c11173 := derived11173 a h
  have h3 : Entails.eval a c11195 := derived11195 a h
  have h4 : Entails.eval a c11194 := derived11194 a h
  have h5 : Entails.eval a c3915 := h 3914 (by decide)
  have h6 : Entails.eval a c3930 := h 3929 (by decide)
  have h7 : Entails.eval a c3909 := h 3908 (by decide)
  have h8 : Entails.eval a c3894 := h 3893 (by decide)
  have h9 : Entails.eval a c3919 := h 3918 (by decide)
  have h10 : Entails.eval a c3933 := h 3932 (by decide)
  have h11 : Entails.eval a c3903 := h 3902 (by decide)
  have h12 : Entails.eval a c11197 := derived11197 a h
  have h13 : Entails.eval a c3996 := h 3995 (by decide)
  have h14 : Entails.eval a c4233 := h 4232 (by decide)
  have h15 : Entails.eval a c10387 := derived10387 a h
  have h16 : Entails.eval a c10419 := derived10419 a h
  have h17 : Entails.eval a c4883 := h 4882 (by decide)
  have h18 : Entails.eval a c3184 := h 3183 (by decide)
  have h19 : Entails.eval a c3566 := h 3565 (by decide)
  have h20 : Entails.eval a c2388 := h 2387 (by decide)
  have h21 : Entails.eval a c11198 := derived11198 a h
  have h22 : Entails.eval a c354 := h 353 (by decide)
  have h23 : Entails.eval a c6094 := h 6093 (by decide)
  have h24 : Entails.eval a c6095 := h 6094 (by decide)
  have h25 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11200 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11200 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11173, some c11194, some c11195, some c11199, some c3908, some c3916, some c3919, some c3926, some c3921, some c3894, some c11197, some c3996, some c10387, some c10419, some c4324, some c4505, some c4327, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p11200 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked11200 : lratChecker f11200 p11200 = .success := by decide +kernel
theorem unsat11200 : Unsatisfiable (PosFin 65) f11200 := by
  apply lratCheckerSound f11200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11200
  · intro a ha; simp [p11200] at ha; subst a; trivial
  · exact checked11200
theorem derived11200 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11200 := by
  apply localUnsat_implies_entails f11200 [c11170, c11173, c11194, c11195, c11199, c3908, c3916, c3919, c3926, c3921, c3894, c11197, c3996, c10387, c10419, c4324, c4505, c4327] c11200 unsat11200 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11173 := derived11173 a h
  have h2 : Entails.eval a c11194 := derived11194 a h
  have h3 : Entails.eval a c11195 := derived11195 a h
  have h4 : Entails.eval a c11199 := derived11199 a h
  have h5 : Entails.eval a c3908 := h 3907 (by decide)
  have h6 : Entails.eval a c3916 := h 3915 (by decide)
  have h7 : Entails.eval a c3919 := h 3918 (by decide)
  have h8 : Entails.eval a c3926 := h 3925 (by decide)
  have h9 : Entails.eval a c3921 := h 3920 (by decide)
  have h10 : Entails.eval a c3894 := h 3893 (by decide)
  have h11 : Entails.eval a c11197 := derived11197 a h
  have h12 : Entails.eval a c3996 := h 3995 (by decide)
  have h13 : Entails.eval a c10387 := derived10387 a h
  have h14 : Entails.eval a c10419 := derived10419 a h
  have h15 : Entails.eval a c4324 := h 4323 (by decide)
  have h16 : Entails.eval a c4505 := h 4504 (by decide)
  have h17 : Entails.eval a c4327 := h 4326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11201 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨26, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11201 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4323, some c4325, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11201 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11201 : lratChecker f11201 p11201 = .success := by decide +kernel
theorem unsat11201 : Unsatisfiable (PosFin 65) f11201 := by
  apply lratCheckerSound f11201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11201
  · intro a ha; simp [p11201] at ha; subst a; trivial
  · exact checked11201
theorem derived11201 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11201 := by
  apply localUnsat_implies_entails f11201 [c4323, c4325] c11201 unsat11201 (by rfl) a
  have h0 : Entails.eval a c4323 := h 4322 (by decide)
  have h1 : Entails.eval a c4325 := h 4324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11202 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨15, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11202 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3856, some c10660, some c3070, some c3313, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11202 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11202 : lratChecker f11202 p11202 = .success := by decide +kernel
theorem unsat11202 : Unsatisfiable (PosFin 65) f11202 := by
  apply lratCheckerSound f11202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11202
  · intro a ha; simp [p11202] at ha; subst a; trivial
  · exact checked11202
theorem derived11202 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11202 := by
  apply localUnsat_implies_entails f11202 [c11170, c3856, c10660, c3070, c3313] c11202 unsat11202 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3856 := h 3855 (by decide)
  have h2 : Entails.eval a c10660 := derived10660 a h
  have h3 : Entails.eval a c3070 := h 3069 (by decide)
  have h4 : Entails.eval a c3313 := h 3312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11203 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11203 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c10420, some c10803, some c4060, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p11203 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11203 : lratChecker f11203 p11203 = .success := by decide +kernel
theorem unsat11203 : Unsatisfiable (PosFin 65) f11203 := by
  apply lratCheckerSound f11203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11203
  · intro a ha; simp [p11203] at ha; subst a; trivial
  · exact checked11203
theorem derived11203 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11203 := by
  apply localUnsat_implies_entails f11203 [c11170, c10420, c10803, c4060] c11203 unsat11203 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c10420 := derived10420 a h
  have h2 : Entails.eval a c10803 := derived10803 a h
  have h3 : Entails.eval a c4060 := h 4059 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11204 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11204 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11202, some c11203, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11204 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11204 : lratChecker f11204 p11204 = .success := by decide +kernel
theorem unsat11204 : Unsatisfiable (PosFin 65) f11204 := by
  apply lratCheckerSound f11204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11204
  · intro a ha; simp [p11204] at ha; subst a; trivial
  · exact checked11204
theorem derived11204 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11204 := by
  apply localUnsat_implies_entails f11204 [c11202, c11203] c11204 unsat11204 (by rfl) a
  have h0 : Entails.eval a c11202 := derived11202 a h
  have h1 : Entails.eval a c11203 := derived11203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11205 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11205 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11204, some c11201, some c10662, some c10806, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p11205 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11205 : lratChecker f11205 p11205 = .success := by decide +kernel
theorem unsat11205 : Unsatisfiable (PosFin 65) f11205 := by
  apply lratCheckerSound f11205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11205
  · intro a ha; simp [p11205] at ha; subst a; trivial
  · exact checked11205
theorem derived11205 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11205 := by
  apply localUnsat_implies_entails f11205 [c11204, c11201, c10662, c10806] c11205 unsat11205 (by rfl) a
  have h0 : Entails.eval a c11204 := derived11204 a h
  have h1 : Entails.eval a c11201 := derived11201 a h
  have h2 : Entails.eval a c10662 := derived10662 a h
  have h3 : Entails.eval a c10806 := derived10806 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11206 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11206 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11193, some c11200, some c10626, some c10495, some c10487, some c10416, some c10813, some c10615, some c11175, some c11205, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11206 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11206 : lratChecker f11206 p11206 = .success := by decide +kernel
theorem unsat11206 : Unsatisfiable (PosFin 65) f11206 := by
  apply lratCheckerSound f11206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11206
  · intro a ha; simp [p11206] at ha; subst a; trivial
  · exact checked11206
theorem derived11206 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11206 := by
  apply localUnsat_implies_entails f11206 [c11193, c11200, c10626, c10495, c10487, c10416, c10813, c10615, c11175, c11205] c11206 unsat11206 (by rfl) a
  have h0 : Entails.eval a c11193 := derived11193 a h
  have h1 : Entails.eval a c11200 := derived11200 a h
  have h2 : Entails.eval a c10626 := derived10626 a h
  have h3 : Entails.eval a c10495 := derived10495 a h
  have h4 : Entails.eval a c10487 := derived10487 a h
  have h5 : Entails.eval a c10416 := derived10416 a h
  have h6 : Entails.eval a c10813 := derived10813 a h
  have h7 : Entails.eval a c10615 := derived10615 a h
  have h8 : Entails.eval a c11175 := derived11175 a h
  have h9 : Entails.eval a c11205 := derived11205 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11207 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11207 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11193, some c11200, some c11206, some c11181, some c10490, some c10817, some c10416, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11207 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11207 : lratChecker f11207 p11207 = .success := by decide +kernel
theorem unsat11207 : Unsatisfiable (PosFin 65) f11207 := by
  apply lratCheckerSound f11207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11207
  · intro a ha; simp [p11207] at ha; subst a; trivial
  · exact checked11207
theorem derived11207 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11207 := by
  apply localUnsat_implies_entails f11207 [c11193, c11200, c11206, c11181, c10490, c10817, c10416] c11207 unsat11207 (by rfl) a
  have h0 : Entails.eval a c11193 := derived11193 a h
  have h1 : Entails.eval a c11200 := derived11200 a h
  have h2 : Entails.eval a c11206 := derived11206 a h
  have h3 : Entails.eval a c11181 := derived11181 a h
  have h4 : Entails.eval a c10490 := derived10490 a h
  have h5 : Entails.eval a c10817 := derived10817 a h
  have h6 : Entails.eval a c10416 := derived10416 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11208 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11208 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10463, some c11171, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11208 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11208 : lratChecker f11208 p11208 = .success := by decide +kernel
theorem unsat11208 : Unsatisfiable (PosFin 65) f11208 := by
  apply lratCheckerSound f11208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11208
  · intro a ha; simp [p11208] at ha; subst a; trivial
  · exact checked11208
theorem derived11208 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11208 := by
  apply localUnsat_implies_entails f11208 [c10463, c11171] c11208 unsat11208 (by rfl) a
  have h0 : Entails.eval a c10463 := derived10463 a h
  have h1 : Entails.eval a c11171 := derived11171 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11209 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11209 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3065, some c3067, some c3066, some c3078, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11209 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11209 : lratChecker f11209 p11209 = .success := by decide +kernel
theorem unsat11209 : Unsatisfiable (PosFin 65) f11209 := by
  apply lratCheckerSound f11209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11209
  · intro a ha; simp [p11209] at ha; subst a; trivial
  · exact checked11209
theorem derived11209 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11209 := by
  apply localUnsat_implies_entails f11209 [c11170, c3065, c3067, c3066, c3078] c11209 unsat11209 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3065 := h 3064 (by decide)
  have h2 : Entails.eval a c3067 := h 3066 (by decide)
  have h3 : Entails.eval a c3066 := h 3065 (by decide)
  have h4 : Entails.eval a c3078 := h 3077 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11210 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11210 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10667, some c10671, some c10669, some c10684, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p11210 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11210 : lratChecker f11210 p11210 = .success := by decide +kernel
theorem unsat11210 : Unsatisfiable (PosFin 65) f11210 := by
  apply lratCheckerSound f11210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11210
  · intro a ha; simp [p11210] at ha; subst a; trivial
  · exact checked11210
theorem derived11210 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11210 := by
  apply localUnsat_implies_entails f11210 [c10667, c10671, c10669, c10684] c11210 unsat11210 (by rfl) a
  have h0 : Entails.eval a c10667 := derived10667 a h
  have h1 : Entails.eval a c10671 := derived10671 a h
  have h2 : Entails.eval a c10669 := derived10669 a h
  have h3 : Entails.eval a c10684 := derived10684 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11211 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11211 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10553, some c10799, some c10428, some c10629, some c10406, some c11172, some c10551, some c10595, some c10369, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11211 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11211 : lratChecker f11211 p11211 = .success := by decide +kernel
theorem unsat11211 : Unsatisfiable (PosFin 65) f11211 := by
  apply lratCheckerSound f11211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11211
  · intro a ha; simp [p11211] at ha; subst a; trivial
  · exact checked11211
theorem derived11211 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11211 := by
  apply localUnsat_implies_entails f11211 [c10553, c10799, c10428, c10629, c10406, c11172, c10551, c10595, c10369] c11211 unsat11211 (by rfl) a
  have h0 : Entails.eval a c10553 := derived10553 a h
  have h1 : Entails.eval a c10799 := derived10799 a h
  have h2 : Entails.eval a c10428 := derived10428 a h
  have h3 : Entails.eval a c10629 := derived10629 a h
  have h4 : Entails.eval a c10406 := derived10406 a h
  have h5 : Entails.eval a c11172 := derived11172 a h
  have h6 : Entails.eval a c10551 := derived10551 a h
  have h7 : Entails.eval a c10595 := derived10595 a h
  have h8 : Entails.eval a c10369 := derived10369 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11212 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11212 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10589, some c10399, some c10587, some c10580, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11212 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11212 : lratChecker f11212 p11212 = .success := by decide +kernel
theorem unsat11212 : Unsatisfiable (PosFin 65) f11212 := by
  apply lratCheckerSound f11212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11212
  · intro a ha; simp [p11212] at ha; subst a; trivial
  · exact checked11212
theorem derived11212 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11212 := by
  apply localUnsat_implies_entails f11212 [c11018, c10589, c10399, c10587, c10580] c11212 unsat11212 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10589 := derived10589 a h
  have h2 : Entails.eval a c10399 := derived10399 a h
  have h3 : Entails.eval a c10587 := derived10587 a h
  have h4 : Entails.eval a c10580 := derived10580 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11213 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11213 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11207, some c11212, some c11174, some c10568, some c11176, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11213 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11213 : lratChecker f11213 p11213 = .success := by decide +kernel
theorem unsat11213 : Unsatisfiable (PosFin 65) f11213 := by
  apply lratCheckerSound f11213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11213
  · intro a ha; simp [p11213] at ha; subst a; trivial
  · exact checked11213
theorem derived11213 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11213 := by
  apply localUnsat_implies_entails f11213 [c11018, c11207, c11212, c11174, c10568, c11176] c11213 unsat11213 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11207 := derived11207 a h
  have h2 : Entails.eval a c11212 := derived11212 a h
  have h3 : Entails.eval a c11174 := derived11174 a h
  have h4 : Entails.eval a c10568 := derived10568 a h
  have h5 : Entails.eval a c11176 := derived11176 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11214 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11214 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11174, some c11212, some c10538, some c11213, some c10564, some c11208, some c11211, some c10501, some c10738, some c10816, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11214 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11214 : lratChecker f11214 p11214 = .success := by decide +kernel
theorem unsat11214 : Unsatisfiable (PosFin 65) f11214 := by
  apply lratCheckerSound f11214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11214
  · intro a ha; simp [p11214] at ha; subst a; trivial
  · exact checked11214
theorem derived11214 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11214 := by
  apply localUnsat_implies_entails f11214 [c11174, c11212, c10538, c11213, c10564, c11208, c11211, c10501, c10738, c10816] c11214 unsat11214 (by rfl) a
  have h0 : Entails.eval a c11174 := derived11174 a h
  have h1 : Entails.eval a c11212 := derived11212 a h
  have h2 : Entails.eval a c10538 := derived10538 a h
  have h3 : Entails.eval a c11213 := derived11213 a h
  have h4 : Entails.eval a c10564 := derived10564 a h
  have h5 : Entails.eval a c11208 := derived11208 a h
  have h6 : Entails.eval a c11211 := derived11211 a h
  have h7 : Entails.eval a c10501 := derived10501 a h
  have h8 : Entails.eval a c10738 := derived10738 a h
  have h9 : Entails.eval a c10816 := derived10816 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11215 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11215 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11207, some c11214, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11215 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11215 : lratChecker f11215 p11215 = .success := by decide +kernel
theorem unsat11215 : Unsatisfiable (PosFin 65) f11215 := by
  apply lratCheckerSound f11215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11215
  · intro a ha; simp [p11215] at ha; subst a; trivial
  · exact checked11215
theorem derived11215 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11215 := by
  apply localUnsat_implies_entails f11215 [c11207, c11214] c11215 unsat11215 (by rfl) a
  have h0 : Entails.eval a c11207 := derived11207 a h
  have h1 : Entails.eval a c11214 := derived11214 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11216 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨34, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11216 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11215, some c11208, some c10688, some c11211, some c10432, some c10593, some c10594, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11216 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11216 : lratChecker f11216 p11216 = .success := by decide +kernel
theorem unsat11216 : Unsatisfiable (PosFin 65) f11216 := by
  apply lratCheckerSound f11216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11216
  · intro a ha; simp [p11216] at ha; subst a; trivial
  · exact checked11216
theorem derived11216 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11216 := by
  apply localUnsat_implies_entails f11216 [c11215, c11208, c10688, c11211, c10432, c10593, c10594] c11216 unsat11216 (by rfl) a
  have h0 : Entails.eval a c11215 := derived11215 a h
  have h1 : Entails.eval a c11208 := derived11208 a h
  have h2 : Entails.eval a c10688 := derived10688 a h
  have h3 : Entails.eval a c11211 := derived11211 a h
  have h4 : Entails.eval a c10432 := derived10432 a h
  have h5 : Entails.eval a c10593 := derived10593 a h
  have h6 : Entails.eval a c10594 := derived10594 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11217 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11217 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10564, some c10568, some c11176, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p11217 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11217 : lratChecker f11217 p11217 = .success := by decide +kernel
theorem unsat11217 : Unsatisfiable (PosFin 65) f11217 := by
  apply lratCheckerSound f11217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11217
  · intro a ha; simp [p11217] at ha; subst a; trivial
  · exact checked11217
theorem derived11217 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11217 := by
  apply localUnsat_implies_entails f11217 [c11018, c10564, c10568, c11176] c11217 unsat11217 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10564 := derived10564 a h
  have h2 : Entails.eval a c10568 := derived10568 a h
  have h3 : Entails.eval a c11176 := derived11176 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11218 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11218 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10538, some c11216, some c11217, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11218 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11218 : lratChecker f11218 p11218 = .success := by decide +kernel
theorem unsat11218 : Unsatisfiable (PosFin 65) f11218 := by
  apply lratCheckerSound f11218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11218
  · intro a ha; simp [p11218] at ha; subst a; trivial
  · exact checked11218
theorem derived11218 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11218 := by
  apply localUnsat_implies_entails f11218 [c10538, c11216, c11217] c11218 unsat11218 (by rfl) a
  have h0 : Entails.eval a c10538 := derived10538 a h
  have h1 : Entails.eval a c11216 := derived11216 a h
  have h2 : Entails.eval a c11217 := derived11217 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11219 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11219 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10459, some c10611, some c10401, some c10629, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11219 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11219 : lratChecker f11219 p11219 = .success := by decide +kernel
theorem unsat11219 : Unsatisfiable (PosFin 65) f11219 := by
  apply lratCheckerSound f11219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11219
  · intro a ha; simp [p11219] at ha; subst a; trivial
  · exact checked11219
theorem derived11219 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11219 := by
  apply localUnsat_implies_entails f11219 [c10459, c10611, c10401, c10629] c11219 unsat11219 (by rfl) a
  have h0 : Entails.eval a c10459 := derived10459 a h
  have h1 : Entails.eval a c10611 := derived10611 a h
  have h2 : Entails.eval a c10401 := derived10401 a h
  have h3 : Entails.eval a c10629 := derived10629 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11220 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11220 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10698, some c10706, some c11208, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p11220 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11220 : lratChecker f11220 p11220 = .success := by decide +kernel
theorem unsat11220 : Unsatisfiable (PosFin 65) f11220 := by
  apply lratCheckerSound f11220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11220
  · intro a ha; simp [p11220] at ha; subst a; trivial
  · exact checked11220
theorem derived11220 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11220 := by
  apply localUnsat_implies_entails f11220 [c10698, c10706, c11208] c11220 unsat11220 (by rfl) a
  have h0 : Entails.eval a c10698 := derived10698 a h
  have h1 : Entails.eval a c10706 := derived10706 a h
  have h2 : Entails.eval a c11208 := derived11208 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11221 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11221 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11215, some c11212, some c11218, some c11219, some c11220, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11221 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11221 : lratChecker f11221 p11221 = .success := by decide +kernel
theorem unsat11221 : Unsatisfiable (PosFin 65) f11221 := by
  apply lratCheckerSound f11221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11221
  · intro a ha; simp [p11221] at ha; subst a; trivial
  · exact checked11221
theorem derived11221 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11221 := by
  apply localUnsat_implies_entails f11221 [c11215, c11212, c11218, c11219, c11220] c11221 unsat11221 (by rfl) a
  have h0 : Entails.eval a c11215 := derived11215 a h
  have h1 : Entails.eval a c11212 := derived11212 a h
  have h2 : Entails.eval a c11218 := derived11218 a h
  have h3 : Entails.eval a c11219 := derived11219 a h
  have h4 : Entails.eval a c11220 := derived11220 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11222 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨20, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11222 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11221, some c3919, some c10630, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11222 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11222 : lratChecker f11222 p11222 = .success := by decide +kernel
theorem unsat11222 : Unsatisfiable (PosFin 65) f11222 := by
  apply lratCheckerSound f11222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11222
  · intro a ha; simp [p11222] at ha; subst a; trivial
  · exact checked11222
theorem derived11222 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11222 := by
  apply localUnsat_implies_entails f11222 [c11170, c11221, c3919, c10630] c11222 unsat11222 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11221 := derived11221 a h
  have h2 : Entails.eval a c3919 := h 3918 (by decide)
  have h3 : Entails.eval a c10630 := derived10630 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11223 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11223 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11221, some c3905, some c10613, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11223 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11223 : lratChecker f11223 p11223 = .success := by decide +kernel
theorem unsat11223 : Unsatisfiable (PosFin 65) f11223 := by
  apply lratCheckerSound f11223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11223
  · intro a ha; simp [p11223] at ha; subst a; trivial
  · exact checked11223
theorem derived11223 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11223 := by
  apply localUnsat_implies_entails f11223 [c11170, c11221, c3905, c10613] c11223 unsat11223 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11221 := derived11221 a h
  have h2 : Entails.eval a c3905 := h 3904 (by decide)
  have h3 : Entails.eval a c10613 := derived10613 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11224 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨57, by decide⟩, true), (⟨24, by decide⟩, false), (⟨13, by decide⟩, true), (⟨20, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11224 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10206, some c10208, some c10604, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11224 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11224 : lratChecker f11224 p11224 = .success := by decide +kernel
theorem unsat11224 : Unsatisfiable (PosFin 65) f11224 := by
  apply lratCheckerSound f11224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11224
  · intro a ha; simp [p11224] at ha; subst a; trivial
  · exact checked11224
theorem derived11224 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11224 := by
  apply localUnsat_implies_entails f11224 [c10206, c10208, c10604] c11224 unsat11224 (by rfl) a
  have h0 : Entails.eval a c10206 := derived10206 a h
  have h1 : Entails.eval a c10208 := derived10208 a h
  have h2 : Entails.eval a c10604 := derived10604 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11225 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨54, by decide⟩, true), (⟨64, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11225 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5985, some c5563, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p11225 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11225 : lratChecker f11225 p11225 = .success := by decide +kernel
theorem unsat11225 : Unsatisfiable (PosFin 65) f11225 := by
  apply lratCheckerSound f11225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11225
  · intro a ha; simp [p11225] at ha; subst a; trivial
  · exact checked11225
theorem derived11225 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11225 := by
  apply localUnsat_implies_entails f11225 [c5985, c5563] c11225 unsat11225 (by rfl) a
  have h0 : Entails.eval a c5985 := h 5984 (by decide)
  have h1 : Entails.eval a c5563 := h 5562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11226 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨13, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11226 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11215, some c7994, some c10559, some c11225, some c10560, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11226 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11226 : lratChecker f11226 p11226 = .success := by decide +kernel
theorem unsat11226 : Unsatisfiable (PosFin 65) f11226 := by
  apply lratCheckerSound f11226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11226
  · intro a ha; simp [p11226] at ha; subst a; trivial
  · exact checked11226
theorem derived11226 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11226 := by
  apply localUnsat_implies_entails f11226 [c11215, c7994, c10559, c11225, c10560] c11226 unsat11226 (by rfl) a
  have h0 : Entails.eval a c11215 := derived11215 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c10559 := derived10559 a h
  have h3 : Entails.eval a c11225 := derived11225 a h
  have h4 : Entails.eval a c10560 := derived10560 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11227 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨54, by decide⟩, true), (⟨57, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11227 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8537, some c11225, some c5964, some c5780, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p11227 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11227 : lratChecker f11227 p11227 = .success := by decide +kernel
theorem unsat11227 : Unsatisfiable (PosFin 65) f11227 := by
  apply lratCheckerSound f11227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11227
  · intro a ha; simp [p11227] at ha; subst a; trivial
  · exact checked11227
theorem derived11227 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11227 := by
  apply localUnsat_implies_entails f11227 [c8537, c11225, c5964, c5780] c11227 unsat11227 (by rfl) a
  have h0 : Entails.eval a c8537 := derived8537 a h
  have h1 : Entails.eval a c11225 := derived11225 a h
  have h2 : Entails.eval a c5964 := h 5963 (by decide)
  have h3 : Entails.eval a c5780 := h 5779 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11228 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11228 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11221, some c11175, some c11223, some c11222, some c11215, some c10417, some c10494, some c10817, some c11226, some c11224, some c10558, some c11227, some c5976, some c5318, some c5462, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11228 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11228 : lratChecker f11228 p11228 = .success := by decide +kernel
theorem unsat11228 : Unsatisfiable (PosFin 65) f11228 := by
  apply lratCheckerSound f11228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11228
  · intro a ha; simp [p11228] at ha; subst a; trivial
  · exact checked11228
theorem derived11228 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11228 := by
  apply localUnsat_implies_entails f11228 [c11221, c11175, c11223, c11222, c11215, c10417, c10494, c10817, c11226, c11224, c10558, c11227, c5976, c5318, c5462] c11228 unsat11228 (by rfl) a
  have h0 : Entails.eval a c11221 := derived11221 a h
  have h1 : Entails.eval a c11175 := derived11175 a h
  have h2 : Entails.eval a c11223 := derived11223 a h
  have h3 : Entails.eval a c11222 := derived11222 a h
  have h4 : Entails.eval a c11215 := derived11215 a h
  have h5 : Entails.eval a c10417 := derived10417 a h
  have h6 : Entails.eval a c10494 := derived10494 a h
  have h7 : Entails.eval a c10817 := derived10817 a h
  have h8 : Entails.eval a c11226 := derived11226 a h
  have h9 : Entails.eval a c11224 := derived11224 a h
  have h10 : Entails.eval a c10558 := derived10558 a h
  have h11 : Entails.eval a c11227 := derived11227 a h
  have h12 : Entails.eval a c5976 := h 5975 (by decide)
  have h13 : Entails.eval a c5318 := h 5317 (by decide)
  have h14 : Entails.eval a c5462 := h 5461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11229 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨63, by decide⟩, true), (⟨13, by decide⟩, false), (⟨50, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11229 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3950, some c3949, some c3962, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11229 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11229 : lratChecker f11229 p11229 = .success := by decide +kernel
theorem unsat11229 : Unsatisfiable (PosFin 65) f11229 := by
  apply lratCheckerSound f11229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11229
  · intro a ha; simp [p11229] at ha; subst a; trivial
  · exact checked11229
theorem derived11229 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11229 := by
  apply localUnsat_implies_entails f11229 [c11170, c3950, c3949, c3962] c11229 unsat11229 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3950 := h 3949 (by decide)
  have h2 : Entails.eval a c3949 := h 3948 (by decide)
  have h3 : Entails.eval a c3962 := h 3961 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11230 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨63, by decide⟩, true), (⟨24, by decide⟩, false), (⟨13, by decide⟩, false), (⟨20, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11230 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3962, some c3959, some c3892, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11230 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11230 : lratChecker f11230 p11230 = .success := by decide +kernel
theorem unsat11230 : Unsatisfiable (PosFin 65) f11230 := by
  apply lratCheckerSound f11230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11230
  · intro a ha; simp [p11230] at ha; subst a; trivial
  · exact checked11230
theorem derived11230 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11230 := by
  apply localUnsat_implies_entails f11230 [c11170, c3962, c3959, c3892] c11230 unsat11230 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3962 := h 3961 (by decide)
  have h2 : Entails.eval a c3959 := h 3958 (by decide)
  have h3 : Entails.eval a c3892 := h 3891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11231 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨13, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11231 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11221, some c11215, some c3922, some c11223, some c10916, some c11229, some c11225, some c11230, some c6240, some c5821, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11231 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11231 : lratChecker f11231 p11231 = .success := by decide +kernel
theorem unsat11231 : Unsatisfiable (PosFin 65) f11231 := by
  apply lratCheckerSound f11231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11231
  · intro a ha; simp [p11231] at ha; subst a; trivial
  · exact checked11231
theorem derived11231 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11231 := by
  apply localUnsat_implies_entails f11231 [c11170, c11221, c11215, c3922, c11223, c10916, c11229, c11225, c11230, c6240, c5821] c11231 unsat11231 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11221 := derived11221 a h
  have h2 : Entails.eval a c11215 := derived11215 a h
  have h3 : Entails.eval a c3922 := h 3921 (by decide)
  have h4 : Entails.eval a c11223 := derived11223 a h
  have h5 : Entails.eval a c10916 := derived10916 a h
  have h6 : Entails.eval a c11229 := derived11229 a h
  have h7 : Entails.eval a c11225 := derived11225 a h
  have h8 : Entails.eval a c11230 := derived11230 a h
  have h9 : Entails.eval a c6240 := h 6239 (by decide)
  have h10 : Entails.eval a c5821 := h 5820 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11232 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11232 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11221, some c11215, some c11175, some c11223, some c11222, some c11228, some c3922, some c3899, some c3915, some c3925, some c3931, some c3903, some c11231, some c7994, some c3952, some c3893, some c11225, some c3961, some c5975, some c5828, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11232 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked11232 : lratChecker f11232 p11232 = .success := by decide +kernel
theorem unsat11232 : Unsatisfiable (PosFin 65) f11232 := by
  apply lratCheckerSound f11232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11232
  · intro a ha; simp [p11232] at ha; subst a; trivial
  · exact checked11232
theorem derived11232 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11232 := by
  apply localUnsat_implies_entails f11232 [c11170, c11221, c11215, c11175, c11223, c11222, c11228, c3922, c3899, c3915, c3925, c3931, c3903, c11231, c7994, c3952, c3893, c11225, c3961, c5975, c5828] c11232 unsat11232 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11221 := derived11221 a h
  have h2 : Entails.eval a c11215 := derived11215 a h
  have h3 : Entails.eval a c11175 := derived11175 a h
  have h4 : Entails.eval a c11223 := derived11223 a h
  have h5 : Entails.eval a c11222 := derived11222 a h
  have h6 : Entails.eval a c11228 := derived11228 a h
  have h7 : Entails.eval a c3922 := h 3921 (by decide)
  have h8 : Entails.eval a c3899 := h 3898 (by decide)
  have h9 : Entails.eval a c3915 := h 3914 (by decide)
  have h10 : Entails.eval a c3925 := h 3924 (by decide)
  have h11 : Entails.eval a c3931 := h 3930 (by decide)
  have h12 : Entails.eval a c3903 := h 3902 (by decide)
  have h13 : Entails.eval a c11231 := derived11231 a h
  have h14 : Entails.eval a c7994 := derived7994 a h
  have h15 : Entails.eval a c3952 := h 3951 (by decide)
  have h16 : Entails.eval a c3893 := h 3892 (by decide)
  have h17 : Entails.eval a c11225 := derived11225 a h
  have h18 : Entails.eval a c3961 := h 3960 (by decide)
  have h19 : Entails.eval a c5975 := h 5974 (by decide)
  have h20 : Entails.eval a c5828 := h 5827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11233 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11233 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11221, some c11215, some c11232, some c10699, some c3896, some c3917, some c4407, some c4504, some c3903, some c4928, some c11177, some c3913, some c4016, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11233 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11233 : lratChecker f11233 p11233 = .success := by decide +kernel
theorem unsat11233 : Unsatisfiable (PosFin 65) f11233 := by
  apply lratCheckerSound f11233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11233
  · intro a ha; simp [p11233] at ha; subst a; trivial
  · exact checked11233
theorem derived11233 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11233 := by
  apply localUnsat_implies_entails f11233 [c11170, c11221, c11215, c11232, c10699, c3896, c3917, c4407, c4504, c3903, c4928, c11177, c3913, c4016] c11233 unsat11233 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11221 := derived11221 a h
  have h2 : Entails.eval a c11215 := derived11215 a h
  have h3 : Entails.eval a c11232 := derived11232 a h
  have h4 : Entails.eval a c10699 := derived10699 a h
  have h5 : Entails.eval a c3896 := h 3895 (by decide)
  have h6 : Entails.eval a c3917 := h 3916 (by decide)
  have h7 : Entails.eval a c4407 := h 4406 (by decide)
  have h8 : Entails.eval a c4504 := h 4503 (by decide)
  have h9 : Entails.eval a c3903 := h 3902 (by decide)
  have h10 : Entails.eval a c4928 := h 4927 (by decide)
  have h11 : Entails.eval a c11177 := derived11177 a h
  have h12 : Entails.eval a c3913 := h 3912 (by decide)
  have h13 : Entails.eval a c4016 := h 4015 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11234 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11234 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11221, some c11215, some c11233, some c10707, some c3934, some c4508, some c4409, some c3902, some c10701, some c10700, some c3368, some c4966, some c3997, some c3627, some c4055, some c3141, some c3073, some c3709, some c4067, some c4712, some c3905, some c11036, some c1018, some c3903, some c9986, some c362, some c3051, some c4102, some c4230, some c360, some c407, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11234 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked11234 : lratChecker f11234 p11234 = .success := by decide +kernel
theorem unsat11234 : Unsatisfiable (PosFin 65) f11234 := by
  apply lratCheckerSound f11234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11234
  · intro a ha; simp [p11234] at ha; subst a; trivial
  · exact checked11234
theorem derived11234 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11234 := by
  apply localUnsat_implies_entails f11234 [c11018, c11170, c11221, c11215, c11233, c10707, c3934, c4508, c4409, c3902, c10701, c10700, c3368, c4966, c3997, c3627, c4055, c3141, c3073, c3709, c4067, c4712, c3905, c11036, c1018, c3903, c9986, c362, c3051, c4102, c4230, c360, c407] c11234 unsat11234 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11221 := derived11221 a h
  have h3 : Entails.eval a c11215 := derived11215 a h
  have h4 : Entails.eval a c11233 := derived11233 a h
  have h5 : Entails.eval a c10707 := derived10707 a h
  have h6 : Entails.eval a c3934 := h 3933 (by decide)
  have h7 : Entails.eval a c4508 := h 4507 (by decide)
  have h8 : Entails.eval a c4409 := h 4408 (by decide)
  have h9 : Entails.eval a c3902 := h 3901 (by decide)
  have h10 : Entails.eval a c10701 := derived10701 a h
  have h11 : Entails.eval a c10700 := derived10700 a h
  have h12 : Entails.eval a c3368 := h 3367 (by decide)
  have h13 : Entails.eval a c4966 := h 4965 (by decide)
  have h14 : Entails.eval a c3997 := h 3996 (by decide)
  have h15 : Entails.eval a c3627 := h 3626 (by decide)
  have h16 : Entails.eval a c4055 := h 4054 (by decide)
  have h17 : Entails.eval a c3141 := h 3140 (by decide)
  have h18 : Entails.eval a c3073 := h 3072 (by decide)
  have h19 : Entails.eval a c3709 := h 3708 (by decide)
  have h20 : Entails.eval a c4067 := h 4066 (by decide)
  have h21 : Entails.eval a c4712 := h 4711 (by decide)
  have h22 : Entails.eval a c3905 := h 3904 (by decide)
  have h23 : Entails.eval a c11036 := derived11036 a h
  have h24 : Entails.eval a c1018 := h 1017 (by decide)
  have h25 : Entails.eval a c3903 := h 3902 (by decide)
  have h26 : Entails.eval a c9986 := derived9986 a h
  have h27 : Entails.eval a c362 := h 361 (by decide)
  have h28 : Entails.eval a c3051 := h 3050 (by decide)
  have h29 : Entails.eval a c4102 := h 4101 (by decide)
  have h30 : Entails.eval a c4230 := h 4229 (by decide)
  have h31 : Entails.eval a c360 := h 359 (by decide)
  have h32 : Entails.eval a c407 := h 406 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11235 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11235 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11221, some c11215, some c10699, some c3896, some c3917, some c4407, some c4504, some c10697, some c11195, some c3903, some c3901, some c3913, some c3367, some c3908, some c3925, some c3074, some c3061, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11235 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked11235 : lratChecker f11235 p11235 = .success := by decide +kernel
theorem unsat11235 : Unsatisfiable (PosFin 65) f11235 := by
  apply lratCheckerSound f11235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11235
  · intro a ha; simp [p11235] at ha; subst a; trivial
  · exact checked11235
theorem derived11235 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11235 := by
  apply localUnsat_implies_entails f11235 [c11170, c11221, c11215, c10699, c3896, c3917, c4407, c4504, c10697, c11195, c3903, c3901, c3913, c3367, c3908, c3925, c3074, c3061] c11235 unsat11235 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11221 := derived11221 a h
  have h2 : Entails.eval a c11215 := derived11215 a h
  have h3 : Entails.eval a c10699 := derived10699 a h
  have h4 : Entails.eval a c3896 := h 3895 (by decide)
  have h5 : Entails.eval a c3917 := h 3916 (by decide)
  have h6 : Entails.eval a c4407 := h 4406 (by decide)
  have h7 : Entails.eval a c4504 := h 4503 (by decide)
  have h8 : Entails.eval a c10697 := derived10697 a h
  have h9 : Entails.eval a c11195 := derived11195 a h
  have h10 : Entails.eval a c3903 := h 3902 (by decide)
  have h11 : Entails.eval a c3901 := h 3900 (by decide)
  have h12 : Entails.eval a c3913 := h 3912 (by decide)
  have h13 : Entails.eval a c3367 := h 3366 (by decide)
  have h14 : Entails.eval a c3908 := h 3907 (by decide)
  have h15 : Entails.eval a c3925 := h 3924 (by decide)
  have h16 : Entails.eval a c3074 := h 3073 (by decide)
  have h17 : Entails.eval a c3061 := h 3060 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11236 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨18, by decide⟩, false), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11236 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11235, some c11221, some c11215, some c3909, some c4508, some c4409, some c3902, some c3916, some c10701, some c10700, some c3368, some c3933, some c3073, some c3996, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11236 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11236 : lratChecker f11236 p11236 = .success := by decide +kernel
theorem unsat11236 : Unsatisfiable (PosFin 65) f11236 := by
  apply lratCheckerSound f11236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11236
  · intro a ha; simp [p11236] at ha; subst a; trivial
  · exact checked11236
theorem derived11236 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11236 := by
  apply localUnsat_implies_entails f11236 [c11170, c11235, c11221, c11215, c3909, c4508, c4409, c3902, c3916, c10701, c10700, c3368, c3933, c3073, c3996] c11236 unsat11236 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11235 := derived11235 a h
  have h2 : Entails.eval a c11221 := derived11221 a h
  have h3 : Entails.eval a c11215 := derived11215 a h
  have h4 : Entails.eval a c3909 := h 3908 (by decide)
  have h5 : Entails.eval a c4508 := h 4507 (by decide)
  have h6 : Entails.eval a c4409 := h 4408 (by decide)
  have h7 : Entails.eval a c3902 := h 3901 (by decide)
  have h8 : Entails.eval a c3916 := h 3915 (by decide)
  have h9 : Entails.eval a c10701 := derived10701 a h
  have h10 : Entails.eval a c10700 := derived10700 a h
  have h11 : Entails.eval a c3368 := h 3367 (by decide)
  have h12 : Entails.eval a c3933 := h 3932 (by decide)
  have h13 : Entails.eval a c3073 := h 3072 (by decide)
  have h14 : Entails.eval a c3996 := h 3995 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11237 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨18, by decide⟩, false), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11237 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11235, some c11221, some c11195, some c11236, some c3925, some c3921, some c3920, some c11222, some c3916, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11237 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11237 : lratChecker f11237 p11237 = .success := by decide +kernel
theorem unsat11237 : Unsatisfiable (PosFin 65) f11237 := by
  apply lratCheckerSound f11237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11237
  · intro a ha; simp [p11237] at ha; subst a; trivial
  · exact checked11237
theorem derived11237 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11237 := by
  apply localUnsat_implies_entails f11237 [c11170, c11235, c11221, c11195, c11236, c3925, c3921, c3920, c11222, c3916] c11237 unsat11237 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11235 := derived11235 a h
  have h2 : Entails.eval a c11221 := derived11221 a h
  have h3 : Entails.eval a c11195 := derived11195 a h
  have h4 : Entails.eval a c11236 := derived11236 a h
  have h5 : Entails.eval a c3925 := h 3924 (by decide)
  have h6 : Entails.eval a c3921 := h 3920 (by decide)
  have h7 : Entails.eval a c3920 := h 3919 (by decide)
  have h8 : Entails.eval a c11222 := derived11222 a h
  have h9 : Entails.eval a c3916 := h 3915 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11238 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11238 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11221, some c11215, some c11235, some c11237, some c10707, some c11175, some c10417, some c10610, some c10494, some c10630, some c11205, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11238 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11238 : lratChecker f11238 p11238 = .success := by decide +kernel
theorem unsat11238 : Unsatisfiable (PosFin 65) f11238 := by
  apply lratCheckerSound f11238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11238
  · intro a ha; simp [p11238] at ha; subst a; trivial
  · exact checked11238
theorem derived11238 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11238 := by
  apply localUnsat_implies_entails f11238 [c11221, c11215, c11235, c11237, c10707, c11175, c10417, c10610, c10494, c10630, c11205] c11238 unsat11238 (by rfl) a
  have h0 : Entails.eval a c11221 := derived11221 a h
  have h1 : Entails.eval a c11215 := derived11215 a h
  have h2 : Entails.eval a c11235 := derived11235 a h
  have h3 : Entails.eval a c11237 := derived11237 a h
  have h4 : Entails.eval a c10707 := derived10707 a h
  have h5 : Entails.eval a c11175 := derived11175 a h
  have h6 : Entails.eval a c10417 := derived10417 a h
  have h7 : Entails.eval a c10610 := derived10610 a h
  have h8 : Entails.eval a c10494 := derived10494 a h
  have h9 : Entails.eval a c10630 := derived10630 a h
  have h10 : Entails.eval a c11205 := derived11205 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11239 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨13, by decide⟩, true), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11239 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11238, some c11234, some c11221, some c324, some c322, some c321, some c10311, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11239 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11239 : lratChecker f11239 p11239 = .success := by decide +kernel
theorem unsat11239 : Unsatisfiable (PosFin 65) f11239 := by
  apply lratCheckerSound f11239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11239
  · intro a ha; simp [p11239] at ha; subst a; trivial
  · exact checked11239
theorem derived11239 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11239 := by
  apply localUnsat_implies_entails f11239 [c11018, c11170, c11238, c11234, c11221, c324, c322, c321, c10311] c11239 unsat11239 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11238 := derived11238 a h
  have h3 : Entails.eval a c11234 := derived11234 a h
  have h4 : Entails.eval a c11221 := derived11221 a h
  have h5 : Entails.eval a c324 := h 323 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c321 := h 320 (by decide)
  have h8 : Entails.eval a c10311 := derived10311 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11240 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11240 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10772, some c10424, some c5756, some c5755, some c1024, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p11240 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11240 : lratChecker f11240 p11240 = .success := by decide +kernel
theorem unsat11240 : Unsatisfiable (PosFin 65) f11240 := by
  apply lratCheckerSound f11240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11240
  · intro a ha; simp [p11240] at ha; subst a; trivial
  · exact checked11240
theorem derived11240 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11240 := by
  apply localUnsat_implies_entails f11240 [c11018, c10772, c10424, c5756, c5755, c1024] c11240 unsat11240 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10772 := derived10772 a h
  have h2 : Entails.eval a c10424 := derived10424 a h
  have h3 : Entails.eval a c5756 := h 5755 (by decide)
  have h4 : Entails.eval a c5755 := h 5754 (by decide)
  have h5 : Entails.eval a c1024 := h 1023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11241 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11241 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11238, some c11234, some c11221, some c11215, some c10439, some c10707, some c10417, some c11239, some c11240, some c3856, some c10664, some c4064, some c4851, some c2640, some c4325, some c2701, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11241 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11241 : lratChecker f11241 p11241 = .success := by decide +kernel
theorem unsat11241 : Unsatisfiable (PosFin 65) f11241 := by
  apply lratCheckerSound f11241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11241
  · intro a ha; simp [p11241] at ha; subst a; trivial
  · exact checked11241
theorem derived11241 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11241 := by
  apply localUnsat_implies_entails f11241 [c11170, c11238, c11234, c11221, c11215, c10439, c10707, c10417, c11239, c11240, c3856, c10664, c4064, c4851, c2640, c4325, c2701] c11241 unsat11241 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11238 := derived11238 a h
  have h2 : Entails.eval a c11234 := derived11234 a h
  have h3 : Entails.eval a c11221 := derived11221 a h
  have h4 : Entails.eval a c11215 := derived11215 a h
  have h5 : Entails.eval a c10439 := derived10439 a h
  have h6 : Entails.eval a c10707 := derived10707 a h
  have h7 : Entails.eval a c10417 := derived10417 a h
  have h8 : Entails.eval a c11239 := derived11239 a h
  have h9 : Entails.eval a c11240 := derived11240 a h
  have h10 : Entails.eval a c3856 := h 3855 (by decide)
  have h11 : Entails.eval a c10664 := derived10664 a h
  have h12 : Entails.eval a c4064 := h 4063 (by decide)
  have h13 : Entails.eval a c4851 := h 4850 (by decide)
  have h14 : Entails.eval a c2640 := h 2639 (by decide)
  have h15 : Entails.eval a c4325 := h 4324 (by decide)
  have h16 : Entails.eval a c2701 := h 2700 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11242 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨17, by decide⟩, true), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨50, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11242 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c5756, some c5755, some c5395, some c3954, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p11242 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11242 : lratChecker f11242 p11242 = .success := by decide +kernel
theorem unsat11242 : Unsatisfiable (PosFin 65) f11242 := by
  apply lratCheckerSound f11242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11242
  · intro a ha; simp [p11242] at ha; subst a; trivial
  · exact checked11242
theorem derived11242 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11242 := by
  apply localUnsat_implies_entails f11242 [c11018, c11170, c5756, c5755, c5395, c3954] c11242 unsat11242 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c5756 := h 5755 (by decide)
  have h3 : Entails.eval a c5755 := h 5754 (by decide)
  have h4 : Entails.eval a c5395 := h 5394 (by decide)
  have h5 : Entails.eval a c3954 := h 3953 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11243 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11243 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11238, some c11234, some c11221, some c11215, some c11223, some c11241, some c3904, some c3898, some c3922, some c11242, some c324, some c322, some c321, some c3954, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11243 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11243 : lratChecker f11243 p11243 = .success := by decide +kernel
theorem unsat11243 : Unsatisfiable (PosFin 65) f11243 := by
  apply lratCheckerSound f11243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11243
  · intro a ha; simp [p11243] at ha; subst a; trivial
  · exact checked11243
theorem derived11243 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11243 := by
  apply localUnsat_implies_entails f11243 [c11018, c11170, c11238, c11234, c11221, c11215, c11223, c11241, c3904, c3898, c3922, c11242, c324, c322, c321, c3954] c11243 unsat11243 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11238 := derived11238 a h
  have h3 : Entails.eval a c11234 := derived11234 a h
  have h4 : Entails.eval a c11221 := derived11221 a h
  have h5 : Entails.eval a c11215 := derived11215 a h
  have h6 : Entails.eval a c11223 := derived11223 a h
  have h7 : Entails.eval a c11241 := derived11241 a h
  have h8 : Entails.eval a c3904 := h 3903 (by decide)
  have h9 : Entails.eval a c3898 := h 3897 (by decide)
  have h10 : Entails.eval a c3922 := h 3921 (by decide)
  have h11 : Entails.eval a c11242 := derived11242 a h
  have h12 : Entails.eval a c324 := h 323 (by decide)
  have h13 : Entails.eval a c322 := h 321 (by decide)
  have h14 : Entails.eval a c321 := h 320 (by decide)
  have h15 : Entails.eval a c3954 := h 3953 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11244 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11244 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11221, some c11215, some c11238, some c11234, some c11243, some c10699, some c3896, some c3917, some c4504, some c10696, some c5743, some c5742, some c3901, some c336, some c4038, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11244 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11244 : lratChecker f11244 p11244 = .success := by decide +kernel
theorem unsat11244 : Unsatisfiable (PosFin 65) f11244 := by
  apply lratCheckerSound f11244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11244
  · intro a ha; simp [p11244] at ha; subst a; trivial
  · exact checked11244
theorem derived11244 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11244 := by
  apply localUnsat_implies_entails f11244 [c11018, c11170, c11221, c11215, c11238, c11234, c11243, c10699, c3896, c3917, c4504, c10696, c5743, c5742, c3901, c336, c4038] c11244 unsat11244 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11221 := derived11221 a h
  have h3 : Entails.eval a c11215 := derived11215 a h
  have h4 : Entails.eval a c11238 := derived11238 a h
  have h5 : Entails.eval a c11234 := derived11234 a h
  have h6 : Entails.eval a c11243 := derived11243 a h
  have h7 : Entails.eval a c10699 := derived10699 a h
  have h8 : Entails.eval a c3896 := h 3895 (by decide)
  have h9 : Entails.eval a c3917 := h 3916 (by decide)
  have h10 : Entails.eval a c4504 := h 4503 (by decide)
  have h11 : Entails.eval a c10696 := derived10696 a h
  have h12 : Entails.eval a c5743 := h 5742 (by decide)
  have h13 : Entails.eval a c5742 := h 5741 (by decide)
  have h14 : Entails.eval a c3901 := h 3900 (by decide)
  have h15 : Entails.eval a c336 := h 335 (by decide)
  have h16 : Entails.eval a c4038 := h 4037 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11245 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11245 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11244, some c11221, some c11215, some c3896, some c3917, some c4403, some c3363, some c3903, some c3901, some c11177, some c3913, some c3932, some c3925, some c4507, some c4930, some c4943, some c3997, some c3933, some c10505, some c3626, some c3700, some c3061, some c2611, some c3142, some c3063, some c11036, some c1017, some c4707, some c10154, some c4150, some c398, some c4046, some c10917, some c6078, some c4102, some c406, some c5832, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11245 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]]
theorem checked11245 : lratChecker f11245 p11245 = .success := by decide +kernel
theorem unsat11245 : Unsatisfiable (PosFin 65) f11245 := by
  apply lratCheckerSound f11245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11245
  · intro a ha; simp [p11245] at ha; subst a; trivial
  · exact checked11245
theorem derived11245 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11245 := by
  apply localUnsat_implies_entails f11245 [c11018, c11170, c11244, c11221, c11215, c3896, c3917, c4403, c3363, c3903, c3901, c11177, c3913, c3932, c3925, c4507, c4930, c4943, c3997, c3933, c10505, c3626, c3700, c3061, c2611, c3142, c3063, c11036, c1017, c4707, c10154, c4150, c398, c4046, c10917, c6078, c4102, c406, c5832] c11245 unsat11245 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11244 := derived11244 a h
  have h3 : Entails.eval a c11221 := derived11221 a h
  have h4 : Entails.eval a c11215 := derived11215 a h
  have h5 : Entails.eval a c3896 := h 3895 (by decide)
  have h6 : Entails.eval a c3917 := h 3916 (by decide)
  have h7 : Entails.eval a c4403 := h 4402 (by decide)
  have h8 : Entails.eval a c3363 := h 3362 (by decide)
  have h9 : Entails.eval a c3903 := h 3902 (by decide)
  have h10 : Entails.eval a c3901 := h 3900 (by decide)
  have h11 : Entails.eval a c11177 := derived11177 a h
  have h12 : Entails.eval a c3913 := h 3912 (by decide)
  have h13 : Entails.eval a c3932 := h 3931 (by decide)
  have h14 : Entails.eval a c3925 := h 3924 (by decide)
  have h15 : Entails.eval a c4507 := h 4506 (by decide)
  have h16 : Entails.eval a c4930 := h 4929 (by decide)
  have h17 : Entails.eval a c4943 := h 4942 (by decide)
  have h18 : Entails.eval a c3997 := h 3996 (by decide)
  have h19 : Entails.eval a c3933 := h 3932 (by decide)
  have h20 : Entails.eval a c10505 := derived10505 a h
  have h21 : Entails.eval a c3626 := h 3625 (by decide)
  have h22 : Entails.eval a c3700 := h 3699 (by decide)
  have h23 : Entails.eval a c3061 := h 3060 (by decide)
  have h24 : Entails.eval a c2611 := h 2610 (by decide)
  have h25 : Entails.eval a c3142 := h 3141 (by decide)
  have h26 : Entails.eval a c3063 := h 3062 (by decide)
  have h27 : Entails.eval a c11036 := derived11036 a h
  have h28 : Entails.eval a c1017 := h 1016 (by decide)
  have h29 : Entails.eval a c4707 := h 4706 (by decide)
  have h30 : Entails.eval a c10154 := derived10154 a h
  have h31 : Entails.eval a c4150 := h 4149 (by decide)
  have h32 : Entails.eval a c398 := h 397 (by decide)
  have h33 : Entails.eval a c4046 := h 4045 (by decide)
  have h34 : Entails.eval a c10917 := derived10917 a h
  have h35 : Entails.eval a c6078 := h 6077 (by decide)
  have h36 : Entails.eval a c4102 := h 4101 (by decide)
  have h37 : Entails.eval a c406 := h 405 (by decide)
  have h38 : Entails.eval a c5832 := h 5831 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11246 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨55, by decide⟩, false), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11246 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11018, some c11245, some c11244, some c11215, some c10690, some c10407, some c10437, some c11222, some c10612, some c10498, some c10610, some c10619, some c10615, some c11221, some c11177, some c3444, some c3848, some c3058, some c4649, some c994, some c853, some c3178, some c5330, some c5500, some c5387, some c10762, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11246 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked11246 : lratChecker f11246 p11246 = .success := by decide +kernel
theorem unsat11246 : Unsatisfiable (PosFin 65) f11246 := by
  apply lratCheckerSound f11246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11246
  · intro a ha; simp [p11246] at ha; subst a; trivial
  · exact checked11246
theorem derived11246 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11246 := by
  apply localUnsat_implies_entails f11246 [c11170, c11018, c11245, c11244, c11215, c10690, c10407, c10437, c11222, c10612, c10498, c10610, c10619, c10615, c11221, c11177, c3444, c3848, c3058, c4649, c994, c853, c3178, c5330, c5500, c5387, c10762] c11246 unsat11246 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11018 := derived11018 a h
  have h2 : Entails.eval a c11245 := derived11245 a h
  have h3 : Entails.eval a c11244 := derived11244 a h
  have h4 : Entails.eval a c11215 := derived11215 a h
  have h5 : Entails.eval a c10690 := derived10690 a h
  have h6 : Entails.eval a c10407 := derived10407 a h
  have h7 : Entails.eval a c10437 := derived10437 a h
  have h8 : Entails.eval a c11222 := derived11222 a h
  have h9 : Entails.eval a c10612 := derived10612 a h
  have h10 : Entails.eval a c10498 := derived10498 a h
  have h11 : Entails.eval a c10610 := derived10610 a h
  have h12 : Entails.eval a c10619 := derived10619 a h
  have h13 : Entails.eval a c10615 := derived10615 a h
  have h14 : Entails.eval a c11221 := derived11221 a h
  have h15 : Entails.eval a c11177 := derived11177 a h
  have h16 : Entails.eval a c3444 := h 3443 (by decide)
  have h17 : Entails.eval a c3848 := h 3847 (by decide)
  have h18 : Entails.eval a c3058 := h 3057 (by decide)
  have h19 : Entails.eval a c4649 := h 4648 (by decide)
  have h20 : Entails.eval a c994 := h 993 (by decide)
  have h21 : Entails.eval a c853 := h 852 (by decide)
  have h22 : Entails.eval a c3178 := h 3177 (by decide)
  have h23 : Entails.eval a c5330 := h 5329 (by decide)
  have h24 : Entails.eval a c5500 := h 5499 (by decide)
  have h25 : Entails.eval a c5387 := h 5386 (by decide)
  have h26 : Entails.eval a c10762 := derived10762 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11247 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11247 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11245, some c11244, some c11215, some c10690, some c10407, some c10437, some c11222, some c10612, some c10498, some c10610, some c10619, some c11221, some c11246, some c3442, some c3847, some c4648, some c996, some c3059, some c3179, some c846, some c5296, some c5297, some c5455, some c10760, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11247 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked11247 : lratChecker f11247 p11247 = .success := by decide +kernel
theorem unsat11247 : Unsatisfiable (PosFin 65) f11247 := by
  apply lratCheckerSound f11247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11247
  · intro a ha; simp [p11247] at ha; subst a; trivial
  · exact checked11247
theorem derived11247 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11247 := by
  apply localUnsat_implies_entails f11247 [c11170, c11245, c11244, c11215, c10690, c10407, c10437, c11222, c10612, c10498, c10610, c10619, c11221, c11246, c3442, c3847, c4648, c996, c3059, c3179, c846, c5296, c5297, c5455, c10760] c11247 unsat11247 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11245 := derived11245 a h
  have h2 : Entails.eval a c11244 := derived11244 a h
  have h3 : Entails.eval a c11215 := derived11215 a h
  have h4 : Entails.eval a c10690 := derived10690 a h
  have h5 : Entails.eval a c10407 := derived10407 a h
  have h6 : Entails.eval a c10437 := derived10437 a h
  have h7 : Entails.eval a c11222 := derived11222 a h
  have h8 : Entails.eval a c10612 := derived10612 a h
  have h9 : Entails.eval a c10498 := derived10498 a h
  have h10 : Entails.eval a c10610 := derived10610 a h
  have h11 : Entails.eval a c10619 := derived10619 a h
  have h12 : Entails.eval a c11221 := derived11221 a h
  have h13 : Entails.eval a c11246 := derived11246 a h
  have h14 : Entails.eval a c3442 := h 3441 (by decide)
  have h15 : Entails.eval a c3847 := h 3846 (by decide)
  have h16 : Entails.eval a c4648 := h 4647 (by decide)
  have h17 : Entails.eval a c996 := h 995 (by decide)
  have h18 : Entails.eval a c3059 := h 3058 (by decide)
  have h19 : Entails.eval a c3179 := h 3178 (by decide)
  have h20 : Entails.eval a c846 := h 845 (by decide)
  have h21 : Entails.eval a c5296 := h 5295 (by decide)
  have h22 : Entails.eval a c5297 := h 5296 (by decide)
  have h23 : Entails.eval a c5455 := h 5454 (by decide)
  have h24 : Entails.eval a c10760 := derived10760 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11248 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11248 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11247, some c11245, some c11244, some c11215, some c10690, some c10407, some c10437, some c11222, some c10612, some c10498, some c10610, some c10619, some c5310, some c5312, some c10565, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11248 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11248 : lratChecker f11248 p11248 = .success := by decide +kernel
theorem unsat11248 : Unsatisfiable (PosFin 65) f11248 := by
  apply lratCheckerSound f11248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11248
  · intro a ha; simp [p11248] at ha; subst a; trivial
  · exact checked11248
theorem derived11248 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11248 := by
  apply localUnsat_implies_entails f11248 [c11018, c11247, c11245, c11244, c11215, c10690, c10407, c10437, c11222, c10612, c10498, c10610, c10619, c5310, c5312, c10565] c11248 unsat11248 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11247 := derived11247 a h
  have h2 : Entails.eval a c11245 := derived11245 a h
  have h3 : Entails.eval a c11244 := derived11244 a h
  have h4 : Entails.eval a c11215 := derived11215 a h
  have h5 : Entails.eval a c10690 := derived10690 a h
  have h6 : Entails.eval a c10407 := derived10407 a h
  have h7 : Entails.eval a c10437 := derived10437 a h
  have h8 : Entails.eval a c11222 := derived11222 a h
  have h9 : Entails.eval a c10612 := derived10612 a h
  have h10 : Entails.eval a c10498 := derived10498 a h
  have h11 : Entails.eval a c10610 := derived10610 a h
  have h12 : Entails.eval a c10619 := derived10619 a h
  have h13 : Entails.eval a c5310 := h 5309 (by decide)
  have h14 : Entails.eval a c5312 := h 5311 (by decide)
  have h15 : Entails.eval a c10565 := derived10565 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11249 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11249 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11244, some c11215, some c11245, some c10690, some c10437, some c10407, some c11222, some c10612, some c10498, some c10610, some c10619, some c11247, some c11248, some c5440, some c5443, some c10565, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11249 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11249 : lratChecker f11249 p11249 = .success := by decide +kernel
theorem unsat11249 : Unsatisfiable (PosFin 65) f11249 := by
  apply lratCheckerSound f11249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11249
  · intro a ha; simp [p11249] at ha; subst a; trivial
  · exact checked11249
theorem derived11249 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11249 := by
  apply localUnsat_implies_entails f11249 [c11018, c11244, c11215, c11245, c10690, c10437, c10407, c11222, c10612, c10498, c10610, c10619, c11247, c11248, c5440, c5443, c10565] c11249 unsat11249 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11244 := derived11244 a h
  have h2 : Entails.eval a c11215 := derived11215 a h
  have h3 : Entails.eval a c11245 := derived11245 a h
  have h4 : Entails.eval a c10690 := derived10690 a h
  have h5 : Entails.eval a c10437 := derived10437 a h
  have h6 : Entails.eval a c10407 := derived10407 a h
  have h7 : Entails.eval a c11222 := derived11222 a h
  have h8 : Entails.eval a c10612 := derived10612 a h
  have h9 : Entails.eval a c10498 := derived10498 a h
  have h10 : Entails.eval a c10610 := derived10610 a h
  have h11 : Entails.eval a c10619 := derived10619 a h
  have h12 : Entails.eval a c11247 := derived11247 a h
  have h13 : Entails.eval a c11248 := derived11248 a h
  have h14 : Entails.eval a c5440 := h 5439 (by decide)
  have h15 : Entails.eval a c5443 := h 5442 (by decide)
  have h16 : Entails.eval a c10565 := derived10565 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11250 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨18, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11250 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11249, some c11244, some c11221, some c10430, some c10385, some c10610, some c10498, some c10630, some c11205, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11250 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11250 : lratChecker f11250 p11250 = .success := by decide +kernel
theorem unsat11250 : Unsatisfiable (PosFin 65) f11250 := by
  apply lratCheckerSound f11250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11250
  · intro a ha; simp [p11250] at ha; subst a; trivial
  · exact checked11250
theorem derived11250 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11250 := by
  apply localUnsat_implies_entails f11250 [c11249, c11244, c11221, c10430, c10385, c10610, c10498, c10630, c11205] c11250 unsat11250 (by rfl) a
  have h0 : Entails.eval a c11249 := derived11249 a h
  have h1 : Entails.eval a c11244 := derived11244 a h
  have h2 : Entails.eval a c11221 := derived11221 a h
  have h3 : Entails.eval a c10430 := derived10430 a h
  have h4 : Entails.eval a c10385 := derived10385 a h
  have h5 : Entails.eval a c10610 := derived10610 a h
  have h6 : Entails.eval a c10498 := derived10498 a h
  have h7 : Entails.eval a c10630 := derived10630 a h
  have h8 : Entails.eval a c11205 := derived11205 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived11250

end CochromaticTwenty.Certificates.FixedCore0
