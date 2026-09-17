import MerLeanExperiment.Certificates.Z12Direct_5_8_4.Steps0100_0199

/-! Generated from the actual pinned z12direct_5_8_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c731 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c721, some c716, some c709, some c729, some c730, some c720, some c726, some c727, some c19, some c160, some c63, some c511, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p731 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 31) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c667, c721, c716, c709, c729, c730, c720, c726, c727, c19, c160, c63, c511] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c721 := derived721 a h
  have h2 : Entails.eval a c716 := derived716 a h
  have h3 : Entails.eval a c709 := derived709 a h
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c730 := derived730 a h
  have h6 : Entails.eval a c720 := derived720 a h
  have h7 : Entails.eval a c726 := derived726 a h
  have h8 : Entails.eval a c727 := derived727 a h
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c511 := h 510 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c721, some c716, some c709, some c19, some c511, some c63, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p732 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 31) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c667, c721, c716, c709, c19, c511, c63] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c721 := derived721 a h
  have h2 : Entails.eval a c716 := derived716 a h
  have h3 : Entails.eval a c709 := derived709 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c511 := h 510 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c716, some c442, some c726, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p733 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 31) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c716, c442, c726] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c716 := derived716 a h
  have h1 : Entails.eval a c442 := h 441 (by decide)
  have h2 : Entails.eval a c726 := derived726 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c731, some c716, some c733, some c183, some c19, some c732, some c160, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p734 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 31) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c667, c731, c716, c733, c183, c19, c732, c160] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c716 := derived716 a h
  have h3 : Entails.eval a c733 := derived733 a h
  have h4 : Entails.eval a c183 := h 182 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c732 := derived732 a h
  have h7 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c731, some c721, some c716, some c19, some c51, some c71, some c63, some c277, some c285, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p735 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 31) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c667, c731, c721, c716, c19, c51, c71, c63, c277, c285] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c721 := derived721 a h
  have h3 : Entails.eval a c716 := derived716 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c277 := h 276 (by decide)
  have h9 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c731, some c721, some c716, some c734, some c735, some c183, some c17, some c443, some c726, some c71, some c62, some c454, some c283, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p736 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 31) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c667, c731, c721, c716, c734, c735, c183, c17, c443, c726, c71, c62, c454, c283] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c721 := derived721 a h
  have h3 : Entails.eval a c716 := derived716 a h
  have h4 : Entails.eval a c734 := derived734 a h
  have h5 : Entails.eval a c735 := derived735 a h
  have h6 : Entails.eval a c183 := h 182 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c443 := h 442 (by decide)
  have h9 : Entails.eval a c726 := derived726 a h
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c454 := h 453 (by decide)
  have h13 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c721, some c716, some c709, some c731, some c736, some c20, some c78, some c730, some c123, some c132, some c135, some c629, some c549, some c137, some c68, some c383, some c82, some c329, some c493, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p737 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 31) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c667, c721, c716, c709, c731, c736, c20, c78, c730, c123, c132, c135, c629, c549, c137, c68, c383, c82, c329, c493] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c721 := derived721 a h
  have h2 : Entails.eval a c716 := derived716 a h
  have h3 : Entails.eval a c709 := derived709 a h
  have h4 : Entails.eval a c731 := derived731 a h
  have h5 : Entails.eval a c736 := derived736 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c730 := derived730 a h
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c132 := h 131 (by decide)
  have h11 : Entails.eval a c135 := h 134 (by decide)
  have h12 : Entails.eval a c629 := derived629 a h
  have h13 : Entails.eval a c549 := derived549 a h
  have h14 : Entails.eval a c137 := h 136 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c383 := h 382 (by decide)
  have h17 : Entails.eval a c82 := h 81 (by decide)
  have h18 : Entails.eval a c329 := h 328 (by decide)
  have h19 : Entails.eval a c493 := h 492 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨16, by decide⟩, false), (⟨28, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c716, some c20, some c721, some c709, some c23, some c7, some c191, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p738 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 31) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c667, c716, c20, c721, c709, c23, c7, c191] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c716 := derived716 a h
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c721 := derived721 a h
  have h4 : Entails.eval a c709 := derived709 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨28, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c721, some c78, some c123, some c716, some c709, some c738, some c19, some c197, some c376, some c98, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p739 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 31) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c667, c721, c78, c123, c716, c709, c738, c19, c197, c376, c98] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c721 := derived721 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c716 := derived716 a h
  have h5 : Entails.eval a c709 := derived709 a h
  have h6 : Entails.eval a c738 := derived738 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c739, some c721, some c78, some c123, some c716, some c20, some c737, some c709, some c75, some c17, some c23, some c186, some c376, some c27, some c227, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p740 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 31) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c667, c739, c721, c78, c123, c716, c20, c737, c709, c75, c17, c23, c186, c376, c27, c227] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c739 := derived739 a h
  have h2 : Entails.eval a c721 := derived721 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c716 := derived716 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c737 := derived737 a h
  have h8 : Entails.eval a c709 := derived709 a h
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c186 := h 185 (by decide)
  have h13 : Entails.eval a c376 := h 375 (by decide)
  have h14 : Entails.eval a c27 := h 26 (by decide)
  have h15 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c737, some c721, some c716, some c709, some c20, some c78, some c123, some c739, some c740, some c19, some c23, some c17, some c191, some c445, some c283, some c192, some c525, some c322, some c348, some c507, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p741 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 31) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c667, c737, c721, c716, c709, c20, c78, c123, c739, c740, c19, c23, c17, c191, c445, c283, c192, c525, c322, c348, c507] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c737 := derived737 a h
  have h2 : Entails.eval a c721 := derived721 a h
  have h3 : Entails.eval a c716 := derived716 a h
  have h4 : Entails.eval a c709 := derived709 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c739 := derived739 a h
  have h9 : Entails.eval a c740 := derived740 a h
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c445 := h 444 (by decide)
  have h15 : Entails.eval a c283 := h 282 (by decide)
  have h16 : Entails.eval a c192 := h 191 (by decide)
  have h17 : Entails.eval a c525 := h 524 (by decide)
  have h18 : Entails.eval a c322 := h 321 (by decide)
  have h19 : Entails.eval a c348 := h 347 (by decide)
  have h20 : Entails.eval a c507 := h 506 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c737, some c721, some c716, some c709, some c271, some c23, some c17, some c445, some c192, some c439, some c25, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p742 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 31) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c667, c737, c721, c716, c709, c271, c23, c17, c445, c192, c439, c25] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c737 := derived737 a h
  have h2 : Entails.eval a c721 := derived721 a h
  have h3 : Entails.eval a c716 := derived716 a h
  have h4 : Entails.eval a c709 := derived709 a h
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c445 := h 444 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c439 := h 438 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c737, some c211, some c210, some c244, some c41, some c243, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p743 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 31) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c737, c211, c210, c244, c41, c243] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c737 := derived737 a h
  have h1 : Entails.eval a c211 := h 210 (by decide)
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c244 := h 243 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c737, some c716, some c709, some c743, some c742, some c19, some c355, some c75, some c348, some c408, some c387, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p744 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 31) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c667, c737, c716, c709, c743, c742, c19, c355, c75, c348, c408, c387] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c737 := derived737 a h
  have h2 : Entails.eval a c716 := derived716 a h
  have h3 : Entails.eval a c709 := derived709 a h
  have h4 : Entails.eval a c743 := derived743 a h
  have h5 : Entails.eval a c742 := derived742 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c348 := h 347 (by decide)
  have h10 : Entails.eval a c408 := h 407 (by decide)
  have h11 : Entails.eval a c387 := h 386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c744, some c741, some c737, some c721, some c716, some c709, some c19, some c51, some c71, some c106, some c17, some c353, some c160, some c511, some c73, some c84, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p745 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 31) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c667, c744, c741, c737, c721, c716, c709, c19, c51, c71, c106, c17, c353, c160, c511, c73, c84] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c744 := derived744 a h
  have h2 : Entails.eval a c741 := derived741 a h
  have h3 : Entails.eval a c737 := derived737 a h
  have h4 : Entails.eval a c721 := derived721 a h
  have h5 : Entails.eval a c716 := derived716 a h
  have h6 : Entails.eval a c709 := derived709 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c160 := h 159 (by decide)
  have h14 : Entails.eval a c511 := h 510 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c709, some c716, some c721, some c737, some c741, some c744, some c745, some c183, some c17, some c71, some c50, some c161, some c100, some c74, some c443, some c84, some c509, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p746 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 31) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c667, c709, c716, c721, c737, c741, c744, c745, c183, c17, c71, c50, c161, c100, c74, c443, c84, c509] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c709 := derived709 a h
  have h2 : Entails.eval a c716 := derived716 a h
  have h3 : Entails.eval a c721 := derived721 a h
  have h4 : Entails.eval a c737 := derived737 a h
  have h5 : Entails.eval a c741 := derived741 a h
  have h6 : Entails.eval a c744 := derived744 a h
  have h7 : Entails.eval a c745 := derived745 a h
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c161 := h 160 (by decide)
  have h13 : Entails.eval a c100 := h 99 (by decide)
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c443 := h 442 (by decide)
  have h16 : Entails.eval a c84 := h 83 (by decide)
  have h17 : Entails.eval a c509 := h 508 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨2, by decide⟩, true), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c176, some c467, some c402, some c7, some c266, some c369, some c264, some c40, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p747 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 31) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c667, c176, c467, c402, c7, c266, c369, c264, c40] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c467 := h 466 (by decide)
  have h3 : Entails.eval a c402 := h 401 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c99, some c470, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p748 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 31) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c667, c746, c99, c470] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c470 := h 469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c176, some c748, some c467, some c747, some c23, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p749 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 31) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c667, c176, c748, c467, c747, c23] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c748 := derived748 a h
  have h3 : Entails.eval a c467 := h 466 (by decide)
  have h4 : Entails.eval a c747 := derived747 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c176, some c100, some c56, some c241, some c345, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p750 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 31) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c667, c176, c100, c56, c241, c345] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c327, some c20, some c183, some c443, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p751 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 31) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c667, c327, c20, c183, c443] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c183 := h 182 (by decide)
  have h4 : Entails.eval a c443 := h 442 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c17, some c57, some c10, some c11, some c67, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p752 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 31) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c667, c746, c17, c57, c10, c11, c67] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c183, some c23, some c20, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p753 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 31) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c667, c183, c23, c20] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c753, some c17, some c752, some c69, some c750, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p754 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 31) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c667, c753, c17, c752, c69, c750] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c752 := derived752 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c750 := derived750 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c71, some c162, some c20, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p755 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 31) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c667, c71, c162, c20] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c753, some c17, some c754, some c755, some c750, some c751, some c749, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p756 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 31) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c667, c753, c17, c754, c755, c750, c751, c749] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c754 := derived754 a h
  have h4 : Entails.eval a c755 := derived755 a h
  have h5 : Entails.eval a c750 := derived750 a h
  have h6 : Entails.eval a c751 := derived751 a h
  have h7 : Entails.eval a c749 := derived749 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c78, some c44, some c161, some c169, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p757 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 31) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c667, c78, c44, c161, c169] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c161 := h 160 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c711, some c10, some c66, some c757, some c246, some c312, some c169, some c105, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p758 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 31) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c667, c746, c711, c10, c66, c757, c246, c312, c169, c105] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c711 := derived711 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c757 := derived757 a h
  have h6 : Entails.eval a c246 := h 245 (by decide)
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c756, some c711, some c758, some c183, some c23, some c21, some c78, some c15, some c246, some c172, some c452, some c420, some c35, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p759 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 31) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c667, c756, c711, c758, c183, c23, c21, c78, c15, c246, c172, c452, c420, c35] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c756 := derived756 a h
  have h2 : Entails.eval a c711 := derived711 a h
  have h3 : Entails.eval a c758 := derived758 a h
  have h4 : Entails.eval a c183 := h 182 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  have h11 : Entails.eval a c452 := h 451 (by decide)
  have h12 : Entails.eval a c420 := h 419 (by decide)
  have h13 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨19, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c23, some c21, some c9, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p760 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 31) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c23, c21, c9] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨1, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c759, some c760, some c178, some c169, some c106, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p761 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 31) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c667, c759, c760, c178, c169, c106] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c759 := derived759 a h
  have h2 : Entails.eval a c760 := derived760 a h
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨26, by decide⟩, false), (⟨4, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c9, some c257, some c225, some c216, some c78, some c324, some c181, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p762 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 31) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c667, c9, c257, c225, c216, c78, c324, c181] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c257 := h 256 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c759, some c760, some c756, some c9, some c761, some c762, some c246, some c228, some c254, some c258, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p763 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 31) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c746, c759, c760, c756, c9, c761, c762, c246, c228, c254, c258] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c759 := derived759 a h
  have h2 : Entails.eval a c760 := derived760 a h
  have h3 : Entails.eval a c756 := derived756 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c761 := derived761 a h
  have h6 : Entails.eval a c762 := derived762 a h
  have h7 : Entails.eval a c246 := h 245 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c254 := h 253 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c763, some c759, some c756, some c761, some c192, some c162, some c266, some c100, some c248, some c229, some c246, some c180, some c305, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p764 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 31) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c667, c746, c763, c759, c756, c761, c192, c162, c266, c100, c248, c229, c246, c180, c305] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c759 := derived759 a h
  have h4 : Entails.eval a c756 := derived756 a h
  have h5 : Entails.eval a c761 := derived761 a h
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c229 := h 228 (by decide)
  have h12 : Entails.eval a c246 := h 245 (by decide)
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c764, some c763, some c759, some c192, some c162, some c266, some c100, some c248, some c374, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p765 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 31) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c667, c764, c763, c759, c192, c162, c266, c100, c248, c374] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c764 := derived764 a h
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c759 := derived759 a h
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c248 := h 247 (by decide)
  have h9 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c667, some c756, some c759, some c760, some c763, some c7, some c765, some c16, some c106, some c359, some c246, some c228, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p766 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 31) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c746, c667, c756, c759, c760, c763, c7, c765, c16, c106, c359, c246, c228] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c756 := derived756 a h
  have h3 : Entails.eval a c759 := derived759 a h
  have h4 : Entails.eval a c760 := derived760 a h
  have h5 : Entails.eval a c763 := derived763 a h
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c765 := derived765 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c246 := h 245 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c17, some c678, some c10, some c288, some c207, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p767 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 31) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c667, c746, c17, c678, c10, c288, c207] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c678 := derived678 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c288 := h 287 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c667, some c766, some c23, some c7, some c767, some c192, some c162, some c266, some c697, some c248, some c10, some c530, some c37, some c678, some c364, some c214, some c308, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p768 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 31) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c746, c667, c766, c23, c7, c767, c192, c162, c266, c697, c248, c10, c530, c37, c678, c364, c214, c308] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c766 := derived766 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c767 := derived767 a h
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c697 := derived697 a h
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c530 := h 529 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c678 := derived678 a h
  have h15 : Entails.eval a c364 := h 363 (by decide)
  have h16 : Entails.eval a c214 := h 213 (by decide)
  have h17 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c176, some c753, some c755, some c686, some c313, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p769 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 31) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c667, c176, c753, c755, c686, c313] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c755 := derived755 a h
  have h4 : Entails.eval a c686 := derived686 a h
  have h5 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, true), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c766, some c697, some c62, some c105, some c69, some c379, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p770 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 31) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c746, c766, c697, c62, c105, c69, c379] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c697 := derived697 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c771 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c768, some c766, some c769, some c678, some c770, some c10, some c183, some c226, some c21, some c78, some c172, some c548, some c472, some c418, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p771 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 31) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c667, c746, c768, c766, c769, c678, c770, c10, c183, c226, c21, c78, c172, c548, c472, c418] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c768 := derived768 a h
  have h3 : Entails.eval a c766 := derived766 a h
  have h4 : Entails.eval a c769 := derived769 a h
  have h5 : Entails.eval a c678 := derived678 a h
  have h6 : Entails.eval a c770 := derived770 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c226 := h 225 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c172 := h 171 (by decide)
  have h13 : Entails.eval a c548 := derived548 a h
  have h14 : Entails.eval a c472 := h 471 (by decide)
  have h15 : Entails.eval a c418 := h 417 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨9, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c667, some c241, some c766, some c207, some c10, some c42, some c183, some c184, some c319, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p772 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 31) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c746, c667, c241, c766, c207, c10, c42, c183, c184, c319] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c241 := h 240 (by decide)
  have h3 : Entails.eval a c766 := derived766 a h
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c183 := h 182 (by decide)
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c678, some c176, some c686, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p773 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 31) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c667, c678, c176, c686] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c678 := derived678 a h
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c686 := derived686 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c772, some c771, some c288, some c169, some c240, some c5, some c183, some c21, some c417, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p774 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 31) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c667, c746, c772, c771, c288, c169, c240, c5, c183, c21, c417] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c772 := derived772 a h
  have h3 : Entails.eval a c771 := derived771 a h
  have h4 : Entails.eval a c288 := h 287 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c240 := h 239 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c417 := h 416 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c766, some c768, some c773, some c774, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p775 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 31) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c766, c768, c773, c774] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c766 := derived766 a h
  have h1 : Entails.eval a c768 := derived768 a h
  have h2 : Entails.eval a c773 := derived773 a h
  have h3 : Entails.eval a c774 := derived774 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c775, some c766, some c758, some c183, some c226, some c78, some c218, some c246, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p776 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 31) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c667, c746, c775, c766, c758, c183, c226, c78, c218, c246] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c775 := derived775 a h
  have h3 : Entails.eval a c766 := derived766 a h
  have h4 : Entails.eval a c758 := derived758 a h
  have h5 : Entails.eval a c183 := h 182 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c667, some c766, some c776, some c176, some c753, some c10, some c17, some c62, some c78, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p777 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 31) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c746, c667, c766, c776, c176, c753, c10, c17, c62, c78] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c766 := derived766 a h
  have h3 : Entails.eval a c776 := derived776 a h
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c753 := derived753 a h
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c766, some c775, some c777, some c678, some c132, some c67, some c773, some c176, some c753, some c752, some c249, some c11, some c17, some c474, some c525, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p778 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 31) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c667, c766, c775, c777, c678, c132, c67, c773, c176, c753, c752, c249, c11, c17, c474, c525] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c775 := derived775 a h
  have h3 : Entails.eval a c777 := derived777 a h
  have h4 : Entails.eval a c678 := derived678 a h
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c773 := derived773 a h
  have h8 : Entails.eval a c176 := h 175 (by decide)
  have h9 : Entails.eval a c753 := derived753 a h
  have h10 : Entails.eval a c752 := derived752 a h
  have h11 : Entails.eval a c249 := h 248 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c474 := h 473 (by decide)
  have h15 : Entails.eval a c525 := h 524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c778, some c678, some c132, some c773, some c176, some c19, some c249, some c162, some c285, some c17, some c126, some c206, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p779 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 31) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c667, c778, c678, c132, c773, c176, c19, c249, c162, c285, c17, c126, c206] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c778 := derived778 a h
  have h2 : Entails.eval a c678 := derived678 a h
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c773 := derived773 a h
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c162 := h 161 (by decide)
  have h9 : Entails.eval a c285 := h 284 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c126 := h 125 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c780 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c779, some c778, some c176, some c19, some c686, some c186, some c261, some c106, some c248, some c460, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p780 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 31) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c667, c779, c778, c176, c19, c686, c186, c261, c106, c248, c460] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c779 := derived779 a h
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c686 := derived686 a h
  have h6 : Entails.eval a c186 := h 185 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c460 := h 459 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c781 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f781 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c106, some c240, some c56, some c35, some c100, some c321, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p781 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked781 : lratChecker f781 p781 = .success := by decide +kernel
theorem unsat781 : Unsatisfiable (PosFin 31) f781 := by
  apply lratCheckerSound f781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p781
  · intro a ha; simp [p781] at ha; subst a; trivial
  · exact checked781
theorem derived781 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c781 := by
  apply localUnsat_implies_entails f781 [c667, c106, c240, c56, c35, c100, c321] c781 unsat781 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c240 := h 239 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c782 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f782 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c667, some c781, some c246, some c35, some c451, some c240, some c393, some c215, some c248, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p782 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked782 : lratChecker f782 p782 = .success := by decide +kernel
theorem unsat782 : Unsatisfiable (PosFin 31) f782 := by
  apply lratCheckerSound f782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p782
  · intro a ha; simp [p782] at ha; subst a; trivial
  · exact checked782
theorem derived782 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c782 := by
  apply localUnsat_implies_entails f782 [c746, c667, c781, c246, c35, c451, c240, c393, c215, c248] c782 unsat782 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c781 := derived781 a h
  have h3 : Entails.eval a c246 := h 245 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c451 := h 450 (by decide)
  have h6 : Entails.eval a c240 := h 239 (by decide)
  have h7 : Entails.eval a c393 := h 392 (by decide)
  have h8 : Entails.eval a c215 := h 214 (by decide)
  have h9 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c783 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f783 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c779, some c780, some c711, some c782, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p783 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked783 : lratChecker f783 p783 = .success := by decide +kernel
theorem unsat783 : Unsatisfiable (PosFin 31) f783 := by
  apply lratCheckerSound f783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p783
  · intro a ha; simp [p783] at ha; subst a; trivial
  · exact checked783
theorem derived783 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c783 := by
  apply localUnsat_implies_entails f783 [c779, c780, c711, c782] c783 unsat783 (by rfl) a
  have h0 : Entails.eval a c779 := derived779 a h
  have h1 : Entails.eval a c780 := derived780 a h
  have h2 : Entails.eval a c711 := derived711 a h
  have h3 : Entails.eval a c782 := derived782 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c784 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c779, some c783, some c17, some c169, some c16, some c711, some c106, some c87, some c246, some c297, some c431, some c312, some c298, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p784 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 31) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c667, c746, c779, c783, c17, c169, c16, c711, c106, c87, c246, c297, c431, c312, c298] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c779 := derived779 a h
  have h3 : Entails.eval a c783 := derived783 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c711 := derived711 a h
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c246 := h 245 (by decide)
  have h11 : Entails.eval a c297 := h 296 (by decide)
  have h12 : Entails.eval a c431 := h 430 (by decide)
  have h13 : Entails.eval a c312 := h 311 (by decide)
  have h14 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c778, some c228, some c230, some c215, some c248, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p785 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 31) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c746, c778, c228, c230, c215, c248] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c778 := derived778 a h
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c230 := h 229 (by decide)
  have h4 : Entails.eval a c215 := h 214 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c786 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c784, some c779, some c778, some c711, some c785, some c246, some c411, some c100, some c278, some c69, some c71, some c158, some c376, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p786 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 31) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c667, c784, c779, c778, c711, c785, c246, c411, c100, c278, c69, c71, c158, c376] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c784 := derived784 a h
  have h2 : Entails.eval a c779 := derived779 a h
  have h3 : Entails.eval a c778 := derived778 a h
  have h4 : Entails.eval a c711 := derived711 a h
  have h5 : Entails.eval a c785 := derived785 a h
  have h6 : Entails.eval a c246 := h 245 (by decide)
  have h7 : Entails.eval a c411 := h 410 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨26, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c778, some c19, some c755, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p787 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 31) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c667, c778, c19, c755] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c778 := derived778 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c755 := derived755 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c784, some c787, some c711, some c779, some c162, some c71, some c9, some c123, some c182, some c257, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p788 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 31) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c667, c784, c787, c711, c779, c162, c71, c9, c123, c182, c257] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c784 := derived784 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c711 := derived711 a h
  have h4 : Entails.eval a c779 := derived779 a h
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c789 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c778, some c779, some c784, some c787, some c711, some c786, some c788, some c18, some c170, some c100, some c246, some c451, some c230, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p789 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 31) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c667, c746, c778, c779, c784, c787, c711, c786, c788, c18, c170, c100, c246, c451, c230] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c779 := derived779 a h
  have h4 : Entails.eval a c784 := derived784 a h
  have h5 : Entails.eval a c787 := derived787 a h
  have h6 : Entails.eval a c711 := derived711 a h
  have h7 : Entails.eval a c786 := derived786 a h
  have h8 : Entails.eval a c788 := derived788 a h
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c100 := h 99 (by decide)
  have h12 : Entails.eval a c246 := h 245 (by decide)
  have h13 : Entails.eval a c451 := h 450 (by decide)
  have h14 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c789, some c778, some c170, some c287, some c18, some c100, some c246, some c180, some c466, some c218, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p790 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 31) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c667, c746, c789, c778, c170, c287, c18, c100, c246, c180, c466, c218] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c789 := derived789 a h
  have h3 : Entails.eval a c778 := derived778 a h
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c246 := h 245 (by decide)
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c466 := h 465 (by decide)
  have h11 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c789, some c778, some c170, some c287, some c18, some c12, some c66, some c10, some c42, some c495, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p791 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 31) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c667, c746, c789, c778, c170, c287, c18, c12, c66, c10, c42, c495] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c789 := derived789 a h
  have h3 : Entails.eval a c778 := derived778 a h
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c495 := h 494 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c778, some c789, some c12, some c170, some c287, some c791, some c790, some c68, some c206, some c10, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p792 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 31) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c667, c746, c778, c789, c12, c170, c287, c791, c790, c68, c206, c10] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c789 := derived789 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c287 := h 286 (by decide)
  have h7 : Entails.eval a c791 := derived791 a h
  have h8 : Entails.eval a c790 := derived790 a h
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c793 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f793 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c667, some c778, some c789, some c12, some c98, some c162, some c69, some c71, some c61, some c15, some c591, some c407, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p793 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked793 : lratChecker f793 p793 = .success := by decide +kernel
theorem unsat793 : Unsatisfiable (PosFin 31) f793 := by
  apply lratCheckerSound f793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p793
  · intro a ha; simp [p793] at ha; subst a; trivial
  · exact checked793
theorem derived793 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c793 := by
  apply localUnsat_implies_entails f793 [c746, c667, c778, c789, c12, c98, c162, c69, c71, c61, c15, c591, c407] c793 unsat793 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c789 := derived789 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c162 := h 161 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c591 := derived591 a h
  have h12 : Entails.eval a c407 := h 406 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c794 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c778, some c789, some c12, some c792, some c98, some c42, some c315, some c246, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p794 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 31) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c667, c746, c778, c789, c12, c792, c98, c42, c315, c246] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c789 := derived789 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c792 := derived792 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c667, some c778, some c789, some c12, some c792, some c793, some c794, some c66, some c68, some c84, some c782, some c78, some c785, some c246, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p795 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 31) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c746, c667, c778, c789, c12, c792, c793, c794, c66, c68, c84, c782, c78, c785, c246] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c789 := derived789 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c792 := derived792 a h
  have h6 : Entails.eval a c793 := derived793 a h
  have h7 : Entails.eval a c794 := derived794 a h
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c782 := derived782 a h
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c785 := derived785 a h
  have h14 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c667, some c778, some c789, some c12, some c795, some c176, some c19, some c78, some c98, some c73, some c84, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p796 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 31) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c746, c667, c778, c789, c12, c795, c176, c19, c78, c98, c73, c84] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c789 := derived789 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c795 := derived795 a h
  have h6 : Entails.eval a c176 := h 175 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c78, some c71, some c118, some c378, some c318, some c514, some c274, some c288, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p797 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 31) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c667, c746, c78, c71, c118, c378, c318, c514, c274, c288] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c514 := h 513 (by decide)
  have h8 : Entails.eval a c274 := h 273 (by decide)
  have h9 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c19, some c17, some c274, some c23, some c21, some c400, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p798 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 31) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c667, c19, c17, c274, c23, c21, c400] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c400 := h 399 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c78, some c19, some c697, some c798, some c161, some c74, some c119, some c66, some c345, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p799 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 31) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c667, c78, c19, c697, c798, c161, c74, c119, c66, c345] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c697 := derived697 a h
  have h4 : Entails.eval a c798 := derived798 a h
  have h5 : Entails.eval a c161 := h 160 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c78, some c799, some c71, some c118, some c797, some c35, some c217, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p800 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 31) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c667, c746, c78, c799, c71, c118, c797, c35, c217] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c799 := derived799 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c797 := derived797 a h
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c796, some c512, some c75, some c548, some c120, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p801 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 31) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c746, c796, c512, c75, c548, c120] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c512 := h 511 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c548 := derived548 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c746, some c667, some c800, some c175, some c437, some c471, some c801, some c19, some c381, some c187, some c148, some c260, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p802 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 31) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c796, c746, c667, c800, c175, c437, c471, c801, c19, c381, c187, c148, c260] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c667 := derived667 a h
  have h3 : Entails.eval a c800 := derived800 a h
  have h4 : Entails.eval a c175 := h 174 (by decide)
  have h5 : Entails.eval a c437 := h 436 (by decide)
  have h6 : Entails.eval a c471 := h 470 (by decide)
  have h7 : Entails.eval a c801 := derived801 a h
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c381 := h 380 (by decide)
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c148 := h 147 (by decide)
  have h12 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c796, some c10, some c90, some c801, some c92, some c193, some c471, some c260, some c142, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p803 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 31) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c667, c746, c796, c10, c90, c801, c92, c193, c471, c260, c142] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c796 := derived796 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c801 := derived801 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c471 := h 470 (by decide)
  have h9 : Entails.eval a c260 := h 259 (by decide)
  have h10 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c667, some c802, some c10, some c803, some c175, some c78, some c42, some c54, some c160, some c515, some c44, some c798, some c119, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p804 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 31) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c746, c667, c802, c10, c803, c175, c78, c42, c54, c160, c515, c44, c798, c119] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c803 := derived803 a h
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c515 := h 514 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c798 := derived798 a h
  have h13 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨13, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c78, some c54, some c515, some c44, some c119, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p805 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 31) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c667, c746, c78, c54, c515, c44, c119] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c515 := h 514 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c78, some c287, some c42, some c62, some c100, some c66, some c29, some c57, some c575, some c467, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p806 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 31) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c667, c746, c78, c287, c42, c62, c100, c66, c29, c57, c575, c467] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c575 := derived575 a h
  have h11 : Entails.eval a c467 := h 466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c796, some c746, some c78, some c806, some c805, some c381, some c468, some c516, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p807 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 31) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c667, c796, c746, c78, c806, c805, c381, c468, c516] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c746 := derived746 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c806 := derived806 a h
  have h5 : Entails.eval a c805 := derived805 a h
  have h6 : Entails.eval a c381 := h 380 (by decide)
  have h7 : Entails.eval a c468 := h 467 (by decide)
  have h8 : Entails.eval a c516 := h 515 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c746, some c667, some c807, some c381, some c193, some c274, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p808 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 31) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c796, c746, c667, c807, c381, c193, c274] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c667 := derived667 a h
  have h3 : Entails.eval a c807 := derived807 a h
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c796, some c667, some c808, some c807, some c78, some c804, some c274, some c12, some c18, some c167, some c363, some c80, some c336, some c124, some c528, some c500, some c103, some c449, some c35, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p809 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 31) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c746, c796, c667, c808, c807, c78, c804, c274, c12, c18, c167, c363, c80, c336, c124, c528, c500, c103, c449, c35] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c667 := derived667 a h
  have h3 : Entails.eval a c808 := derived808 a h
  have h4 : Entails.eval a c807 := derived807 a h
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c804 := derived804 a h
  have h7 : Entails.eval a c274 := h 273 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c528 := h 527 (by decide)
  have h16 : Entails.eval a c500 := h 499 (by decide)
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c449 := h 448 (by decide)
  have h19 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c78, some c804, some c807, some c808, some c809, some c288, some c515, some c514, some c42, some c290, some c522, some c167, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p810 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 31) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c667, c746, c78, c804, c807, c808, c809, c288, c515, c514, c42, c290, c522, c167] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c804 := derived804 a h
  have h4 : Entails.eval a c807 := derived807 a h
  have h5 : Entails.eval a c808 := derived808 a h
  have h6 : Entails.eval a c809 := derived809 a h
  have h7 : Entails.eval a c288 := h 287 (by decide)
  have h8 : Entails.eval a c515 := h 514 (by decide)
  have h9 : Entails.eval a c514 := h 513 (by decide)
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c522 := h 521 (by decide)
  have h13 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c746, some c78, some c810, some c71, some c54, some c514, some c42, some c118, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p811 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 31) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c667, c746, c78, c810, c71, c54, c514, c42, c118] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c810 := derived810 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c514 := h 513 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c796, some c746, some c78, some c810, some c71, some c44, some c288, some c63, some c274, some c106, some c58, some c30, some c404, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p812 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 31) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c667, c796, c746, c78, c810, c71, c44, c288, c63, c274, c106, c58, c30, c404] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c746 := derived746 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c810 := derived810 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c288 := h 287 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c274 := h 273 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c58 := h 57 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c404 := h 403 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c667, some c78, some c810, some c71, some c812, some c534, some c811, some c41, some c803, some c92, some c66, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p813 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 31) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c796, c667, c78, c810, c71, c812, c534, c811, c41, c803, c92, c66] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c810 := derived810 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c812 := derived812 a h
  have h6 : Entails.eval a c534 := derived534 a h
  have h7 : Entails.eval a c811 := derived811 a h
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c803 := derived803 a h
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c20, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p814 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 31) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c667, c20] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c815 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c24, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p815 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 31) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c796, c24] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c816 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨12, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c35, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p816 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 31) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c667, c35] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c817 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c37, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p817 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 31) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c667, c37] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c818 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨22, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c41, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p818 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 31) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c796, c41] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c819 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c667, some c90, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p819 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 31) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c796, c667, c90] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c91, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p820 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 31) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c796, c91] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c821 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c667, some c92, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p821 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 31) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c796, c667, c92] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c93, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p822 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 31) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c796, c93] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c823 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c113, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p823 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 31) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c796, c113] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c824 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c131, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p824 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 31) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c667, c131] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c825 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c132, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p825 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 31) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c667, c132] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c826 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c173, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p826 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 31) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c746, c173] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c827 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c796, some c174, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p827 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 31) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c746, c796, c174] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨12, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c218, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p828 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 31) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c746, c218] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c829 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c269, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p829 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 31) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c796, c269] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c830 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c289, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p830 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 31) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c746, c289] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived830

end CochromaticTwenty.Certificates.Z12Direct_5_8_4
