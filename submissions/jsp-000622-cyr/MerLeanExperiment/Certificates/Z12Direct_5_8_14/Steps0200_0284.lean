import MerLeanExperiment.Certificates.Z12Direct_5_8_14.Steps0100_0199

/-! Generated from the actual pinned z12direct_5_8_14-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_14
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c731 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, true), (⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c422, some c730, some c111, some c43, some c18, some c173, some c375, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p731 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 31) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c644, c422, c730, c111, c43, c18, c173, c375] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c422 := h 421 (by decide)
  have h2 : Entails.eval a c730 := derived730 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c375 := h 374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, false), (⟨28, by decide⟩, true), (⟨17, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c111, some c43, some c99, some c51, some c699, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p732 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 31) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c111, c43, c99, c51, c699] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c699 := derived699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨24, by decide⟩, true), (⟨25, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c51, some c419, some c197, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p733 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 31) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c51, c419, c197] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c419 := h 418 (by decide)
  have h2 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c729, some c731, some c732, some c82, some c733, some c194, some c479, some c699, some c121, some c98, some c66, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p734 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 31) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c644, c729, c731, c732, c82, c733, c194, c479, c699, c121, c98, c66] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c729 := derived729 a h
  have h2 : Entails.eval a c731 := derived731 a h
  have h3 : Entails.eval a c732 := derived732 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c733 := derived733 a h
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c479 := h 478 (by decide)
  have h8 : Entails.eval a c699 := derived699 a h
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨28, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c413, some c474, some c159, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p735 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 31) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c413, c474, c159] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c413 := h 412 (by decide)
  have h1 : Entails.eval a c474 := h 473 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c728, some c686, some c666, some c734, some c633, some c406, some c699, some c32, some c205, some c735, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p736 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 31) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c728, c686, c666, c734, c633, c406, c699, c32, c205, c735] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c728 := derived728 a h
  have h1 : Entails.eval a c686 := derived686 a h
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c734 := derived734 a h
  have h4 : Entails.eval a c633 := derived633 a h
  have h5 : Entails.eval a c406 := h 405 (by decide)
  have h6 : Entails.eval a c699 := derived699 a h
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c205 := h 204 (by decide)
  have h9 : Entails.eval a c735 := derived735 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨8, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c40, some c176, some c175, some c138, some c322, some c12, some c102, some c635, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p737 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 31) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c644, c40, c176, c175, c138, c322, c12, c102, c635] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c175 := h 174 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c635 := derived635 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c34, some c51, some c699, some c32, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p738 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 31) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c34, c51, c699, c32] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c699 := derived699 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c465, some c466, some c464, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p739 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 31) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c465, c466, c464] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c465 := h 464 (by decide)
  have h1 : Entails.eval a c466 := h 465 (by decide)
  have h2 : Entails.eval a c464 := h 463 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c686, some c666, some c736, some c738, some c205, some c176, some c138, some c465, some c739, some c732, some c737, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p740 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 31) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c686, c666, c736, c738, c205, c176, c138, c465, c739, c732, c737] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c686 := derived686 a h
  have h1 : Entails.eval a c666 := derived666 a h
  have h2 : Entails.eval a c736 := derived736 a h
  have h3 : Entails.eval a c738 := derived738 a h
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c465 := h 464 (by decide)
  have h8 : Entails.eval a c739 := derived739 a h
  have h9 : Entails.eval a c732 := derived732 a h
  have h10 : Entails.eval a c737 := derived737 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c693, some c699, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p741 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 31) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c693, c699] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c693 := derived693 a h
  have h1 : Entails.eval a c699 := derived699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c742 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c694, some c741, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p742 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 31) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c694, c741] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c694 := derived694 a h
  have h1 : Entails.eval a c741 := derived741 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c743 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c740, some c742, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p743 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 31) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c740, c742] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c740 := derived740 a h
  have h1 : Entails.eval a c742 := derived742 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c744 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c728, some c743, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p744 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 31) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c728, c743] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c728 := derived728 a h
  have h1 : Entails.eval a c743 := derived743 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c745 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c742, some c744, some c699, some c28, some c47, some c33, some c690, some c64, some c131, some c149, some c55, some c91, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p745 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 31) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c644, c742, c744, c699, c28, c47, c33, c690, c64, c131, c149, c55, c91] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c742 := derived742 a h
  have h2 : Entails.eval a c744 := derived744 a h
  have h3 : Entails.eval a c699 := derived699 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c690 := derived690 a h
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c660, some c49, some c2, some c633, some c130, some c276, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p746 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 31) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c644, c660, c49, c2, c633, c130, c276] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c660 := derived660 a h
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c633 := derived633 a h
  have h5 : Entails.eval a c130 := h 129 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c744, some c745, some c51, some c746, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p747 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 31) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c744, c745, c51, c746] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c744 := derived744 a h
  have h1 : Entails.eval a c745 := derived745 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c746 := derived746 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c744, some c747, some c45, some c49, some c75, some c107, some c567, some c21, some c13, some c251, some c116, some c348, some c189, some c481, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p748 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 31) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c644, c744, c747, c45, c49, c75, c107, c567, c21, c13, c251, c116, c348, c189, c481] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c744 := derived744 a h
  have h2 : Entails.eval a c747 := derived747 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c567 := derived567 a h
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c348 := h 347 (by decide)
  have h13 : Entails.eval a c189 := h 188 (by decide)
  have h14 : Entails.eval a c481 := h 480 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c744, some c747, some c45, some c748, some c133, some c629, some c330, some c368, some c221, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p749 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 31) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c644, c744, c747, c45, c748, c133, c629, c330, c368, c221] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c744 := derived744 a h
  have h2 : Entails.eval a c747 := derived747 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c748 := derived748 a h
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c629 := derived629 a h
  have h7 : Entails.eval a c330 := h 329 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c744, some c747, some c45, some c749, some c47, some c75, some c49, some c616, some c108, some c79, some c142, some c15, some c304, some c116, some c302, some c188, some c424, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p750 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 31) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c644, c744, c747, c45, c749, c47, c75, c49, c616, c108, c79, c142, c15, c304, c116, c302, c188, c424] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c744 := derived744 a h
  have h2 : Entails.eval a c747 := derived747 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c749 := derived749 a h
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c616 := derived616 a h
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c142 := h 141 (by decide)
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c304 := h 303 (by decide)
  have h14 : Entails.eval a c116 := h 115 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c188 := h 187 (by decide)
  have h17 : Entails.eval a c424 := h 423 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨14, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c750, some c47, some c75, some c108, some c167, some c60, some c24, some c33, some c254, some c7, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p751 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 31) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c644, c750, c47, c75, c108, c167, c60, c24, c33, c254, c7] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c254 := h 253 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c644, some c47, some c45, some c131, some c207, some c335, some c33, some c32, some c7, some c64, some c293, some c451, some c269, some c116, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p752 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 31) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c750, c644, c47, c45, c131, c207, c335, c33, c32, c7, c64, c293, c451, c269, c116] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c335 := h 334 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c451 := h 450 (by decide)
  have h13 : Entails.eval a c269 := h 268 (by decide)
  have h14 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c644, some c47, some c752, some c75, some c108, some c751, some c79, some c142, some c24, some c302, some c435, some c7, some c344, some c255, some c160, some c296, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p753 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 31) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c750, c644, c47, c752, c75, c108, c751, c79, c142, c24, c302, c435, c7, c344, c255, c160, c296] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c752 := derived752 a h
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c751 := derived751 a h
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c142 := h 141 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c302 := h 301 (by decide)
  have h11 : Entails.eval a c435 := h 434 (by decide)
  have h12 : Entails.eval a c7 := h 6 (by decide)
  have h13 : Entails.eval a c344 := h 343 (by decide)
  have h14 : Entails.eval a c255 := h 254 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c750, some c753, some c47, some c75, some c108, some c79, some c142, some c24, some c302, some c7, some c25, some c255, some c152, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p754 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 31) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c644, c750, c753, c47, c75, c108, c79, c142, c24, c302, c7, c25, c255, c152] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c142 := h 141 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c302 := h 301 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c255 := h 254 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c131, some c178, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p755 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 31) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c131, c178] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c131 := h 130 (by decide)
  have h1 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c756 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c644, some c47, some c753, some c755, some c45, some c108, some c754, some c79, some c60, some c142, some c213, some c94, some c393, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p756 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 31) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c750, c644, c47, c753, c755, c45, c108, c754, c79, c60, c142, c213, c94, c393] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c755 := derived755 a h
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c754 := derived754 a h
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c213 := h 212 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c393 := h 392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c644, some c47, some c756, some c49, some c75, some c45, some c106, some c635, some c20, some c25, some c8, some c16, some c198, some c171, some c226, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p757 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 31) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c750, c644, c47, c756, c49, c75, c45, c106, c635, c20, c25, c8, c16, c198, c171, c226] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c756 := derived756 a h
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c635 := derived635 a h
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c198 := h 197 (by decide)
  have h14 : Entails.eval a c171 := h 170 (by decide)
  have h15 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c644, some c49, some c757, some c45, some c633, some c130, some c35, some c285, some c34, some c64, some c7, some c342, some c29, some c53, some c275, some c380, some c482, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p758 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 31) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c750, c644, c49, c757, c45, c633, c130, c35, c285, c34, c64, c7, c342, c29, c53, c275, c380, c482] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c757 := derived757 a h
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c633 := derived633 a h
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c7 := h 6 (by decide)
  have h12 : Entails.eval a c342 := h 341 (by decide)
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c275 := h 274 (by decide)
  have h16 : Entails.eval a c380 := h 379 (by decide)
  have h17 : Entails.eval a c482 := h 481 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c750, some c757, some c49, some c758, some c75, some c107, some c567, some c22, some c25, some c9, some c17, some c198, some c171, some c226, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p759 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 31) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c644, c750, c757, c49, c758, c75, c107, c567, c22, c25, c9, c17, c198, c171, c226] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c758 := derived758 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c567 := derived567 a h
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c9 := h 8 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c198 := h 197 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c644, some c757, some c759, some c51, some c45, some c629, some c31, some c133, some c25, some c199, some c377, some c7, some c519, some c116, some c517, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p760 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 31) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c750, c644, c757, c759, c51, c45, c629, c31, c133, c25, c199, c377, c7, c519, c116, c517] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c759 := derived759 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c629 := derived629 a h
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c7 := h 6 (by decide)
  have h13 : Entails.eval a c519 := h 518 (by decide)
  have h14 : Entails.eval a c116 := h 115 (by decide)
  have h15 : Entails.eval a c517 := h 516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c750, some c760, some c757, some c759, some c51, some c45, some c629, some c273, some c321, some c359, some c246, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p761 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 31) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c644, c750, c760, c757, c759, c51, c45, c629, c273, c321, c359, c246] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c760 := derived760 a h
  have h3 : Entails.eval a c757 := derived757 a h
  have h4 : Entails.eval a c759 := derived759 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c629 := derived629 a h
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c321 := h 320 (by decide)
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c750, some c757, some c759, some c51, some c45, some c629, some c760, some c761, some c116, some c499, some c447, some c360, some c246, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p762 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 31) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c644, c750, c757, c759, c51, c45, c629, c760, c761, c116, c499, c447, c360, c246] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c759 := derived759 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c629 := derived629 a h
  have h7 : Entails.eval a c760 := derived760 a h
  have h8 : Entails.eval a c761 := derived761 a h
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c499 := h 498 (by decide)
  have h11 : Entails.eval a c447 := h 446 (by decide)
  have h12 : Entails.eval a c360 := h 359 (by decide)
  have h13 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨17, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c360, some c271, some c202, some c94, some c147, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p763 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 31) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c644, c360, c271, c202, c94, c147] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c629, some c206, some c20, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p764 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 31) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c644, c629, c206, c20] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c764, some c51, some c359, some c499, some c72, some c134, some c14, some c567, some c4, some c24, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p765 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 31) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c644, c764, c51, c359, c499, c72, c134, c14, c567, c4, c24] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c764 := derived764 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c499 := h 498 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c567 := derived567 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c644, some c500, some c763, some c666, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p766 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 31) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c762, c644, c500, c763, c666] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c500 := h 499 (by decide)
  have h3 : Entails.eval a c763 := derived763 a h
  have h4 : Entails.eval a c666 := derived666 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c764, some c765, some c766, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p767 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 31) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c764, c765, c766] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c764 := derived764 a h
  have h1 : Entails.eval a c765 := derived765 a h
  have h2 : Entails.eval a c766 := derived766 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c762, some c767, some c5, some c51, some c228, some c30, some c666, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p768 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 31) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c750, c762, c767, c5, c51, c228, c30, c666] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c767 := derived767 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c666 := derived666 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c750, some c51, some c767, some c5, some c25, some c768, some c629, some c206, some c44, some c16, some c110, some c81, some c144, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p769 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 31) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c762, c750, c51, c767, c5, c25, c768, c629, c206, c44, c16, c110, c81, c144] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c767 := derived767 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c768 := derived768 a h
  have h7 : Entails.eval a c629 := derived629 a h
  have h8 : Entails.eval a c206 := h 205 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c750, some c20, some c315, some c25, some c7, some c182, some c16, some c312, some c247, some c144, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p770 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 31) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c644, c750, c20, c315, c25, c7, c182, c16, c312, c247, c144] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c182 := h 181 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c312 := h 311 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c771 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c750, some c644, some c25, some c769, some c226, some c209, some c198, some c135, some c478, some c187, some c409, some c414, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p771 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 31) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c762, c750, c644, c25, c769, c226, c209, c198, c135, c478, c187, c409, c414] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c644 := derived644 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c769 := derived769 a h
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c478 := h 477 (by decide)
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c409 := h 408 (by decide)
  have h12 : Entails.eval a c414 := h 413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c750, some c769, some c770, some c25, some c771, some c666, some c171, some c34, some c137, some c519, some c94, some c172, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p772 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 31) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c762, c750, c769, c770, c25, c771, c666, c171, c34, c137, c519, c94, c172] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c769 := derived769 a h
  have h3 : Entails.eval a c770 := derived770 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c771 := derived771 a h
  have h6 : Entails.eval a c666 := derived666 a h
  have h7 : Entails.eval a c171 := h 170 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c137 := h 136 (by decide)
  have h10 : Entails.eval a c519 := h 518 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨26, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c750, some c763, some c342, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p773 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 31) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c644, c750, c763, c342] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c769, some c772, some c773, some c275, some c135, some c137, some c14, some c400, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p774 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 31) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c644, c769, c772, c773, c275, c135, c137, c14, c400] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c769 := derived769 a h
  have h2 : Entails.eval a c772 := derived772 a h
  have h3 : Entails.eval a c773 := derived773 a h
  have h4 : Entails.eval a c275 := h 274 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c137 := h 136 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c400 := h 399 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c750, some c644, some c769, some c774, some c665, some c666, some c681, some c209, some c342, some c226, some c488, some c125, some c390, some c135, some c230, some c374, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p775 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 31) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c762, c750, c644, c769, c774, c665, c666, c681, c209, c342, c226, c488, c125, c390, c135, c230, c374] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c644 := derived644 a h
  have h3 : Entails.eval a c769 := derived769 a h
  have h4 : Entails.eval a c774 := derived774 a h
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c666 := derived666 a h
  have h7 : Entails.eval a c681 := derived681 a h
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c342 := h 341 (by decide)
  have h10 : Entails.eval a c226 := h 225 (by decide)
  have h11 : Entails.eval a c488 := h 487 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c390 := h 389 (by decide)
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c230 := h 229 (by decide)
  have h16 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c644, some c762, some c275, some c184, some c72, some c115, some c270, some c110, some c387, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p776 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 31) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c750, c644, c762, c275, c184, c72, c115, c270, c110, c387] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c762 := derived762 a h
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c387 := h 386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨24, by decide⟩, false), (⟨26, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c750, some c644, some c184, some c275, some c776, some c389, some c459, some c97, some c325, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p777 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 31) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c762, c750, c644, c184, c275, c776, c389, c459, c97, c325] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c644 := derived644 a h
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c275 := h 274 (by decide)
  have h5 : Entails.eval a c776 := derived776 a h
  have h6 : Entails.eval a c389 := h 388 (by decide)
  have h7 : Entails.eval a c459 := h 458 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c750, some c775, some c769, some c777, some c763, some c242, some c107, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p778 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 31) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c644, c750, c775, c769, c777, c763, c242, c107] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c775 := derived775 a h
  have h3 : Entails.eval a c769 := derived769 a h
  have h4 : Entails.eval a c777 := derived777 a h
  have h5 : Entails.eval a c763 := derived763 a h
  have h6 : Entails.eval a c242 := h 241 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, false), (⟨26, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c769, some c107, some c371, some c114, some c331, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p779 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 31) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c750, c769, c107, c371, c114, c331] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c769 := derived769 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c780 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c762, some c184, some c279, some c48, some c110, some c387, some c43, some c688, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p780 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 31) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c750, c762, c184, c279, c48, c110, c387, c43, c688] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c279 := h 278 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c387 := h 386 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c688 := derived688 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c781 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f781 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c762, some c775, some c769, some c184, some c778, some c779, some c780, some c75, some c567, some c294, some c355, some c503, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p781 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked781 : lratChecker f781 p781 = .success := by decide +kernel
theorem unsat781 : Unsatisfiable (PosFin 31) f781 := by
  apply lratCheckerSound f781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p781
  · intro a ha; simp [p781] at ha; subst a; trivial
  · exact checked781
theorem derived781 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c781 := by
  apply localUnsat_implies_entails f781 [c750, c762, c775, c769, c184, c778, c779, c780, c75, c567, c294, c355, c503] c781 unsat781 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c775 := derived775 a h
  have h3 : Entails.eval a c769 := derived769 a h
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c778 := derived778 a h
  have h6 : Entails.eval a c779 := derived779 a h
  have h7 : Entails.eval a c780 := derived780 a h
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c567 := derived567 a h
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c503 := h 502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c782 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f782 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c25, some c781, some c775, some c769, some c75, some c567, some c264, some c183, some c295, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p782 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked782 : lratChecker f782 p782 = .success := by decide +kernel
theorem unsat782 : Unsatisfiable (PosFin 31) f782 := by
  apply lratCheckerSound f782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p782
  · intro a ha; simp [p782] at ha; subst a; trivial
  · exact checked782
theorem derived782 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c782 := by
  apply localUnsat_implies_entails f782 [c750, c25, c781, c775, c769, c75, c567, c264, c183, c295] c782 unsat782 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c781 := derived781 a h
  have h3 : Entails.eval a c775 := derived775 a h
  have h4 : Entails.eval a c769 := derived769 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c567 := derived567 a h
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c783 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f783 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c644, some c781, some c775, some c769, some c779, some c782, some c245, some c265, some c34, some c250, some c208, some c622, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p783 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked783 : lratChecker f783 p783 = .success := by decide +kernel
theorem unsat783 : Unsatisfiable (PosFin 31) f783 := by
  apply lratCheckerSound f783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p783
  · intro a ha; simp [p783] at ha; subst a; trivial
  · exact checked783
theorem derived783 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c783 := by
  apply localUnsat_implies_entails f783 [c750, c644, c781, c775, c769, c779, c782, c245, c265, c34, c250, c208, c622] c783 unsat783 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c781 := derived781 a h
  have h3 : Entails.eval a c775 := derived775 a h
  have h4 : Entails.eval a c769 := derived769 a h
  have h5 : Entails.eval a c779 := derived779 a h
  have h6 : Entails.eval a c782 := derived782 a h
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  have h12 : Entails.eval a c622 := derived622 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c784 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c644, some c762, some c750, some c769, some c775, some c781, some c783, some c310, some c325, some c766, some c275, some c14, some c483, some c97, some c457, some c34, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p784 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 31) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c644, c762, c750, c769, c775, c781, c783, c310, c325, c766, c275, c14, c483, c97, c457, c34] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c769 := derived769 a h
  have h4 : Entails.eval a c775 := derived775 a h
  have h5 : Entails.eval a c781 := derived781 a h
  have h6 : Entails.eval a c783 := derived783 a h
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  have h9 : Entails.eval a c766 := derived766 a h
  have h10 : Entails.eval a c275 := h 274 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c483 := h 482 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c457 := h 456 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c644, some c762, some c784, some c5, some c50, some c769, some c441, some c766, some c450, some c14, some c390, some c340, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p785 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 31) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c750, c644, c762, c784, c5, c50, c769, c441, c766, c450, c14, c390, c340] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c762 := derived762 a h
  have h3 : Entails.eval a c784 := derived784 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c769 := derived769 a h
  have h7 : Entails.eval a c441 := h 440 (by decide)
  have h8 : Entails.eval a c766 := derived766 a h
  have h9 : Entails.eval a c450 := h 449 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c390 := h 389 (by decide)
  have h12 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c786 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c750, some c644, some c784, some c5, some c50, some c769, some c785, some c773, some c14, some c335, some c125, some c337, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p786 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 31) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c762, c750, c644, c784, c5, c50, c769, c785, c773, c14, c335, c125, c337] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c644 := derived644 a h
  have h3 : Entails.eval a c784 := derived784 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c769 := derived769 a h
  have h7 : Entails.eval a c785 := derived785 a h
  have h8 : Entails.eval a c773 := derived773 a h
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c335 := h 334 (by decide)
  have h11 : Entails.eval a c125 := h 124 (by decide)
  have h12 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c762, some c784, some c786, some c184, some c174, some c176, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p787 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 31) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c750, c762, c784, c786, c184, c174, c176] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c784 := derived784 a h
  have h3 : Entails.eval a c786 := derived786 a h
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c174 := h 173 (by decide)
  have h6 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c762, some c184, some c174, some c176, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p788 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 31) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c750, c762, c184, c174, c176] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c789 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c762, some c787, some c788, some c5, some c50, some c176, some c138, some c42, some c606, some c43, some c385, some c106, some c492, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p789 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 31) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c750, c762, c787, c788, c5, c50, c176, c138, c42, c606, c43, c385, c106, c492] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c788 := derived788 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c176 := h 175 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c606 := derived606 a h
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c492 := h 491 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c762, some c787, some c50, some c5, some c788, some c789, some c205, some c29, some c28, some c65, some c384, some c439, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p790 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 31) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c750, c762, c787, c50, c5, c788, c789, c205, c29, c28, c65, c384, c439] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c788 := derived788 a h
  have h6 : Entails.eval a c789 := derived789 a h
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c384 := h 383 (by decide)
  have h12 : Entails.eval a c439 := h 438 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨15, by decide⟩, false), (⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c787, some c644, some c790, some c262, some c22, some c46, some c42, some c399, some c400, some c123, some c113, some c509, some c447, some c93, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p791 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 31) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c787, c644, c790, c262, c22, c46, c42, c399, c400, c123, c113, c509, c447, c93] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c790 := derived790 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c399 := h 398 (by decide)
  have h8 : Entails.eval a c400 := h 399 (by decide)
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c509 := h 508 (by decide)
  have h12 : Entails.eval a c447 := h 446 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c787, some c762, some c750, some c262, some c791, some c209, some c688, some c353, some c65, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p792 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 31) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c787, c762, c750, c262, c791, c209, c688, c353, c65] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c791 := derived791 a h
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c688 := derived688 a h
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c793 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f793 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c787, some c750, some c762, some c32, some c666, some c209, some c28, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p793 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked793 : lratChecker f793 p793 = .success := by decide +kernel
theorem unsat793 : Unsatisfiable (PosFin 31) f793 := by
  apply lratCheckerSound f793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p793
  · intro a ha; simp [p793] at ha; subst a; trivial
  · exact checked793
theorem derived793 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c793 := by
  apply localUnsat_implies_entails f793 [c787, c750, c762, c32, c666, c209, c28] c793 unsat793 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c762 := derived762 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c666 := derived666 a h
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c794 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c787, some c750, some c25, some c790, some c793, some c226, some c227, some c666, some c171, some c467, some c30, some c42, some c370, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p794 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 31) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c762, c787, c750, c25, c790, c793, c226, c227, c666, c171, c467, c30, c42, c370] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c787 := derived787 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c790 := derived790 a h
  have h5 : Entails.eval a c793 := derived793 a h
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c666 := derived666 a h
  have h9 : Entails.eval a c171 := h 170 (by decide)
  have h10 : Entails.eval a c467 := h 466 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c750, some c787, some c790, some c793, some c25, some c794, some c209, some c688, some c198, some c65, some c512, some c403, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p795 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 31) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c762, c750, c787, c790, c793, c25, c794, c209, c688, c198, c65, c512, c403] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c790 := derived790 a h
  have h4 : Entails.eval a c793 := derived793 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c794 := derived794 a h
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c688 := derived688 a h
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c512 := h 511 (by decide)
  have h12 : Entails.eval a c403 := h 402 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c762, some c787, some c790, some c793, some c795, some c792, some c184, some c209, some c688, some c36, some c65, some c512, some c403, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p796 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 31) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c750, c762, c787, c790, c793, c795, c792, c184, c209, c688, c36, c65, c512, c403] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c790 := derived790 a h
  have h4 : Entails.eval a c793 := derived793 a h
  have h5 : Entails.eval a c795 := derived795 a h
  have h6 : Entails.eval a c792 := derived792 a h
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c688 := derived688 a h
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c512 := h 511 (by decide)
  have h13 : Entails.eval a c403 := h 402 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c750, some c762, some c644, some c790, some c793, some c795, some c792, some c665, some c34, some c97, some c65, some c325, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p797 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 31) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c750, c762, c644, c790, c793, c795, c792, c665, c34, c97, c65, c325] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c644 := derived644 a h
  have h3 : Entails.eval a c790 := derived790 a h
  have h4 : Entails.eval a c793 := derived793 a h
  have h5 : Entails.eval a c795 := derived795 a h
  have h6 : Entails.eval a c792 := derived792 a h
  have h7 : Entails.eval a c665 := derived665 a h
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c750, some c644, some c792, some c184, some c796, some c797, some c666, some c681, some c65, some c387, some c325, some c224, some c110, some c457, some c338, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p798 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 31) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c762, c750, c644, c792, c184, c796, c797, c666, c681, c65, c387, c325, c224, c110, c457, c338] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c644 := derived644 a h
  have h3 : Entails.eval a c792 := derived792 a h
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c796 := derived796 a h
  have h6 : Entails.eval a c797 := derived797 a h
  have h7 : Entails.eval a c666 := derived666 a h
  have h8 : Entails.eval a c681 := derived681 a h
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c387 := h 386 (by decide)
  have h11 : Entails.eval a c325 := h 324 (by decide)
  have h12 : Entails.eval a c224 := h 223 (by decide)
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c457 := h 456 (by decide)
  have h15 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c790, some c793, some c795, some c798, some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p799 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 31) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c790, c793, c795, c798] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c790 := derived790 a h
  have h1 : Entails.eval a c793 := derived793 a h
  have h2 : Entails.eval a c795 := derived795 a h
  have h3 : Entails.eval a c798 := derived798 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c644, some c750, some c799, some c787, some c793, some c666, some c681, some c209, some c65, some c226, some c362, some c27, some c225, some c448, some c201, some c451, some c341, some c397, some c190, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p800 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 31) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c762, c644, c750, c799, c787, c793, c666, c681, c209, c65, c226, c362, c27, c225, c448, c201, c451, c341, c397, c190] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c799 := derived799 a h
  have h4 : Entails.eval a c787 := derived787 a h
  have h5 : Entails.eval a c793 := derived793 a h
  have h6 : Entails.eval a c666 := derived666 a h
  have h7 : Entails.eval a c681 := derived681 a h
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c226 := h 225 (by decide)
  have h11 : Entails.eval a c362 := h 361 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c225 := h 224 (by decide)
  have h14 : Entails.eval a c448 := h 447 (by decide)
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c451 := h 450 (by decide)
  have h17 : Entails.eval a c341 := h 340 (by decide)
  have h18 : Entails.eval a c397 := h 396 (by decide)
  have h19 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c799, some c762, some c750, some c644, some c800, some c793, some c30, some c207, some c755, some c22, some c355, some c25, some c263, some c151, some c412, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p801 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 31) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c799, c762, c750, c644, c800, c793, c30, c207, c755, c22, c355, c25, c263, c151, c412] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c799 := derived799 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c644 := derived644 a h
  have h4 : Entails.eval a c800 := derived800 a h
  have h5 : Entails.eval a c793 := derived793 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c755 := derived755 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c151 := h 150 (by decide)
  have h14 : Entails.eval a c412 := h 411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c799, some c644, some c793, some c800, some c801, some c203, some c148, some c92, some c252, some c300, some c60, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p802 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 31) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c799, c644, c793, c800, c801, c203, c148, c92, c252, c300, c60] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c799 := derived799 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c793 := derived793 a h
  have h3 : Entails.eval a c800 := derived800 a h
  have h4 : Entails.eval a c801 := derived801 a h
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c300 := h 299 (by decide)
  have h10 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c802, some c762, some c50, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p803 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 31) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c802, c762, c50] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c802, some c762, some c750, some c5, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p804 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 31) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c802, c762, c750, c5] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c802, some c788, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p805 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 31) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c802, c788] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c788 := derived788 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c806 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c802, some c803, some c787, some c805, some c804, some c644, some c799, some c65, some c361, some c491, some c309, some c324, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p806 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 31) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c802, c803, c787, c805, c804, c644, c799, c65, c361, c491, c309, c324] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c803 := derived803 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c805 := derived805 a h
  have h4 : Entails.eval a c804 := derived804 a h
  have h5 : Entails.eval a c644 := derived644 a h
  have h6 : Entails.eval a c799 := derived799 a h
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c491 := h 490 (by decide)
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c805, some c802, some c750, some c804, some c787, some c644, some c799, some c806, some c323, some c353, some c233, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p807 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 31) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c805, c802, c750, c804, c787, c644, c799, c806, c323, c353, c233] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c805 := derived805 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c804 := derived804 a h
  have h4 : Entails.eval a c787 := derived787 a h
  have h5 : Entails.eval a c644 := derived644 a h
  have h6 : Entails.eval a c799 := derived799 a h
  have h7 : Entails.eval a c806 := derived806 a h
  have h8 : Entails.eval a c323 := h 322 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c762, some c805, some c787, some c804, some c803, some c644, some c750, some c807, some c666, some c681, some c65, some c384, some c501, some c27, some c292, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p808 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 31) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c762, c805, c787, c804, c803, c644, c750, c807, c666, c681, c65, c384, c501, c27, c292] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c805 := derived805 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c804 := derived804 a h
  have h4 : Entails.eval a c803 := derived803 a h
  have h5 : Entails.eval a c644 := derived644 a h
  have h6 : Entails.eval a c750 := derived750 a h
  have h7 : Entails.eval a c807 := derived807 a h
  have h8 : Entails.eval a c666 := derived666 a h
  have h9 : Entails.eval a c681 := derived681 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c384 := h 383 (by decide)
  have h12 : Entails.eval a c501 := h 500 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c808, some c803, some c787, some c28, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p809 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 31) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c808, c803, c787, c28] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c808 := derived808 a h
  have h1 : Entails.eval a c803 := derived803 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c809, some c762, some c666, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p810 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 31) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c809, c762, c666] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c809 := derived809 a h
  have h1 : Entails.eval a c762 := derived762 a h
  have h2 : Entails.eval a c666 := derived666 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c809, some c802, some c762, some c205, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p811 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 31) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c809, c802, c762, c205] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c809 := derived809 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c762 := derived762 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c810, some c799, some c644, some c804, some c808, some c272, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p812 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 31) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c810, c799, c644, c804, c808, c272] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c810 := derived810 a h
  have h1 : Entails.eval a c799 := derived799 a h
  have h2 : Entails.eval a c644 := derived644 a h
  have h3 : Entails.eval a c804 := derived804 a h
  have h4 : Entails.eval a c808 := derived808 a h
  have h5 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c811, some c802, some c762, some c176, some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p813 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 31) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c811, c802, c762, c176] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c811 := derived811 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c762 := derived762 a h
  have h3 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c805, some c811, some c808, some c787, some c386, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p814 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 31) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c812, c805, c811, c808, c787, c386] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c805 := derived805 a h
  have h2 : Entails.eval a c811 := derived811 a h
  have h3 : Entails.eval a c808 := derived808 a h
  have h4 : Entails.eval a c787 := derived787 a h
  have h5 : Entails.eval a c386 := h 385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c814, some c813, some c802, some c762, some c138]
def p815 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 31) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c814, c813, c802, c762, c138] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c814 := derived814 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c762 := derived762 a h
  have h4 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived815

end CochromaticTwenty.Certificates.Z12Direct_5_8_14
