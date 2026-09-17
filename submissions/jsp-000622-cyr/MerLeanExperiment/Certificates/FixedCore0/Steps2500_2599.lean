import MerLeanExperiment.Certificates.FixedCore0.Steps2400_2499

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10051 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10051 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10049, some c10050, some c5046, some c2808, some c2809, some c2820, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10051 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10051 : lratChecker f10051 p10051 = .success := by decide +kernel
theorem unsat10051 : Unsatisfiable (PosFin 65) f10051 := by
  apply lratCheckerSound f10051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10051
  · intro a ha; simp [p10051] at ha; subst a; trivial
  · exact checked10051
theorem derived10051 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10051 := by
  apply localUnsat_implies_entails f10051 [c10049, c10050, c5046, c2808, c2809, c2820] c10051 unsat10051 (by rfl) a
  have h0 : Entails.eval a c10049 := derived10049 a h
  have h1 : Entails.eval a c10050 := derived10050 a h
  have h2 : Entails.eval a c5046 := h 5045 (by decide)
  have h3 : Entails.eval a c2808 := h 2807 (by decide)
  have h4 : Entails.eval a c2809 := h 2808 (by decide)
  have h5 : Entails.eval a c2820 := h 2819 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10052 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10052 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10042, some c1591, some c1595, some c1594, some c1629, some c1616, some c1853, some c1670, some c1700, some c1638, some c1592, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10052 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10052 : lratChecker f10052 p10052 = .success := by decide +kernel
theorem unsat10052 : Unsatisfiable (PosFin 65) f10052 := by
  apply lratCheckerSound f10052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10052
  · intro a ha; simp [p10052] at ha; subst a; trivial
  · exact checked10052
theorem derived10052 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10052 := by
  apply localUnsat_implies_entails f10052 [c9748, c10042, c1591, c1595, c1594, c1629, c1616, c1853, c1670, c1700, c1638, c1592] c10052 unsat10052 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10042 := derived10042 a h
  have h2 : Entails.eval a c1591 := h 1590 (by decide)
  have h3 : Entails.eval a c1595 := h 1594 (by decide)
  have h4 : Entails.eval a c1594 := h 1593 (by decide)
  have h5 : Entails.eval a c1629 := h 1628 (by decide)
  have h6 : Entails.eval a c1616 := h 1615 (by decide)
  have h7 : Entails.eval a c1853 := h 1852 (by decide)
  have h8 : Entails.eval a c1670 := h 1669 (by decide)
  have h9 : Entails.eval a c1700 := h 1699 (by decide)
  have h10 : Entails.eval a c1638 := h 1637 (by decide)
  have h11 : Entails.eval a c1592 := h 1591 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10053 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨54, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10053 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10035, some c10046, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10053 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10053 : lratChecker f10053 p10053 = .success := by decide +kernel
theorem unsat10053 : Unsatisfiable (PosFin 65) f10053 := by
  apply lratCheckerSound f10053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10053
  · intro a ha; simp [p10053] at ha; subst a; trivial
  · exact checked10053
theorem derived10053 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10053 := by
  apply localUnsat_implies_entails f10053 [c10035, c10046] c10053 unsat10053 (by rfl) a
  have h0 : Entails.eval a c10035 := derived10035 a h
  have h1 : Entails.eval a c10046 := derived10046 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10054 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10054 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10052, some c10053, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10054 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10054 : lratChecker f10054 p10054 = .success := by decide +kernel
theorem unsat10054 : Unsatisfiable (PosFin 65) f10054 := by
  apply lratCheckerSound f10054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10054
  · intro a ha; simp [p10054] at ha; subst a; trivial
  · exact checked10054
theorem derived10054 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10054 := by
  apply localUnsat_implies_entails f10054 [c10052, c10053] c10054 unsat10054 (by rfl) a
  have h0 : Entails.eval a c10052 := derived10052 a h
  have h1 : Entails.eval a c10053 := derived10053 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10055 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10055 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1595, some c1594, some c4266, some c850, some c2979, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10055 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10055 : lratChecker f10055 p10055 = .success := by decide +kernel
theorem unsat10055 : Unsatisfiable (PosFin 65) f10055 := by
  apply lratCheckerSound f10055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10055
  · intro a ha; simp [p10055] at ha; subst a; trivial
  · exact checked10055
theorem derived10055 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10055 := by
  apply localUnsat_implies_entails f10055 [c9748, c1595, c1594, c4266, c850, c2979] c10055 unsat10055 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1595 := h 1594 (by decide)
  have h2 : Entails.eval a c1594 := h 1593 (by decide)
  have h3 : Entails.eval a c4266 := h 4265 (by decide)
  have h4 : Entails.eval a c850 := h 849 (by decide)
  have h5 : Entails.eval a c2979 := h 2978 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10056 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10056 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4274, some c1607, some c999, some c750, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10056 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10056 : lratChecker f10056 p10056 = .success := by decide +kernel
theorem unsat10056 : Unsatisfiable (PosFin 65) f10056 := by
  apply lratCheckerSound f10056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10056
  · intro a ha; simp [p10056] at ha; subst a; trivial
  · exact checked10056
theorem derived10056 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10056 := by
  apply localUnsat_implies_entails f10056 [c9748, c4274, c1607, c999, c750] c10056 unsat10056 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4274 := h 4273 (by decide)
  have h2 : Entails.eval a c1607 := h 1606 (by decide)
  have h3 : Entails.eval a c999 := h 998 (by decide)
  have h4 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10057 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨63, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10057 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10051, some c1664, some c1667, some c1649, some c1647, some c10054, some c10055, some c10056, some c4267, some c4271, some c1597, some c3751, some c3700, some c2894, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10057 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked10057 : lratChecker f10057 p10057 = .success := by decide +kernel
theorem unsat10057 : Unsatisfiable (PosFin 65) f10057 := by
  apply lratCheckerSound f10057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10057
  · intro a ha; simp [p10057] at ha; subst a; trivial
  · exact checked10057
theorem derived10057 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10057 := by
  apply localUnsat_implies_entails f10057 [c9748, c10051, c1664, c1667, c1649, c1647, c10054, c10055, c10056, c4267, c4271, c1597, c3751, c3700, c2894] c10057 unsat10057 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10051 := derived10051 a h
  have h2 : Entails.eval a c1664 := h 1663 (by decide)
  have h3 : Entails.eval a c1667 := h 1666 (by decide)
  have h4 : Entails.eval a c1649 := h 1648 (by decide)
  have h5 : Entails.eval a c1647 := h 1646 (by decide)
  have h6 : Entails.eval a c10054 := derived10054 a h
  have h7 : Entails.eval a c10055 := derived10055 a h
  have h8 : Entails.eval a c10056 := derived10056 a h
  have h9 : Entails.eval a c4267 := h 4266 (by decide)
  have h10 : Entails.eval a c4271 := h 4270 (by decide)
  have h11 : Entails.eval a c1597 := h 1596 (by decide)
  have h12 : Entails.eval a c3751 := h 3750 (by decide)
  have h13 : Entails.eval a c3700 := h 3699 (by decide)
  have h14 : Entails.eval a c2894 := h 2893 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10058 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10058 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2971, some c2035, some c3176, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10058 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10058 : lratChecker f10058 p10058 = .success := by decide +kernel
theorem unsat10058 : Unsatisfiable (PosFin 65) f10058 := by
  apply lratCheckerSound f10058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10058
  · intro a ha; simp [p10058] at ha; subst a; trivial
  · exact checked10058
theorem derived10058 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10058 := by
  apply localUnsat_implies_entails f10058 [c9748, c2971, c2035, c3176] c10058 unsat10058 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2971 := h 2970 (by decide)
  have h2 : Entails.eval a c2035 := h 2034 (by decide)
  have h3 : Entails.eval a c3176 := h 3175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10059 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10059 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3098, some c2931, some c2979, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p10059 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10059 : lratChecker f10059 p10059 = .success := by decide +kernel
theorem unsat10059 : Unsatisfiable (PosFin 65) f10059 := by
  apply lratCheckerSound f10059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10059
  · intro a ha; simp [p10059] at ha; subst a; trivial
  · exact checked10059
theorem derived10059 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10059 := by
  apply localUnsat_implies_entails f10059 [c3098, c2931, c2979] c10059 unsat10059 (by rfl) a
  have h0 : Entails.eval a c3098 := h 3097 (by decide)
  have h1 : Entails.eval a c2931 := h 2930 (by decide)
  have h2 : Entails.eval a c2979 := h 2978 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10060 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10060 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3695, some c4844, some c3427, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p10060 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10060 : lratChecker f10060 p10060 = .success := by decide +kernel
theorem unsat10060 : Unsatisfiable (PosFin 65) f10060 := by
  apply lratCheckerSound f10060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10060
  · intro a ha; simp [p10060] at ha; subst a; trivial
  · exact checked10060
theorem derived10060 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10060 := by
  apply localUnsat_implies_entails f10060 [c3695, c4844, c3427] c10060 unsat10060 (by rfl) a
  have h0 : Entails.eval a c3695 := h 3694 (by decide)
  have h1 : Entails.eval a c4844 := h 4843 (by decide)
  have h2 : Entails.eval a c3427 := h 3426 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10061 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10061 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10042, some c10058, some c10059, some c10060, some c849, some c848, some c1691, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10061 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10061 : lratChecker f10061 p10061 = .success := by decide +kernel
theorem unsat10061 : Unsatisfiable (PosFin 65) f10061 := by
  apply lratCheckerSound f10061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10061
  · intro a ha; simp [p10061] at ha; subst a; trivial
  · exact checked10061
theorem derived10061 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10061 := by
  apply localUnsat_implies_entails f10061 [c9748, c10042, c10058, c10059, c10060, c849, c848, c1691] c10061 unsat10061 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10042 := derived10042 a h
  have h2 : Entails.eval a c10058 := derived10058 a h
  have h3 : Entails.eval a c10059 := derived10059 a h
  have h4 : Entails.eval a c10060 := derived10060 a h
  have h5 : Entails.eval a c849 := h 848 (by decide)
  have h6 : Entails.eval a c848 := h 847 (by decide)
  have h7 : Entails.eval a c1691 := h 1690 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10062 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10062 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1683, some c1682, some c1684, some c9803, some c4849, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p10062 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10062 : lratChecker f10062 p10062 = .success := by decide +kernel
theorem unsat10062 : Unsatisfiable (PosFin 65) f10062 := by
  apply lratCheckerSound f10062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10062
  · intro a ha; simp [p10062] at ha; subst a; trivial
  · exact checked10062
theorem derived10062 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10062 := by
  apply localUnsat_implies_entails f10062 [c9748, c1683, c1682, c1684, c9803, c4849] c10062 unsat10062 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1683 := h 1682 (by decide)
  have h2 : Entails.eval a c1682 := h 1681 (by decide)
  have h3 : Entails.eval a c1684 := h 1683 (by decide)
  have h4 : Entails.eval a c9803 := derived9803 a h
  have h5 : Entails.eval a c4849 := h 4848 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10063 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨37, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10063 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1719, some c1720, some c1721, some c1723, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10063 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10063 : lratChecker f10063 p10063 = .success := by decide +kernel
theorem unsat10063 : Unsatisfiable (PosFin 65) f10063 := by
  apply lratCheckerSound f10063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10063
  · intro a ha; simp [p10063] at ha; subst a; trivial
  · exact checked10063
theorem derived10063 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10063 := by
  apply localUnsat_implies_entails f10063 [c9748, c1719, c1720, c1721, c1723] c10063 unsat10063 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1719 := h 1718 (by decide)
  have h2 : Entails.eval a c1720 := h 1719 (by decide)
  have h3 : Entails.eval a c1721 := h 1720 (by decide)
  have h4 : Entails.eval a c1723 := h 1722 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10064 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10064 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1672, some c1676, some c10062, some c1669, some c10063, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10064 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10064 : lratChecker f10064 p10064 = .success := by decide +kernel
theorem unsat10064 : Unsatisfiable (PosFin 65) f10064 := by
  apply lratCheckerSound f10064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10064
  · intro a ha; simp [p10064] at ha; subst a; trivial
  · exact checked10064
theorem derived10064 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10064 := by
  apply localUnsat_implies_entails f10064 [c9748, c1672, c1676, c10062, c1669, c10063] c10064 unsat10064 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1672 := h 1671 (by decide)
  have h2 : Entails.eval a c1676 := h 1675 (by decide)
  have h3 : Entails.eval a c10062 := derived10062 a h
  have h4 : Entails.eval a c1669 := h 1668 (by decide)
  have h5 : Entails.eval a c10063 := derived10063 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10065 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨16, by decide⟩, false), (⟨63, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10065 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1732, some c1741, some c1730, some c1731, some c10064, some c10061, some c4693, some c1817, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10065 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10065 : lratChecker f10065 p10065 = .success := by decide +kernel
theorem unsat10065 : Unsatisfiable (PosFin 65) f10065 := by
  apply lratCheckerSound f10065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10065
  · intro a ha; simp [p10065] at ha; subst a; trivial
  · exact checked10065
theorem derived10065 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10065 := by
  apply localUnsat_implies_entails f10065 [c9748, c1732, c1741, c1730, c1731, c10064, c10061, c4693, c1817] c10065 unsat10065 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1732 := h 1731 (by decide)
  have h2 : Entails.eval a c1741 := h 1740 (by decide)
  have h3 : Entails.eval a c1730 := h 1729 (by decide)
  have h4 : Entails.eval a c1731 := h 1730 (by decide)
  have h5 : Entails.eval a c10064 := derived10064 a h
  have h6 : Entails.eval a c10061 := derived10061 a h
  have h7 : Entails.eval a c4693 := h 4692 (by decide)
  have h8 : Entails.eval a c1817 := h 1816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10066 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨50, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10066 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4275, some c1001, some c750, some c993, some c746, some c735, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10066 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10066 : lratChecker f10066 p10066 = .success := by decide +kernel
theorem unsat10066 : Unsatisfiable (PosFin 65) f10066 := by
  apply lratCheckerSound f10066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10066
  · intro a ha; simp [p10066] at ha; subst a; trivial
  · exact checked10066
theorem derived10066 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10066 := by
  apply localUnsat_implies_entails f10066 [c4275, c1001, c750, c993, c746, c735] c10066 unsat10066 (by rfl) a
  have h0 : Entails.eval a c4275 := h 4274 (by decide)
  have h1 : Entails.eval a c1001 := h 1000 (by decide)
  have h2 : Entails.eval a c750 := h 749 (by decide)
  have h3 : Entails.eval a c993 := h 992 (by decide)
  have h4 : Entails.eval a c746 := h 745 (by decide)
  have h5 : Entails.eval a c735 := h 734 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10067 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10067 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4266, some c4269, some c10058, some c2979, some c850, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10067 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10067 : lratChecker f10067 p10067 = .success := by decide +kernel
theorem unsat10067 : Unsatisfiable (PosFin 65) f10067 := by
  apply lratCheckerSound f10067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10067
  · intro a ha; simp [p10067] at ha; subst a; trivial
  · exact checked10067
theorem derived10067 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10067 := by
  apply localUnsat_implies_entails f10067 [c4266, c4269, c10058, c2979, c850] c10067 unsat10067 (by rfl) a
  have h0 : Entails.eval a c4266 := h 4265 (by decide)
  have h1 : Entails.eval a c4269 := h 4268 (by decide)
  have h2 : Entails.eval a c10058 := derived10058 a h
  have h3 : Entails.eval a c2979 := h 2978 (by decide)
  have h4 : Entails.eval a c850 := h 849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10068 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨16, by decide⟩, false), (⟨63, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10068 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10065, some c4301, some c4315, some c4302, some c4299, some c10067, some c10066, some c4271, some c4274, some c998, some c999, some c750, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10068 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10068 : lratChecker f10068 p10068 = .success := by decide +kernel
theorem unsat10068 : Unsatisfiable (PosFin 65) f10068 := by
  apply lratCheckerSound f10068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10068
  · intro a ha; simp [p10068] at ha; subst a; trivial
  · exact checked10068
theorem derived10068 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10068 := by
  apply localUnsat_implies_entails f10068 [c10065, c4301, c4315, c4302, c4299, c10067, c10066, c4271, c4274, c998, c999, c750] c10068 unsat10068 (by rfl) a
  have h0 : Entails.eval a c10065 := derived10065 a h
  have h1 : Entails.eval a c4301 := h 4300 (by decide)
  have h2 : Entails.eval a c4315 := h 4314 (by decide)
  have h3 : Entails.eval a c4302 := h 4301 (by decide)
  have h4 : Entails.eval a c4299 := h 4298 (by decide)
  have h5 : Entails.eval a c10067 := derived10067 a h
  have h6 : Entails.eval a c10066 := derived10066 a h
  have h7 : Entails.eval a c4271 := h 4270 (by decide)
  have h8 : Entails.eval a c4274 := h 4273 (by decide)
  have h9 : Entails.eval a c998 := h 997 (by decide)
  have h10 : Entails.eval a c999 := h 998 (by decide)
  have h11 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10069 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10069 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3487, some c3511, some c2905, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p10069 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10069 : lratChecker f10069 p10069 = .success := by decide +kernel
theorem unsat10069 : Unsatisfiable (PosFin 65) f10069 := by
  apply lratCheckerSound f10069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10069
  · intro a ha; simp [p10069] at ha; subst a; trivial
  · exact checked10069
theorem derived10069 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10069 := by
  apply localUnsat_implies_entails f10069 [c3487, c3511, c2905] c10069 unsat10069 (by rfl) a
  have h0 : Entails.eval a c3487 := h 3486 (by decide)
  have h1 : Entails.eval a c3511 := h 3510 (by decide)
  have h2 : Entails.eval a c2905 := h 2904 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10070 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10070 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1732, some c1741, some c1730, some c1731, some c1734, some c10065, some c10054, some c1668, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10070 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10070 : lratChecker f10070 p10070 = .success := by decide +kernel
theorem unsat10070 : Unsatisfiable (PosFin 65) f10070 := by
  apply lratCheckerSound f10070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10070
  · intro a ha; simp [p10070] at ha; subst a; trivial
  · exact checked10070
theorem derived10070 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10070 := by
  apply localUnsat_implies_entails f10070 [c9748, c1732, c1741, c1730, c1731, c1734, c10065, c10054, c1668] c10070 unsat10070 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1732 := h 1731 (by decide)
  have h2 : Entails.eval a c1741 := h 1740 (by decide)
  have h3 : Entails.eval a c1730 := h 1729 (by decide)
  have h4 : Entails.eval a c1731 := h 1730 (by decide)
  have h5 : Entails.eval a c1734 := h 1733 (by decide)
  have h6 : Entails.eval a c10065 := derived10065 a h
  have h7 : Entails.eval a c10054 := derived10054 a h
  have h8 : Entails.eval a c1668 := h 1667 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10071 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10071 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10051, some c10069, some c10057, some c10068, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10071 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10071 : lratChecker f10071 p10071 = .success := by decide +kernel
theorem unsat10071 : Unsatisfiable (PosFin 65) f10071 := by
  apply lratCheckerSound f10071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10071
  · intro a ha; simp [p10071] at ha; subst a; trivial
  · exact checked10071
theorem derived10071 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10071 := by
  apply localUnsat_implies_entails f10071 [c10051, c10069, c10057, c10068] c10071 unsat10071 (by rfl) a
  have h0 : Entails.eval a c10051 := derived10051 a h
  have h1 : Entails.eval a c10069 := derived10069 a h
  have h2 : Entails.eval a c10057 := derived10057 a h
  have h3 : Entails.eval a c10068 := derived10068 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10072 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10072 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10069, some c10051, some c10070, some c4301, some c4302, some c4299, some c10071, some c3726, some c3247, some c5083, some c3425, some c2236, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10072 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10072 : lratChecker f10072 p10072 = .success := by decide +kernel
theorem unsat10072 : Unsatisfiable (PosFin 65) f10072 := by
  apply lratCheckerSound f10072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10072
  · intro a ha; simp [p10072] at ha; subst a; trivial
  · exact checked10072
theorem derived10072 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10072 := by
  apply localUnsat_implies_entails f10072 [c9748, c10069, c10051, c10070, c4301, c4302, c4299, c10071, c3726, c3247, c5083, c3425, c2236] c10072 unsat10072 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10069 := derived10069 a h
  have h2 : Entails.eval a c10051 := derived10051 a h
  have h3 : Entails.eval a c10070 := derived10070 a h
  have h4 : Entails.eval a c4301 := h 4300 (by decide)
  have h5 : Entails.eval a c4302 := h 4301 (by decide)
  have h6 : Entails.eval a c4299 := h 4298 (by decide)
  have h7 : Entails.eval a c10071 := derived10071 a h
  have h8 : Entails.eval a c3726 := h 3725 (by decide)
  have h9 : Entails.eval a c3247 := h 3246 (by decide)
  have h10 : Entails.eval a c5083 := h 5082 (by decide)
  have h11 : Entails.eval a c3425 := h 3424 (by decide)
  have h12 : Entails.eval a c2236 := h 2235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10073 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10073 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1840, some c1839, some c1838, some c789, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p10073 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10073 : lratChecker f10073 p10073 = .success := by decide +kernel
theorem unsat10073 : Unsatisfiable (PosFin 65) f10073 := by
  apply lratCheckerSound f10073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10073
  · intro a ha; simp [p10073] at ha; subst a; trivial
  · exact checked10073
theorem derived10073 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10073 := by
  apply localUnsat_implies_entails f10073 [c9748, c1840, c1839, c1838, c789] c10073 unsat10073 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1840 := h 1839 (by decide)
  have h2 : Entails.eval a c1839 := h 1838 (by decide)
  have h3 : Entails.eval a c1838 := h 1837 (by decide)
  have h4 : Entails.eval a c789 := h 788 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10074 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10074 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10073, some c1595, some c1594, some c1629, some c1616, some c768, some c1597, some c771, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10074 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10074 : lratChecker f10074 p10074 = .success := by decide +kernel
theorem unsat10074 : Unsatisfiable (PosFin 65) f10074 := by
  apply lratCheckerSound f10074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10074
  · intro a ha; simp [p10074] at ha; subst a; trivial
  · exact checked10074
theorem derived10074 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10074 := by
  apply localUnsat_implies_entails f10074 [c9748, c10073, c1595, c1594, c1629, c1616, c768, c1597, c771] c10074 unsat10074 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10073 := derived10073 a h
  have h2 : Entails.eval a c1595 := h 1594 (by decide)
  have h3 : Entails.eval a c1594 := h 1593 (by decide)
  have h4 : Entails.eval a c1629 := h 1628 (by decide)
  have h5 : Entails.eval a c1616 := h 1615 (by decide)
  have h6 : Entails.eval a c768 := h 767 (by decide)
  have h7 : Entails.eval a c1597 := h 1596 (by decide)
  have h8 : Entails.eval a c771 := h 770 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10075 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨63, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10075 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1667, some c1649, some c1888, some c10074, some c1829, some c1836, some c1616, some c1619, some c795, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10075 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10075 : lratChecker f10075 p10075 = .success := by decide +kernel
theorem unsat10075 : Unsatisfiable (PosFin 65) f10075 := by
  apply lratCheckerSound f10075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10075
  · intro a ha; simp [p10075] at ha; subst a; trivial
  · exact checked10075
theorem derived10075 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10075 := by
  apply localUnsat_implies_entails f10075 [c9748, c1667, c1649, c1888, c10074, c1829, c1836, c1616, c1619, c795] c10075 unsat10075 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1667 := h 1666 (by decide)
  have h2 : Entails.eval a c1649 := h 1648 (by decide)
  have h3 : Entails.eval a c1888 := h 1887 (by decide)
  have h4 : Entails.eval a c10074 := derived10074 a h
  have h5 : Entails.eval a c1829 := h 1828 (by decide)
  have h6 : Entails.eval a c1836 := h 1835 (by decide)
  have h7 : Entails.eval a c1616 := h 1615 (by decide)
  have h8 : Entails.eval a c1619 := h 1618 (by decide)
  have h9 : Entails.eval a c795 := h 794 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10076 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨6, by decide⟩, true), (⟨58, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10076 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10075, some c2822, some c2777, some c2816, some c10043, some c8003, some c10044, some c5039, some c5040, some c5038, some c789, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10076 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10076 : lratChecker f10076 p10076 = .success := by decide +kernel
theorem unsat10076 : Unsatisfiable (PosFin 65) f10076 := by
  apply lratCheckerSound f10076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10076
  · intro a ha; simp [p10076] at ha; subst a; trivial
  · exact checked10076
theorem derived10076 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10076 := by
  apply localUnsat_implies_entails f10076 [c9748, c10075, c2822, c2777, c2816, c10043, c8003, c10044, c5039, c5040, c5038, c789] c10076 unsat10076 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10075 := derived10075 a h
  have h2 : Entails.eval a c2822 := h 2821 (by decide)
  have h3 : Entails.eval a c2777 := h 2776 (by decide)
  have h4 : Entails.eval a c2816 := h 2815 (by decide)
  have h5 : Entails.eval a c10043 := derived10043 a h
  have h6 : Entails.eval a c8003 := derived8003 a h
  have h7 : Entails.eval a c10044 := derived10044 a h
  have h8 : Entails.eval a c5039 := h 5038 (by decide)
  have h9 : Entails.eval a c5040 := h 5039 (by decide)
  have h10 : Entails.eval a c5038 := h 5037 (by decide)
  have h11 : Entails.eval a c789 := h 788 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10077 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10077 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2784, some c10050, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10077 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10077 : lratChecker f10077 p10077 = .success := by decide +kernel
theorem unsat10077 : Unsatisfiable (PosFin 65) f10077 := by
  apply lratCheckerSound f10077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10077
  · intro a ha; simp [p10077] at ha; subst a; trivial
  · exact checked10077
theorem derived10077 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10077 := by
  apply localUnsat_implies_entails f10077 [c2784, c10050] c10077 unsat10077 (by rfl) a
  have h0 : Entails.eval a c2784 := h 2783 (by decide)
  have h1 : Entails.eval a c10050 := derived10050 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10078 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10078 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10040, some c1595, some c1594, some c4266, some c1616, some c4249, some c9907, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10078 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10078 : lratChecker f10078 p10078 = .success := by decide +kernel
theorem unsat10078 : Unsatisfiable (PosFin 65) f10078 := by
  apply lratCheckerSound f10078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10078
  · intro a ha; simp [p10078] at ha; subst a; trivial
  · exact checked10078
theorem derived10078 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10078 := by
  apply localUnsat_implies_entails f10078 [c9748, c10040, c1595, c1594, c4266, c1616, c4249, c9907] c10078 unsat10078 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10040 := derived10040 a h
  have h2 : Entails.eval a c1595 := h 1594 (by decide)
  have h3 : Entails.eval a c1594 := h 1593 (by decide)
  have h4 : Entails.eval a c4266 := h 4265 (by decide)
  have h5 : Entails.eval a c1616 := h 1615 (by decide)
  have h6 : Entails.eval a c4249 := h 4248 (by decide)
  have h7 : Entails.eval a c9907 := derived9907 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10079 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10079 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10077, some c9880, some c10076, some c4395, some c4394, some c2638, some c10078, some c10044, some c10043, some c10066, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10079 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10079 : lratChecker f10079 p10079 = .success := by decide +kernel
theorem unsat10079 : Unsatisfiable (PosFin 65) f10079 := by
  apply lratCheckerSound f10079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10079
  · intro a ha; simp [p10079] at ha; subst a; trivial
  · exact checked10079
theorem derived10079 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10079 := by
  apply localUnsat_implies_entails f10079 [c10077, c9880, c10076, c4395, c4394, c2638, c10078, c10044, c10043, c10066] c10079 unsat10079 (by rfl) a
  have h0 : Entails.eval a c10077 := derived10077 a h
  have h1 : Entails.eval a c9880 := derived9880 a h
  have h2 : Entails.eval a c10076 := derived10076 a h
  have h3 : Entails.eval a c4395 := h 4394 (by decide)
  have h4 : Entails.eval a c4394 := h 4393 (by decide)
  have h5 : Entails.eval a c2638 := h 2637 (by decide)
  have h6 : Entails.eval a c10078 := derived10078 a h
  have h7 : Entails.eval a c10044 := derived10044 a h
  have h8 : Entails.eval a c10043 := derived10043 a h
  have h9 : Entails.eval a c10066 := derived10066 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10080 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10080 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3705, some c3755, some c2983, some c3431, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p10080 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10080 : lratChecker f10080 p10080 = .success := by decide +kernel
theorem unsat10080 : Unsatisfiable (PosFin 65) f10080 := by
  apply lratCheckerSound f10080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10080
  · intro a ha; simp [p10080] at ha; subst a; trivial
  · exact checked10080
theorem derived10080 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10080 := by
  apply localUnsat_implies_entails f10080 [c3705, c3755, c2983, c3431] c10080 unsat10080 (by rfl) a
  have h0 : Entails.eval a c3705 := h 3704 (by decide)
  have h1 : Entails.eval a c3755 := h 3754 (by decide)
  have h2 : Entails.eval a c2983 := h 2982 (by decide)
  have h3 : Entails.eval a c3431 := h 3430 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10081 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10081 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2766, some c2767, some c2769, some c781, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10081 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10081 : lratChecker f10081 p10081 = .success := by decide +kernel
theorem unsat10081 : Unsatisfiable (PosFin 65) f10081 := by
  apply lratCheckerSound f10081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10081
  · intro a ha; simp [p10081] at ha; subst a; trivial
  · exact checked10081
theorem derived10081 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10081 := by
  apply localUnsat_implies_entails f10081 [c2766, c2767, c2769, c781] c10081 unsat10081 (by rfl) a
  have h0 : Entails.eval a c2766 := h 2765 (by decide)
  have h1 : Entails.eval a c2767 := h 2766 (by decide)
  have h2 : Entails.eval a c2769 := h 2768 (by decide)
  have h3 : Entails.eval a c781 := h 780 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10082 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10082 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3695, some c2968, some c3749, some c3427, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p10082 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10082 : lratChecker f10082 p10082 = .success := by decide +kernel
theorem unsat10082 : Unsatisfiable (PosFin 65) f10082 := by
  apply lratCheckerSound f10082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10082
  · intro a ha; simp [p10082] at ha; subst a; trivial
  · exact checked10082
theorem derived10082 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10082 := by
  apply localUnsat_implies_entails f10082 [c3695, c2968, c3749, c3427] c10082 unsat10082 (by rfl) a
  have h0 : Entails.eval a c3695 := h 3694 (by decide)
  have h1 : Entails.eval a c2968 := h 2967 (by decide)
  have h2 : Entails.eval a c3749 := h 3748 (by decide)
  have h3 : Entails.eval a c3427 := h 3426 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10083 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10083 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10080, some c771, some c10082, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p10083 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10083 : lratChecker f10083 p10083 = .success := by decide +kernel
theorem unsat10083 : Unsatisfiable (PosFin 65) f10083 := by
  apply lratCheckerSound f10083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10083
  · intro a ha; simp [p10083] at ha; subst a; trivial
  · exact checked10083
theorem derived10083 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10083 := by
  apply localUnsat_implies_entails f10083 [c10080, c771, c10082] c10083 unsat10083 (by rfl) a
  have h0 : Entails.eval a c10080 := derived10080 a h
  have h1 : Entails.eval a c771 := h 770 (by decide)
  have h2 : Entails.eval a c10082 := derived10082 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10084 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨30, by decide⟩, false), (⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨21, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10084 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c863, some c850, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p10084 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10084 : lratChecker f10084 p10084 = .success := by decide +kernel
theorem unsat10084 : Unsatisfiable (PosFin 65) f10084 := by
  apply lratCheckerSound f10084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10084
  · intro a ha; simp [p10084] at ha; subst a; trivial
  · exact checked10084
theorem derived10084 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10084 := by
  apply localUnsat_implies_entails f10084 [c863, c850] c10084 unsat10084 (by rfl) a
  have h0 : Entails.eval a c863 := h 862 (by decide)
  have h1 : Entails.eval a c850 := h 849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10085 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10085 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2782, some c2777, some c8003, some c10081, some c10083, some c2765, some c2762, some c2768, some c781, some c784, some c2764, some c2761, some c794, some c773, some c811, some c810, some c801, some c2763, some c10084, some c2932, some c2933, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10085 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked10085 : lratChecker f10085 p10085 = .success := by decide +kernel
theorem unsat10085 : Unsatisfiable (PosFin 65) f10085 := by
  apply lratCheckerSound f10085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10085
  · intro a ha; simp [p10085] at ha; subst a; trivial
  · exact checked10085
theorem derived10085 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10085 := by
  apply localUnsat_implies_entails f10085 [c9748, c2782, c2777, c8003, c10081, c10083, c2765, c2762, c2768, c781, c784, c2764, c2761, c794, c773, c811, c810, c801, c2763, c10084, c2932, c2933] c10085 unsat10085 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2782 := h 2781 (by decide)
  have h2 : Entails.eval a c2777 := h 2776 (by decide)
  have h3 : Entails.eval a c8003 := derived8003 a h
  have h4 : Entails.eval a c10081 := derived10081 a h
  have h5 : Entails.eval a c10083 := derived10083 a h
  have h6 : Entails.eval a c2765 := h 2764 (by decide)
  have h7 : Entails.eval a c2762 := h 2761 (by decide)
  have h8 : Entails.eval a c2768 := h 2767 (by decide)
  have h9 : Entails.eval a c781 := h 780 (by decide)
  have h10 : Entails.eval a c784 := h 783 (by decide)
  have h11 : Entails.eval a c2764 := h 2763 (by decide)
  have h12 : Entails.eval a c2761 := h 2760 (by decide)
  have h13 : Entails.eval a c794 := h 793 (by decide)
  have h14 : Entails.eval a c773 := h 772 (by decide)
  have h15 : Entails.eval a c811 := h 810 (by decide)
  have h16 : Entails.eval a c810 := h 809 (by decide)
  have h17 : Entails.eval a c801 := h 800 (by decide)
  have h18 : Entails.eval a c2763 := h 2762 (by decide)
  have h19 : Entails.eval a c10084 := derived10084 a h
  have h20 : Entails.eval a c2932 := h 2931 (by decide)
  have h21 : Entails.eval a c2933 := h 2932 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10086 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10086 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10069, some c10077, some c10075, some c2778, some c2777, some c10085, some c4693, some c1817, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10086 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10086 : lratChecker f10086 p10086 = .success := by decide +kernel
theorem unsat10086 : Unsatisfiable (PosFin 65) f10086 := by
  apply lratCheckerSound f10086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10086
  · intro a ha; simp [p10086] at ha; subst a; trivial
  · exact checked10086
theorem derived10086 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10086 := by
  apply localUnsat_implies_entails f10086 [c9748, c10069, c10077, c10075, c2778, c2777, c10085, c4693, c1817] c10086 unsat10086 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10069 := derived10069 a h
  have h2 : Entails.eval a c10077 := derived10077 a h
  have h3 : Entails.eval a c10075 := derived10075 a h
  have h4 : Entails.eval a c2778 := h 2777 (by decide)
  have h5 : Entails.eval a c2777 := h 2776 (by decide)
  have h6 : Entails.eval a c10085 := derived10085 a h
  have h7 : Entails.eval a c4693 := h 4692 (by decide)
  have h8 : Entails.eval a c1817 := h 1816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10087 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10087 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4302, some c4301, some c4299, some c10081, some c10083, some c2765, some c4272, some c2768, some c1551, some c2919, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10087 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10087 : lratChecker f10087 p10087 = .success := by decide +kernel
theorem unsat10087 : Unsatisfiable (PosFin 65) f10087 := by
  apply lratCheckerSound f10087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10087
  · intro a ha; simp [p10087] at ha; subst a; trivial
  · exact checked10087
theorem derived10087 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10087 := by
  apply localUnsat_implies_entails f10087 [c9748, c4302, c4301, c4299, c10081, c10083, c2765, c4272, c2768, c1551, c2919] c10087 unsat10087 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4302 := h 4301 (by decide)
  have h2 : Entails.eval a c4301 := h 4300 (by decide)
  have h3 : Entails.eval a c4299 := h 4298 (by decide)
  have h4 : Entails.eval a c10081 := derived10081 a h
  have h5 : Entails.eval a c10083 := derived10083 a h
  have h6 : Entails.eval a c2765 := h 2764 (by decide)
  have h7 : Entails.eval a c4272 := h 4271 (by decide)
  have h8 : Entails.eval a c2768 := h 2767 (by decide)
  have h9 : Entails.eval a c1551 := h 1550 (by decide)
  have h10 : Entails.eval a c2919 := h 2918 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10088 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10088 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10069, some c10072, some c10077, some c10079, some c10086, some c4301, some c4302, some c4299, some c4315, some c10087, some c10055, some c10056, some c10066, some c4271, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10088 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10088 : lratChecker f10088 p10088 = .success := by decide +kernel
theorem unsat10088 : Unsatisfiable (PosFin 65) f10088 := by
  apply lratCheckerSound f10088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10088
  · intro a ha; simp [p10088] at ha; subst a; trivial
  · exact checked10088
theorem derived10088 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10088 := by
  apply localUnsat_implies_entails f10088 [c10069, c10072, c10077, c10079, c10086, c4301, c4302, c4299, c4315, c10087, c10055, c10056, c10066, c4271] c10088 unsat10088 (by rfl) a
  have h0 : Entails.eval a c10069 := derived10069 a h
  have h1 : Entails.eval a c10072 := derived10072 a h
  have h2 : Entails.eval a c10077 := derived10077 a h
  have h3 : Entails.eval a c10079 := derived10079 a h
  have h4 : Entails.eval a c10086 := derived10086 a h
  have h5 : Entails.eval a c4301 := h 4300 (by decide)
  have h6 : Entails.eval a c4302 := h 4301 (by decide)
  have h7 : Entails.eval a c4299 := h 4298 (by decide)
  have h8 : Entails.eval a c4315 := h 4314 (by decide)
  have h9 : Entails.eval a c10087 := derived10087 a h
  have h10 : Entails.eval a c10055 := derived10055 a h
  have h11 : Entails.eval a c10056 := derived10056 a h
  have h12 : Entails.eval a c10066 := derived10066 a h
  have h13 : Entails.eval a c4271 := h 4270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10089 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨52, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10089 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4308, some c4685, some c1803, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10089 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10089 : lratChecker f10089 p10089 = .success := by decide +kernel
theorem unsat10089 : Unsatisfiable (PosFin 65) f10089 := by
  apply lratCheckerSound f10089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10089
  · intro a ha; simp [p10089] at ha; subst a; trivial
  · exact checked10089
theorem derived10089 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10089 := by
  apply localUnsat_implies_entails f10089 [c9748, c4308, c4685, c1803] c10089 unsat10089 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4308 := h 4307 (by decide)
  have h2 : Entails.eval a c4685 := h 4684 (by decide)
  have h3 : Entails.eval a c1803 := h 1802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10090 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10090 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10069, some c10088, some c10089, some c3485, some c5100, some c5083, some c2253, some c2249, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10090 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10090 : lratChecker f10090 p10090 = .success := by decide +kernel
theorem unsat10090 : Unsatisfiable (PosFin 65) f10090 := by
  apply lratCheckerSound f10090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10090
  · intro a ha; simp [p10090] at ha; subst a; trivial
  · exact checked10090
theorem derived10090 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10090 := by
  apply localUnsat_implies_entails f10090 [c9748, c10069, c10088, c10089, c3485, c5100, c5083, c2253, c2249] c10090 unsat10090 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10069 := derived10069 a h
  have h2 : Entails.eval a c10088 := derived10088 a h
  have h3 : Entails.eval a c10089 := derived10089 a h
  have h4 : Entails.eval a c3485 := h 3484 (by decide)
  have h5 : Entails.eval a c5100 := h 5099 (by decide)
  have h6 : Entails.eval a c5083 := h 5082 (by decide)
  have h7 : Entails.eval a c2253 := h 2252 (by decide)
  have h8 : Entails.eval a c2249 := h 2248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10091 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨63, by decide⟩, true), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10091 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2778, some c10085, some c3025, some c3051, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10091 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10091 : lratChecker f10091 p10091 = .success := by decide +kernel
theorem unsat10091 : Unsatisfiable (PosFin 65) f10091 := by
  apply lratCheckerSound f10091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10091
  · intro a ha; simp [p10091] at ha; subst a; trivial
  · exact checked10091
theorem derived10091 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10091 := by
  apply localUnsat_implies_entails f10091 [c2778, c10085, c3025, c3051] c10091 unsat10091 (by rfl) a
  have h0 : Entails.eval a c2778 := h 2777 (by decide)
  have h1 : Entails.eval a c10085 := derived10085 a h
  have h2 : Entails.eval a c3025 := h 3024 (by decide)
  have h3 : Entails.eval a c3051 := h 3050 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10092 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨63, by decide⟩, true), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10092 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2778, some c2777, some c2782, some c8003, some c10091, some c4139, some c9874, some c10043, some c10081, some c5039, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10092 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10092 : lratChecker f10092 p10092 = .success := by decide +kernel
theorem unsat10092 : Unsatisfiable (PosFin 65) f10092 := by
  apply lratCheckerSound f10092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10092
  · intro a ha; simp [p10092] at ha; subst a; trivial
  · exact checked10092
theorem derived10092 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10092 := by
  apply localUnsat_implies_entails f10092 [c9748, c2778, c2777, c2782, c8003, c10091, c4139, c9874, c10043, c10081, c5039] c10092 unsat10092 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2778 := h 2777 (by decide)
  have h2 : Entails.eval a c2777 := h 2776 (by decide)
  have h3 : Entails.eval a c2782 := h 2781 (by decide)
  have h4 : Entails.eval a c8003 := derived8003 a h
  have h5 : Entails.eval a c10091 := derived10091 a h
  have h6 : Entails.eval a c4139 := h 4138 (by decide)
  have h7 : Entails.eval a c9874 := derived9874 a h
  have h8 : Entails.eval a c10043 := derived10043 a h
  have h9 : Entails.eval a c10081 := derived10081 a h
  have h10 : Entails.eval a c5039 := h 5038 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10093 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10093 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1829, some c1836, some c1851, some c1850, some c775, some c1864, some c800, some c773, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10093 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10093 : lratChecker f10093 p10093 = .success := by decide +kernel
theorem unsat10093 : Unsatisfiable (PosFin 65) f10093 := by
  apply lratCheckerSound f10093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10093
  · intro a ha; simp [p10093] at ha; subst a; trivial
  · exact checked10093
theorem derived10093 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10093 := by
  apply localUnsat_implies_entails f10093 [c9748, c1829, c1836, c1851, c1850, c775, c1864, c800, c773] c10093 unsat10093 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1829 := h 1828 (by decide)
  have h2 : Entails.eval a c1836 := h 1835 (by decide)
  have h3 : Entails.eval a c1851 := h 1850 (by decide)
  have h4 : Entails.eval a c1850 := h 1849 (by decide)
  have h5 : Entails.eval a c775 := h 774 (by decide)
  have h6 : Entails.eval a c1864 := h 1863 (by decide)
  have h7 : Entails.eval a c800 := h 799 (by decide)
  have h8 : Entails.eval a c773 := h 772 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10094 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10094 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1830, some c1832, some c1851, some c781, some c799, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p10094 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10094 : lratChecker f10094 p10094 = .success := by decide +kernel
theorem unsat10094 : Unsatisfiable (PosFin 65) f10094 := by
  apply lratCheckerSound f10094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10094
  · intro a ha; simp [p10094] at ha; subst a; trivial
  · exact checked10094
theorem derived10094 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10094 := by
  apply localUnsat_implies_entails f10094 [c9748, c1830, c1832, c1851, c781, c799] c10094 unsat10094 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1830 := h 1829 (by decide)
  have h2 : Entails.eval a c1832 := h 1831 (by decide)
  have h3 : Entails.eval a c1851 := h 1850 (by decide)
  have h4 : Entails.eval a c781 := h 780 (by decide)
  have h5 : Entails.eval a c799 := h 798 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10095 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨63, by decide⟩, true), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10095 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10092, some c1898, some c1909, some c1890, some c1888, some c10093, some c10073, some c1827, some c10094, some c771, some c9874, some c10082, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10095 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10095 : lratChecker f10095 p10095 = .success := by decide +kernel
theorem unsat10095 : Unsatisfiable (PosFin 65) f10095 := by
  apply lratCheckerSound f10095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10095
  · intro a ha; simp [p10095] at ha; subst a; trivial
  · exact checked10095
theorem derived10095 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10095 := by
  apply localUnsat_implies_entails f10095 [c9748, c10092, c1898, c1909, c1890, c1888, c10093, c10073, c1827, c10094, c771, c9874, c10082] c10095 unsat10095 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10092 := derived10092 a h
  have h2 : Entails.eval a c1898 := h 1897 (by decide)
  have h3 : Entails.eval a c1909 := h 1908 (by decide)
  have h4 : Entails.eval a c1890 := h 1889 (by decide)
  have h5 : Entails.eval a c1888 := h 1887 (by decide)
  have h6 : Entails.eval a c10093 := derived10093 a h
  have h7 : Entails.eval a c10073 := derived10073 a h
  have h8 : Entails.eval a c1827 := h 1826 (by decide)
  have h9 : Entails.eval a c10094 := derived10094 a h
  have h10 : Entails.eval a c771 := h 770 (by decide)
  have h11 : Entails.eval a c9874 := derived9874 a h
  have h12 : Entails.eval a c10082 := derived10082 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10096 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨16, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10096 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4302, some c4301, some c4299, some c10083, some c2765, some c4272, some c2768, some c2919, some c3758, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10096 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10096 : lratChecker f10096 p10096 = .success := by decide +kernel
theorem unsat10096 : Unsatisfiable (PosFin 65) f10096 := by
  apply lratCheckerSound f10096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10096
  · intro a ha; simp [p10096] at ha; subst a; trivial
  · exact checked10096
theorem derived10096 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10096 := by
  apply localUnsat_implies_entails f10096 [c4302, c4301, c4299, c10083, c2765, c4272, c2768, c2919, c3758] c10096 unsat10096 (by rfl) a
  have h0 : Entails.eval a c4302 := h 4301 (by decide)
  have h1 : Entails.eval a c4301 := h 4300 (by decide)
  have h2 : Entails.eval a c4299 := h 4298 (by decide)
  have h3 : Entails.eval a c10083 := derived10083 a h
  have h4 : Entails.eval a c2765 := h 2764 (by decide)
  have h5 : Entails.eval a c4272 := h 4271 (by decide)
  have h6 : Entails.eval a c2768 := h 2767 (by decide)
  have h7 : Entails.eval a c2919 := h 2918 (by decide)
  have h8 : Entails.eval a c3758 := h 3757 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10097 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10097 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4302, some c4301, some c4299, some c10081, some c10096, some c9874, some c10043, some c5039, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10097 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10097 : lratChecker f10097 p10097 = .success := by decide +kernel
theorem unsat10097 : Unsatisfiable (PosFin 65) f10097 := by
  apply lratCheckerSound f10097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10097
  · intro a ha; simp [p10097] at ha; subst a; trivial
  · exact checked10097
theorem derived10097 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10097 := by
  apply localUnsat_implies_entails f10097 [c4302, c4301, c4299, c10081, c10096, c9874, c10043, c5039] c10097 unsat10097 (by rfl) a
  have h0 : Entails.eval a c4302 := h 4301 (by decide)
  have h1 : Entails.eval a c4301 := h 4300 (by decide)
  have h2 : Entails.eval a c4299 := h 4298 (by decide)
  have h3 : Entails.eval a c10081 := derived10081 a h
  have h4 : Entails.eval a c10096 := derived10096 a h
  have h5 : Entails.eval a c9874 := derived9874 a h
  have h6 : Entails.eval a c10043 := derived10043 a h
  have h7 : Entails.eval a c5039 := h 5038 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10098 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10098 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4302, some c4301, some c4299, some c4271, some c4272, some c960, some c4276, some c4284, some c755, some c800, some c2304, some c4014, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10098 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10098 : lratChecker f10098 p10098 = .success := by decide +kernel
theorem unsat10098 : Unsatisfiable (PosFin 65) f10098 := by
  apply lratCheckerSound f10098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10098
  · intro a ha; simp [p10098] at ha; subst a; trivial
  · exact checked10098
theorem derived10098 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10098 := by
  apply localUnsat_implies_entails f10098 [c9748, c4302, c4301, c4299, c4271, c4272, c960, c4276, c4284, c755, c800, c2304, c4014] c10098 unsat10098 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4302 := h 4301 (by decide)
  have h2 : Entails.eval a c4301 := h 4300 (by decide)
  have h3 : Entails.eval a c4299 := h 4298 (by decide)
  have h4 : Entails.eval a c4271 := h 4270 (by decide)
  have h5 : Entails.eval a c4272 := h 4271 (by decide)
  have h6 : Entails.eval a c960 := h 959 (by decide)
  have h7 : Entails.eval a c4276 := h 4275 (by decide)
  have h8 : Entails.eval a c4284 := h 4283 (by decide)
  have h9 : Entails.eval a c755 := h 754 (by decide)
  have h10 : Entails.eval a c800 := h 799 (by decide)
  have h11 : Entails.eval a c2304 := h 2303 (by decide)
  have h12 : Entails.eval a c4014 := h 4013 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10099 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10099 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10090, some c10095, some c4301, some c4302, some c4299, some c4315, some c10097, some c10098, some c10066, some c4266, some c772, some c733, some c805, some c771, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10099 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10099 : lratChecker f10099 p10099 = .success := by decide +kernel
theorem unsat10099 : Unsatisfiable (PosFin 65) f10099 := by
  apply lratCheckerSound f10099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10099
  · intro a ha; simp [p10099] at ha; subst a; trivial
  · exact checked10099
theorem derived10099 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10099 := by
  apply localUnsat_implies_entails f10099 [c10090, c10095, c4301, c4302, c4299, c4315, c10097, c10098, c10066, c4266, c772, c733, c805, c771] c10099 unsat10099 (by rfl) a
  have h0 : Entails.eval a c10090 := derived10090 a h
  have h1 : Entails.eval a c10095 := derived10095 a h
  have h2 : Entails.eval a c4301 := h 4300 (by decide)
  have h3 : Entails.eval a c4302 := h 4301 (by decide)
  have h4 : Entails.eval a c4299 := h 4298 (by decide)
  have h5 : Entails.eval a c4315 := h 4314 (by decide)
  have h6 : Entails.eval a c10097 := derived10097 a h
  have h7 : Entails.eval a c10098 := derived10098 a h
  have h8 : Entails.eval a c10066 := derived10066 a h
  have h9 : Entails.eval a c4266 := h 4265 (by decide)
  have h10 : Entails.eval a c772 := h 771 (by decide)
  have h11 : Entails.eval a c733 := h 732 (by decide)
  have h12 : Entails.eval a c805 := h 804 (by decide)
  have h13 : Entails.eval a c771 := h 770 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10100 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10100 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10090, some c10099, some c4130, some c3742, some c2755, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10100 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10100 : lratChecker f10100 p10100 = .success := by decide +kernel
theorem unsat10100 : Unsatisfiable (PosFin 65) f10100 := by
  apply lratCheckerSound f10100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10100
  · intro a ha; simp [p10100] at ha; subst a; trivial
  · exact checked10100
theorem derived10100 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10100 := by
  apply localUnsat_implies_entails f10100 [c10090, c10099, c4130, c3742, c2755] c10100 unsat10100 (by rfl) a
  have h0 : Entails.eval a c10090 := derived10090 a h
  have h1 : Entails.eval a c10099 := derived10099 a h
  have h2 : Entails.eval a c4130 := h 4129 (by decide)
  have h3 : Entails.eval a c3742 := h 3741 (by decide)
  have h4 : Entails.eval a c2755 := h 2754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10101 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨63, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10101 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10100, some c1732, some c1730, some c1741, some c10090, some c10068, some c4139, some c9874, some c10043, some c10042, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10101 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10101 : lratChecker f10101 p10101 = .success := by decide +kernel
theorem unsat10101 : Unsatisfiable (PosFin 65) f10101 := by
  apply lratCheckerSound f10101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10101
  · intro a ha; simp [p10101] at ha; subst a; trivial
  · exact checked10101
theorem derived10101 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10101 := by
  apply localUnsat_implies_entails f10101 [c9748, c10100, c1732, c1730, c1741, c10090, c10068, c4139, c9874, c10043, c10042] c10101 unsat10101 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10100 := derived10100 a h
  have h2 : Entails.eval a c1732 := h 1731 (by decide)
  have h3 : Entails.eval a c1730 := h 1729 (by decide)
  have h4 : Entails.eval a c1741 := h 1740 (by decide)
  have h5 : Entails.eval a c10090 := derived10090 a h
  have h6 : Entails.eval a c10068 := derived10068 a h
  have h7 : Entails.eval a c4139 := h 4138 (by decide)
  have h8 : Entails.eval a c9874 := derived9874 a h
  have h9 : Entails.eval a c10043 := derived10043 a h
  have h10 : Entails.eval a c10042 := derived10042 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10102 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10102 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1672, some c1676, some c1836, some c10046, some c10063, some c1851, some c1850, some c4237, some c378, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10102 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10102 : lratChecker f10102 p10102 = .success := by decide +kernel
theorem unsat10102 : Unsatisfiable (PosFin 65) f10102 := by
  apply lratCheckerSound f10102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10102
  · intro a ha; simp [p10102] at ha; subst a; trivial
  · exact checked10102
theorem derived10102 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10102 := by
  apply localUnsat_implies_entails f10102 [c9748, c1672, c1676, c1836, c10046, c10063, c1851, c1850, c4237, c378] c10102 unsat10102 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1672 := h 1671 (by decide)
  have h2 : Entails.eval a c1676 := h 1675 (by decide)
  have h3 : Entails.eval a c1836 := h 1835 (by decide)
  have h4 : Entails.eval a c10046 := derived10046 a h
  have h5 : Entails.eval a c10063 := derived10063 a h
  have h6 : Entails.eval a c1851 := h 1850 (by decide)
  have h7 : Entails.eval a c1850 := h 1849 (by decide)
  have h8 : Entails.eval a c4237 := h 4236 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10103 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨63, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10103 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10100, some c10090, some c1732, some c1741, some c1730, some c10101, some c1909, some c10102, some c10042, some c10061, some c9874, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10103 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10103 : lratChecker f10103 p10103 = .success := by decide +kernel
theorem unsat10103 : Unsatisfiable (PosFin 65) f10103 := by
  apply lratCheckerSound f10103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10103
  · intro a ha; simp [p10103] at ha; subst a; trivial
  · exact checked10103
theorem derived10103 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10103 := by
  apply localUnsat_implies_entails f10103 [c9748, c10100, c10090, c1732, c1741, c1730, c10101, c1909, c10102, c10042, c10061, c9874] c10103 unsat10103 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10100 := derived10100 a h
  have h2 : Entails.eval a c10090 := derived10090 a h
  have h3 : Entails.eval a c1732 := h 1731 (by decide)
  have h4 : Entails.eval a c1741 := h 1740 (by decide)
  have h5 : Entails.eval a c1730 := h 1729 (by decide)
  have h6 : Entails.eval a c10101 := derived10101 a h
  have h7 : Entails.eval a c1909 := h 1908 (by decide)
  have h8 : Entails.eval a c10102 := derived10102 a h
  have h9 : Entails.eval a c10042 := derived10042 a h
  have h10 : Entails.eval a c10061 := derived10061 a h
  have h11 : Entails.eval a c9874 := derived9874 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10104 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10104 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4302, some c4301, some c4299, some c10066, some c4271, some c4272, some c960, some c4274, some c998, some c750, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10104 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10104 : lratChecker f10104 p10104 = .success := by decide +kernel
theorem unsat10104 : Unsatisfiable (PosFin 65) f10104 := by
  apply lratCheckerSound f10104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10104
  · intro a ha; simp [p10104] at ha; subst a; trivial
  · exact checked10104
theorem derived10104 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10104 := by
  apply localUnsat_implies_entails f10104 [c4302, c4301, c4299, c10066, c4271, c4272, c960, c4274, c998, c750] c10104 unsat10104 (by rfl) a
  have h0 : Entails.eval a c4302 := h 4301 (by decide)
  have h1 : Entails.eval a c4301 := h 4300 (by decide)
  have h2 : Entails.eval a c4299 := h 4298 (by decide)
  have h3 : Entails.eval a c10066 := derived10066 a h
  have h4 : Entails.eval a c4271 := h 4270 (by decide)
  have h5 : Entails.eval a c4272 := h 4271 (by decide)
  have h6 : Entails.eval a c960 := h 959 (by decide)
  have h7 : Entails.eval a c4274 := h 4273 (by decide)
  have h8 : Entails.eval a c998 := h 997 (by decide)
  have h9 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10105 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10105 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10100, some c10090, some c10103, some c4301, some c4302, some c4299, some c4315, some c10104, some c9874, some c10067, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10105 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10105 : lratChecker f10105 p10105 = .success := by decide +kernel
theorem unsat10105 : Unsatisfiable (PosFin 65) f10105 := by
  apply lratCheckerSound f10105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10105
  · intro a ha; simp [p10105] at ha; subst a; trivial
  · exact checked10105
theorem derived10105 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10105 := by
  apply localUnsat_implies_entails f10105 [c10100, c10090, c10103, c4301, c4302, c4299, c4315, c10104, c9874, c10067] c10105 unsat10105 (by rfl) a
  have h0 : Entails.eval a c10100 := derived10100 a h
  have h1 : Entails.eval a c10090 := derived10090 a h
  have h2 : Entails.eval a c10103 := derived10103 a h
  have h3 : Entails.eval a c4301 := h 4300 (by decide)
  have h4 : Entails.eval a c4302 := h 4301 (by decide)
  have h5 : Entails.eval a c4299 := h 4298 (by decide)
  have h6 : Entails.eval a c4315 := h 4314 (by decide)
  have h7 : Entails.eval a c10104 := derived10104 a h
  have h8 : Entails.eval a c9874 := derived9874 a h
  have h9 : Entails.eval a c10067 := derived10067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10106 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10106 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10090, some c10105, some c4130, some c3047, some c3019, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10106 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10106 : lratChecker f10106 p10106 = .success := by decide +kernel
theorem unsat10106 : Unsatisfiable (PosFin 65) f10106 := by
  apply lratCheckerSound f10106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10106
  · intro a ha; simp [p10106] at ha; subst a; trivial
  · exact checked10106
theorem derived10106 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10106 := by
  apply localUnsat_implies_entails f10106 [c10090, c10105, c4130, c3047, c3019] c10106 unsat10106 (by rfl) a
  have h0 : Entails.eval a c10090 := derived10090 a h
  have h1 : Entails.eval a c10105 := derived10105 a h
  have h2 : Entails.eval a c4130 := h 4129 (by decide)
  have h3 : Entails.eval a c3047 := h 3046 (by decide)
  have h4 : Entails.eval a c3019 := h 3018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10107 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10107 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3049, some c2961, some c4301, some c4291, some c2635, some c3024, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10107 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10107 : lratChecker f10107 p10107 = .success := by decide +kernel
theorem unsat10107 : Unsatisfiable (PosFin 65) f10107 := by
  apply lratCheckerSound f10107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10107
  · intro a ha; simp [p10107] at ha; subst a; trivial
  · exact checked10107
theorem derived10107 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10107 := by
  apply localUnsat_implies_entails f10107 [c3049, c2961, c4301, c4291, c2635, c3024] c10107 unsat10107 (by rfl) a
  have h0 : Entails.eval a c3049 := h 3048 (by decide)
  have h1 : Entails.eval a c2961 := h 2960 (by decide)
  have h2 : Entails.eval a c4301 := h 4300 (by decide)
  have h3 : Entails.eval a c4291 := h 4290 (by decide)
  have h4 : Entails.eval a c2635 := h 2634 (by decide)
  have h5 : Entails.eval a c3024 := h 3023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10108 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10108 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10090, some c10107, some c10106, some c10089, some c4130, some c3047, some c3019, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10108 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10108 : lratChecker f10108 p10108 = .success := by decide +kernel
theorem unsat10108 : Unsatisfiable (PosFin 65) f10108 := by
  apply lratCheckerSound f10108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10108
  · intro a ha; simp [p10108] at ha; subst a; trivial
  · exact checked10108
theorem derived10108 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10108 := by
  apply localUnsat_implies_entails f10108 [c10090, c10107, c10106, c10089, c4130, c3047, c3019] c10108 unsat10108 (by rfl) a
  have h0 : Entails.eval a c10090 := derived10090 a h
  have h1 : Entails.eval a c10107 := derived10107 a h
  have h2 : Entails.eval a c10106 := derived10106 a h
  have h3 : Entails.eval a c10089 := derived10089 a h
  have h4 : Entails.eval a c4130 := h 4129 (by decide)
  have h5 : Entails.eval a c3047 := h 3046 (by decide)
  have h6 : Entails.eval a c3019 := h 3018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10109 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10109 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4687, some c2255, some c2364, some c5108, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10109 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10109 : lratChecker f10109 p10109 = .success := by decide +kernel
theorem unsat10109 : Unsatisfiable (PosFin 65) f10109 := by
  apply lratCheckerSound f10109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10109
  · intro a ha; simp [p10109] at ha; subst a; trivial
  · exact checked10109
theorem derived10109 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10109 := by
  apply localUnsat_implies_entails f10109 [c9748, c4687, c2255, c2364, c5108] c10109 unsat10109 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4687 := h 4686 (by decide)
  have h2 : Entails.eval a c2255 := h 2254 (by decide)
  have h3 : Entails.eval a c2364 := h 2363 (by decide)
  have h4 : Entails.eval a c5108 := h 5107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10110 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10110 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10109, some c10021, some c10108, some c4680, some c4304, some c3542, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10110 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10110 : lratChecker f10110 p10110 = .success := by decide +kernel
theorem unsat10110 : Unsatisfiable (PosFin 65) f10110 := by
  apply lratCheckerSound f10110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10110
  · intro a ha; simp [p10110] at ha; subst a; trivial
  · exact checked10110
theorem derived10110 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10110 := by
  apply localUnsat_implies_entails f10110 [c10109, c10021, c10108, c4680, c4304, c3542] c10110 unsat10110 (by rfl) a
  have h0 : Entails.eval a c10109 := derived10109 a h
  have h1 : Entails.eval a c10021 := derived10021 a h
  have h2 : Entails.eval a c10108 := derived10108 a h
  have h3 : Entails.eval a c4680 := h 4679 (by decide)
  have h4 : Entails.eval a c4304 := h 4303 (by decide)
  have h5 : Entails.eval a c3542 := h 3541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10111 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨9, by decide⟩, false), (⟨61, by decide⟩, false), (⟨57, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10111 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4688, some c2365, some c2903, some c3486, some c3489, some c10089, some c3529, some c2626, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10111 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10111 : lratChecker f10111 p10111 = .success := by decide +kernel
theorem unsat10111 : Unsatisfiable (PosFin 65) f10111 := by
  apply lratCheckerSound f10111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10111
  · intro a ha; simp [p10111] at ha; subst a; trivial
  · exact checked10111
theorem derived10111 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10111 := by
  apply localUnsat_implies_entails f10111 [c9748, c4688, c2365, c2903, c3486, c3489, c10089, c3529, c2626] c10111 unsat10111 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4688 := h 4687 (by decide)
  have h2 : Entails.eval a c2365 := h 2364 (by decide)
  have h3 : Entails.eval a c2903 := h 2902 (by decide)
  have h4 : Entails.eval a c3486 := h 3485 (by decide)
  have h5 : Entails.eval a c3489 := h 3488 (by decide)
  have h6 : Entails.eval a c10089 := derived10089 a h
  have h7 : Entails.eval a c3529 := h 3528 (by decide)
  have h8 : Entails.eval a c2626 := h 2625 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10112 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨14, by decide⟩, true), (⟨61, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10112 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4306, some c1800, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10112 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10112 : lratChecker f10112 p10112 = .success := by decide +kernel
theorem unsat10112 : Unsatisfiable (PosFin 65) f10112 := by
  apply lratCheckerSound f10112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10112
  · intro a ha; simp [p10112] at ha; subst a; trivial
  · exact checked10112
theorem derived10112 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10112 := by
  apply localUnsat_implies_entails f10112 [c9748, c4306, c1800] c10112 unsat10112 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4306 := h 4305 (by decide)
  have h2 : Entails.eval a c1800 := h 1799 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10113 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10113 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10021, some c10109, some c10110, some c4688, some c2365, some c3410, some c3013, some c10111, some c4136, some c4137, some c4139, some c10112, some c10089, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10113 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10113 : lratChecker f10113 p10113 = .success := by decide +kernel
theorem unsat10113 : Unsatisfiable (PosFin 65) f10113 := by
  apply lratCheckerSound f10113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10113
  · intro a ha; simp [p10113] at ha; subst a; trivial
  · exact checked10113
theorem derived10113 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10113 := by
  apply localUnsat_implies_entails f10113 [c9748, c10021, c10109, c10110, c4688, c2365, c3410, c3013, c10111, c4136, c4137, c4139, c10112, c10089] c10113 unsat10113 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10021 := derived10021 a h
  have h2 : Entails.eval a c10109 := derived10109 a h
  have h3 : Entails.eval a c10110 := derived10110 a h
  have h4 : Entails.eval a c4688 := h 4687 (by decide)
  have h5 : Entails.eval a c2365 := h 2364 (by decide)
  have h6 : Entails.eval a c3410 := h 3409 (by decide)
  have h7 : Entails.eval a c3013 := h 3012 (by decide)
  have h8 : Entails.eval a c10111 := derived10111 a h
  have h9 : Entails.eval a c4136 := h 4135 (by decide)
  have h10 : Entails.eval a c4137 := h 4136 (by decide)
  have h11 : Entails.eval a c4139 := h 4138 (by decide)
  have h12 : Entails.eval a c10112 := derived10112 a h
  have h13 : Entails.eval a c10089 := derived10089 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10114 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10114 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4366, some c4365, some c4367, some c1703, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10114 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10114 : lratChecker f10114 p10114 = .success := by decide +kernel
theorem unsat10114 : Unsatisfiable (PosFin 65) f10114 := by
  apply lratCheckerSound f10114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10114
  · intro a ha; simp [p10114] at ha; subst a; trivial
  · exact checked10114
theorem derived10114 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10114 := by
  apply localUnsat_implies_entails f10114 [c9748, c4366, c4365, c4367, c1703] c10114 unsat10114 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4366 := h 4365 (by decide)
  have h2 : Entails.eval a c4365 := h 4364 (by decide)
  have h3 : Entails.eval a c4367 := h 4366 (by decide)
  have h4 : Entails.eval a c1703 := h 1702 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10115 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10115 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1672, some c4360, some c10063, some c4358, some c10114, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10115 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10115 : lratChecker f10115 p10115 = .success := by decide +kernel
theorem unsat10115 : Unsatisfiable (PosFin 65) f10115 := by
  apply lratCheckerSound f10115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10115
  · intro a ha; simp [p10115] at ha; subst a; trivial
  · exact checked10115
theorem derived10115 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10115 := by
  apply localUnsat_implies_entails f10115 [c9748, c1672, c4360, c10063, c4358, c10114] c10115 unsat10115 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1672 := h 1671 (by decide)
  have h2 : Entails.eval a c4360 := h 4359 (by decide)
  have h3 : Entails.eval a c10063 := derived10063 a h
  have h4 : Entails.eval a c4358 := h 4357 (by decide)
  have h5 : Entails.eval a c10114 := derived10114 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10116 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨63, by decide⟩, true), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10116 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10069, some c10086, some c4373, some c9364, some c1730, some c1731, some c10115, some c10061, some c4693, some c1817, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10116 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10116 : lratChecker f10116 p10116 = .success := by decide +kernel
theorem unsat10116 : Unsatisfiable (PosFin 65) f10116 := by
  apply lratCheckerSound f10116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10116
  · intro a ha; simp [p10116] at ha; subst a; trivial
  · exact checked10116
theorem derived10116 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10116 := by
  apply localUnsat_implies_entails f10116 [c9748, c10069, c10086, c4373, c9364, c1730, c1731, c10115, c10061, c4693, c1817] c10116 unsat10116 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10069 := derived10069 a h
  have h2 : Entails.eval a c10086 := derived10086 a h
  have h3 : Entails.eval a c4373 := h 4372 (by decide)
  have h4 : Entails.eval a c9364 := derived9364 a h
  have h5 : Entails.eval a c1730 := h 1729 (by decide)
  have h6 : Entails.eval a c1731 := h 1730 (by decide)
  have h7 : Entails.eval a c10115 := derived10115 a h
  have h8 : Entails.eval a c10061 := derived10061 a h
  have h9 : Entails.eval a c4693 := h 4692 (by decide)
  have h10 : Entails.eval a c1817 := h 1816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10117 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10117 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4302, some c4301, some c4299, some c10055, some c10056, some c10066, some c4271, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10117 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10117 : lratChecker f10117 p10117 = .success := by decide +kernel
theorem unsat10117 : Unsatisfiable (PosFin 65) f10117 := by
  apply lratCheckerSound f10117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10117
  · intro a ha; simp [p10117] at ha; subst a; trivial
  · exact checked10117
theorem derived10117 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10117 := by
  apply localUnsat_implies_entails f10117 [c4302, c4301, c4299, c10055, c10056, c10066, c4271] c10117 unsat10117 (by rfl) a
  have h0 : Entails.eval a c4302 := h 4301 (by decide)
  have h1 : Entails.eval a c4301 := h 4300 (by decide)
  have h2 : Entails.eval a c4299 := h 4298 (by decide)
  have h3 : Entails.eval a c10055 := derived10055 a h
  have h4 : Entails.eval a c10056 := derived10056 a h
  have h5 : Entails.eval a c10066 := derived10066 a h
  have h6 : Entails.eval a c4271 := h 4270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10118 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨63, by decide⟩, true), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10118 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10069, some c10116, some c4301, some c4302, some c4299, some c4315, some c10117, some c10087, some c10067, some c10066, some c4271, some c4272, some c740, some c4274, some c998, some c750, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10118 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked10118 : lratChecker f10118 p10118 = .success := by decide +kernel
theorem unsat10118 : Unsatisfiable (PosFin 65) f10118 := by
  apply lratCheckerSound f10118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10118
  · intro a ha; simp [p10118] at ha; subst a; trivial
  · exact checked10118
theorem derived10118 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10118 := by
  apply localUnsat_implies_entails f10118 [c10069, c10116, c4301, c4302, c4299, c4315, c10117, c10087, c10067, c10066, c4271, c4272, c740, c4274, c998, c750] c10118 unsat10118 (by rfl) a
  have h0 : Entails.eval a c10069 := derived10069 a h
  have h1 : Entails.eval a c10116 := derived10116 a h
  have h2 : Entails.eval a c4301 := h 4300 (by decide)
  have h3 : Entails.eval a c4302 := h 4301 (by decide)
  have h4 : Entails.eval a c4299 := h 4298 (by decide)
  have h5 : Entails.eval a c4315 := h 4314 (by decide)
  have h6 : Entails.eval a c10117 := derived10117 a h
  have h7 : Entails.eval a c10087 := derived10087 a h
  have h8 : Entails.eval a c10067 := derived10067 a h
  have h9 : Entails.eval a c10066 := derived10066 a h
  have h10 : Entails.eval a c4271 := h 4270 (by decide)
  have h11 : Entails.eval a c4272 := h 4271 (by decide)
  have h12 : Entails.eval a c740 := h 739 (by decide)
  have h13 : Entails.eval a c4274 := h 4273 (by decide)
  have h14 : Entails.eval a c998 := h 997 (by decide)
  have h15 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10119 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨63, by decide⟩, true), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10119 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10075, some c2777, some c2782, some c10043, some c8003, some c10081, some c771, some c796, some c2798, some c2795, some c2764, some c777, some c781, some c2805, some c2796, some c2797, some c2807, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10119 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked10119 : lratChecker f10119 p10119 = .success := by decide +kernel
theorem unsat10119 : Unsatisfiable (PosFin 65) f10119 := by
  apply lratCheckerSound f10119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10119
  · intro a ha; simp [p10119] at ha; subst a; trivial
  · exact checked10119
theorem derived10119 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10119 := by
  apply localUnsat_implies_entails f10119 [c9748, c10075, c2777, c2782, c10043, c8003, c10081, c771, c796, c2798, c2795, c2764, c777, c781, c2805, c2796, c2797, c2807] c10119 unsat10119 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10075 := derived10075 a h
  have h2 : Entails.eval a c2777 := h 2776 (by decide)
  have h3 : Entails.eval a c2782 := h 2781 (by decide)
  have h4 : Entails.eval a c10043 := derived10043 a h
  have h5 : Entails.eval a c8003 := derived8003 a h
  have h6 : Entails.eval a c10081 := derived10081 a h
  have h7 : Entails.eval a c771 := h 770 (by decide)
  have h8 : Entails.eval a c796 := h 795 (by decide)
  have h9 : Entails.eval a c2798 := h 2797 (by decide)
  have h10 : Entails.eval a c2795 := h 2794 (by decide)
  have h11 : Entails.eval a c2764 := h 2763 (by decide)
  have h12 : Entails.eval a c777 := h 776 (by decide)
  have h13 : Entails.eval a c781 := h 780 (by decide)
  have h14 : Entails.eval a c2805 := h 2804 (by decide)
  have h15 : Entails.eval a c2796 := h 2795 (by decide)
  have h16 : Entails.eval a c2797 := h 2796 (by decide)
  have h17 : Entails.eval a c2807 := h 2806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10120 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨63, by decide⟩, true), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10120 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10119, some c1732, some c1730, some c10115, some c10042, some c10052, some c4359, some c2802, some c4363, some c4369, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10120 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10120 : lratChecker f10120 p10120 = .success := by decide +kernel
theorem unsat10120 : Unsatisfiable (PosFin 65) f10120 := by
  apply lratCheckerSound f10120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10120
  · intro a ha; simp [p10120] at ha; subst a; trivial
  · exact checked10120
theorem derived10120 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10120 := by
  apply localUnsat_implies_entails f10120 [c9748, c10119, c1732, c1730, c10115, c10042, c10052, c4359, c2802, c4363, c4369] c10120 unsat10120 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10119 := derived10119 a h
  have h2 : Entails.eval a c1732 := h 1731 (by decide)
  have h3 : Entails.eval a c1730 := h 1729 (by decide)
  have h4 : Entails.eval a c10115 := derived10115 a h
  have h5 : Entails.eval a c10042 := derived10042 a h
  have h6 : Entails.eval a c10052 := derived10052 a h
  have h7 : Entails.eval a c4359 := h 4358 (by decide)
  have h8 : Entails.eval a c2802 := h 2801 (by decide)
  have h9 : Entails.eval a c4363 := h 4362 (by decide)
  have h10 : Entails.eval a c4369 := h 4368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10121 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨63, by decide⟩, true), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10121 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9880, some c10120, some c4693, some c1818, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10121 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10121 : lratChecker f10121 p10121 = .success := by decide +kernel
theorem unsat10121 : Unsatisfiable (PosFin 65) f10121 := by
  apply lratCheckerSound f10121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10121
  · intro a ha; simp [p10121] at ha; subst a; trivial
  · exact checked10121
theorem derived10121 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10121 := by
  apply localUnsat_implies_entails f10121 [c9748, c9880, c10120, c4693, c1818] c10121 unsat10121 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9880 := derived9880 a h
  have h2 : Entails.eval a c10120 := derived10120 a h
  have h3 : Entails.eval a c4693 := h 4692 (by decide)
  have h4 : Entails.eval a c1818 := h 1817 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10122 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10122 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4302, some c4301, some c4299, some c2607, some c4381, some c10043, some c10056, some c1616, some c1594, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10122 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10122 : lratChecker f10122 p10122 = .success := by decide +kernel
theorem unsat10122 : Unsatisfiable (PosFin 65) f10122 := by
  apply lratCheckerSound f10122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10122
  · intro a ha; simp [p10122] at ha; subst a; trivial
  · exact checked10122
theorem derived10122 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10122 := by
  apply localUnsat_implies_entails f10122 [c9748, c4302, c4301, c4299, c2607, c4381, c10043, c10056, c1616, c1594] c10122 unsat10122 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4302 := h 4301 (by decide)
  have h2 : Entails.eval a c4301 := h 4300 (by decide)
  have h3 : Entails.eval a c4299 := h 4298 (by decide)
  have h4 : Entails.eval a c2607 := h 2606 (by decide)
  have h5 : Entails.eval a c4381 := h 4380 (by decide)
  have h6 : Entails.eval a c10043 := derived10043 a h
  have h7 : Entails.eval a c10056 := derived10056 a h
  have h8 : Entails.eval a c1616 := h 1615 (by decide)
  have h9 : Entails.eval a c1594 := h 1593 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10123 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10123 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10121, some c4301, some c4302, some c4299, some c4315, some c10122, some c10066, some c4266, some c994, some c733, some c1003, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10123 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10123 : lratChecker f10123 p10123 = .success := by decide +kernel
theorem unsat10123 : Unsatisfiable (PosFin 65) f10123 := by
  apply lratCheckerSound f10123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10123
  · intro a ha; simp [p10123] at ha; subst a; trivial
  · exact checked10123
theorem derived10123 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10123 := by
  apply localUnsat_implies_entails f10123 [c10121, c4301, c4302, c4299, c4315, c10122, c10066, c4266, c994, c733, c1003] c10123 unsat10123 (by rfl) a
  have h0 : Entails.eval a c10121 := derived10121 a h
  have h1 : Entails.eval a c4301 := h 4300 (by decide)
  have h2 : Entails.eval a c4302 := h 4301 (by decide)
  have h3 : Entails.eval a c4299 := h 4298 (by decide)
  have h4 : Entails.eval a c4315 := h 4314 (by decide)
  have h5 : Entails.eval a c10122 := derived10122 a h
  have h6 : Entails.eval a c10066 := derived10066 a h
  have h7 : Entails.eval a c4266 := h 4265 (by decide)
  have h8 : Entails.eval a c994 := h 993 (by decide)
  have h9 : Entails.eval a c733 := h 732 (by decide)
  have h10 : Entails.eval a c1003 := h 1002 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10124 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10124 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10069, some c10118, some c10123, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10124 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10124 : lratChecker f10124 p10124 = .success := by decide +kernel
theorem unsat10124 : Unsatisfiable (PosFin 65) f10124 := by
  apply lratCheckerSound f10124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10124
  · intro a ha; simp [p10124] at ha; subst a; trivial
  · exact checked10124
theorem derived10124 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10124 := by
  apply localUnsat_implies_entails f10124 [c10069, c10118, c10123] c10124 unsat10124 (by rfl) a
  have h0 : Entails.eval a c10069 := derived10069 a h
  have h1 : Entails.eval a c10118 := derived10118 a h
  have h2 : Entails.eval a c10123 := derived10123 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10125 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10125 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10069, some c10124, some c3485, some c5100, some c2262, some c5083, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10125 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10125 : lratChecker f10125 p10125 = .success := by decide +kernel
theorem unsat10125 : Unsatisfiable (PosFin 65) f10125 := by
  apply lratCheckerSound f10125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10125
  · intro a ha; simp [p10125] at ha; subst a; trivial
  · exact checked10125
theorem derived10125 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10125 := by
  apply localUnsat_implies_entails f10125 [c9748, c10069, c10124, c3485, c5100, c2262, c5083] c10125 unsat10125 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10069 := derived10069 a h
  have h2 : Entails.eval a c10124 := derived10124 a h
  have h3 : Entails.eval a c3485 := h 3484 (by decide)
  have h4 : Entails.eval a c5100 := h 5099 (by decide)
  have h5 : Entails.eval a c2262 := h 2261 (by decide)
  have h6 : Entails.eval a c5083 := h 5082 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10126 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10126 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4680, some c4304, some c3542, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10126 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10126 : lratChecker f10126 p10126 = .success := by decide +kernel
theorem unsat10126 : Unsatisfiable (PosFin 65) f10126 := by
  apply lratCheckerSound f10126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10126
  · intro a ha; simp [p10126] at ha; subst a; trivial
  · exact checked10126
theorem derived10126 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10126 := by
  apply localUnsat_implies_entails f10126 [c4680, c4304, c3542] c10126 unsat10126 (by rfl) a
  have h0 : Entails.eval a c4680 := h 4679 (by decide)
  have h1 : Entails.eval a c4304 := h 4303 (by decide)
  have h2 : Entails.eval a c3542 := h 3541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10127 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10127 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10069, some c10125, some c10089, some c3485, some c5100, some c2262, some c5083, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10127 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10127 : lratChecker f10127 p10127 = .success := by decide +kernel
theorem unsat10127 : Unsatisfiable (PosFin 65) f10127 := by
  apply lratCheckerSound f10127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10127
  · intro a ha; simp [p10127] at ha; subst a; trivial
  · exact checked10127
theorem derived10127 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10127 := by
  apply localUnsat_implies_entails f10127 [c9748, c10069, c10125, c10089, c3485, c5100, c2262, c5083] c10127 unsat10127 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10069 := derived10069 a h
  have h2 : Entails.eval a c10125 := derived10125 a h
  have h3 : Entails.eval a c10089 := derived10089 a h
  have h4 : Entails.eval a c3485 := h 3484 (by decide)
  have h5 : Entails.eval a c5100 := h 5099 (by decide)
  have h6 : Entails.eval a c2262 := h 2261 (by decide)
  have h7 : Entails.eval a c5083 := h 5082 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10128 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10128 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10085, some c10093, some c10073, some c10083, some c1827, some c10094, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10128 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10128 : lratChecker f10128 p10128 = .success := by decide +kernel
theorem unsat10128 : Unsatisfiable (PosFin 65) f10128 := by
  apply lratCheckerSound f10128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10128
  · intro a ha; simp [p10128] at ha; subst a; trivial
  · exact checked10128
theorem derived10128 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10128 := by
  apply localUnsat_implies_entails f10128 [c9748, c10085, c10093, c10073, c10083, c1827, c10094] c10128 unsat10128 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10085 := derived10085 a h
  have h2 : Entails.eval a c10093 := derived10093 a h
  have h3 : Entails.eval a c10073 := derived10073 a h
  have h4 : Entails.eval a c10083 := derived10083 a h
  have h5 : Entails.eval a c1827 := h 1826 (by decide)
  have h6 : Entails.eval a c10094 := derived10094 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10129 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10129 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10128, some c10115, some c10061, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10129 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10129 : lratChecker f10129 p10129 = .success := by decide +kernel
theorem unsat10129 : Unsatisfiable (PosFin 65) f10129 := by
  apply lratCheckerSound f10129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10129
  · intro a ha; simp [p10129] at ha; subst a; trivial
  · exact checked10129
theorem derived10129 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10129 := by
  apply localUnsat_implies_entails f10129 [c10128, c10115, c10061] c10129 unsat10129 (by rfl) a
  have h0 : Entails.eval a c10128 := derived10128 a h
  have h1 : Entails.eval a c10115 := derived10115 a h
  have h2 : Entails.eval a c10061 := derived10061 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10130 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10130 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10129, some c9145, some c9797, some c8003, some c3772, some c2904, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10130 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10130 : lratChecker f10130 p10130 = .success := by decide +kernel
theorem unsat10130 : Unsatisfiable (PosFin 65) f10130 := by
  apply lratCheckerSound f10130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10130
  · intro a ha; simp [p10130] at ha; subst a; trivial
  · exact checked10130
theorem derived10130 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10130 := by
  apply localUnsat_implies_entails f10130 [c9748, c10129, c9145, c9797, c8003, c3772, c2904] c10130 unsat10130 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10129 := derived10129 a h
  have h2 : Entails.eval a c9145 := derived9145 a h
  have h3 : Entails.eval a c9797 := derived9797 a h
  have h4 : Entails.eval a c8003 := derived8003 a h
  have h5 : Entails.eval a c3772 := h 3771 (by decide)
  have h6 : Entails.eval a c2904 := h 2903 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10131 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨6, by decide⟩, true), (⟨63, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10131 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4693, some c1816, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10131 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10131 : lratChecker f10131 p10131 = .success := by decide +kernel
theorem unsat10131 : Unsatisfiable (PosFin 65) f10131 := by
  apply lratCheckerSound f10131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10131
  · intro a ha; simp [p10131] at ha; subst a; trivial
  · exact checked10131
theorem derived10131 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10131 := by
  apply localUnsat_implies_entails f10131 [c9748, c4693, c1816] c10131 unsat10131 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4693 := h 4692 (by decide)
  have h2 : Entails.eval a c1816 := h 1815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10132 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10132 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10043, some c10093, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10132 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10132 : lratChecker f10132 p10132 = .success := by decide +kernel
theorem unsat10132 : Unsatisfiable (PosFin 65) f10132 := by
  apply lratCheckerSound f10132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10132
  · intro a ha; simp [p10132] at ha; subst a; trivial
  · exact checked10132
theorem derived10132 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10132 := by
  apply localUnsat_implies_entails f10132 [c10043, c10093] c10132 unsat10132 (by rfl) a
  have h0 : Entails.eval a c10043 := derived10043 a h
  have h1 : Entails.eval a c10093 := derived10093 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10133 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10133 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10081, some c771, some c796, some c2798, some c2764, some c973, some c975, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10133 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10133 : lratChecker f10133 p10133 = .success := by decide +kernel
theorem unsat10133 : Unsatisfiable (PosFin 65) f10133 := by
  apply lratCheckerSound f10133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10133
  · intro a ha; simp [p10133] at ha; subst a; trivial
  · exact checked10133
theorem derived10133 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10133 := by
  apply localUnsat_implies_entails f10133 [c10081, c771, c796, c2798, c2764, c973, c975] c10133 unsat10133 (by rfl) a
  have h0 : Entails.eval a c10081 := derived10081 a h
  have h1 : Entails.eval a c771 := h 770 (by decide)
  have h2 : Entails.eval a c796 := h 795 (by decide)
  have h3 : Entails.eval a c2798 := h 2797 (by decide)
  have h4 : Entails.eval a c2764 := h 2763 (by decide)
  have h5 : Entails.eval a c973 := h 972 (by decide)
  have h6 : Entails.eval a c975 := h 974 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10134 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10134 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10132, some c10133, some c10073, some c1827, some c10094, some c1867, some c771, some c1866, some c776, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10134 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10134 : lratChecker f10134 p10134 = .success := by decide +kernel
theorem unsat10134 : Unsatisfiable (PosFin 65) f10134 := by
  apply lratCheckerSound f10134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10134
  · intro a ha; simp [p10134] at ha; subst a; trivial
  · exact checked10134
theorem derived10134 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10134 := by
  apply localUnsat_implies_entails f10134 [c9748, c10132, c10133, c10073, c1827, c10094, c1867, c771, c1866, c776] c10134 unsat10134 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10132 := derived10132 a h
  have h2 : Entails.eval a c10133 := derived10133 a h
  have h3 : Entails.eval a c10073 := derived10073 a h
  have h4 : Entails.eval a c1827 := h 1826 (by decide)
  have h5 : Entails.eval a c10094 := derived10094 a h
  have h6 : Entails.eval a c1867 := h 1866 (by decide)
  have h7 : Entails.eval a c771 := h 770 (by decide)
  have h8 : Entails.eval a c1866 := h 1865 (by decide)
  have h9 : Entails.eval a c776 := h 775 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10135 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10135 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10134, some c10115, some c10042, some c1669, some c4359, some c10063, some c4362, some c4363, some c394, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10135 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10135 : lratChecker f10135 p10135 = .success := by decide +kernel
theorem unsat10135 : Unsatisfiable (PosFin 65) f10135 := by
  apply lratCheckerSound f10135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10135
  · intro a ha; simp [p10135] at ha; subst a; trivial
  · exact checked10135
theorem derived10135 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10135 := by
  apply localUnsat_implies_entails f10135 [c9748, c10134, c10115, c10042, c1669, c4359, c10063, c4362, c4363, c394] c10135 unsat10135 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10134 := derived10134 a h
  have h2 : Entails.eval a c10115 := derived10115 a h
  have h3 : Entails.eval a c10042 := derived10042 a h
  have h4 : Entails.eval a c1669 := h 1668 (by decide)
  have h5 : Entails.eval a c4359 := h 4358 (by decide)
  have h6 : Entails.eval a c10063 := derived10063 a h
  have h7 : Entails.eval a c4362 := h 4361 (by decide)
  have h8 : Entails.eval a c4363 := h 4362 (by decide)
  have h9 : Entails.eval a c394 := h 393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10136 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨12, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10136 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2740, some c2732, some c8007, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p10136 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10136 : lratChecker f10136 p10136 = .success := by decide +kernel
theorem unsat10136 : Unsatisfiable (PosFin 65) f10136 := by
  apply lratCheckerSound f10136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10136
  · intro a ha; simp [p10136] at ha; subst a; trivial
  · exact checked10136
theorem derived10136 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10136 := by
  apply localUnsat_implies_entails f10136 [c2740, c2732, c8007] c10136 unsat10136 (by rfl) a
  have h0 : Entails.eval a c2740 := h 2739 (by decide)
  have h1 : Entails.eval a c2732 := h 2731 (by decide)
  have h2 : Entails.eval a c8007 := derived8007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10137 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨63, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10137 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10127, some c10131, some c10130, some c10135, some c9145, some c10136, some c1732, some c1730, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10137 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10137 : lratChecker f10137 p10137 = .success := by decide +kernel
theorem unsat10137 : Unsatisfiable (PosFin 65) f10137 := by
  apply lratCheckerSound f10137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10137
  · intro a ha; simp [p10137] at ha; subst a; trivial
  · exact checked10137
theorem derived10137 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10137 := by
  apply localUnsat_implies_entails f10137 [c9748, c10127, c10131, c10130, c10135, c9145, c10136, c1732, c1730] c10137 unsat10137 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10127 := derived10127 a h
  have h2 : Entails.eval a c10131 := derived10131 a h
  have h3 : Entails.eval a c10130 := derived10130 a h
  have h4 : Entails.eval a c10135 := derived10135 a h
  have h5 : Entails.eval a c9145 := derived9145 a h
  have h6 : Entails.eval a c10136 := derived10136 a h
  have h7 : Entails.eval a c1732 := h 1731 (by decide)
  have h8 : Entails.eval a c1730 := h 1729 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10138 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨63, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10138 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10127, some c10137, some c4301, some c4302, some c4299, some c4315, some c10104, some c4266, some c4269, some c4264, some c734, some c952, some c1003, some c959, some c1006, some c995, some c1005, some c4265, some c1015, some c4287, some c730, some c94, some c950, some c115, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10138 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked10138 : lratChecker f10138 p10138 = .success := by decide +kernel
theorem unsat10138 : Unsatisfiable (PosFin 65) f10138 := by
  apply lratCheckerSound f10138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10138
  · intro a ha; simp [p10138] at ha; subst a; trivial
  · exact checked10138
theorem derived10138 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10138 := by
  apply localUnsat_implies_entails f10138 [c10127, c10137, c4301, c4302, c4299, c4315, c10104, c4266, c4269, c4264, c734, c952, c1003, c959, c1006, c995, c1005, c4265, c1015, c4287, c730, c94, c950, c115] c10138 unsat10138 (by rfl) a
  have h0 : Entails.eval a c10127 := derived10127 a h
  have h1 : Entails.eval a c10137 := derived10137 a h
  have h2 : Entails.eval a c4301 := h 4300 (by decide)
  have h3 : Entails.eval a c4302 := h 4301 (by decide)
  have h4 : Entails.eval a c4299 := h 4298 (by decide)
  have h5 : Entails.eval a c4315 := h 4314 (by decide)
  have h6 : Entails.eval a c10104 := derived10104 a h
  have h7 : Entails.eval a c4266 := h 4265 (by decide)
  have h8 : Entails.eval a c4269 := h 4268 (by decide)
  have h9 : Entails.eval a c4264 := h 4263 (by decide)
  have h10 : Entails.eval a c734 := h 733 (by decide)
  have h11 : Entails.eval a c952 := h 951 (by decide)
  have h12 : Entails.eval a c1003 := h 1002 (by decide)
  have h13 : Entails.eval a c959 := h 958 (by decide)
  have h14 : Entails.eval a c1006 := h 1005 (by decide)
  have h15 : Entails.eval a c995 := h 994 (by decide)
  have h16 : Entails.eval a c1005 := h 1004 (by decide)
  have h17 : Entails.eval a c4265 := h 4264 (by decide)
  have h18 : Entails.eval a c1015 := h 1014 (by decide)
  have h19 : Entails.eval a c4287 := h 4286 (by decide)
  have h20 : Entails.eval a c730 := h 729 (by decide)
  have h21 : Entails.eval a c94 := h 93 (by decide)
  have h22 : Entails.eval a c950 := h 949 (by decide)
  have h23 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10139 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10139 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2961, some c3544, some c3094, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p10139 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10139 : lratChecker f10139 p10139 = .success := by decide +kernel
theorem unsat10139 : Unsatisfiable (PosFin 65) f10139 := by
  apply lratCheckerSound f10139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10139
  · intro a ha; simp [p10139] at ha; subst a; trivial
  · exact checked10139
theorem derived10139 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10139 := by
  apply localUnsat_implies_entails f10139 [c2961, c3544, c3094] c10139 unsat10139 (by rfl) a
  have h0 : Entails.eval a c2961 := h 2960 (by decide)
  have h1 : Entails.eval a c3544 := h 3543 (by decide)
  have h2 : Entails.eval a c3094 := h 3093 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10140 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10140 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10139, some c4301, some c4291, some c2635, some c2651, some c3775, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10140 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10140 : lratChecker f10140 p10140 = .success := by decide +kernel
theorem unsat10140 : Unsatisfiable (PosFin 65) f10140 := by
  apply lratCheckerSound f10140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10140
  · intro a ha; simp [p10140] at ha; subst a; trivial
  · exact checked10140
theorem derived10140 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10140 := by
  apply localUnsat_implies_entails f10140 [c10139, c4301, c4291, c2635, c2651, c3775] c10140 unsat10140 (by rfl) a
  have h0 : Entails.eval a c10139 := derived10139 a h
  have h1 : Entails.eval a c4301 := h 4300 (by decide)
  have h2 : Entails.eval a c4291 := h 4290 (by decide)
  have h3 : Entails.eval a c2635 := h 2634 (by decide)
  have h4 : Entails.eval a c2651 := h 2650 (by decide)
  have h5 : Entails.eval a c3775 := h 3774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10141 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨63, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10141 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4376, some c1792, some c4094, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10141 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10141 : lratChecker f10141 p10141 = .success := by decide +kernel
theorem unsat10141 : Unsatisfiable (PosFin 65) f10141 := by
  apply lratCheckerSound f10141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10141
  · intro a ha; simp [p10141] at ha; subst a; trivial
  · exact checked10141
theorem derived10141 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10141 := by
  apply localUnsat_implies_entails f10141 [c9748, c4376, c1792, c4094] c10141 unsat10141 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4376 := h 4375 (by decide)
  have h2 : Entails.eval a c1792 := h 1791 (by decide)
  have h3 : Entails.eval a c4094 := h 4093 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10142 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10142 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10141, some c4301, some c4302, some c4299, some c2623, some c3955, some c3006, some c3088, some c2236, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10142 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10142 : lratChecker f10142 p10142 = .success := by decide +kernel
theorem unsat10142 : Unsatisfiable (PosFin 65) f10142 := by
  apply lratCheckerSound f10142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10142
  · intro a ha; simp [p10142] at ha; subst a; trivial
  · exact checked10142
theorem derived10142 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10142 := by
  apply localUnsat_implies_entails f10142 [c9748, c10141, c4301, c4302, c4299, c2623, c3955, c3006, c3088, c2236] c10142 unsat10142 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10141 := derived10141 a h
  have h2 : Entails.eval a c4301 := h 4300 (by decide)
  have h3 : Entails.eval a c4302 := h 4301 (by decide)
  have h4 : Entails.eval a c4299 := h 4298 (by decide)
  have h5 : Entails.eval a c2623 := h 2622 (by decide)
  have h6 : Entails.eval a c3955 := h 3954 (by decide)
  have h7 : Entails.eval a c3006 := h 3005 (by decide)
  have h8 : Entails.eval a c3088 := h 3087 (by decide)
  have h9 : Entails.eval a c2236 := h 2235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10143 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨54, by decide⟩, false), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10143 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10127, some c10140, some c10142, some c10089, some c10138, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10143 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10143 : lratChecker f10143 p10143 = .success := by decide +kernel
theorem unsat10143 : Unsatisfiable (PosFin 65) f10143 := by
  apply lratCheckerSound f10143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10143
  · intro a ha; simp [p10143] at ha; subst a; trivial
  · exact checked10143
theorem derived10143 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10143 := by
  apply localUnsat_implies_entails f10143 [c10127, c10140, c10142, c10089, c10138] c10143 unsat10143 (by rfl) a
  have h0 : Entails.eval a c10127 := derived10127 a h
  have h1 : Entails.eval a c10140 := derived10140 a h
  have h2 : Entails.eval a c10142 := derived10142 a h
  have h3 : Entails.eval a c10089 := derived10089 a h
  have h4 : Entails.eval a c10138 := derived10138 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10144 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10144 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10113, some c10021, some c10126, some c10143, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10144 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10144 : lratChecker f10144 p10144 = .success := by decide +kernel
theorem unsat10144 : Unsatisfiable (PosFin 65) f10144 := by
  apply lratCheckerSound f10144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10144
  · intro a ha; simp [p10144] at ha; subst a; trivial
  · exact checked10144
theorem derived10144 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10144 := by
  apply localUnsat_implies_entails f10144 [c10113, c10021, c10126, c10143] c10144 unsat10144 (by rfl) a
  have h0 : Entails.eval a c10113 := derived10113 a h
  have h1 : Entails.eval a c10021 := derived10021 a h
  have h2 : Entails.eval a c10126 := derived10126 a h
  have h3 : Entails.eval a c10143 := derived10143 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10145 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨61, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10145 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10112, some c9259, some c9912, some c2627, some c3517, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10145 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10145 : lratChecker f10145 p10145 = .success := by decide +kernel
theorem unsat10145 : Unsatisfiable (PosFin 65) f10145 := by
  apply lratCheckerSound f10145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10145
  · intro a ha; simp [p10145] at ha; subst a; trivial
  · exact checked10145
theorem derived10145 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10145 := by
  apply localUnsat_implies_entails f10145 [c10112, c9259, c9912, c2627, c3517] c10145 unsat10145 (by rfl) a
  have h0 : Entails.eval a c10112 := derived10112 a h
  have h1 : Entails.eval a c9259 := derived9259 a h
  have h2 : Entails.eval a c9912 := derived9912 a h
  have h3 : Entails.eval a c2627 := h 2626 (by decide)
  have h4 : Entails.eval a c3517 := h 3516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10146 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨61, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10146 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2954, some c2959, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p10146 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10146 : lratChecker f10146 p10146 = .success := by decide +kernel
theorem unsat10146 : Unsatisfiable (PosFin 65) f10146 := by
  apply lratCheckerSound f10146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10146
  · intro a ha; simp [p10146] at ha; subst a; trivial
  · exact checked10146
theorem derived10146 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10146 := by
  apply localUnsat_implies_entails f10146 [c2954, c2959] c10146 unsat10146 (by rfl) a
  have h0 : Entails.eval a c2954 := h 2953 (by decide)
  have h1 : Entails.eval a c2959 := h 2958 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10147 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨61, by decide⟩, false), (⟨57, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10147 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4688, some c2365, some c2903, some c3738, some c10111, some c3206, some c10145, some c10089, some c10142, some c10146, some c4291, some c4307, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10147 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10147 : lratChecker f10147 p10147 = .success := by decide +kernel
theorem unsat10147 : Unsatisfiable (PosFin 65) f10147 := by
  apply lratCheckerSound f10147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10147
  · intro a ha; simp [p10147] at ha; subst a; trivial
  · exact checked10147
theorem derived10147 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10147 := by
  apply localUnsat_implies_entails f10147 [c9748, c4688, c2365, c2903, c3738, c10111, c3206, c10145, c10089, c10142, c10146, c4291, c4307] c10147 unsat10147 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4688 := h 4687 (by decide)
  have h2 : Entails.eval a c2365 := h 2364 (by decide)
  have h3 : Entails.eval a c2903 := h 2902 (by decide)
  have h4 : Entails.eval a c3738 := h 3737 (by decide)
  have h5 : Entails.eval a c10111 := derived10111 a h
  have h6 : Entails.eval a c3206 := h 3205 (by decide)
  have h7 : Entails.eval a c10145 := derived10145 a h
  have h8 : Entails.eval a c10089 := derived10089 a h
  have h9 : Entails.eval a c10142 := derived10142 a h
  have h10 : Entails.eval a c10146 := derived10146 a h
  have h11 : Entails.eval a c4291 := h 4290 (by decide)
  have h12 : Entails.eval a c4307 := h 4306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10148 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨16, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10148 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4303, some c1892, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10148 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10148 : lratChecker f10148 p10148 = .success := by decide +kernel
theorem unsat10148 : Unsatisfiable (PosFin 65) f10148 := by
  apply lratCheckerSound f10148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10148
  · intro a ha; simp [p10148] at ha; subst a; trivial
  · exact checked10148
theorem derived10148 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10148 := by
  apply localUnsat_implies_entails f10148 [c9748, c4303, c1892] c10148 unsat10148 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4303 := h 4302 (by decide)
  have h2 : Entails.eval a c1892 := h 1891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10149 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10149 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10113, some c10021, some c10144, some c4688, some c2365, some c2903, some c2925, some c3738, some c10147, some c10148, some c3529, some c2629, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10149 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10149 : lratChecker f10149 p10149 = .success := by decide +kernel
theorem unsat10149 : Unsatisfiable (PosFin 65) f10149 := by
  apply lratCheckerSound f10149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10149
  · intro a ha; simp [p10149] at ha; subst a; trivial
  · exact checked10149
theorem derived10149 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10149 := by
  apply localUnsat_implies_entails f10149 [c9748, c10113, c10021, c10144, c4688, c2365, c2903, c2925, c3738, c10147, c10148, c3529, c2629] c10149 unsat10149 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10113 := derived10113 a h
  have h2 : Entails.eval a c10021 := derived10021 a h
  have h3 : Entails.eval a c10144 := derived10144 a h
  have h4 : Entails.eval a c4688 := h 4687 (by decide)
  have h5 : Entails.eval a c2365 := h 2364 (by decide)
  have h6 : Entails.eval a c2903 := h 2902 (by decide)
  have h7 : Entails.eval a c2925 := h 2924 (by decide)
  have h8 : Entails.eval a c3738 := h 3737 (by decide)
  have h9 : Entails.eval a c10147 := derived10147 a h
  have h10 : Entails.eval a c10148 := derived10148 a h
  have h11 : Entails.eval a c3529 := h 3528 (by decide)
  have h12 : Entails.eval a c2629 := h 2628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10150 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨57, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10150 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9145, some c4301, some c4312, some c4299, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10150 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10150 : lratChecker f10150 p10150 = .success := by decide +kernel
theorem unsat10150 : Unsatisfiable (PosFin 65) f10150 := by
  apply lratCheckerSound f10150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10150
  · intro a ha; simp [p10150] at ha; subst a; trivial
  · exact checked10150
theorem derived10150 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10150 := by
  apply localUnsat_implies_entails f10150 [c9145, c4301, c4312, c4299] c10150 unsat10150 (by rfl) a
  have h0 : Entails.eval a c9145 := derived9145 a h
  have h1 : Entails.eval a c4301 := h 4300 (by decide)
  have h2 : Entails.eval a c4312 := h 4311 (by decide)
  have h3 : Entails.eval a c4299 := h 4298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived10150

end CochromaticTwenty.Certificates.FixedCore0
