import MerLeanExperiment.Certificates.FixedCore0.Steps3100_3199

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10751 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨14, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10751 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2369, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10751 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10751 : lratChecker f10751 p10751 = .success := by decide +kernel
theorem unsat10751 : Unsatisfiable (PosFin 65) f10751 := by
  apply lratCheckerSound f10751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10751
  · intro a ha; simp [p10751] at ha; subst a; trivial
  · exact checked10751
theorem derived10751 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10751 := by
  apply localUnsat_implies_entails f10751 [c9748, c2369] c10751 unsat10751 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2369 := h 2368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10752 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨60, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10752 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2361, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10752 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10752 : lratChecker f10752 p10752 = .success := by decide +kernel
theorem unsat10752 : Unsatisfiable (PosFin 65) f10752 := by
  apply lratCheckerSound f10752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10752
  · intro a ha; simp [p10752] at ha; subst a; trivial
  · exact checked10752
theorem derived10752 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10752 := by
  apply localUnsat_implies_entails f10752 [c9748, c2361] c10752 unsat10752 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2361 := h 2360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10753 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨60, by decide⟩, true), (⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10753 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2362, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10753 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10753 : lratChecker f10753 p10753 = .success := by decide +kernel
theorem unsat10753 : Unsatisfiable (PosFin 65) f10753 := by
  apply lratCheckerSound f10753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10753
  · intro a ha; simp [p10753] at ha; subst a; trivial
  · exact checked10753
theorem derived10753 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10753 := by
  apply localUnsat_implies_entails f10753 [c9748, c2362] c10753 unsat10753 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2362 := h 2361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10754 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨61, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10754 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1804, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10754 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10754 : lratChecker f10754 p10754 = .success := by decide +kernel
theorem unsat10754 : Unsatisfiable (PosFin 65) f10754 := by
  apply lratCheckerSound f10754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10754
  · intro a ha; simp [p10754] at ha; subst a; trivial
  · exact checked10754
theorem derived10754 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10754 := by
  apply localUnsat_implies_entails f10754 [c9748, c1804] c10754 unsat10754 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1804 := h 1803 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10755 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10755 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2370, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10755 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10755 : lratChecker f10755 p10755 = .success := by decide +kernel
theorem unsat10755 : Unsatisfiable (PosFin 65) f10755 := by
  apply lratCheckerSound f10755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10755
  · intro a ha; simp [p10755] at ha; subst a; trivial
  · exact checked10755
theorem derived10755 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10755 := by
  apply localUnsat_implies_entails f10755 [c9748, c2370] c10755 unsat10755 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2370 := h 2369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10756 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10756 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2255, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p10756 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10756 : lratChecker f10756 p10756 = .success := by decide +kernel
theorem unsat10756 : Unsatisfiable (PosFin 65) f10756 := by
  apply lratCheckerSound f10756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10756
  · intro a ha; simp [p10756] at ha; subst a; trivial
  · exact checked10756
theorem derived10756 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10756 := by
  apply localUnsat_implies_entails f10756 [c9748, c2255] c10756 unsat10756 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2255 := h 2254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10757 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10757 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2364, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10757 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10757 : lratChecker f10757 p10757 = .success := by decide +kernel
theorem unsat10757 : Unsatisfiable (PosFin 65) f10757 := by
  apply lratCheckerSound f10757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10757
  · intro a ha; simp [p10757] at ha; subst a; trivial
  · exact checked10757
theorem derived10757 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10757 := by
  apply localUnsat_implies_entails f10757 [c9748, c2364] c10757 unsat10757 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2364 := h 2363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10758 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨57, by decide⟩, true), (⟨56, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10758 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2246, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10758 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10758 : lratChecker f10758 p10758 = .success := by decide +kernel
theorem unsat10758 : Unsatisfiable (PosFin 65) f10758 := by
  apply lratCheckerSound f10758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10758
  · intro a ha; simp [p10758] at ha; subst a; trivial
  · exact checked10758
theorem derived10758 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10758 := by
  apply localUnsat_implies_entails f10758 [c9748, c2246] c10758 unsat10758 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2246 := h 2245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10759 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10759 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2366, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10759 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10759 : lratChecker f10759 p10759 = .success := by decide +kernel
theorem unsat10759 : Unsatisfiable (PosFin 65) f10759 := by
  apply lratCheckerSound f10759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10759
  · intro a ha; simp [p10759] at ha; subst a; trivial
  · exact checked10759
theorem derived10759 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10759 := by
  apply localUnsat_implies_entails f10759 [c9748, c2366] c10759 unsat10759 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2366 := h 2365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10760 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10760 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2363, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10760 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10760 : lratChecker f10760 p10760 = .success := by decide +kernel
theorem unsat10760 : Unsatisfiable (PosFin 65) f10760 := by
  apply lratCheckerSound f10760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10760
  · intro a ha; simp [p10760] at ha; subst a; trivial
  · exact checked10760
theorem derived10760 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10760 := by
  apply localUnsat_implies_entails f10760 [c9748, c2363] c10760 unsat10760 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2363 := h 2362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10761 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10761 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2354, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10761 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10761 : lratChecker f10761 p10761 = .success := by decide +kernel
theorem unsat10761 : Unsatisfiable (PosFin 65) f10761 := by
  apply lratCheckerSound f10761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10761
  · intro a ha; simp [p10761] at ha; subst a; trivial
  · exact checked10761
theorem derived10761 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10761 := by
  apply localUnsat_implies_entails f10761 [c9748, c2354] c10761 unsat10761 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2354 := h 2353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10762 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10762 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2355, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10762 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10762 : lratChecker f10762 p10762 = .success := by decide +kernel
theorem unsat10762 : Unsatisfiable (PosFin 65) f10762 := by
  apply lratCheckerSound f10762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10762
  · intro a ha; simp [p10762] at ha; subst a; trivial
  · exact checked10762
theorem derived10762 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10762 := by
  apply localUnsat_implies_entails f10762 [c9748, c2355] c10762 unsat10762 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2355 := h 2354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10763 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨22, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10763 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2221, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p10763 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10763 : lratChecker f10763 p10763 = .success := by decide +kernel
theorem unsat10763 : Unsatisfiable (PosFin 65) f10763 := by
  apply lratCheckerSound f10763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10763
  · intro a ha; simp [p10763] at ha; subst a; trivial
  · exact checked10763
theorem derived10763 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10763 := by
  apply localUnsat_implies_entails f10763 [c9748, c2221] c10763 unsat10763 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2221 := h 2220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10764 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨13, by decide⟩, true), (⟨28, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10764 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2223, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10764 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10764 : lratChecker f10764 p10764 = .success := by decide +kernel
theorem unsat10764 : Unsatisfiable (PosFin 65) f10764 := by
  apply lratCheckerSound f10764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10764
  · intro a ha; simp [p10764] at ha; subst a; trivial
  · exact checked10764
theorem derived10764 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10764 := by
  apply localUnsat_implies_entails f10764 [c9748, c2223] c10764 unsat10764 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2223 := h 2222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10765 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨60, by decide⟩, false), (⟨14, by decide⟩, true), (⟨56, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10765 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2377, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10765 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10765 : lratChecker f10765 p10765 = .success := by decide +kernel
theorem unsat10765 : Unsatisfiable (PosFin 65) f10765 := by
  apply lratCheckerSound f10765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10765
  · intro a ha; simp [p10765] at ha; subst a; trivial
  · exact checked10765
theorem derived10765 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10765 := by
  apply localUnsat_implies_entails f10765 [c9748, c2377] c10765 unsat10765 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2377 := h 2376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10766 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨31, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10766 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2220, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10766 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10766 : lratChecker f10766 p10766 = .success := by decide +kernel
theorem unsat10766 : Unsatisfiable (PosFin 65) f10766 := by
  apply lratCheckerSound f10766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10766
  · intro a ha; simp [p10766] at ha; subst a; trivial
  · exact checked10766
theorem derived10766 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10766 := by
  apply localUnsat_implies_entails f10766 [c9748, c2220] c10766 unsat10766 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2220 := h 2219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10767 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10767 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1756, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p10767 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10767 : lratChecker f10767 p10767 = .success := by decide +kernel
theorem unsat10767 : Unsatisfiable (PosFin 65) f10767 := by
  apply lratCheckerSound f10767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10767
  · intro a ha; simp [p10767] at ha; subst a; trivial
  · exact checked10767
theorem derived10767 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10767 := by
  apply localUnsat_implies_entails f10767 [c9748, c1756] c10767 unsat10767 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1756 := h 1755 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10768 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10768 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1779, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p10768 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10768 : lratChecker f10768 p10768 = .success := by decide +kernel
theorem unsat10768 : Unsatisfiable (PosFin 65) f10768 := by
  apply lratCheckerSound f10768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10768
  · intro a ha; simp [p10768] at ha; subst a; trivial
  · exact checked10768
theorem derived10768 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10768 := by
  apply localUnsat_implies_entails f10768 [c9748, c1779] c10768 unsat10768 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1779 := h 1778 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10769 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10769 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2183, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10769 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10769 : lratChecker f10769 p10769 = .success := by decide +kernel
theorem unsat10769 : Unsatisfiable (PosFin 65) f10769 := by
  apply lratCheckerSound f10769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10769
  · intro a ha; simp [p10769] at ha; subst a; trivial
  · exact checked10769
theorem derived10769 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10769 := by
  apply localUnsat_implies_entails f10769 [c9748, c2183] c10769 unsat10769 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2183 := h 2182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10770 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10770 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2207, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p10770 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10770 : lratChecker f10770 p10770 = .success := by decide +kernel
theorem unsat10770 : Unsatisfiable (PosFin 65) f10770 := by
  apply lratCheckerSound f10770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10770
  · intro a ha; simp [p10770] at ha; subst a; trivial
  · exact checked10770
theorem derived10770 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10770 := by
  apply localUnsat_implies_entails f10770 [c9748, c2207] c10770 unsat10770 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2207 := h 2206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10771 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10771 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1758, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10771 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10771 : lratChecker f10771 p10771 = .success := by decide +kernel
theorem unsat10771 : Unsatisfiable (PosFin 65) f10771 := by
  apply lratCheckerSound f10771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10771
  · intro a ha; simp [p10771] at ha; subst a; trivial
  · exact checked10771
theorem derived10771 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10771 := by
  apply localUnsat_implies_entails f10771 [c9748, c1758] c10771 unsat10771 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1758 := h 1757 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10772 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10772 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2206, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10772 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10772 : lratChecker f10772 p10772 = .success := by decide +kernel
theorem unsat10772 : Unsatisfiable (PosFin 65) f10772 := by
  apply lratCheckerSound f10772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10772
  · intro a ha; simp [p10772] at ha; subst a; trivial
  · exact checked10772
theorem derived10772 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10772 := by
  apply localUnsat_implies_entails f10772 [c9748, c2206] c10772 unsat10772 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2206 := h 2205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10773 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10773 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1762, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10773 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10773 : lratChecker f10773 p10773 = .success := by decide +kernel
theorem unsat10773 : Unsatisfiable (PosFin 65) f10773 := by
  apply lratCheckerSound f10773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10773
  · intro a ha; simp [p10773] at ha; subst a; trivial
  · exact checked10773
theorem derived10773 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10773 := by
  apply localUnsat_implies_entails f10773 [c9748, c1762] c10773 unsat10773 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1762 := h 1761 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10774 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10774 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2197, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10774 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10774 : lratChecker f10774 p10774 = .success := by decide +kernel
theorem unsat10774 : Unsatisfiable (PosFin 65) f10774 := by
  apply lratCheckerSound f10774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10774
  · intro a ha; simp [p10774] at ha; subst a; trivial
  · exact checked10774
theorem derived10774 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10774 := by
  apply localUnsat_implies_entails f10774 [c9748, c2197] c10774 unsat10774 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2197 := h 2196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10775 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10775 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1763, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10775 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10775 : lratChecker f10775 p10775 = .success := by decide +kernel
theorem unsat10775 : Unsatisfiable (PosFin 65) f10775 := by
  apply lratCheckerSound f10775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10775
  · intro a ha; simp [p10775] at ha; subst a; trivial
  · exact checked10775
theorem derived10775 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10775 := by
  apply localUnsat_implies_entails f10775 [c9748, c1763] c10775 unsat10775 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1763 := h 1762 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10776 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨28, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10776 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2348, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10776 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10776 : lratChecker f10776 p10776 = .success := by decide +kernel
theorem unsat10776 : Unsatisfiable (PosFin 65) f10776 := by
  apply lratCheckerSound f10776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10776
  · intro a ha; simp [p10776] at ha; subst a; trivial
  · exact checked10776
theorem derived10776 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10776 := by
  apply localUnsat_implies_entails f10776 [c9748, c2348] c10776 unsat10776 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2348 := h 2347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10777 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10777 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1778, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10777 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10777 : lratChecker f10777 p10777 = .success := by decide +kernel
theorem unsat10777 : Unsatisfiable (PosFin 65) f10777 := by
  apply lratCheckerSound f10777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10777
  · intro a ha; simp [p10777] at ha; subst a; trivial
  · exact checked10777
theorem derived10777 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10777 := by
  apply localUnsat_implies_entails f10777 [c9748, c1778] c10777 unsat10777 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1778 := h 1777 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10778 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨51, by decide⟩, true), (⟨14, by decide⟩, true), (⟨56, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10778 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2247, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10778 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10778 : lratChecker f10778 p10778 = .success := by decide +kernel
theorem unsat10778 : Unsatisfiable (PosFin 65) f10778 := by
  apply lratCheckerSound f10778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10778
  · intro a ha; simp [p10778] at ha; subst a; trivial
  · exact checked10778
theorem derived10778 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10778 := by
  apply localUnsat_implies_entails f10778 [c9748, c2247] c10778 unsat10778 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2247 := h 2246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10779 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨14, by decide⟩, true), (⟨56, by decide⟩, true), (⟨63, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10779 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2269, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10779 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10779 : lratChecker f10779 p10779 = .success := by decide +kernel
theorem unsat10779 : Unsatisfiable (PosFin 65) f10779 := by
  apply lratCheckerSound f10779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10779
  · intro a ha; simp [p10779] at ha; subst a; trivial
  · exact checked10779
theorem derived10779 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10779 := by
  apply localUnsat_implies_entails f10779 [c9748, c2269] c10779 unsat10779 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2269 := h 2268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10780 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10780 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2070, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10780 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10780 : lratChecker f10780 p10780 = .success := by decide +kernel
theorem unsat10780 : Unsatisfiable (PosFin 65) f10780 := by
  apply lratCheckerSound f10780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10780
  · intro a ha; simp [p10780] at ha; subst a; trivial
  · exact checked10780
theorem derived10780 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10780 := by
  apply localUnsat_implies_entails f10780 [c9748, c2070] c10780 unsat10780 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2070 := h 2069 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10781 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨15, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10781 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2064, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10781 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10781 : lratChecker f10781 p10781 = .success := by decide +kernel
theorem unsat10781 : Unsatisfiable (PosFin 65) f10781 := by
  apply lratCheckerSound f10781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10781
  · intro a ha; simp [p10781] at ha; subst a; trivial
  · exact checked10781
theorem derived10781 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10781 := by
  apply localUnsat_implies_entails f10781 [c9748, c2064] c10781 unsat10781 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2064 := h 2063 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10782 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10782 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2066, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10782 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10782 : lratChecker f10782 p10782 = .success := by decide +kernel
theorem unsat10782 : Unsatisfiable (PosFin 65) f10782 := by
  apply lratCheckerSound f10782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10782
  · intro a ha; simp [p10782] at ha; subst a; trivial
  · exact checked10782
theorem derived10782 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10782 := by
  apply localUnsat_implies_entails f10782 [c9748, c2066] c10782 unsat10782 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2066 := h 2065 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10783 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10783 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1542, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10783 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10783 : lratChecker f10783 p10783 = .success := by decide +kernel
theorem unsat10783 : Unsatisfiable (PosFin 65) f10783 := by
  apply lratCheckerSound f10783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10783
  · intro a ha; simp [p10783] at ha; subst a; trivial
  · exact checked10783
theorem derived10783 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10783 := by
  apply localUnsat_implies_entails f10783 [c9748, c1542] c10783 unsat10783 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1542 := h 1541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10784 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10784 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2050, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10784 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10784 : lratChecker f10784 p10784 = .success := by decide +kernel
theorem unsat10784 : Unsatisfiable (PosFin 65) f10784 := by
  apply lratCheckerSound f10784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10784
  · intro a ha; simp [p10784] at ha; subst a; trivial
  · exact checked10784
theorem derived10784 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10784 := by
  apply localUnsat_implies_entails f10784 [c9748, c2050] c10784 unsat10784 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2050 := h 2049 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10785 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, true), (⟨56, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10785 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2358, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10785 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10785 : lratChecker f10785 p10785 = .success := by decide +kernel
theorem unsat10785 : Unsatisfiable (PosFin 65) f10785 := by
  apply lratCheckerSound f10785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10785
  · intro a ha; simp [p10785] at ha; subst a; trivial
  · exact checked10785
theorem derived10785 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10785 := by
  apply localUnsat_implies_entails f10785 [c9748, c2358] c10785 unsat10785 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2358 := h 2357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10786 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨22, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10786 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1456, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10786 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10786 : lratChecker f10786 p10786 = .success := by decide +kernel
theorem unsat10786 : Unsatisfiable (PosFin 65) f10786 := by
  apply lratCheckerSound f10786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10786
  · intro a ha; simp [p10786] at ha; subst a; trivial
  · exact checked10786
theorem derived10786 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10786 := by
  apply localUnsat_implies_entails f10786 [c9748, c1456] c10786 unsat10786 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1456 := h 1455 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10787 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10787 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1924, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10787 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10787 : lratChecker f10787 p10787 = .success := by decide +kernel
theorem unsat10787 : Unsatisfiable (PosFin 65) f10787 := by
  apply lratCheckerSound f10787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10787
  · intro a ha; simp [p10787] at ha; subst a; trivial
  · exact checked10787
theorem derived10787 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10787 := by
  apply localUnsat_implies_entails f10787 [c9748, c1924] c10787 unsat10787 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1924 := h 1923 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10788 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨7, by decide⟩, true), (⟨31, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10788 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1975, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10788 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10788 : lratChecker f10788 p10788 = .success := by decide +kernel
theorem unsat10788 : Unsatisfiable (PosFin 65) f10788 := by
  apply lratCheckerSound f10788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10788
  · intro a ha; simp [p10788] at ha; subst a; trivial
  · exact checked10788
theorem derived10788 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10788 := by
  apply localUnsat_implies_entails f10788 [c9748, c1975] c10788 unsat10788 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1975 := h 1974 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10789 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10789 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2365, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10789 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10789 : lratChecker f10789 p10789 = .success := by decide +kernel
theorem unsat10789 : Unsatisfiable (PosFin 65) f10789 := by
  apply lratCheckerSound f10789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10789
  · intro a ha; simp [p10789] at ha; subst a; trivial
  · exact checked10789
theorem derived10789 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10789 := by
  apply localUnsat_implies_entails f10789 [c9748, c2365] c10789 unsat10789 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2365 := h 2364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10790 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10790 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2214, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10790 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10790 : lratChecker f10790 p10790 = .success := by decide +kernel
theorem unsat10790 : Unsatisfiable (PosFin 65) f10790 := by
  apply lratCheckerSound f10790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10790
  · intro a ha; simp [p10790] at ha; subst a; trivial
  · exact checked10790
theorem derived10790 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10790 := by
  apply localUnsat_implies_entails f10790 [c9748, c2214] c10790 unsat10790 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2214 := h 2213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10791 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10791 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1552, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10791 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10791 : lratChecker f10791 p10791 = .success := by decide +kernel
theorem unsat10791 : Unsatisfiable (PosFin 65) f10791 := by
  apply lratCheckerSound f10791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10791
  · intro a ha; simp [p10791] at ha; subst a; trivial
  · exact checked10791
theorem derived10791 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10791 := by
  apply localUnsat_implies_entails f10791 [c9748, c1552] c10791 unsat10791 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1552 := h 1551 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10792 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10792 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1678, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10792 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10792 : lratChecker f10792 p10792 = .success := by decide +kernel
theorem unsat10792 : Unsatisfiable (PosFin 65) f10792 := by
  apply lratCheckerSound f10792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10792
  · intro a ha; simp [p10792] at ha; subst a; trivial
  · exact checked10792
theorem derived10792 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10792 := by
  apply localUnsat_implies_entails f10792 [c9748, c1678] c10792 unsat10792 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1678 := h 1677 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10793 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10793 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1971, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10793 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10793 : lratChecker f10793 p10793 = .success := by decide +kernel
theorem unsat10793 : Unsatisfiable (PosFin 65) f10793 := by
  apply lratCheckerSound f10793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10793
  · intro a ha; simp [p10793] at ha; subst a; trivial
  · exact checked10793
theorem derived10793 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10793 := by
  apply localUnsat_implies_entails f10793 [c9748, c1971] c10793 unsat10793 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1971 := h 1970 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10794 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10794 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1982, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10794 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10794 : lratChecker f10794 p10794 = .success := by decide +kernel
theorem unsat10794 : Unsatisfiable (PosFin 65) f10794 := by
  apply lratCheckerSound f10794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10794
  · intro a ha; simp [p10794] at ha; subst a; trivial
  · exact checked10794
theorem derived10794 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10794 := by
  apply localUnsat_implies_entails f10794 [c9748, c1982] c10794 unsat10794 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1982 := h 1981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10795 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨28, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10795 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2296, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p10795 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10795 : lratChecker f10795 p10795 = .success := by decide +kernel
theorem unsat10795 : Unsatisfiable (PosFin 65) f10795 := by
  apply lratCheckerSound f10795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10795
  · intro a ha; simp [p10795] at ha; subst a; trivial
  · exact checked10795
theorem derived10795 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10795 := by
  apply localUnsat_implies_entails f10795 [c9748, c2296] c10795 unsat10795 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2296 := h 2295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10796 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10796 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1473, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p10796 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10796 : lratChecker f10796 p10796 = .success := by decide +kernel
theorem unsat10796 : Unsatisfiable (PosFin 65) f10796 := by
  apply lratCheckerSound f10796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10796
  · intro a ha; simp [p10796] at ha; subst a; trivial
  · exact checked10796
theorem derived10796 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10796 := by
  apply localUnsat_implies_entails f10796 [c9748, c1473] c10796 unsat10796 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1473 := h 1472 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10797 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10797 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1460, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10797 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10797 : lratChecker f10797 p10797 = .success := by decide +kernel
theorem unsat10797 : Unsatisfiable (PosFin 65) f10797 := by
  apply lratCheckerSound f10797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10797
  · intro a ha; simp [p10797] at ha; subst a; trivial
  · exact checked10797
theorem derived10797 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10797 := by
  apply localUnsat_implies_entails f10797 [c9748, c1460] c10797 unsat10797 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1460 := h 1459 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10798 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10798 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1694, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10798 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10798 : lratChecker f10798 p10798 = .success := by decide +kernel
theorem unsat10798 : Unsatisfiable (PosFin 65) f10798 := by
  apply lratCheckerSound f10798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10798
  · intro a ha; simp [p10798] at ha; subst a; trivial
  · exact checked10798
theorem derived10798 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10798 := by
  apply localUnsat_implies_entails f10798 [c9748, c1694] c10798 unsat10798 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1694 := h 1693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10799 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10799 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1848, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10799 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10799 : lratChecker f10799 p10799 = .success := by decide +kernel
theorem unsat10799 : Unsatisfiable (PosFin 65) f10799 := by
  apply lratCheckerSound f10799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10799
  · intro a ha; simp [p10799] at ha; subst a; trivial
  · exact checked10799
theorem derived10799 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10799 := by
  apply localUnsat_implies_entails f10799 [c9748, c1848] c10799 unsat10799 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1848 := h 1847 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10800 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10800 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1472, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10800 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10800 : lratChecker f10800 p10800 = .success := by decide +kernel
theorem unsat10800 : Unsatisfiable (PosFin 65) f10800 := by
  apply lratCheckerSound f10800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10800
  · intro a ha; simp [p10800] at ha; subst a; trivial
  · exact checked10800
theorem derived10800 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10800 := by
  apply localUnsat_implies_entails f10800 [c9748, c1472] c10800 unsat10800 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1472 := h 1471 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10801 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10801 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1696, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10801 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10801 : lratChecker f10801 p10801 = .success := by decide +kernel
theorem unsat10801 : Unsatisfiable (PosFin 65) f10801 := by
  apply lratCheckerSound f10801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10801
  · intro a ha; simp [p10801] at ha; subst a; trivial
  · exact checked10801
theorem derived10801 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10801 := by
  apply localUnsat_implies_entails f10801 [c9748, c1696] c10801 unsat10801 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1696 := h 1695 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10802 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10802 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2218, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p10802 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10802 : lratChecker f10802 p10802 = .success := by decide +kernel
theorem unsat10802 : Unsatisfiable (PosFin 65) f10802 := by
  apply lratCheckerSound f10802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10802
  · intro a ha; simp [p10802] at ha; subst a; trivial
  · exact checked10802
theorem derived10802 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10802 := by
  apply localUnsat_implies_entails f10802 [c9748, c2218] c10802 unsat10802 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2218 := h 2217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10803 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10803 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2342, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10803 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10803 : lratChecker f10803 p10803 = .success := by decide +kernel
theorem unsat10803 : Unsatisfiable (PosFin 65) f10803 := by
  apply lratCheckerSound f10803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10803
  · intro a ha; simp [p10803] at ha; subst a; trivial
  · exact checked10803
theorem derived10803 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10803 := by
  apply localUnsat_implies_entails f10803 [c9748, c2342] c10803 unsat10803 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2342 := h 2341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10804 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10804 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2209, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10804 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10804 : lratChecker f10804 p10804 = .success := by decide +kernel
theorem unsat10804 : Unsatisfiable (PosFin 65) f10804 := by
  apply lratCheckerSound f10804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10804
  · intro a ha; simp [p10804] at ha; subst a; trivial
  · exact checked10804
theorem derived10804 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10804 := by
  apply localUnsat_implies_entails f10804 [c9748, c2209] c10804 unsat10804 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2209 := h 2208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10805 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10805 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1635, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10805 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10805 : lratChecker f10805 p10805 = .success := by decide +kernel
theorem unsat10805 : Unsatisfiable (PosFin 65) f10805 := by
  apply lratCheckerSound f10805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10805
  · intro a ha; simp [p10805] at ha; subst a; trivial
  · exact checked10805
theorem derived10805 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10805 := by
  apply localUnsat_implies_entails f10805 [c9748, c1635] c10805 unsat10805 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1635 := h 1634 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10806 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10806 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1981, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10806 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10806 : lratChecker f10806 p10806 = .success := by decide +kernel
theorem unsat10806 : Unsatisfiable (PosFin 65) f10806 := by
  apply lratCheckerSound f10806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10806
  · intro a ha; simp [p10806] at ha; subst a; trivial
  · exact checked10806
theorem derived10806 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10806 := by
  apply localUnsat_implies_entails f10806 [c9748, c1981] c10806 unsat10806 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1981 := h 1980 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10807 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10807 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1989, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p10807 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10807 : lratChecker f10807 p10807 = .success := by decide +kernel
theorem unsat10807 : Unsatisfiable (PosFin 65) f10807 := by
  apply lratCheckerSound f10807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10807
  · intro a ha; simp [p10807] at ha; subst a; trivial
  · exact checked10807
theorem derived10807 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10807 := by
  apply localUnsat_implies_entails f10807 [c9748, c1989] c10807 unsat10807 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1989 := h 1988 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10808 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10808 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2200, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p10808 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10808 : lratChecker f10808 p10808 = .success := by decide +kernel
theorem unsat10808 : Unsatisfiable (PosFin 65) f10808 := by
  apply lratCheckerSound f10808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10808
  · intro a ha; simp [p10808] at ha; subst a; trivial
  · exact checked10808
theorem derived10808 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10808 := by
  apply localUnsat_implies_entails f10808 [c9748, c2200] c10808 unsat10808 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2200 := h 2199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10809 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10809 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1549, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p10809 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10809 : lratChecker f10809 p10809 = .success := by decide +kernel
theorem unsat10809 : Unsatisfiable (PosFin 65) f10809 := by
  apply lratCheckerSound f10809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10809
  · intro a ha; simp [p10809] at ha; subst a; trivial
  · exact checked10809
theorem derived10809 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10809 := by
  apply localUnsat_implies_entails f10809 [c9748, c1549] c10809 unsat10809 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1549 := h 1548 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10810 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10810 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2040, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p10810 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10810 : lratChecker f10810 p10810 = .success := by decide +kernel
theorem unsat10810 : Unsatisfiable (PosFin 65) f10810 := by
  apply lratCheckerSound f10810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10810
  · intro a ha; simp [p10810] at ha; subst a; trivial
  · exact checked10810
theorem derived10810 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10810 := by
  apply localUnsat_implies_entails f10810 [c9748, c2040] c10810 unsat10810 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2040 := h 2039 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10811 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10811 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1612, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10811 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10811 : lratChecker f10811 p10811 = .success := by decide +kernel
theorem unsat10811 : Unsatisfiable (PosFin 65) f10811 := by
  apply lratCheckerSound f10811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10811
  · intro a ha; simp [p10811] at ha; subst a; trivial
  · exact checked10811
theorem derived10811 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10811 := by
  apply localUnsat_implies_entails f10811 [c9748, c1612] c10811 unsat10811 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1612 := h 1611 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10812 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10812 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1843, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10812 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10812 : lratChecker f10812 p10812 = .success := by decide +kernel
theorem unsat10812 : Unsatisfiable (PosFin 65) f10812 := by
  apply lratCheckerSound f10812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10812
  · intro a ha; simp [p10812] at ha; subst a; trivial
  · exact checked10812
theorem derived10812 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10812 := by
  apply localUnsat_implies_entails f10812 [c9748, c1843] c10812 unsat10812 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1843 := h 1842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10813 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10813 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2285, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p10813 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10813 : lratChecker f10813 p10813 = .success := by decide +kernel
theorem unsat10813 : Unsatisfiable (PosFin 65) f10813 := by
  apply lratCheckerSound f10813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10813
  · intro a ha; simp [p10813] at ha; subst a; trivial
  · exact checked10813
theorem derived10813 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10813 := by
  apply localUnsat_implies_entails f10813 [c9748, c2285] c10813 unsat10813 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2285 := h 2284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10814 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10814 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1697, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p10814 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10814 : lratChecker f10814 p10814 = .success := by decide +kernel
theorem unsat10814 : Unsatisfiable (PosFin 65) f10814 := by
  apply lratCheckerSound f10814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10814
  · intro a ha; simp [p10814] at ha; subst a; trivial
  · exact checked10814
theorem derived10814 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10814 := by
  apply localUnsat_implies_entails f10814 [c9748, c1697] c10814 unsat10814 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1697 := h 1696 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10815 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨31, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10815 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2287, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p10815 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10815 : lratChecker f10815 p10815 = .success := by decide +kernel
theorem unsat10815 : Unsatisfiable (PosFin 65) f10815 := by
  apply lratCheckerSound f10815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10815
  · intro a ha; simp [p10815] at ha; subst a; trivial
  · exact checked10815
theorem derived10815 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10815 := by
  apply localUnsat_implies_entails f10815 [c9748, c2287] c10815 unsat10815 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2287 := h 2286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10816 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10816 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1842, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p10816 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10816 : lratChecker f10816 p10816 = .success := by decide +kernel
theorem unsat10816 : Unsatisfiable (PosFin 65) f10816 := by
  apply lratCheckerSound f10816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10816
  · intro a ha; simp [p10816] at ha; subst a; trivial
  · exact checked10816
theorem derived10816 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10816 := by
  apply localUnsat_implies_entails f10816 [c9748, c1842] c10816 unsat10816 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1842 := h 1841 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10817 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10817 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2311, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p10817 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10817 : lratChecker f10817 p10817 = .success := by decide +kernel
theorem unsat10817 : Unsatisfiable (PosFin 65) f10817 := by
  apply lratCheckerSound f10817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10817
  · intro a ha; simp [p10817] at ha; subst a; trivial
  · exact checked10817
theorem derived10817 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10817 := by
  apply localUnsat_implies_entails f10817 [c9748, c2311] c10817 unsat10817 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2311 := h 2310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10818 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨14, by decide⟩, true), (⟨28, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10818 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2198, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10818 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10818 : lratChecker f10818 p10818 = .success := by decide +kernel
theorem unsat10818 : Unsatisfiable (PosFin 65) f10818 := by
  apply lratCheckerSound f10818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10818
  · intro a ha; simp [p10818] at ha; subst a; trivial
  · exact checked10818
theorem derived10818 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10818 := by
  apply localUnsat_implies_entails f10818 [c9748, c2198] c10818 unsat10818 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2198 := h 2197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10819 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10819 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1674, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10819 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10819 : lratChecker f10819 p10819 = .success := by decide +kernel
theorem unsat10819 : Unsatisfiable (PosFin 65) f10819 := by
  apply lratCheckerSound f10819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10819
  · intro a ha; simp [p10819] at ha; subst a; trivial
  · exact checked10819
theorem derived10819 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10819 := by
  apply localUnsat_implies_entails f10819 [c9748, c1674] c10819 unsat10819 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1674 := h 1673 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10820 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10820 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1690, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p10820 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10820 : lratChecker f10820 p10820 = .success := by decide +kernel
theorem unsat10820 : Unsatisfiable (PosFin 65) f10820 := by
  apply lratCheckerSound f10820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10820
  · intro a ha; simp [p10820] at ha; subst a; trivial
  · exact checked10820
theorem derived10820 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10820 := by
  apply localUnsat_implies_entails f10820 [c9748, c1690] c10820 unsat10820 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1690 := h 1689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10821 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨28, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10821 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1764, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10821 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10821 : lratChecker f10821 p10821 = .success := by decide +kernel
theorem unsat10821 : Unsatisfiable (PosFin 65) f10821 := by
  apply lratCheckerSound f10821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10821
  · intro a ha; simp [p10821] at ha; subst a; trivial
  · exact checked10821
theorem derived10821 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10821 := by
  apply localUnsat_implies_entails f10821 [c9748, c1764] c10821 unsat10821 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1764 := h 1763 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10822 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨28, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10822 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1767, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10822 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10822 : lratChecker f10822 p10822 = .success := by decide +kernel
theorem unsat10822 : Unsatisfiable (PosFin 65) f10822 := by
  apply lratCheckerSound f10822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10822
  · intro a ha; simp [p10822] at ha; subst a; trivial
  · exact checked10822
theorem derived10822 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10822 := by
  apply localUnsat_implies_entails f10822 [c9748, c1767] c10822 unsat10822 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1767 := h 1766 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10823 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨14, by decide⟩, true), (⟨18, by decide⟩, false), (⟨13, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10823 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2201, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p10823 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10823 : lratChecker f10823 p10823 = .success := by decide +kernel
theorem unsat10823 : Unsatisfiable (PosFin 65) f10823 := by
  apply lratCheckerSound f10823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10823
  · intro a ha; simp [p10823] at ha; subst a; trivial
  · exact checked10823
theorem derived10823 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10823 := by
  apply localUnsat_implies_entails f10823 [c9748, c2201] c10823 unsat10823 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2201 := h 2200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10824 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10824 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1673, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p10824 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10824 : lratChecker f10824 p10824 = .success := by decide +kernel
theorem unsat10824 : Unsatisfiable (PosFin 65) f10824 := by
  apply lratCheckerSound f10824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10824
  · intro a ha; simp [p10824] at ha; subst a; trivial
  · exact checked10824
theorem derived10824 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10824 := by
  apply localUnsat_implies_entails f10824 [c9748, c1673] c10824 unsat10824 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1673 := h 1672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10825 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10825 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1675, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p10825 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10825 : lratChecker f10825 p10825 = .success := by decide +kernel
theorem unsat10825 : Unsatisfiable (PosFin 65) f10825 := by
  apply lratCheckerSound f10825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10825
  · intro a ha; simp [p10825] at ha; subst a; trivial
  · exact checked10825
theorem derived10825 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10825 := by
  apply localUnsat_implies_entails f10825 [c9748, c1675] c10825 unsat10825 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1675 := h 1674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10826 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10826 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1457, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10826 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10826 : lratChecker f10826 p10826 = .success := by decide +kernel
theorem unsat10826 : Unsatisfiable (PosFin 65) f10826 := by
  apply lratCheckerSound f10826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10826
  · intro a ha; simp [p10826] at ha; subst a; trivial
  · exact checked10826
theorem derived10826 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10826 := by
  apply localUnsat_implies_entails f10826 [c9748, c1457] c10826 unsat10826 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1457 := h 1456 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10827 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10827 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2039, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10827 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10827 : lratChecker f10827 p10827 = .success := by decide +kernel
theorem unsat10827 : Unsatisfiable (PosFin 65) f10827 := by
  apply lratCheckerSound f10827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10827
  · intro a ha; simp [p10827] at ha; subst a; trivial
  · exact checked10827
theorem derived10827 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10827 := by
  apply localUnsat_implies_entails f10827 [c9748, c2039] c10827 unsat10827 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2039 := h 2038 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10828 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10828 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2196, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p10828 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10828 : lratChecker f10828 p10828 = .success := by decide +kernel
theorem unsat10828 : Unsatisfiable (PosFin 65) f10828 := by
  apply lratCheckerSound f10828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10828
  · intro a ha; simp [p10828] at ha; subst a; trivial
  · exact checked10828
theorem derived10828 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10828 := by
  apply localUnsat_implies_entails f10828 [c9748, c2196] c10828 unsat10828 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2196 := h 2195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10829 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10829 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1698, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10829 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10829 : lratChecker f10829 p10829 = .success := by decide +kernel
theorem unsat10829 : Unsatisfiable (PosFin 65) f10829 := by
  apply lratCheckerSound f10829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10829
  · intro a ha; simp [p10829] at ha; subst a; trivial
  · exact checked10829
theorem derived10829 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10829 := by
  apply localUnsat_implies_entails f10829 [c9748, c1698] c10829 unsat10829 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1698 := h 1697 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10830 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10830 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1770, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10830 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10830 : lratChecker f10830 p10830 = .success := by decide +kernel
theorem unsat10830 : Unsatisfiable (PosFin 65) f10830 := by
  apply lratCheckerSound f10830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10830
  · intro a ha; simp [p10830] at ha; subst a; trivial
  · exact checked10830
theorem derived10830 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10830 := by
  apply localUnsat_implies_entails f10830 [c9748, c1770] c10830 unsat10830 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1770 := h 1769 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10831 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10831 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8374, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10831 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10831 : lratChecker f10831 p10831 = .success := by decide +kernel
theorem unsat10831 : Unsatisfiable (PosFin 65) f10831 := by
  apply lratCheckerSound f10831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10831
  · intro a ha; simp [p10831] at ha; subst a; trivial
  · exact checked10831
theorem derived10831 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10831 := by
  apply localUnsat_implies_entails f10831 [c9748, c8374] c10831 unsat10831 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8374 := derived8374 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10832 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10832 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c3793, some c5082, some c3523, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10832 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10832 : lratChecker f10832 p10832 = .success := by decide +kernel
theorem unsat10832 : Unsatisfiable (PosFin 65) f10832 := by
  apply lratCheckerSound f10832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10832
  · intro a ha; simp [p10832] at ha; subst a; trivial
  · exact checked10832
theorem derived10832 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10832 := by
  apply localUnsat_implies_entails f10832 [c8269, c3793, c5082, c3523] c10832 unsat10832 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c3793 := h 3792 (by decide)
  have h2 : Entails.eval a c5082 := h 5081 (by decide)
  have h3 : Entails.eval a c3523 := h 3522 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10833 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨52, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10833 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c10832, some c10131, some c4683, some c10371, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10833 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10833 : lratChecker f10833 p10833 = .success := by decide +kernel
theorem unsat10833 : Unsatisfiable (PosFin 65) f10833 := by
  apply lratCheckerSound f10833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10833
  · intro a ha; simp [p10833] at ha; subst a; trivial
  · exact checked10833
theorem derived10833 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10833 := by
  apply localUnsat_implies_entails f10833 [c7994, c10832, c10131, c4683, c10371] c10833 unsat10833 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c10832 := derived10832 a h
  have h2 : Entails.eval a c10131 := derived10131 a h
  have h3 : Entails.eval a c4683 := h 4682 (by decide)
  have h4 : Entails.eval a c10371 := derived10371 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10834 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨52, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10834 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8300, some c10833, some c4424, some c4306, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10834 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10834 : lratChecker f10834 p10834 = .success := by decide +kernel
theorem unsat10834 : Unsatisfiable (PosFin 65) f10834 := by
  apply lratCheckerSound f10834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10834
  · intro a ha; simp [p10834] at ha; subst a; trivial
  · exact checked10834
theorem derived10834 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10834 := by
  apply localUnsat_implies_entails f10834 [c8380, c8300, c10833, c4424, c4306] c10834 unsat10834 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8300 := derived8300 a h
  have h2 : Entails.eval a c10833 := derived10833 a h
  have h3 : Entails.eval a c4424 := h 4423 (by decide)
  have h4 : Entails.eval a c4306 := h 4305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10835 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10835 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c4338, some c3949, some c4195, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p10835 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10835 : lratChecker f10835 p10835 = .success := by decide +kernel
theorem unsat10835 : Unsatisfiable (PosFin 65) f10835 := by
  apply lratCheckerSound f10835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10835
  · intro a ha; simp [p10835] at ha; subst a; trivial
  · exact checked10835
theorem derived10835 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10835 := by
  apply localUnsat_implies_entails f10835 [c8269, c4338, c3949, c4195] c10835 unsat10835 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c4338 := h 4337 (by decide)
  have h2 : Entails.eval a c3949 := h 3948 (by decide)
  have h3 : Entails.eval a c4195 := h 4194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10836 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10836 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8300, some c10835, some c3391, some c2495, some c2650, some c4786, some c10327, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10836 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10836 : lratChecker f10836 p10836 = .success := by decide +kernel
theorem unsat10836 : Unsatisfiable (PosFin 65) f10836 := by
  apply lratCheckerSound f10836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10836
  · intro a ha; simp [p10836] at ha; subst a; trivial
  · exact checked10836
theorem derived10836 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10836 := by
  apply localUnsat_implies_entails f10836 [c8380, c8300, c10835, c3391, c2495, c2650, c4786, c10327] c10836 unsat10836 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8300 := derived8300 a h
  have h2 : Entails.eval a c10835 := derived10835 a h
  have h3 : Entails.eval a c3391 := h 3390 (by decide)
  have h4 : Entails.eval a c2495 := h 2494 (by decide)
  have h5 : Entails.eval a c2650 := h 2649 (by decide)
  have h6 : Entails.eval a c4786 := h 4785 (by decide)
  have h7 : Entails.eval a c10327 := derived10327 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10837 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10837 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3391, some c10336, some c4786, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10837 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10837 : lratChecker f10837 p10837 = .success := by decide +kernel
theorem unsat10837 : Unsatisfiable (PosFin 65) f10837 := by
  apply lratCheckerSound f10837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10837
  · intro a ha; simp [p10837] at ha; subst a; trivial
  · exact checked10837
theorem derived10837 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10837 := by
  apply localUnsat_implies_entails f10837 [c3391, c10336, c4786] c10837 unsat10837 (by rfl) a
  have h0 : Entails.eval a c3391 := h 3390 (by decide)
  have h1 : Entails.eval a c10336 := derived10336 a h
  have h2 : Entails.eval a c4786 := h 4785 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10838 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10838 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10187, some c10197, some c10202, some c10204, some c8300, some c8380, some c10834, some c10836, some c10837, some c10191, some c10371, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10838 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10838 : lratChecker f10838 p10838 = .success := by decide +kernel
theorem unsat10838 : Unsatisfiable (PosFin 65) f10838 := by
  apply lratCheckerSound f10838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10838
  · intro a ha; simp [p10838] at ha; subst a; trivial
  · exact checked10838
theorem derived10838 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10838 := by
  apply localUnsat_implies_entails f10838 [c10187, c10197, c10202, c10204, c8300, c8380, c10834, c10836, c10837, c10191, c10371] c10838 unsat10838 (by rfl) a
  have h0 : Entails.eval a c10187 := derived10187 a h
  have h1 : Entails.eval a c10197 := derived10197 a h
  have h2 : Entails.eval a c10202 := derived10202 a h
  have h3 : Entails.eval a c10204 := derived10204 a h
  have h4 : Entails.eval a c8300 := derived8300 a h
  have h5 : Entails.eval a c8380 := derived8380 a h
  have h6 : Entails.eval a c10834 := derived10834 a h
  have h7 : Entails.eval a c10836 := derived10836 a h
  have h8 : Entails.eval a c10837 := derived10837 a h
  have h9 : Entails.eval a c10191 := derived10191 a h
  have h10 : Entails.eval a c10371 := derived10371 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10839 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨61, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10839 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10191, some c10346, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p10839 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10839 : lratChecker f10839 p10839 = .success := by decide +kernel
theorem unsat10839 : Unsatisfiable (PosFin 65) f10839 := by
  apply lratCheckerSound f10839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10839
  · intro a ha; simp [p10839] at ha; subst a; trivial
  · exact checked10839
theorem derived10839 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10839 := by
  apply localUnsat_implies_entails f10839 [c10191, c10346] c10839 unsat10839 (by rfl) a
  have h0 : Entails.eval a c10191 := derived10191 a h
  have h1 : Entails.eval a c10346 := derived10346 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10840 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10840 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10754, some c10334, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10840 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10840 : lratChecker f10840 p10840 = .success := by decide +kernel
theorem unsat10840 : Unsatisfiable (PosFin 65) f10840 := by
  apply lratCheckerSound f10840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10840
  · intro a ha; simp [p10840] at ha; subst a; trivial
  · exact checked10840
theorem derived10840 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10840 := by
  apply localUnsat_implies_entails f10840 [c10754, c10334] c10840 unsat10840 (by rfl) a
  have h0 : Entails.eval a c10754 := derived10754 a h
  have h1 : Entails.eval a c10334 := derived10334 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10841 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10841 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2956, some c10353, some c10161, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10841 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10841 : lratChecker f10841 p10841 = .success := by decide +kernel
theorem unsat10841 : Unsatisfiable (PosFin 65) f10841 := by
  apply lratCheckerSound f10841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10841
  · intro a ha; simp [p10841] at ha; subst a; trivial
  · exact checked10841
theorem derived10841 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10841 := by
  apply localUnsat_implies_entails f10841 [c2956, c10353, c10161] c10841 unsat10841 (by rfl) a
  have h0 : Entails.eval a c2956 := h 2955 (by decide)
  have h1 : Entails.eval a c10353 := derived10353 a h
  have h2 : Entails.eval a c10161 := derived10161 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10842 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10842 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10838, some c10187, some c10840, some c10599, some c4780, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10842 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10842 : lratChecker f10842 p10842 = .success := by decide +kernel
theorem unsat10842 : Unsatisfiable (PosFin 65) f10842 := by
  apply lratCheckerSound f10842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10842
  · intro a ha; simp [p10842] at ha; subst a; trivial
  · exact checked10842
theorem derived10842 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10842 := by
  apply localUnsat_implies_entails f10842 [c10838, c10187, c10840, c10599, c4780] c10842 unsat10842 (by rfl) a
  have h0 : Entails.eval a c10838 := derived10838 a h
  have h1 : Entails.eval a c10187 := derived10187 a h
  have h2 : Entails.eval a c10840 := derived10840 a h
  have h3 : Entails.eval a c10599 := derived10599 a h
  have h4 : Entails.eval a c4780 := h 4779 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10843 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨63, by decide⟩, false), (⟨52, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10843 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4778, some c4788, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10843 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10843 : lratChecker f10843 p10843 = .success := by decide +kernel
theorem unsat10843 : Unsatisfiable (PosFin 65) f10843 := by
  apply lratCheckerSound f10843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10843
  · intro a ha; simp [p10843] at ha; subst a; trivial
  · exact checked10843
theorem derived10843 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10843 := by
  apply localUnsat_implies_entails f10843 [c4778, c4788] c10843 unsat10843 (by rfl) a
  have h0 : Entails.eval a c4778 := h 4777 (by decide)
  have h1 : Entails.eval a c4788 := h 4787 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10844 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10844 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10203, some c3396, some c3132, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10844 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10844 : lratChecker f10844 p10844 = .success := by decide +kernel
theorem unsat10844 : Unsatisfiable (PosFin 65) f10844 := by
  apply lratCheckerSound f10844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10844
  · intro a ha; simp [p10844] at ha; subst a; trivial
  · exact checked10844
theorem derived10844 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10844 := by
  apply localUnsat_implies_entails f10844 [c10203, c3396, c3132] c10844 unsat10844 (by rfl) a
  have h0 : Entails.eval a c10203 := derived10203 a h
  have h1 : Entails.eval a c3396 := h 3395 (by decide)
  have h2 : Entails.eval a c3132 := h 3131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10845 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10845 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10838, some c10187, some c10841, some c10842, some c10203, some c10844, some c10843, some c10520, some c10648, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10845 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10845 : lratChecker f10845 p10845 = .success := by decide +kernel
theorem unsat10845 : Unsatisfiable (PosFin 65) f10845 := by
  apply lratCheckerSound f10845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10845
  · intro a ha; simp [p10845] at ha; subst a; trivial
  · exact checked10845
theorem derived10845 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10845 := by
  apply localUnsat_implies_entails f10845 [c10838, c10187, c10841, c10842, c10203, c10844, c10843, c10520, c10648] c10845 unsat10845 (by rfl) a
  have h0 : Entails.eval a c10838 := derived10838 a h
  have h1 : Entails.eval a c10187 := derived10187 a h
  have h2 : Entails.eval a c10841 := derived10841 a h
  have h3 : Entails.eval a c10842 := derived10842 a h
  have h4 : Entails.eval a c10203 := derived10203 a h
  have h5 : Entails.eval a c10844 := derived10844 a h
  have h6 : Entails.eval a c10843 := derived10843 a h
  have h7 : Entails.eval a c10520 := derived10520 a h
  have h8 : Entails.eval a c10648 := derived10648 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10846 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10846 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10520, some c10648, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10846 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10846 : lratChecker f10846 p10846 = .success := by decide +kernel
theorem unsat10846 : Unsatisfiable (PosFin 65) f10846 := by
  apply lratCheckerSound f10846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10846
  · intro a ha; simp [p10846] at ha; subst a; trivial
  · exact checked10846
theorem derived10846 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10846 := by
  apply localUnsat_implies_entails f10846 [c10520, c10648] c10846 unsat10846 (by rfl) a
  have h0 : Entails.eval a c10520 := derived10520 a h
  have h1 : Entails.eval a c10648 := derived10648 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10847 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10847 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10838, some c10187, some c10842, some c10846, some c3149, some c3168, some c3152, some c3145, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10847 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10847 : lratChecker f10847 p10847 = .success := by decide +kernel
theorem unsat10847 : Unsatisfiable (PosFin 65) f10847 := by
  apply lratCheckerSound f10847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10847
  · intro a ha; simp [p10847] at ha; subst a; trivial
  · exact checked10847
theorem derived10847 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10847 := by
  apply localUnsat_implies_entails f10847 [c10838, c10187, c10842, c10846, c3149, c3168, c3152, c3145] c10847 unsat10847 (by rfl) a
  have h0 : Entails.eval a c10838 := derived10838 a h
  have h1 : Entails.eval a c10187 := derived10187 a h
  have h2 : Entails.eval a c10842 := derived10842 a h
  have h3 : Entails.eval a c10846 := derived10846 a h
  have h4 : Entails.eval a c3149 := h 3148 (by decide)
  have h5 : Entails.eval a c3168 := h 3167 (by decide)
  have h6 : Entails.eval a c3152 := h 3151 (by decide)
  have h7 : Entails.eval a c3145 := h 3144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10848 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10848 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10838, some c10187, some c10845, some c10847, some c3166, some c10334, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10848 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10848 : lratChecker f10848 p10848 = .success := by decide +kernel
theorem unsat10848 : Unsatisfiable (PosFin 65) f10848 := by
  apply lratCheckerSound f10848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10848
  · intro a ha; simp [p10848] at ha; subst a; trivial
  · exact checked10848
theorem derived10848 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10848 := by
  apply localUnsat_implies_entails f10848 [c10838, c10187, c10845, c10847, c3166, c10334] c10848 unsat10848 (by rfl) a
  have h0 : Entails.eval a c10838 := derived10838 a h
  have h1 : Entails.eval a c10187 := derived10187 a h
  have h2 : Entails.eval a c10845 := derived10845 a h
  have h3 : Entails.eval a c10847 := derived10847 a h
  have h4 : Entails.eval a c3166 := h 3165 (by decide)
  have h5 : Entails.eval a c10334 := derived10334 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10849 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10849 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4525, some c10781, some c10161, some c10172, some c3503, some c3508, some c3510, some c4179, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10849 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10849 : lratChecker f10849 p10849 = .success := by decide +kernel
theorem unsat10849 : Unsatisfiable (PosFin 65) f10849 := by
  apply lratCheckerSound f10849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10849
  · intro a ha; simp [p10849] at ha; subst a; trivial
  · exact checked10849
theorem derived10849 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10849 := by
  apply localUnsat_implies_entails f10849 [c4525, c10781, c10161, c10172, c3503, c3508, c3510, c4179] c10849 unsat10849 (by rfl) a
  have h0 : Entails.eval a c4525 := h 4524 (by decide)
  have h1 : Entails.eval a c10781 := derived10781 a h
  have h2 : Entails.eval a c10161 := derived10161 a h
  have h3 : Entails.eval a c10172 := derived10172 a h
  have h4 : Entails.eval a c3503 := h 3502 (by decide)
  have h5 : Entails.eval a c3508 := h 3507 (by decide)
  have h6 : Entails.eval a c3510 := h 3509 (by decide)
  have h7 : Entails.eval a c4179 := h 4178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10850 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨58, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10850 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4357, some c10780, some c10265, some c10172, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10850 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10850 : lratChecker f10850 p10850 = .success := by decide +kernel
theorem unsat10850 : Unsatisfiable (PosFin 65) f10850 := by
  apply lratCheckerSound f10850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10850
  · intro a ha; simp [p10850] at ha; subst a; trivial
  · exact checked10850
theorem derived10850 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10850 := by
  apply localUnsat_implies_entails f10850 [c4357, c10780, c10265, c10172] c10850 unsat10850 (by rfl) a
  have h0 : Entails.eval a c4357 := h 4356 (by decide)
  have h1 : Entails.eval a c10780 := derived10780 a h
  have h2 : Entails.eval a c10265 := derived10265 a h
  have h3 : Entails.eval a c10172 := derived10172 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived10850

end CochromaticTwenty.Certificates.FixedCore0
