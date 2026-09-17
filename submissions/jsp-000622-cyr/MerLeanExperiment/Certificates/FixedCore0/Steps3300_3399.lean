import MerLeanExperiment.Certificates.FixedCore0.Steps3200_3299

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10851 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10851 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10838, some c10187, some c10848, some c10849, some c10850, some c4353, some c10246, some c4939, some c4050, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10851 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10851 : lratChecker f10851 p10851 = .success := by decide +kernel
theorem unsat10851 : Unsatisfiable (PosFin 65) f10851 := by
  apply lratCheckerSound f10851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10851
  · intro a ha; simp [p10851] at ha; subst a; trivial
  · exact checked10851
theorem derived10851 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10851 := by
  apply localUnsat_implies_entails f10851 [c10838, c10187, c10848, c10849, c10850, c4353, c10246, c4939, c4050] c10851 unsat10851 (by rfl) a
  have h0 : Entails.eval a c10838 := derived10838 a h
  have h1 : Entails.eval a c10187 := derived10187 a h
  have h2 : Entails.eval a c10848 := derived10848 a h
  have h3 : Entails.eval a c10849 := derived10849 a h
  have h4 : Entails.eval a c10850 := derived10850 a h
  have h5 : Entails.eval a c4353 := h 4352 (by decide)
  have h6 : Entails.eval a c10246 := derived10246 a h
  have h7 : Entails.eval a c4939 := h 4938 (by decide)
  have h8 : Entails.eval a c4050 := h 4049 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10852 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨13, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10852 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10851, some c10838, some c10187, some c4314, some c4412, some c4289, some c10850, some c4291, some c4515, some c10262, some c3947, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10852 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10852 : lratChecker f10852 p10852 = .success := by decide +kernel
theorem unsat10852 : Unsatisfiable (PosFin 65) f10852 := by
  apply lratCheckerSound f10852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10852
  · intro a ha; simp [p10852] at ha; subst a; trivial
  · exact checked10852
theorem derived10852 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10852 := by
  apply localUnsat_implies_entails f10852 [c10851, c10838, c10187, c4314, c4412, c4289, c10850, c4291, c4515, c10262, c3947] c10852 unsat10852 (by rfl) a
  have h0 : Entails.eval a c10851 := derived10851 a h
  have h1 : Entails.eval a c10838 := derived10838 a h
  have h2 : Entails.eval a c10187 := derived10187 a h
  have h3 : Entails.eval a c4314 := h 4313 (by decide)
  have h4 : Entails.eval a c4412 := h 4411 (by decide)
  have h5 : Entails.eval a c4289 := h 4288 (by decide)
  have h6 : Entails.eval a c10850 := derived10850 a h
  have h7 : Entails.eval a c4291 := h 4290 (by decide)
  have h8 : Entails.eval a c4515 := h 4514 (by decide)
  have h9 : Entails.eval a c10262 := derived10262 a h
  have h10 : Entails.eval a c3947 := h 3946 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10853 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨64, by decide⟩, true), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10853 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10334, some c10841, some c3166, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10853 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10853 : lratChecker f10853 p10853 = .success := by decide +kernel
theorem unsat10853 : Unsatisfiable (PosFin 65) f10853 := by
  apply lratCheckerSound f10853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10853
  · intro a ha; simp [p10853] at ha; subst a; trivial
  · exact checked10853
theorem derived10853 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10853 := by
  apply localUnsat_implies_entails f10853 [c10334, c10841, c3166] c10853 unsat10853 (by rfl) a
  have h0 : Entails.eval a c10334 := derived10334 a h
  have h1 : Entails.eval a c10841 := derived10841 a h
  have h2 : Entails.eval a c3166 := h 3165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10854 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10854 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10838, some c10187, some c10851, some c10852, some c10853, some c10842, some c10846, some c4678, some c4673, some c4674, some c4672, some c4692, some c4682, some c4676, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10854 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10854 : lratChecker f10854 p10854 = .success := by decide +kernel
theorem unsat10854 : Unsatisfiable (PosFin 65) f10854 := by
  apply lratCheckerSound f10854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10854
  · intro a ha; simp [p10854] at ha; subst a; trivial
  · exact checked10854
theorem derived10854 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10854 := by
  apply localUnsat_implies_entails f10854 [c10838, c10187, c10851, c10852, c10853, c10842, c10846, c4678, c4673, c4674, c4672, c4692, c4682, c4676] c10854 unsat10854 (by rfl) a
  have h0 : Entails.eval a c10838 := derived10838 a h
  have h1 : Entails.eval a c10187 := derived10187 a h
  have h2 : Entails.eval a c10851 := derived10851 a h
  have h3 : Entails.eval a c10852 := derived10852 a h
  have h4 : Entails.eval a c10853 := derived10853 a h
  have h5 : Entails.eval a c10842 := derived10842 a h
  have h6 : Entails.eval a c10846 := derived10846 a h
  have h7 : Entails.eval a c4678 := h 4677 (by decide)
  have h8 : Entails.eval a c4673 := h 4672 (by decide)
  have h9 : Entails.eval a c4674 := h 4673 (by decide)
  have h10 : Entails.eval a c4672 := h 4671 (by decide)
  have h11 : Entails.eval a c4692 := h 4691 (by decide)
  have h12 : Entails.eval a c4682 := h 4681 (by decide)
  have h13 : Entails.eval a c4676 := h 4675 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10855 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10855 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10854, some c10838, some c10187, some c10842, some c10846, some c10847, some c10193, some c10843, some c10601, some c10529, some c10303, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10855 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10855 : lratChecker f10855 p10855 = .success := by decide +kernel
theorem unsat10855 : Unsatisfiable (PosFin 65) f10855 := by
  apply lratCheckerSound f10855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10855
  · intro a ha; simp [p10855] at ha; subst a; trivial
  · exact checked10855
theorem derived10855 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10855 := by
  apply localUnsat_implies_entails f10855 [c10854, c10838, c10187, c10842, c10846, c10847, c10193, c10843, c10601, c10529, c10303] c10855 unsat10855 (by rfl) a
  have h0 : Entails.eval a c10854 := derived10854 a h
  have h1 : Entails.eval a c10838 := derived10838 a h
  have h2 : Entails.eval a c10187 := derived10187 a h
  have h3 : Entails.eval a c10842 := derived10842 a h
  have h4 : Entails.eval a c10846 := derived10846 a h
  have h5 : Entails.eval a c10847 := derived10847 a h
  have h6 : Entails.eval a c10193 := derived10193 a h
  have h7 : Entails.eval a c10843 := derived10843 a h
  have h8 : Entails.eval a c10601 := derived10601 a h
  have h9 : Entails.eval a c10529 := derived10529 a h
  have h10 : Entails.eval a c10303 := derived10303 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10856 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨60, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10856 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10838, some c10187, some c10855, some c10854, some c10290, some c3166, some c10193, some c10843, some c3138, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10856 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10856 : lratChecker f10856 p10856 = .success := by decide +kernel
theorem unsat10856 : Unsatisfiable (PosFin 65) f10856 := by
  apply lratCheckerSound f10856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10856
  · intro a ha; simp [p10856] at ha; subst a; trivial
  · exact checked10856
theorem derived10856 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10856 := by
  apply localUnsat_implies_entails f10856 [c10838, c10187, c10855, c10854, c10290, c3166, c10193, c10843, c3138] c10856 unsat10856 (by rfl) a
  have h0 : Entails.eval a c10838 := derived10838 a h
  have h1 : Entails.eval a c10187 := derived10187 a h
  have h2 : Entails.eval a c10855 := derived10855 a h
  have h3 : Entails.eval a c10854 := derived10854 a h
  have h4 : Entails.eval a c10290 := derived10290 a h
  have h5 : Entails.eval a c3166 := h 3165 (by decide)
  have h6 : Entails.eval a c10193 := derived10193 a h
  have h7 : Entails.eval a c10843 := derived10843 a h
  have h8 : Entails.eval a c3138 := h 3137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10857 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10857 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10839, some c10194, some c4496, some c5071, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10857 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10857 : lratChecker f10857 p10857 = .success := by decide +kernel
theorem unsat10857 : Unsatisfiable (PosFin 65) f10857 := by
  apply lratCheckerSound f10857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10857
  · intro a ha; simp [p10857] at ha; subst a; trivial
  · exact checked10857
theorem derived10857 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10857 := by
  apply localUnsat_implies_entails f10857 [c10839, c10194, c4496, c5071] c10857 unsat10857 (by rfl) a
  have h0 : Entails.eval a c10839 := derived10839 a h
  have h1 : Entails.eval a c10194 := derived10194 a h
  have h2 : Entails.eval a c4496 := h 4495 (by decide)
  have h3 : Entails.eval a c5071 := h 5070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10858 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10858 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10854, some c10838, some c10187, some c10855, some c10290, some c10353, some c3166, some c4973, some c2516, some c3348, some c10857, some c10193, some c10856, some c10843, some c10308, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10858 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked10858 : lratChecker f10858 p10858 = .success := by decide +kernel
theorem unsat10858 : Unsatisfiable (PosFin 65) f10858 := by
  apply lratCheckerSound f10858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10858
  · intro a ha; simp [p10858] at ha; subst a; trivial
  · exact checked10858
theorem derived10858 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10858 := by
  apply localUnsat_implies_entails f10858 [c10854, c10838, c10187, c10855, c10290, c10353, c3166, c4973, c2516, c3348, c10857, c10193, c10856, c10843, c10308] c10858 unsat10858 (by rfl) a
  have h0 : Entails.eval a c10854 := derived10854 a h
  have h1 : Entails.eval a c10838 := derived10838 a h
  have h2 : Entails.eval a c10187 := derived10187 a h
  have h3 : Entails.eval a c10855 := derived10855 a h
  have h4 : Entails.eval a c10290 := derived10290 a h
  have h5 : Entails.eval a c10353 := derived10353 a h
  have h6 : Entails.eval a c3166 := h 3165 (by decide)
  have h7 : Entails.eval a c4973 := h 4972 (by decide)
  have h8 : Entails.eval a c2516 := h 2515 (by decide)
  have h9 : Entails.eval a c3348 := h 3347 (by decide)
  have h10 : Entails.eval a c10857 := derived10857 a h
  have h11 : Entails.eval a c10193 := derived10193 a h
  have h12 : Entails.eval a c10856 := derived10856 a h
  have h13 : Entails.eval a c10843 := derived10843 a h
  have h14 : Entails.eval a c10308 := derived10308 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10859 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨64, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10859 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4314, some c4353, some c10246, some c4939, some c4096, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10859 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10859 : lratChecker f10859 p10859 = .success := by decide +kernel
theorem unsat10859 : Unsatisfiable (PosFin 65) f10859 := by
  apply lratCheckerSound f10859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10859
  · intro a ha; simp [p10859] at ha; subst a; trivial
  · exact checked10859
theorem derived10859 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10859 := by
  apply localUnsat_implies_entails f10859 [c4314, c4353, c10246, c4939, c4096] c10859 unsat10859 (by rfl) a
  have h0 : Entails.eval a c4314 := h 4313 (by decide)
  have h1 : Entails.eval a c4353 := h 4352 (by decide)
  have h2 : Entails.eval a c10246 := derived10246 a h
  have h3 : Entails.eval a c4939 := h 4938 (by decide)
  have h4 : Entails.eval a c4096 := h 4095 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10860 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨60, by decide⟩, false), (⟨14, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10860 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4085, some c4075, some c4074, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10860 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10860 : lratChecker f10860 p10860 = .success := by decide +kernel
theorem unsat10860 : Unsatisfiable (PosFin 65) f10860 := by
  apply lratCheckerSound f10860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10860
  · intro a ha; simp [p10860] at ha; subst a; trivial
  · exact checked10860
theorem derived10860 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10860 := by
  apply localUnsat_implies_entails f10860 [c4085, c4075, c4074] c10860 unsat10860 (by rfl) a
  have h0 : Entails.eval a c4085 := h 4084 (by decide)
  have h1 : Entails.eval a c4075 := h 4074 (by decide)
  have h2 : Entails.eval a c4074 := h 4073 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10861 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨60, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10861 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4192, some c4182, some c4179, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10861 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10861 : lratChecker f10861 p10861 = .success := by decide +kernel
theorem unsat10861 : Unsatisfiable (PosFin 65) f10861 := by
  apply lratCheckerSound f10861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10861
  · intro a ha; simp [p10861] at ha; subst a; trivial
  · exact checked10861
theorem derived10861 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10861 := by
  apply localUnsat_implies_entails f10861 [c4192, c4182, c4179] c10861 unsat10861 (by rfl) a
  have h0 : Entails.eval a c4192 := h 4191 (by decide)
  have h1 : Entails.eval a c4182 := h 4181 (by decide)
  have h2 : Entails.eval a c4179 := h 4178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10862 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨60, by decide⟩, false), (⟨6, by decide⟩, false), (⟨64, by decide⟩, true), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10862 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4332, some c4351, some c4333, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10862 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10862 : lratChecker f10862 p10862 = .success := by decide +kernel
theorem unsat10862 : Unsatisfiable (PosFin 65) f10862 := by
  apply lratCheckerSound f10862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10862
  · intro a ha; simp [p10862] at ha; subst a; trivial
  · exact checked10862
theorem derived10862 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10862 := by
  apply localUnsat_implies_entails f10862 [c4332, c4351, c4333] c10862 unsat10862 (by rfl) a
  have h0 : Entails.eval a c4332 := h 4331 (by decide)
  have h1 : Entails.eval a c4351 := h 4350 (by decide)
  have h2 : Entails.eval a c4333 := h 4332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10863 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨60, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨64, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10863 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10250, some c10271, some c10861, some c4291, some c4673, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10863 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10863 : lratChecker f10863 p10863 = .success := by decide +kernel
theorem unsat10863 : Unsatisfiable (PosFin 65) f10863 := by
  apply lratCheckerSound f10863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10863
  · intro a ha; simp [p10863] at ha; subst a; trivial
  · exact checked10863
theorem derived10863 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10863 := by
  apply localUnsat_implies_entails f10863 [c10250, c10271, c10861, c4291, c4673] c10863 unsat10863 (by rfl) a
  have h0 : Entails.eval a c10250 := derived10250 a h
  have h1 : Entails.eval a c10271 := derived10271 a h
  have h2 : Entails.eval a c10861 := derived10861 a h
  have h3 : Entails.eval a c4291 := h 4290 (by decide)
  have h4 : Entails.eval a c4673 := h 4672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10864 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10864 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10858, some c10838, some c10187, some c10859, some c10862, some c10863, some c10860, some c10781, some c10780, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10864 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10864 : lratChecker f10864 p10864 = .success := by decide +kernel
theorem unsat10864 : Unsatisfiable (PosFin 65) f10864 := by
  apply lratCheckerSound f10864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10864
  · intro a ha; simp [p10864] at ha; subst a; trivial
  · exact checked10864
theorem derived10864 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10864 := by
  apply localUnsat_implies_entails f10864 [c10858, c10838, c10187, c10859, c10862, c10863, c10860, c10781, c10780] c10864 unsat10864 (by rfl) a
  have h0 : Entails.eval a c10858 := derived10858 a h
  have h1 : Entails.eval a c10838 := derived10838 a h
  have h2 : Entails.eval a c10187 := derived10187 a h
  have h3 : Entails.eval a c10859 := derived10859 a h
  have h4 : Entails.eval a c10862 := derived10862 a h
  have h5 : Entails.eval a c10863 := derived10863 a h
  have h6 : Entails.eval a c10860 := derived10860 a h
  have h7 : Entails.eval a c10781 := derived10781 a h
  have h8 : Entails.eval a c10780 := derived10780 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10865 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10865 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10187, some c10838, some c10854, some c10858, some c10864, some c10290, some c10521, some c10646, some c4357, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10865 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10865 : lratChecker f10865 p10865 = .success := by decide +kernel
theorem unsat10865 : Unsatisfiable (PosFin 65) f10865 := by
  apply lratCheckerSound f10865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10865
  · intro a ha; simp [p10865] at ha; subst a; trivial
  · exact checked10865
theorem derived10865 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10865 := by
  apply localUnsat_implies_entails f10865 [c10187, c10838, c10854, c10858, c10864, c10290, c10521, c10646, c4357] c10865 unsat10865 (by rfl) a
  have h0 : Entails.eval a c10187 := derived10187 a h
  have h1 : Entails.eval a c10838 := derived10838 a h
  have h2 : Entails.eval a c10854 := derived10854 a h
  have h3 : Entails.eval a c10858 := derived10858 a h
  have h4 : Entails.eval a c10864 := derived10864 a h
  have h5 : Entails.eval a c10290 := derived10290 a h
  have h6 : Entails.eval a c10521 := derived10521 a h
  have h7 : Entails.eval a c10646 := derived10646 a h
  have h8 : Entails.eval a c4357 := h 4356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10866 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨60, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10866 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10865, some c10862, some c10651, some c10751, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10866 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10866 : lratChecker f10866 p10866 = .success := by decide +kernel
theorem unsat10866 : Unsatisfiable (PosFin 65) f10866 := by
  apply lratCheckerSound f10866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10866
  · intro a ha; simp [p10866] at ha; subst a; trivial
  · exact checked10866
theorem derived10866 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10866 := by
  apply localUnsat_implies_entails f10866 [c10865, c10862, c10651, c10751] c10866 unsat10866 (by rfl) a
  have h0 : Entails.eval a c10865 := derived10865 a h
  have h1 : Entails.eval a c10862 := derived10862 a h
  have h2 : Entails.eval a c10651 := derived10651 a h
  have h3 : Entails.eval a c10751 := derived10751 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10867 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨43, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, true), (⟨63, by decide⟩, true), (⟨60, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10867 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c477, some c3830, some c3832, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10867 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10867 : lratChecker f10867 p10867 = .success := by decide +kernel
theorem unsat10867 : Unsatisfiable (PosFin 65) f10867 := by
  apply lratCheckerSound f10867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10867
  · intro a ha; simp [p10867] at ha; subst a; trivial
  · exact checked10867
theorem derived10867 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10867 := by
  apply localUnsat_implies_entails f10867 [c477, c3830, c3832] c10867 unsat10867 (by rfl) a
  have h0 : Entails.eval a c477 := h 476 (by decide)
  have h1 : Entails.eval a c3830 := h 3829 (by decide)
  have h2 : Entails.eval a c3832 := h 3831 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10868 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨43, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨10, by decide⟩, true), (⟨57, by decide⟩, true), (⟨15, by decide⟩, true), (⟨63, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10868 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7314, some c7416, some c4932, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10868 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10868 : lratChecker f10868 p10868 = .success := by decide +kernel
theorem unsat10868 : Unsatisfiable (PosFin 65) f10868 := by
  apply lratCheckerSound f10868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10868
  · intro a ha; simp [p10868] at ha; subst a; trivial
  · exact checked10868
theorem derived10868 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10868 := by
  apply localUnsat_implies_entails f10868 [c7314, c7416, c4932] c10868 unsat10868 (by rfl) a
  have h0 : Entails.eval a c7314 := h 7313 (by decide)
  have h1 : Entails.eval a c7416 := h 7415 (by decide)
  have h2 : Entails.eval a c4932 := h 4931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10869 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨15, by decide⟩, true), (⟨63, by decide⟩, true), (⟨60, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10869 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10765, some c2604, some c10865, some c10651, some c10207, some c3618, some c10785, some c4179, some c9185, some c2789, some c3283, some c10269, some c4196, some c10867, some c10868, some c3497, some c463, some c6598, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10869 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked10869 : lratChecker f10869 p10869 = .success := by decide +kernel
theorem unsat10869 : Unsatisfiable (PosFin 65) f10869 := by
  apply lratCheckerSound f10869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10869
  · intro a ha; simp [p10869] at ha; subst a; trivial
  · exact checked10869
theorem derived10869 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10869 := by
  apply localUnsat_implies_entails f10869 [c10765, c2604, c10865, c10651, c10207, c3618, c10785, c4179, c9185, c2789, c3283, c10269, c4196, c10867, c10868, c3497, c463, c6598] c10869 unsat10869 (by rfl) a
  have h0 : Entails.eval a c10765 := derived10765 a h
  have h1 : Entails.eval a c2604 := h 2603 (by decide)
  have h2 : Entails.eval a c10865 := derived10865 a h
  have h3 : Entails.eval a c10651 := derived10651 a h
  have h4 : Entails.eval a c10207 := derived10207 a h
  have h5 : Entails.eval a c3618 := h 3617 (by decide)
  have h6 : Entails.eval a c10785 := derived10785 a h
  have h7 : Entails.eval a c4179 := h 4178 (by decide)
  have h8 : Entails.eval a c9185 := derived9185 a h
  have h9 : Entails.eval a c2789 := h 2788 (by decide)
  have h10 : Entails.eval a c3283 := h 3282 (by decide)
  have h11 : Entails.eval a c10269 := derived10269 a h
  have h12 : Entails.eval a c4196 := h 4195 (by decide)
  have h13 : Entails.eval a c10867 := derived10867 a h
  have h14 : Entails.eval a c10868 := derived10868 a h
  have h15 : Entails.eval a c3497 := h 3496 (by decide)
  have h16 : Entails.eval a c463 := h 462 (by decide)
  have h17 : Entails.eval a c6598 := h 6597 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10870 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨60, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10870 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10866, some c8269, some c7994, some c10865, some c10651, some c10762, some c10765, some c10785, some c10328, some c10210, some c3962, some c4425, some c10207, some c2604, some c4179, some c8296, some c3618, some c2789, some c3283, some c4895, some c9185, some c10869, some c557, some c4933, some c483, some c816, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10870 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked10870 : lratChecker f10870 p10870 = .success := by decide +kernel
theorem unsat10870 : Unsatisfiable (PosFin 65) f10870 := by
  apply lratCheckerSound f10870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10870
  · intro a ha; simp [p10870] at ha; subst a; trivial
  · exact checked10870
theorem derived10870 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10870 := by
  apply localUnsat_implies_entails f10870 [c10866, c8269, c7994, c10865, c10651, c10762, c10765, c10785, c10328, c10210, c3962, c4425, c10207, c2604, c4179, c8296, c3618, c2789, c3283, c4895, c9185, c10869, c557, c4933, c483, c816] c10870 unsat10870 (by rfl) a
  have h0 : Entails.eval a c10866 := derived10866 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c10865 := derived10865 a h
  have h4 : Entails.eval a c10651 := derived10651 a h
  have h5 : Entails.eval a c10762 := derived10762 a h
  have h6 : Entails.eval a c10765 := derived10765 a h
  have h7 : Entails.eval a c10785 := derived10785 a h
  have h8 : Entails.eval a c10328 := derived10328 a h
  have h9 : Entails.eval a c10210 := derived10210 a h
  have h10 : Entails.eval a c3962 := h 3961 (by decide)
  have h11 : Entails.eval a c4425 := h 4424 (by decide)
  have h12 : Entails.eval a c10207 := derived10207 a h
  have h13 : Entails.eval a c2604 := h 2603 (by decide)
  have h14 : Entails.eval a c4179 := h 4178 (by decide)
  have h15 : Entails.eval a c8296 := derived8296 a h
  have h16 : Entails.eval a c3618 := h 3617 (by decide)
  have h17 : Entails.eval a c2789 := h 2788 (by decide)
  have h18 : Entails.eval a c3283 := h 3282 (by decide)
  have h19 : Entails.eval a c4895 := h 4894 (by decide)
  have h20 : Entails.eval a c9185 := derived9185 a h
  have h21 : Entails.eval a c10869 := derived10869 a h
  have h22 : Entails.eval a c557 := h 556 (by decide)
  have h23 : Entails.eval a c4933 := h 4932 (by decide)
  have h24 : Entails.eval a c483 := h 482 (by decide)
  have h25 : Entails.eval a c816 := h 815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10871 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨49, by decide⟩, true), (⟨57, by decide⟩, true), (⟨56, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, true), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10871 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c557, some c483, some c555, some c816, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10871 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10871 : lratChecker f10871 p10871 = .success := by decide +kernel
theorem unsat10871 : Unsatisfiable (PosFin 65) f10871 := by
  apply lratCheckerSound f10871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10871
  · intro a ha; simp [p10871] at ha; subst a; trivial
  · exact checked10871
theorem derived10871 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10871 := by
  apply localUnsat_implies_entails f10871 [c557, c483, c555, c816] c10871 unsat10871 (by rfl) a
  have h0 : Entails.eval a c557 := h 556 (by decide)
  have h1 : Entails.eval a c483 := h 482 (by decide)
  have h2 : Entails.eval a c555 := h 554 (by decide)
  have h3 : Entails.eval a c816 := h 815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10872 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, false), (⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨15, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10872 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c6953, some c6598, some c3185, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p10872 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10872 : lratChecker f10872 p10872 = .success := by decide +kernel
theorem unsat10872 : Unsatisfiable (PosFin 65) f10872 := by
  apply lratCheckerSound f10872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10872
  · intro a ha; simp [p10872] at ha; subst a; trivial
  · exact checked10872
theorem derived10872 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10872 := by
  apply localUnsat_implies_entails f10872 [c8269, c7994, c6953, c6598, c3185] c10872 unsat10872 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c6953 := h 6952 (by decide)
  have h3 : Entails.eval a c6598 := h 6597 (by decide)
  have h4 : Entails.eval a c3185 := h 3184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10873 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨43, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨49, by decide⟩, true), (⟨15, by decide⟩, false), (⟨63, by decide⟩, true), (⟨60, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10873 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c542, some c2641, some c7311, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10873 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10873 : lratChecker f10873 p10873 = .success := by decide +kernel
theorem unsat10873 : Unsatisfiable (PosFin 65) f10873 := by
  apply lratCheckerSound f10873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10873
  · intro a ha; simp [p10873] at ha; subst a; trivial
  · exact checked10873
theorem derived10873 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10873 := by
  apply localUnsat_implies_entails f10873 [c542, c2641, c7311] c10873 unsat10873 (by rfl) a
  have h0 : Entails.eval a c542 := h 541 (by decide)
  have h1 : Entails.eval a c2641 := h 2640 (by decide)
  have h2 : Entails.eval a c7311 := h 7310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10874 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨14, by decide⟩, true), (⟨61, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10874 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10866, some c7994, some c8269, some c10870, some c4355, some c4339, some c4357, some c4343, some c4331, some c10779, some c3962, some c4425, some c4527, some c10207, some c2604, some c2645, some c8380, some c3618, some c2789, some c3284, some c4900, some c3476, some c10871, some c10873, some c10872, some c477, some c4329, some c4513, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10874 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked10874 : lratChecker f10874 p10874 = .success := by decide +kernel
theorem unsat10874 : Unsatisfiable (PosFin 65) f10874 := by
  apply lratCheckerSound f10874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10874
  · intro a ha; simp [p10874] at ha; subst a; trivial
  · exact checked10874
theorem derived10874 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10874 := by
  apply localUnsat_implies_entails f10874 [c10866, c7994, c8269, c10870, c4355, c4339, c4357, c4343, c4331, c10779, c3962, c4425, c4527, c10207, c2604, c2645, c8380, c3618, c2789, c3284, c4900, c3476, c10871, c10873, c10872, c477, c4329, c4513] c10874 unsat10874 (by rfl) a
  have h0 : Entails.eval a c10866 := derived10866 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c10870 := derived10870 a h
  have h4 : Entails.eval a c4355 := h 4354 (by decide)
  have h5 : Entails.eval a c4339 := h 4338 (by decide)
  have h6 : Entails.eval a c4357 := h 4356 (by decide)
  have h7 : Entails.eval a c4343 := h 4342 (by decide)
  have h8 : Entails.eval a c4331 := h 4330 (by decide)
  have h9 : Entails.eval a c10779 := derived10779 a h
  have h10 : Entails.eval a c3962 := h 3961 (by decide)
  have h11 : Entails.eval a c4425 := h 4424 (by decide)
  have h12 : Entails.eval a c4527 := h 4526 (by decide)
  have h13 : Entails.eval a c10207 := derived10207 a h
  have h14 : Entails.eval a c2604 := h 2603 (by decide)
  have h15 : Entails.eval a c2645 := h 2644 (by decide)
  have h16 : Entails.eval a c8380 := derived8380 a h
  have h17 : Entails.eval a c3618 := h 3617 (by decide)
  have h18 : Entails.eval a c2789 := h 2788 (by decide)
  have h19 : Entails.eval a c3284 := h 3283 (by decide)
  have h20 : Entails.eval a c4900 := h 4899 (by decide)
  have h21 : Entails.eval a c3476 := h 3475 (by decide)
  have h22 : Entails.eval a c10871 := derived10871 a h
  have h23 : Entails.eval a c10873 := derived10873 a h
  have h24 : Entails.eval a c10872 := derived10872 a h
  have h25 : Entails.eval a c477 := h 476 (by decide)
  have h26 : Entails.eval a c4329 := h 4328 (by decide)
  have h27 : Entails.eval a c4513 := h 4512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10875 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨64, by decide⟩, false), (⟨60, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10875 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c4348, some c4338, some c8300, some c4349, some c4354, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10875 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10875 : lratChecker f10875 p10875 = .success := by decide +kernel
theorem unsat10875 : Unsatisfiable (PosFin 65) f10875 := by
  apply lratCheckerSound f10875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10875
  · intro a ha; simp [p10875] at ha; subst a; trivial
  · exact checked10875
theorem derived10875 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10875 := by
  apply localUnsat_implies_entails f10875 [c8269, c4348, c4338, c8300, c4349, c4354] c10875 unsat10875 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c4348 := h 4347 (by decide)
  have h2 : Entails.eval a c4338 := h 4337 (by decide)
  have h3 : Entails.eval a c8300 := derived8300 a h
  have h4 : Entails.eval a c4349 := h 4348 (by decide)
  have h5 : Entails.eval a c4354 := h 4353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10876 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10876 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10874, some c10875, some c10759, some c10752, some c8380, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10876 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10876 : lratChecker f10876 p10876 = .success := by decide +kernel
theorem unsat10876 : Unsatisfiable (PosFin 65) f10876 := by
  apply lratCheckerSound f10876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10876
  · intro a ha; simp [p10876] at ha; subst a; trivial
  · exact checked10876
theorem derived10876 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10876 := by
  apply localUnsat_implies_entails f10876 [c10874, c10875, c10759, c10752, c8380] c10876 unsat10876 (by rfl) a
  have h0 : Entails.eval a c10874 := derived10874 a h
  have h1 : Entails.eval a c10875 := derived10875 a h
  have h2 : Entails.eval a c10759 := derived10759 a h
  have h3 : Entails.eval a c10752 := derived10752 a h
  have h4 : Entails.eval a c8380 := derived8380 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10877 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨61, by decide⟩, false), (⟨53, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10877 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10874, some c10876, some c4353, some c10750, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p10877 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10877 : lratChecker f10877 p10877 = .success := by decide +kernel
theorem unsat10877 : Unsatisfiable (PosFin 65) f10877 := by
  apply lratCheckerSound f10877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10877
  · intro a ha; simp [p10877] at ha; subst a; trivial
  · exact checked10877
theorem derived10877 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10877 := by
  apply localUnsat_implies_entails f10877 [c10874, c10876, c4353, c10750] c10877 unsat10877 (by rfl) a
  have h0 : Entails.eval a c10874 := derived10874 a h
  have h1 : Entails.eval a c10876 := derived10876 a h
  have h2 : Entails.eval a c4353 := h 4352 (by decide)
  have h3 : Entails.eval a c10750 := derived10750 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10878 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨15, by decide⟩, true), (⟨64, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10878 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4691, some c3168, some c10523, some c2489, some c2632, some c3017, some c3349, some c10161, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10878 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10878 : lratChecker f10878 p10878 = .success := by decide +kernel
theorem unsat10878 : Unsatisfiable (PosFin 65) f10878 := by
  apply lratCheckerSound f10878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10878
  · intro a ha; simp [p10878] at ha; subst a; trivial
  · exact checked10878
theorem derived10878 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10878 := by
  apply localUnsat_implies_entails f10878 [c4691, c3168, c10523, c2489, c2632, c3017, c3349, c10161] c10878 unsat10878 (by rfl) a
  have h0 : Entails.eval a c4691 := h 4690 (by decide)
  have h1 : Entails.eval a c3168 := h 3167 (by decide)
  have h2 : Entails.eval a c10523 := derived10523 a h
  have h3 : Entails.eval a c2489 := h 2488 (by decide)
  have h4 : Entails.eval a c2632 := h 2631 (by decide)
  have h5 : Entails.eval a c3017 := h 3016 (by decide)
  have h6 : Entails.eval a c3349 := h 3348 (by decide)
  have h7 : Entails.eval a c10161 := derived10161 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10879 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10879 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3765, some c9217, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10879 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10879 : lratChecker f10879 p10879 = .success := by decide +kernel
theorem unsat10879 : Unsatisfiable (PosFin 65) f10879 := by
  apply lratCheckerSound f10879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10879
  · intro a ha; simp [p10879] at ha; subst a; trivial
  · exact checked10879
theorem derived10879 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10879 := by
  apply localUnsat_implies_entails f10879 [c3765, c9217] c10879 unsat10879 (by rfl) a
  have h0 : Entails.eval a c3765 := h 3764 (by decide)
  have h1 : Entails.eval a c9217 := derived9217 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10880 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨60, by decide⟩, false), (⟨64, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10880 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2615, some c2631, some c2618, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10880 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10880 : lratChecker f10880 p10880 = .success := by decide +kernel
theorem unsat10880 : Unsatisfiable (PosFin 65) f10880 := by
  apply lratCheckerSound f10880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10880
  · intro a ha; simp [p10880] at ha; subst a; trivial
  · exact checked10880
theorem derived10880 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10880 := by
  apply localUnsat_implies_entails f10880 [c2615, c2631, c2618] c10880 unsat10880 (by rfl) a
  have h0 : Entails.eval a c2615 := h 2614 (by decide)
  have h1 : Entails.eval a c2631 := h 2630 (by decide)
  have h2 : Entails.eval a c2618 := h 2617 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10881 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10881 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9293, some c9785, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p10881 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10881 : lratChecker f10881 p10881 = .success := by decide +kernel
theorem unsat10881 : Unsatisfiable (PosFin 65) f10881 := by
  apply lratCheckerSound f10881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10881
  · intro a ha; simp [p10881] at ha; subst a; trivial
  · exact checked10881
theorem derived10881 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10881 := by
  apply localUnsat_implies_entails f10881 [c9293, c9785] c10881 unsat10881 (by rfl) a
  have h0 : Entails.eval a c9293 := derived9293 a h
  have h1 : Entails.eval a c9785 := derived9785 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10882 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨15, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10882 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10879, some c10881, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10882 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10882 : lratChecker f10882 p10882 = .success := by decide +kernel
theorem unsat10882 : Unsatisfiable (PosFin 65) f10882 := by
  apply lratCheckerSound f10882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10882
  · intro a ha; simp [p10882] at ha; subst a; trivial
  · exact checked10882
theorem derived10882 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10882 := by
  apply localUnsat_implies_entails f10882 [c10879, c10881] c10882 unsat10882 (by rfl) a
  have h0 : Entails.eval a c10879 := derived10879 a h
  have h1 : Entails.eval a c10881 := derived10881 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10883 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨60, by decide⟩, false), (⟨64, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10883 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3166, some c3149, some c3151, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10883 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10883 : lratChecker f10883 p10883 = .success := by decide +kernel
theorem unsat10883 : Unsatisfiable (PosFin 65) f10883 := by
  apply lratCheckerSound f10883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10883
  · intro a ha; simp [p10883] at ha; subst a; trivial
  · exact checked10883
theorem derived10883 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10883 := by
  apply localUnsat_implies_entails f10883 [c3166, c3149, c3151] c10883 unsat10883 (by rfl) a
  have h0 : Entails.eval a c3166 := h 3165 (by decide)
  have h1 : Entails.eval a c3149 := h 3148 (by decide)
  have h2 : Entails.eval a c3151 := h 3150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10884 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨55, by decide⟩, false), (⟨57, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10884 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2435, some c3619, some c10782, some c2517, some c4047, some c10540, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10884 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10884 : lratChecker f10884 p10884 = .success := by decide +kernel
theorem unsat10884 : Unsatisfiable (PosFin 65) f10884 := by
  apply lratCheckerSound f10884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10884
  · intro a ha; simp [p10884] at ha; subst a; trivial
  · exact checked10884
theorem derived10884 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10884 := by
  apply localUnsat_implies_entails f10884 [c2435, c3619, c10782, c2517, c4047, c10540] c10884 unsat10884 (by rfl) a
  have h0 : Entails.eval a c2435 := h 2434 (by decide)
  have h1 : Entails.eval a c3619 := h 3618 (by decide)
  have h2 : Entails.eval a c10782 := derived10782 a h
  have h3 : Entails.eval a c2517 := h 2516 (by decide)
  have h4 : Entails.eval a c4047 := h 4046 (by decide)
  have h5 : Entails.eval a c10540 := derived10540 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10885 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨60, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10885 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10865, some c2494, some c2470, some c2500, some c2499, some c2474, some c2495, some c10884, some c10261, some c4162, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10885 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10885 : lratChecker f10885 p10885 = .success := by decide +kernel
theorem unsat10885 : Unsatisfiable (PosFin 65) f10885 := by
  apply lratCheckerSound f10885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10885
  · intro a ha; simp [p10885] at ha; subst a; trivial
  · exact checked10885
theorem derived10885 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10885 := by
  apply localUnsat_implies_entails f10885 [c10865, c2494, c2470, c2500, c2499, c2474, c2495, c10884, c10261, c4162] c10885 unsat10885 (by rfl) a
  have h0 : Entails.eval a c10865 := derived10865 a h
  have h1 : Entails.eval a c2494 := h 2493 (by decide)
  have h2 : Entails.eval a c2470 := h 2469 (by decide)
  have h3 : Entails.eval a c2500 := h 2499 (by decide)
  have h4 : Entails.eval a c2499 := h 2498 (by decide)
  have h5 : Entails.eval a c2474 := h 2473 (by decide)
  have h6 : Entails.eval a c2495 := h 2494 (by decide)
  have h7 : Entails.eval a c10884 := derived10884 a h
  have h8 : Entails.eval a c10261 := derived10261 a h
  have h9 : Entails.eval a c4162 := h 4161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10886 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨64, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10886 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10877, some c10865, some c10878, some c10883, some c10882, some c10880, some c10885, some c4389, some c10021, some c2421, some c2429, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10886 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10886 : lratChecker f10886 p10886 = .success := by decide +kernel
theorem unsat10886 : Unsatisfiable (PosFin 65) f10886 := by
  apply lratCheckerSound f10886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10886
  · intro a ha; simp [p10886] at ha; subst a; trivial
  · exact checked10886
theorem derived10886 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10886 := by
  apply localUnsat_implies_entails f10886 [c10877, c10865, c10878, c10883, c10882, c10880, c10885, c4389, c10021, c2421, c2429] c10886 unsat10886 (by rfl) a
  have h0 : Entails.eval a c10877 := derived10877 a h
  have h1 : Entails.eval a c10865 := derived10865 a h
  have h2 : Entails.eval a c10878 := derived10878 a h
  have h3 : Entails.eval a c10883 := derived10883 a h
  have h4 : Entails.eval a c10882 := derived10882 a h
  have h5 : Entails.eval a c10880 := derived10880 a h
  have h6 : Entails.eval a c10885 := derived10885 a h
  have h7 : Entails.eval a c4389 := h 4388 (by decide)
  have h8 : Entails.eval a c10021 := derived10021 a h
  have h9 : Entails.eval a c2421 := h 2420 (by decide)
  have h10 : Entails.eval a c2429 := h 2428 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10887 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨7, by decide⟩, false), (⟨61, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10887 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10886, some c4351, some c4353, some c4357, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10887 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10887 : lratChecker f10887 p10887 = .success := by decide +kernel
theorem unsat10887 : Unsatisfiable (PosFin 65) f10887 := by
  apply lratCheckerSound f10887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10887
  · intro a ha; simp [p10887] at ha; subst a; trivial
  · exact checked10887
theorem derived10887 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10887 := by
  apply localUnsat_implies_entails f10887 [c10886, c4351, c4353, c4357] c10887 unsat10887 (by rfl) a
  have h0 : Entails.eval a c10886 := derived10886 a h
  have h1 : Entails.eval a c4351 := h 4350 (by decide)
  have h2 : Entails.eval a c4353 := h 4352 (by decide)
  have h3 : Entails.eval a c4357 := h 4356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10888 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨52, by decide⟩, false), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10888 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4780, some c4784, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10888 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10888 : lratChecker f10888 p10888 = .success := by decide +kernel
theorem unsat10888 : Unsatisfiable (PosFin 65) f10888 := by
  apply lratCheckerSound f10888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10888
  · intro a ha; simp [p10888] at ha; subst a; trivial
  · exact checked10888
theorem derived10888 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10888 := by
  apply localUnsat_implies_entails f10888 [c4780, c4784] c10888 unsat10888 (by rfl) a
  have h0 : Entails.eval a c4780 := h 4779 (by decide)
  have h1 : Entails.eval a c4784 := h 4783 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10889 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10889 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10865, some c10203, some c10888, some c3377, some c3380, some c3394, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10889 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10889 : lratChecker f10889 p10889 = .success := by decide +kernel
theorem unsat10889 : Unsatisfiable (PosFin 65) f10889 := by
  apply lratCheckerSound f10889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10889
  · intro a ha; simp [p10889] at ha; subst a; trivial
  · exact checked10889
theorem derived10889 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10889 := by
  apply localUnsat_implies_entails f10889 [c10865, c10203, c10888, c3377, c3380, c3394] c10889 unsat10889 (by rfl) a
  have h0 : Entails.eval a c10865 := derived10865 a h
  have h1 : Entails.eval a c10203 := derived10203 a h
  have h2 : Entails.eval a c10888 := derived10888 a h
  have h3 : Entails.eval a c3377 := h 3376 (by decide)
  have h4 : Entails.eval a c3380 := h 3379 (by decide)
  have h5 : Entails.eval a c3394 := h 3393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10890 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10890 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4694, some c4315, some c4675, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10890 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10890 : lratChecker f10890 p10890 = .success := by decide +kernel
theorem unsat10890 : Unsatisfiable (PosFin 65) f10890 := by
  apply lratCheckerSound f10890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10890
  · intro a ha; simp [p10890] at ha; subst a; trivial
  · exact checked10890
theorem derived10890 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10890 := by
  apply localUnsat_implies_entails f10890 [c4694, c4315, c4675] c10890 unsat10890 (by rfl) a
  have h0 : Entails.eval a c4694 := h 4693 (by decide)
  have h1 : Entails.eval a c4315 := h 4314 (by decide)
  have h2 : Entails.eval a c4675 := h 4674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10891 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10891 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10889, some c3165, some c3174, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10891 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10891 : lratChecker f10891 p10891 = .success := by decide +kernel
theorem unsat10891 : Unsatisfiable (PosFin 65) f10891 := by
  apply lratCheckerSound f10891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10891
  · intro a ha; simp [p10891] at ha; subst a; trivial
  · exact checked10891
theorem derived10891 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10891 := by
  apply localUnsat_implies_entails f10891 [c10889, c3165, c3174] c10891 unsat10891 (by rfl) a
  have h0 : Entails.eval a c10889 := derived10889 a h
  have h1 : Entails.eval a c3165 := h 3164 (by decide)
  have h2 : Entails.eval a c3174 := h 3173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10892 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10892 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10887, some c8269, some c7994, some c10877, some c10865, some c10890, some c10891, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10892 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10892 : lratChecker f10892 p10892 = .success := by decide +kernel
theorem unsat10892 : Unsatisfiable (PosFin 65) f10892 := by
  apply lratCheckerSound f10892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10892
  · intro a ha; simp [p10892] at ha; subst a; trivial
  · exact checked10892
theorem derived10892 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10892 := by
  apply localUnsat_implies_entails f10892 [c10887, c8269, c7994, c10877, c10865, c10890, c10891] c10892 unsat10892 (by rfl) a
  have h0 : Entails.eval a c10887 := derived10887 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c10877 := derived10877 a h
  have h4 : Entails.eval a c10865 := derived10865 a h
  have h5 : Entails.eval a c10890 := derived10890 a h
  have h6 : Entails.eval a c10891 := derived10891 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10893 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨60, by decide⟩, true), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10893 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3165, some c3159, some c3148, some c3146, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10893 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10893 : lratChecker f10893 p10893 = .success := by decide +kernel
theorem unsat10893 : Unsatisfiable (PosFin 65) f10893 := by
  apply lratCheckerSound f10893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10893
  · intro a ha; simp [p10893] at ha; subst a; trivial
  · exact checked10893
theorem derived10893 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10893 := by
  apply localUnsat_implies_entails f10893 [c3165, c3159, c3148, c3146] c10893 unsat10893 (by rfl) a
  have h0 : Entails.eval a c3165 := h 3164 (by decide)
  have h1 : Entails.eval a c3159 := h 3158 (by decide)
  have h2 : Entails.eval a c3148 := h 3147 (by decide)
  have h3 : Entails.eval a c3146 := h 3145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10894 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨60, by decide⟩, true), (⟨64, by decide⟩, false), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10894 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c10893, some c10203, some c8300, some c8380, some c10888, some c3393, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10894 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10894 : lratChecker f10894 p10894 = .success := by decide +kernel
theorem unsat10894 : Unsatisfiable (PosFin 65) f10894 := by
  apply lratCheckerSound f10894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10894
  · intro a ha; simp [p10894] at ha; subst a; trivial
  · exact checked10894
theorem derived10894 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10894 := by
  apply localUnsat_implies_entails f10894 [c7994, c10893, c10203, c8300, c8380, c10888, c3393] c10894 unsat10894 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c10893 := derived10893 a h
  have h2 : Entails.eval a c10203 := derived10203 a h
  have h3 : Entails.eval a c8300 := derived8300 a h
  have h4 : Entails.eval a c8380 := derived8380 a h
  have h5 : Entails.eval a c10888 := derived10888 a h
  have h6 : Entails.eval a c3393 := h 3392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10895 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10895 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10865, some c10877, some c10887, some c7994, some c8269, some c10892, some c10893, some c10894, some c4681, some c4297, some c10834, some c10888, some c9285, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10895 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10895 : lratChecker f10895 p10895 = .success := by decide +kernel
theorem unsat10895 : Unsatisfiable (PosFin 65) f10895 := by
  apply lratCheckerSound f10895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10895
  · intro a ha; simp [p10895] at ha; subst a; trivial
  · exact checked10895
theorem derived10895 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10895 := by
  apply localUnsat_implies_entails f10895 [c10865, c10877, c10887, c7994, c8269, c10892, c10893, c10894, c4681, c4297, c10834, c10888, c9285] c10895 unsat10895 (by rfl) a
  have h0 : Entails.eval a c10865 := derived10865 a h
  have h1 : Entails.eval a c10877 := derived10877 a h
  have h2 : Entails.eval a c10887 := derived10887 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c10892 := derived10892 a h
  have h6 : Entails.eval a c10893 := derived10893 a h
  have h7 : Entails.eval a c10894 := derived10894 a h
  have h8 : Entails.eval a c4681 := h 4680 (by decide)
  have h9 : Entails.eval a c4297 := h 4296 (by decide)
  have h10 : Entails.eval a c10834 := derived10834 a h
  have h11 : Entails.eval a c10888 := derived10888 a h
  have h12 : Entails.eval a c9285 := derived9285 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10896 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨55, by decide⟩, true), (⟨8, by decide⟩, false), (⟨14, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10896 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5017, some c4099, some c10527, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10896 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10896 : lratChecker f10896 p10896 = .success := by decide +kernel
theorem unsat10896 : Unsatisfiable (PosFin 65) f10896 := by
  apply lratCheckerSound f10896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10896
  · intro a ha; simp [p10896] at ha; subst a; trivial
  · exact checked10896
theorem derived10896 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10896 := by
  apply localUnsat_implies_entails f10896 [c5017, c4099, c10527] c10896 unsat10896 (by rfl) a
  have h0 : Entails.eval a c5017 := h 5016 (by decide)
  have h1 : Entails.eval a c4099 := h 4098 (by decide)
  have h2 : Entails.eval a c10527 := derived10527 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10897 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨8, by decide⟩, false), (⟨64, by decide⟩, false), (⟨60, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10897 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8300, some c8380, some c10896, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p10897 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10897 : lratChecker f10897 p10897 = .success := by decide +kernel
theorem unsat10897 : Unsatisfiable (PosFin 65) f10897 := by
  apply lratCheckerSound f10897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10897
  · intro a ha; simp [p10897] at ha; subst a; trivial
  · exact checked10897
theorem derived10897 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10897 := by
  apply localUnsat_implies_entails f10897 [c8300, c8380, c10896] c10897 unsat10897 (by rfl) a
  have h0 : Entails.eval a c8300 := derived8300 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c10896 := derived10896 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10898 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨60, by decide⟩, true), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10898 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10895, some c10865, some c8269, some c10170, some c10897, some c10211, some c10167, some c2684, some c4959, some c5007, some c4416, some c10179, some c4631, some c3383, some c9790, some c9769, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10898 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked10898 : lratChecker f10898 p10898 = .success := by decide +kernel
theorem unsat10898 : Unsatisfiable (PosFin 65) f10898 := by
  apply lratCheckerSound f10898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10898
  · intro a ha; simp [p10898] at ha; subst a; trivial
  · exact checked10898
theorem derived10898 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10898 := by
  apply localUnsat_implies_entails f10898 [c10895, c10865, c8269, c10170, c10897, c10211, c10167, c2684, c4959, c5007, c4416, c10179, c4631, c3383, c9790, c9769] c10898 unsat10898 (by rfl) a
  have h0 : Entails.eval a c10895 := derived10895 a h
  have h1 : Entails.eval a c10865 := derived10865 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c10170 := derived10170 a h
  have h4 : Entails.eval a c10897 := derived10897 a h
  have h5 : Entails.eval a c10211 := derived10211 a h
  have h6 : Entails.eval a c10167 := derived10167 a h
  have h7 : Entails.eval a c2684 := h 2683 (by decide)
  have h8 : Entails.eval a c4959 := h 4958 (by decide)
  have h9 : Entails.eval a c5007 := h 5006 (by decide)
  have h10 : Entails.eval a c4416 := h 4415 (by decide)
  have h11 : Entails.eval a c10179 := derived10179 a h
  have h12 : Entails.eval a c4631 := h 4630 (by decide)
  have h13 : Entails.eval a c3383 := h 3382 (by decide)
  have h14 : Entails.eval a c9790 := derived9790 a h
  have h15 : Entails.eval a c9769 := derived9769 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10899 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨57, by decide⟩, false), (⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10899 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3087, some c10279, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10899 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10899 : lratChecker f10899 p10899 = .success := by decide +kernel
theorem unsat10899 : Unsatisfiable (PosFin 65) f10899 := by
  apply lratCheckerSound f10899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10899
  · intro a ha; simp [p10899] at ha; subst a; trivial
  · exact checked10899
theorem derived10899 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10899 := by
  apply localUnsat_implies_entails f10899 [c3087, c10279] c10899 unsat10899 (by rfl) a
  have h0 : Entails.eval a c3087 := h 3086 (by decide)
  have h1 : Entails.eval a c10279 := derived10279 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10900 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10900 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c484, some c34, some c488, some c7323, some c8694, some c8424, some c399, some c401, some c400, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10900 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10900 : lratChecker f10900 p10900 = .success := by decide +kernel
theorem unsat10900 : Unsatisfiable (PosFin 65) f10900 := by
  apply lratCheckerSound f10900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10900
  · intro a ha; simp [p10900] at ha; subst a; trivial
  · exact checked10900
theorem derived10900 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10900 := by
  apply localUnsat_implies_entails f10900 [c484, c34, c488, c7323, c8694, c8424, c399, c401, c400] c10900 unsat10900 (by rfl) a
  have h0 : Entails.eval a c484 := h 483 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c488 := h 487 (by decide)
  have h3 : Entails.eval a c7323 := h 7322 (by decide)
  have h4 : Entails.eval a c8694 := derived8694 a h
  have h5 : Entails.eval a c8424 := derived8424 a h
  have h6 : Entails.eval a c399 := h 398 (by decide)
  have h7 : Entails.eval a c401 := h 400 (by decide)
  have h8 : Entails.eval a c400 := h 399 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10901 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨64, by decide⟩, true), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10901 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9775, some c10899, some c9853, some c3424, some c2601, some c10260, some c2575, some c3482, some c10900, some c8807, some c9864, some c2571, some c3974, some c1045, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10901 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10901 : lratChecker f10901 p10901 = .success := by decide +kernel
theorem unsat10901 : Unsatisfiable (PosFin 65) f10901 := by
  apply lratCheckerSound f10901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10901
  · intro a ha; simp [p10901] at ha; subst a; trivial
  · exact checked10901
theorem derived10901 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10901 := by
  apply localUnsat_implies_entails f10901 [c9775, c10899, c9853, c3424, c2601, c10260, c2575, c3482, c10900, c8807, c9864, c2571, c3974, c1045] c10901 unsat10901 (by rfl) a
  have h0 : Entails.eval a c9775 := derived9775 a h
  have h1 : Entails.eval a c10899 := derived10899 a h
  have h2 : Entails.eval a c9853 := derived9853 a h
  have h3 : Entails.eval a c3424 := h 3423 (by decide)
  have h4 : Entails.eval a c2601 := h 2600 (by decide)
  have h5 : Entails.eval a c10260 := derived10260 a h
  have h6 : Entails.eval a c2575 := h 2574 (by decide)
  have h7 : Entails.eval a c3482 := h 3481 (by decide)
  have h8 : Entails.eval a c10900 := derived10900 a h
  have h9 : Entails.eval a c8807 := derived8807 a h
  have h10 : Entails.eval a c9864 := derived9864 a h
  have h11 : Entails.eval a c2571 := h 2570 (by decide)
  have h12 : Entails.eval a c3974 := h 3973 (by decide)
  have h13 : Entails.eval a c1045 := h 1044 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10902 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨8, by decide⟩, false), (⟨64, by decide⟩, true), (⟨60, by decide⟩, true), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10902 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10298, some c4526, some c3659, some c3773, some c4422, some c2632, some c2864, some c9853, some c2489, some c9775, some c10899, some c10901, some c3097, some c3879, some c3873, some c4038, some c4029, some c10900, some c8807, some c4116, some c550, some c6746, some c1045, some c1019, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10902 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked10902 : lratChecker f10902 p10902 = .success := by decide +kernel
theorem unsat10902 : Unsatisfiable (PosFin 65) f10902 := by
  apply lratCheckerSound f10902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10902
  · intro a ha; simp [p10902] at ha; subst a; trivial
  · exact checked10902
theorem derived10902 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10902 := by
  apply localUnsat_implies_entails f10902 [c10298, c4526, c3659, c3773, c4422, c2632, c2864, c9853, c2489, c9775, c10899, c10901, c3097, c3879, c3873, c4038, c4029, c10900, c8807, c4116, c550, c6746, c1045, c1019] c10902 unsat10902 (by rfl) a
  have h0 : Entails.eval a c10298 := derived10298 a h
  have h1 : Entails.eval a c4526 := h 4525 (by decide)
  have h2 : Entails.eval a c3659 := h 3658 (by decide)
  have h3 : Entails.eval a c3773 := h 3772 (by decide)
  have h4 : Entails.eval a c4422 := h 4421 (by decide)
  have h5 : Entails.eval a c2632 := h 2631 (by decide)
  have h6 : Entails.eval a c2864 := h 2863 (by decide)
  have h7 : Entails.eval a c9853 := derived9853 a h
  have h8 : Entails.eval a c2489 := h 2488 (by decide)
  have h9 : Entails.eval a c9775 := derived9775 a h
  have h10 : Entails.eval a c10899 := derived10899 a h
  have h11 : Entails.eval a c10901 := derived10901 a h
  have h12 : Entails.eval a c3097 := h 3096 (by decide)
  have h13 : Entails.eval a c3879 := h 3878 (by decide)
  have h14 : Entails.eval a c3873 := h 3872 (by decide)
  have h15 : Entails.eval a c4038 := h 4037 (by decide)
  have h16 : Entails.eval a c4029 := h 4028 (by decide)
  have h17 : Entails.eval a c10900 := derived10900 a h
  have h18 : Entails.eval a c8807 := derived8807 a h
  have h19 : Entails.eval a c4116 := h 4115 (by decide)
  have h20 : Entails.eval a c550 := h 549 (by decide)
  have h21 : Entails.eval a c6746 := h 6745 (by decide)
  have h22 : Entails.eval a c1045 := h 1044 (by decide)
  have h23 : Entails.eval a c1019 := h 1018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10903 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, false), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10903 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3097, some c3877, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10903 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10903 : lratChecker f10903 p10903 = .success := by decide +kernel
theorem unsat10903 : Unsatisfiable (PosFin 65) f10903 := by
  apply lratCheckerSound f10903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10903
  · intro a ha; simp [p10903] at ha; subst a; trivial
  · exact checked10903
theorem derived10903 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10903 := by
  apply localUnsat_implies_entails f10903 [c3097, c3877] c10903 unsat10903 (by rfl) a
  have h0 : Entails.eval a c3097 := h 3096 (by decide)
  have h1 : Entails.eval a c3877 := h 3876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10904 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10904 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10895, some c10865, some c10898, some c10158, some c10298, some c4422, some c4526, some c3659, some c3773, some c2632, some c2864, some c2489, some c9789, some c10902, some c10903, some c10722, some c10257, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10904 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked10904 : lratChecker f10904 p10904 = .success := by decide +kernel
theorem unsat10904 : Unsatisfiable (PosFin 65) f10904 := by
  apply lratCheckerSound f10904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10904
  · intro a ha; simp [p10904] at ha; subst a; trivial
  · exact checked10904
theorem derived10904 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10904 := by
  apply localUnsat_implies_entails f10904 [c10895, c10865, c10898, c10158, c10298, c4422, c4526, c3659, c3773, c2632, c2864, c2489, c9789, c10902, c10903, c10722, c10257] c10904 unsat10904 (by rfl) a
  have h0 : Entails.eval a c10895 := derived10895 a h
  have h1 : Entails.eval a c10865 := derived10865 a h
  have h2 : Entails.eval a c10898 := derived10898 a h
  have h3 : Entails.eval a c10158 := derived10158 a h
  have h4 : Entails.eval a c10298 := derived10298 a h
  have h5 : Entails.eval a c4422 := h 4421 (by decide)
  have h6 : Entails.eval a c4526 := h 4525 (by decide)
  have h7 : Entails.eval a c3659 := h 3658 (by decide)
  have h8 : Entails.eval a c3773 := h 3772 (by decide)
  have h9 : Entails.eval a c2632 := h 2631 (by decide)
  have h10 : Entails.eval a c2864 := h 2863 (by decide)
  have h11 : Entails.eval a c2489 := h 2488 (by decide)
  have h12 : Entails.eval a c9789 := derived9789 a h
  have h13 : Entails.eval a c10902 := derived10902 a h
  have h14 : Entails.eval a c10903 := derived10903 a h
  have h15 : Entails.eval a c10722 := derived10722 a h
  have h16 : Entails.eval a c10257 := derived10257 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10905 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10905 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10895, some c10904, some c10173, some c10865, some c10158, some c4095, some c4088, some c10295, some c4026, some c3957, some c3946, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10905 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10905 : lratChecker f10905 p10905 = .success := by decide +kernel
theorem unsat10905 : Unsatisfiable (PosFin 65) f10905 := by
  apply lratCheckerSound f10905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10905
  · intro a ha; simp [p10905] at ha; subst a; trivial
  · exact checked10905
theorem derived10905 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10905 := by
  apply localUnsat_implies_entails f10905 [c10895, c10904, c10173, c10865, c10158, c4095, c4088, c10295, c4026, c3957, c3946] c10905 unsat10905 (by rfl) a
  have h0 : Entails.eval a c10895 := derived10895 a h
  have h1 : Entails.eval a c10904 := derived10904 a h
  have h2 : Entails.eval a c10173 := derived10173 a h
  have h3 : Entails.eval a c10865 := derived10865 a h
  have h4 : Entails.eval a c10158 := derived10158 a h
  have h5 : Entails.eval a c4095 := h 4094 (by decide)
  have h6 : Entails.eval a c4088 := h 4087 (by decide)
  have h7 : Entails.eval a c10295 := derived10295 a h
  have h8 : Entails.eval a c4026 := h 4025 (by decide)
  have h9 : Entails.eval a c3957 := h 3956 (by decide)
  have h10 : Entails.eval a c3946 := h 3945 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10906 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10906 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10895, some c10904, some c10173, some c10905, some c8269, some c10170, some c4083, some c4072, some c10165, some c4044, some c3944, some c3958, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10906 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10906 : lratChecker f10906 p10906 = .success := by decide +kernel
theorem unsat10906 : Unsatisfiable (PosFin 65) f10906 := by
  apply lratCheckerSound f10906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10906
  · intro a ha; simp [p10906] at ha; subst a; trivial
  · exact checked10906
theorem derived10906 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10906 := by
  apply localUnsat_implies_entails f10906 [c10895, c10904, c10173, c10905, c8269, c10170, c4083, c4072, c10165, c4044, c3944, c3958] c10906 unsat10906 (by rfl) a
  have h0 : Entails.eval a c10895 := derived10895 a h
  have h1 : Entails.eval a c10904 := derived10904 a h
  have h2 : Entails.eval a c10173 := derived10173 a h
  have h3 : Entails.eval a c10905 := derived10905 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c10170 := derived10170 a h
  have h6 : Entails.eval a c4083 := h 4082 (by decide)
  have h7 : Entails.eval a c4072 := h 4071 (by decide)
  have h8 : Entails.eval a c10165 := derived10165 a h
  have h9 : Entails.eval a c4044 := h 4043 (by decide)
  have h10 : Entails.eval a c3944 := h 3943 (by decide)
  have h11 : Entails.eval a c3958 := h 3957 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10907 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10907 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10895, some c10865, some c10906, some c10725, some c10230, some c4097, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10907 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10907 : lratChecker f10907 p10907 = .success := by decide +kernel
theorem unsat10907 : Unsatisfiable (PosFin 65) f10907 := by
  apply lratCheckerSound f10907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10907
  · intro a ha; simp [p10907] at ha; subst a; trivial
  · exact checked10907
theorem derived10907 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10907 := by
  apply localUnsat_implies_entails f10907 [c10895, c10865, c10906, c10725, c10230, c4097] c10907 unsat10907 (by rfl) a
  have h0 : Entails.eval a c10895 := derived10895 a h
  have h1 : Entails.eval a c10865 := derived10865 a h
  have h2 : Entails.eval a c10906 := derived10906 a h
  have h3 : Entails.eval a c10725 := derived10725 a h
  have h4 : Entails.eval a c10230 := derived10230 a h
  have h5 : Entails.eval a c4097 := h 4096 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10908 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨63, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10908 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10895, some c10865, some c10230, some c10725, some c7994, some c10907, some c3885, some c9770, some c2758, some c2556, some c2694, some c9995, some c10881, some c3052, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10908 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10908 : lratChecker f10908 p10908 = .success := by decide +kernel
theorem unsat10908 : Unsatisfiable (PosFin 65) f10908 := by
  apply lratCheckerSound f10908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10908
  · intro a ha; simp [p10908] at ha; subst a; trivial
  · exact checked10908
theorem derived10908 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10908 := by
  apply localUnsat_implies_entails f10908 [c10895, c10865, c10230, c10725, c7994, c10907, c3885, c9770, c2758, c2556, c2694, c9995, c10881, c3052] c10908 unsat10908 (by rfl) a
  have h0 : Entails.eval a c10895 := derived10895 a h
  have h1 : Entails.eval a c10865 := derived10865 a h
  have h2 : Entails.eval a c10230 := derived10230 a h
  have h3 : Entails.eval a c10725 := derived10725 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c10907 := derived10907 a h
  have h6 : Entails.eval a c3885 := h 3884 (by decide)
  have h7 : Entails.eval a c9770 := derived9770 a h
  have h8 : Entails.eval a c2758 := h 2757 (by decide)
  have h9 : Entails.eval a c2556 := h 2555 (by decide)
  have h10 : Entails.eval a c2694 := h 2693 (by decide)
  have h11 : Entails.eval a c9995 := derived9995 a h
  have h12 : Entails.eval a c10881 := derived10881 a h
  have h13 : Entails.eval a c3052 := h 3051 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10909 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10909 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10907, some c7994, some c10908, some c10521, some c10750, some c4526, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10909 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10909 : lratChecker f10909 p10909 = .success := by decide +kernel
theorem unsat10909 : Unsatisfiable (PosFin 65) f10909 := by
  apply lratCheckerSound f10909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10909
  · intro a ha; simp [p10909] at ha; subst a; trivial
  · exact checked10909
theorem derived10909 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10909 := by
  apply localUnsat_implies_entails f10909 [c10907, c7994, c10908, c10521, c10750, c4526] c10909 unsat10909 (by rfl) a
  have h0 : Entails.eval a c10907 := derived10907 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c10908 := derived10908 a h
  have h3 : Entails.eval a c10521 := derived10521 a h
  have h4 : Entails.eval a c10750 := derived10750 a h
  have h5 : Entails.eval a c4526 := h 4525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10910 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨60, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10910 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10521, some c10750, some c4526, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10910 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10910 : lratChecker f10910 p10910 = .success := by decide +kernel
theorem unsat10910 : Unsatisfiable (PosFin 65) f10910 := by
  apply lratCheckerSound f10910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10910
  · intro a ha; simp [p10910] at ha; subst a; trivial
  · exact checked10910
theorem derived10910 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10910 := by
  apply localUnsat_implies_entails f10910 [c10521, c10750, c4526] c10910 unsat10910 (by rfl) a
  have h0 : Entails.eval a c10521 := derived10521 a h
  have h1 : Entails.eval a c10750 := derived10750 a h
  have h2 : Entails.eval a c4526 := h 4525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10911 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨60, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10911 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4523, some c4522, some c8380, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10911 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10911 : lratChecker f10911 p10911 = .success := by decide +kernel
theorem unsat10911 : Unsatisfiable (PosFin 65) f10911 := by
  apply lratCheckerSound f10911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10911
  · intro a ha; simp [p10911] at ha; subst a; trivial
  · exact checked10911
theorem derived10911 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10911 := by
  apply localUnsat_implies_entails f10911 [c4523, c4522, c8380] c10911 unsat10911 (by rfl) a
  have h0 : Entails.eval a c4523 := h 4522 (by decide)
  have h1 : Entails.eval a c4522 := h 4521 (by decide)
  have h2 : Entails.eval a c8380 := derived8380 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10912 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨60, by decide⟩, true), (⟨63, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10912 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10910, some c8269, some c10911, some c10762, some c10761, some c10236, some c3962, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10912 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10912 : lratChecker f10912 p10912 = .success := by decide +kernel
theorem unsat10912 : Unsatisfiable (PosFin 65) f10912 := by
  apply lratCheckerSound f10912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10912
  · intro a ha; simp [p10912] at ha; subst a; trivial
  · exact checked10912
theorem derived10912 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10912 := by
  apply localUnsat_implies_entails f10912 [c10910, c8269, c10911, c10762, c10761, c10236, c3962] c10912 unsat10912 (by rfl) a
  have h0 : Entails.eval a c10910 := derived10910 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c10911 := derived10911 a h
  have h3 : Entails.eval a c10762 := derived10762 a h
  have h4 : Entails.eval a c10761 := derived10761 a h
  have h5 : Entails.eval a c10236 := derived10236 a h
  have h6 : Entails.eval a c3962 := h 3961 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10913 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨63, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10913 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10910, some c8269, some c10912, some c10165, some c10292, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10913 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10913 : lratChecker f10913 p10913 = .success := by decide +kernel
theorem unsat10913 : Unsatisfiable (PosFin 65) f10913 := by
  apply lratCheckerSound f10913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10913
  · intro a ha; simp [p10913] at ha; subst a; trivial
  · exact checked10913
theorem derived10913 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10913 := by
  apply localUnsat_implies_entails f10913 [c10910, c8269, c10912, c10165, c10292] c10913 unsat10913 (by rfl) a
  have h0 : Entails.eval a c10910 := derived10910 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c10912 := derived10912 a h
  have h3 : Entails.eval a c10165 := derived10165 a h
  have h4 : Entails.eval a c10292 := derived10292 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10914 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨64, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10914 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c10165, some c10292, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10914 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10914 : lratChecker f10914 p10914 = .success := by decide +kernel
theorem unsat10914 : Unsatisfiable (PosFin 65) f10914 := by
  apply lratCheckerSound f10914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10914
  · intro a ha; simp [p10914] at ha; subst a; trivial
  · exact checked10914
theorem derived10914 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10914 := by
  apply localUnsat_implies_entails f10914 [c8269, c10165, c10292] c10914 unsat10914 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c10165 := derived10165 a h
  have h2 : Entails.eval a c10292 := derived10292 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10915 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨5, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10915 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c10914, some c3948, some c3940, some c3944, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p10915 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10915 : lratChecker f10915 p10915 = .success := by decide +kernel
theorem unsat10915 : Unsatisfiable (PosFin 65) f10915 := by
  apply lratCheckerSound f10915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10915
  · intro a ha; simp [p10915] at ha; subst a; trivial
  · exact checked10915
theorem derived10915 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10915 := by
  apply localUnsat_implies_entails f10915 [c8269, c10914, c3948, c3940, c3944] c10915 unsat10915 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c10914 := derived10914 a h
  have h2 : Entails.eval a c3948 := h 3947 (by decide)
  have h3 : Entails.eval a c3940 := h 3939 (by decide)
  have h4 : Entails.eval a c3944 := h 3943 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10916 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10916 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3948, some c3940, some c3944, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p10916 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10916 : lratChecker f10916 p10916 = .success := by decide +kernel
theorem unsat10916 : Unsatisfiable (PosFin 65) f10916 := by
  apply lratCheckerSound f10916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10916
  · intro a ha; simp [p10916] at ha; subst a; trivial
  · exact checked10916
theorem derived10916 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10916 := by
  apply localUnsat_implies_entails f10916 [c3948, c3940, c3944] c10916 unsat10916 (by rfl) a
  have h0 : Entails.eval a c3948 := h 3947 (by decide)
  have h1 : Entails.eval a c3940 := h 3939 (by decide)
  have h2 : Entails.eval a c3944 := h 3943 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10917 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨63, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10917 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3964, some c3962, some c4047, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10917 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10917 : lratChecker f10917 p10917 = .success := by decide +kernel
theorem unsat10917 : Unsatisfiable (PosFin 65) f10917 := by
  apply lratCheckerSound f10917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10917
  · intro a ha; simp [p10917] at ha; subst a; trivial
  · exact checked10917
theorem derived10917 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10917 := by
  apply localUnsat_implies_entails f10917 [c3964, c3962, c4047] c10917 unsat10917 (by rfl) a
  have h0 : Entails.eval a c3964 := h 3963 (by decide)
  have h1 : Entails.eval a c3962 := h 3961 (by decide)
  have h2 : Entails.eval a c4047 := h 4046 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10918 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10918 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10895, some c10907, some c10909, some c10913, some c10173, some c10915, some c10158, some c10865, some c10161, some c10917, some c2558, some c10765, some c2656, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10918 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10918 : lratChecker f10918 p10918 = .success := by decide +kernel
theorem unsat10918 : Unsatisfiable (PosFin 65) f10918 := by
  apply lratCheckerSound f10918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10918
  · intro a ha; simp [p10918] at ha; subst a; trivial
  · exact checked10918
theorem derived10918 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10918 := by
  apply localUnsat_implies_entails f10918 [c10895, c10907, c10909, c10913, c10173, c10915, c10158, c10865, c10161, c10917, c2558, c10765, c2656] c10918 unsat10918 (by rfl) a
  have h0 : Entails.eval a c10895 := derived10895 a h
  have h1 : Entails.eval a c10907 := derived10907 a h
  have h2 : Entails.eval a c10909 := derived10909 a h
  have h3 : Entails.eval a c10913 := derived10913 a h
  have h4 : Entails.eval a c10173 := derived10173 a h
  have h5 : Entails.eval a c10915 := derived10915 a h
  have h6 : Entails.eval a c10158 := derived10158 a h
  have h7 : Entails.eval a c10865 := derived10865 a h
  have h8 : Entails.eval a c10161 := derived10161 a h
  have h9 : Entails.eval a c10917 := derived10917 a h
  have h10 : Entails.eval a c2558 := h 2557 (by decide)
  have h11 : Entails.eval a c10765 := derived10765 a h
  have h12 : Entails.eval a c2656 := h 2655 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10919 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10919 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10865, some c10895, some c10907, some c10909, some c10913, some c10173, some c10915, some c10918, some c10295, some c10212, some c10305, some c3883, some c10651, some c2657, some c4661, some c2687, some c3409, some c3335, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10919 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked10919 : lratChecker f10919 p10919 = .success := by decide +kernel
theorem unsat10919 : Unsatisfiable (PosFin 65) f10919 := by
  apply lratCheckerSound f10919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10919
  · intro a ha; simp [p10919] at ha; subst a; trivial
  · exact checked10919
theorem derived10919 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10919 := by
  apply localUnsat_implies_entails f10919 [c10865, c10895, c10907, c10909, c10913, c10173, c10915, c10918, c10295, c10212, c10305, c3883, c10651, c2657, c4661, c2687, c3409, c3335] c10919 unsat10919 (by rfl) a
  have h0 : Entails.eval a c10865 := derived10865 a h
  have h1 : Entails.eval a c10895 := derived10895 a h
  have h2 : Entails.eval a c10907 := derived10907 a h
  have h3 : Entails.eval a c10909 := derived10909 a h
  have h4 : Entails.eval a c10913 := derived10913 a h
  have h5 : Entails.eval a c10173 := derived10173 a h
  have h6 : Entails.eval a c10915 := derived10915 a h
  have h7 : Entails.eval a c10918 := derived10918 a h
  have h8 : Entails.eval a c10295 := derived10295 a h
  have h9 : Entails.eval a c10212 := derived10212 a h
  have h10 : Entails.eval a c10305 := derived10305 a h
  have h11 : Entails.eval a c3883 := h 3882 (by decide)
  have h12 : Entails.eval a c10651 := derived10651 a h
  have h13 : Entails.eval a c2657 := h 2656 (by decide)
  have h14 : Entails.eval a c4661 := h 4660 (by decide)
  have h15 : Entails.eval a c2687 := h 2686 (by decide)
  have h16 : Entails.eval a c3409 := h 3408 (by decide)
  have h17 : Entails.eval a c3335 := h 3334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10920 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10920 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10919, some c10214, some c10348, some c10599, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10920 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10920 : lratChecker f10920 p10920 = .success := by decide +kernel
theorem unsat10920 : Unsatisfiable (PosFin 65) f10920 := by
  apply lratCheckerSound f10920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10920
  · intro a ha; simp [p10920] at ha; subst a; trivial
  · exact checked10920
theorem derived10920 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10920 := by
  apply localUnsat_implies_entails f10920 [c10919, c10214, c10348, c10599] c10920 unsat10920 (by rfl) a
  have h0 : Entails.eval a c10919 := derived10919 a h
  have h1 : Entails.eval a c10214 := derived10214 a h
  have h2 : Entails.eval a c10348 := derived10348 a h
  have h3 : Entails.eval a c10599 := derived10599 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10921 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨60, by decide⟩, true), (⟨6, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10921 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10520, some c10363, some c10365, some c8380, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10921 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10921 : lratChecker f10921 p10921 = .success := by decide +kernel
theorem unsat10921 : Unsatisfiable (PosFin 65) f10921 := by
  apply lratCheckerSound f10921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10921
  · intro a ha; simp [p10921] at ha; subst a; trivial
  · exact checked10921
theorem derived10921 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10921 := by
  apply localUnsat_implies_entails f10921 [c10520, c10363, c10365, c8380] c10921 unsat10921 (by rfl) a
  have h0 : Entails.eval a c10520 := derived10520 a h
  have h1 : Entails.eval a c10363 := derived10363 a h
  have h2 : Entails.eval a c10365 := derived10365 a h
  have h3 : Entails.eval a c8380 := derived8380 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10922 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10922 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10919, some c10921, some c10648, some c10749, some c10341, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10922 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10922 : lratChecker f10922 p10922 = .success := by decide +kernel
theorem unsat10922 : Unsatisfiable (PosFin 65) f10922 := by
  apply lratCheckerSound f10922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10922
  · intro a ha; simp [p10922] at ha; subst a; trivial
  · exact checked10922
theorem derived10922 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10922 := by
  apply localUnsat_implies_entails f10922 [c10919, c10921, c10648, c10749, c10341] c10922 unsat10922 (by rfl) a
  have h0 : Entails.eval a c10919 := derived10919 a h
  have h1 : Entails.eval a c10921 := derived10921 a h
  have h2 : Entails.eval a c10648 := derived10648 a h
  have h3 : Entails.eval a c10749 := derived10749 a h
  have h4 : Entails.eval a c10341 := derived10341 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10923 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨16, by decide⟩, false), (⟨63, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10923 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10352, some c5013, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10923 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10923 : lratChecker f10923 p10923 = .success := by decide +kernel
theorem unsat10923 : Unsatisfiable (PosFin 65) f10923 := by
  apply lratCheckerSound f10923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10923
  · intro a ha; simp [p10923] at ha; subst a; trivial
  · exact checked10923
theorem derived10923 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10923 := by
  apply localUnsat_implies_entails f10923 [c10352, c5013] c10923 unsat10923 (by rfl) a
  have h0 : Entails.eval a c10352 := derived10352 a h
  have h1 : Entails.eval a c5013 := h 5012 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10924 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10924 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10922, some c10919, some c10920, some c10923, some c10647, some c5018, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10924 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10924 : lratChecker f10924 p10924 = .success := by decide +kernel
theorem unsat10924 : Unsatisfiable (PosFin 65) f10924 := by
  apply lratCheckerSound f10924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10924
  · intro a ha; simp [p10924] at ha; subst a; trivial
  · exact checked10924
theorem derived10924 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10924 := by
  apply localUnsat_implies_entails f10924 [c10922, c10919, c10920, c10923, c10647, c5018] c10924 unsat10924 (by rfl) a
  have h0 : Entails.eval a c10922 := derived10922 a h
  have h1 : Entails.eval a c10919 := derived10919 a h
  have h2 : Entails.eval a c10920 := derived10920 a h
  have h3 : Entails.eval a c10923 := derived10923 a h
  have h4 : Entails.eval a c10647 := derived10647 a h
  have h5 : Entails.eval a c5018 := h 5017 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10925 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10925 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10922, some c10919, some c10924, some c10724, some c10539, some c5019, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10925 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10925 : lratChecker f10925 p10925 = .success := by decide +kernel
theorem unsat10925 : Unsatisfiable (PosFin 65) f10925 := by
  apply lratCheckerSound f10925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10925
  · intro a ha; simp [p10925] at ha; subst a; trivial
  · exact checked10925
theorem derived10925 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10925 := by
  apply localUnsat_implies_entails f10925 [c10922, c10919, c10924, c10724, c10539, c5019] c10925 unsat10925 (by rfl) a
  have h0 : Entails.eval a c10922 := derived10922 a h
  have h1 : Entails.eval a c10919 := derived10919 a h
  have h2 : Entails.eval a c10924 := derived10924 a h
  have h3 : Entails.eval a c10724 := derived10724 a h
  have h4 : Entails.eval a c10539 := derived10539 a h
  have h5 : Entails.eval a c5019 := h 5018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10926 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨63, by decide⟩, false), (⟨61, by decide⟩, false), (⟨14, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10926 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5015, some c4097, some c10567, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10926 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10926 : lratChecker f10926 p10926 = .success := by decide +kernel
theorem unsat10926 : Unsatisfiable (PosFin 65) f10926 := by
  apply lratCheckerSound f10926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10926
  · intro a ha; simp [p10926] at ha; subst a; trivial
  · exact checked10926
theorem derived10926 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10926 := by
  apply localUnsat_implies_entails f10926 [c5015, c4097, c10567] c10926 unsat10926 (by rfl) a
  have h0 : Entails.eval a c5015 := h 5014 (by decide)
  have h1 : Entails.eval a c4097 := h 4096 (by decide)
  have h2 : Entails.eval a c10567 := derived10567 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10927 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10927 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10925, some c10922, some c10919, some c10865, some c7994, some c10351, some c10926, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10927 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10927 : lratChecker f10927 p10927 = .success := by decide +kernel
theorem unsat10927 : Unsatisfiable (PosFin 65) f10927 := by
  apply lratCheckerSound f10927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10927
  · intro a ha; simp [p10927] at ha; subst a; trivial
  · exact checked10927
theorem derived10927 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10927 := by
  apply localUnsat_implies_entails f10927 [c10925, c10922, c10919, c10865, c7994, c10351, c10926] c10927 unsat10927 (by rfl) a
  have h0 : Entails.eval a c10925 := derived10925 a h
  have h1 : Entails.eval a c10922 := derived10922 a h
  have h2 : Entails.eval a c10919 := derived10919 a h
  have h3 : Entails.eval a c10865 := derived10865 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c10351 := derived10351 a h
  have h6 : Entails.eval a c10926 := derived10926 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10928 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false), (⟨54, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10928 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4787, some c5014, some c10650, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p10928 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10928 : lratChecker f10928 p10928 = .success := by decide +kernel
theorem unsat10928 : Unsatisfiable (PosFin 65) f10928 := by
  apply lratCheckerSound f10928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10928
  · intro a ha; simp [p10928] at ha; subst a; trivial
  · exact checked10928
theorem derived10928 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10928 := by
  apply localUnsat_implies_entails f10928 [c4787, c5014, c10650] c10928 unsat10928 (by rfl) a
  have h0 : Entails.eval a c4787 := h 4786 (by decide)
  have h1 : Entails.eval a c5014 := h 5013 (by decide)
  have h2 : Entails.eval a c10650 := derived10650 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10929 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10929 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10865, some c10919, some c10922, some c10927, some c10920, some c10923, some c10928, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10929 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10929 : lratChecker f10929 p10929 = .success := by decide +kernel
theorem unsat10929 : Unsatisfiable (PosFin 65) f10929 := by
  apply lratCheckerSound f10929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10929
  · intro a ha; simp [p10929] at ha; subst a; trivial
  · exact checked10929
theorem derived10929 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10929 := by
  apply localUnsat_implies_entails f10929 [c10865, c10919, c10922, c10927, c10920, c10923, c10928] c10929 unsat10929 (by rfl) a
  have h0 : Entails.eval a c10865 := derived10865 a h
  have h1 : Entails.eval a c10919 := derived10919 a h
  have h2 : Entails.eval a c10922 := derived10922 a h
  have h3 : Entails.eval a c10927 := derived10927 a h
  have h4 : Entails.eval a c10920 := derived10920 a h
  have h5 : Entails.eval a c10923 := derived10923 a h
  have h6 : Entails.eval a c10928 := derived10928 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10930 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10930 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5010, some c4781, some c10729, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p10930 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10930 : lratChecker f10930 p10930 = .success := by decide +kernel
theorem unsat10930 : Unsatisfiable (PosFin 65) f10930 := by
  apply lratCheckerSound f10930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10930
  · intro a ha; simp [p10930] at ha; subst a; trivial
  · exact checked10930
theorem derived10930 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10930 := by
  apply localUnsat_implies_entails f10930 [c5010, c4781, c10729] c10930 unsat10930 (by rfl) a
  have h0 : Entails.eval a c5010 := h 5009 (by decide)
  have h1 : Entails.eval a c4781 := h 4780 (by decide)
  have h2 : Entails.eval a c10729 := derived10729 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10931 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10931 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10930, some c4688, some c3162, some c3386, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10931 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10931 : lratChecker f10931 p10931 = .success := by decide +kernel
theorem unsat10931 : Unsatisfiable (PosFin 65) f10931 := by
  apply lratCheckerSound f10931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10931
  · intro a ha; simp [p10931] at ha; subst a; trivial
  · exact checked10931
theorem derived10931 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10931 := by
  apply localUnsat_implies_entails f10931 [c10929, c10930, c4688, c3162, c3386] c10931 unsat10931 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10930 := derived10930 a h
  have h2 : Entails.eval a c4688 := h 4687 (by decide)
  have h3 : Entails.eval a c3162 := h 3161 (by decide)
  have h4 : Entails.eval a c3386 := h 3385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10932 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨58, by decide⟩, true), (⟨63, by decide⟩, true), (⟨16, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10932 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10591, some c10576, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10932 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10932 : lratChecker f10932 p10932 = .success := by decide +kernel
theorem unsat10932 : Unsatisfiable (PosFin 65) f10932 := by
  apply lratCheckerSound f10932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10932
  · intro a ha; simp [p10932] at ha; subst a; trivial
  · exact checked10932
theorem derived10932 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10932 := by
  apply localUnsat_implies_entails f10932 [c10929, c10591, c10576] c10932 unsat10932 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10591 := derived10591 a h
  have h2 : Entails.eval a c10576 := derived10576 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10933 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨3, by decide⟩, false), (⟨58, by decide⟩, true), (⟨12, by decide⟩, true), (⟨63, by decide⟩, true), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10933 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3985, some c3097, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p10933 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10933 : lratChecker f10933 p10933 = .success := by decide +kernel
theorem unsat10933 : Unsatisfiable (PosFin 65) f10933 := by
  apply lratCheckerSound f10933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10933
  · intro a ha; simp [p10933] at ha; subst a; trivial
  · exact checked10933
theorem derived10933 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10933 := by
  apply localUnsat_implies_entails f10933 [c3985, c3097] c10933 unsat10933 (by rfl) a
  have h0 : Entails.eval a c3985 := h 3984 (by decide)
  have h1 : Entails.eval a c3097 := h 3096 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10934 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨59, by decide⟩, false), (⟨57, by decide⟩, false), (⟨5, by decide⟩, false), (⟨56, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10934 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c1045, some c990, some c984, some c6708, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10934 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10934 : lratChecker f10934 p10934 = .success := by decide +kernel
theorem unsat10934 : Unsatisfiable (PosFin 65) f10934 := by
  apply lratCheckerSound f10934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10934
  · intro a ha; simp [p10934] at ha; subst a; trivial
  · exact checked10934
theorem derived10934 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10934 := by
  apply localUnsat_implies_entails f10934 [c10929, c1045, c990, c984, c6708] c10934 unsat10934 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c1045 := h 1044 (by decide)
  have h2 : Entails.eval a c990 := h 989 (by decide)
  have h3 : Entails.eval a c984 := h 983 (by decide)
  have h4 : Entails.eval a c6708 := h 6707 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10935 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨59, by decide⟩, false), (⟨51, by decide⟩, false), (⟨13, by decide⟩, false), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false), (⟨5, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10935 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c556, some c543, some c3863, some c7289, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10935 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10935 : lratChecker f10935 p10935 = .success := by decide +kernel
theorem unsat10935 : Unsatisfiable (PosFin 65) f10935 := by
  apply lratCheckerSound f10935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10935
  · intro a ha; simp [p10935] at ha; subst a; trivial
  · exact checked10935
theorem derived10935 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10935 := by
  apply localUnsat_implies_entails f10935 [c10929, c556, c543, c3863, c7289] c10935 unsat10935 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c556 := h 555 (by decide)
  have h2 : Entails.eval a c543 := h 542 (by decide)
  have h3 : Entails.eval a c3863 := h 3862 (by decide)
  have h4 : Entails.eval a c7289 := h 7288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10936 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10936 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10931, some c10929, some c10729, some c10926, some c4971, some c4737, some c4636, some c9789, some c10930, some c5031, some c3386, some c10933, some c10932, some c3410, some c10903, some c9775, some c3879, some c10715, some c10899, some c4140, some c4244, some c3873, some c10935, some c10934, some c38, some c485, some c489, some c8480, some c988, some c7332, some c6521, some c5128, some c3988, some c5401, some c5374, some c5648, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10936 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked10936 : lratChecker f10936 p10936 = .success := by decide +kernel
theorem unsat10936 : Unsatisfiable (PosFin 65) f10936 := by
  apply lratCheckerSound f10936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10936
  · intro a ha; simp [p10936] at ha; subst a; trivial
  · exact checked10936
theorem derived10936 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10936 := by
  apply localUnsat_implies_entails f10936 [c10931, c10929, c10729, c10926, c4971, c4737, c4636, c9789, c10930, c5031, c3386, c10933, c10932, c3410, c10903, c9775, c3879, c10715, c10899, c4140, c4244, c3873, c10935, c10934, c38, c485, c489, c8480, c988, c7332, c6521, c5128, c3988, c5401, c5374, c5648] c10936 unsat10936 (by rfl) a
  have h0 : Entails.eval a c10931 := derived10931 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10729 := derived10729 a h
  have h3 : Entails.eval a c10926 := derived10926 a h
  have h4 : Entails.eval a c4971 := h 4970 (by decide)
  have h5 : Entails.eval a c4737 := h 4736 (by decide)
  have h6 : Entails.eval a c4636 := h 4635 (by decide)
  have h7 : Entails.eval a c9789 := derived9789 a h
  have h8 : Entails.eval a c10930 := derived10930 a h
  have h9 : Entails.eval a c5031 := h 5030 (by decide)
  have h10 : Entails.eval a c3386 := h 3385 (by decide)
  have h11 : Entails.eval a c10933 := derived10933 a h
  have h12 : Entails.eval a c10932 := derived10932 a h
  have h13 : Entails.eval a c3410 := h 3409 (by decide)
  have h14 : Entails.eval a c10903 := derived10903 a h
  have h15 : Entails.eval a c9775 := derived9775 a h
  have h16 : Entails.eval a c3879 := h 3878 (by decide)
  have h17 : Entails.eval a c10715 := derived10715 a h
  have h18 : Entails.eval a c10899 := derived10899 a h
  have h19 : Entails.eval a c4140 := h 4139 (by decide)
  have h20 : Entails.eval a c4244 := h 4243 (by decide)
  have h21 : Entails.eval a c3873 := h 3872 (by decide)
  have h22 : Entails.eval a c10935 := derived10935 a h
  have h23 : Entails.eval a c10934 := derived10934 a h
  have h24 : Entails.eval a c38 := h 37 (by decide)
  have h25 : Entails.eval a c485 := h 484 (by decide)
  have h26 : Entails.eval a c489 := h 488 (by decide)
  have h27 : Entails.eval a c8480 := derived8480 a h
  have h28 : Entails.eval a c988 := h 987 (by decide)
  have h29 : Entails.eval a c7332 := h 7331 (by decide)
  have h30 : Entails.eval a c6521 := h 6520 (by decide)
  have h31 : Entails.eval a c5128 := h 5127 (by decide)
  have h32 : Entails.eval a c3988 := h 3987 (by decide)
  have h33 : Entails.eval a c5401 := h 5400 (by decide)
  have h34 : Entails.eval a c5374 := h 5373 (by decide)
  have h35 : Entails.eval a c5648 := h 5647 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10937 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10937 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10931, some c10929, some c10729, some c4971, some c4737, some c10930, some c4636, some c5031, some c3386, some c3410, some c10936, some c9789, some c10926, some c10933, some c10244, some c10932, some c2629, some c10173, some c2585, some c10899, some c10260, some c10262, some c10715, some c2601, some c38, some c4214, some c489, some c2573, some c4216, some c6645, some c66, some c6659, some c7078, some c10225, some c1043, some c1050, some c4199, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10937 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked10937 : lratChecker f10937 p10937 = .success := by decide +kernel
theorem unsat10937 : Unsatisfiable (PosFin 65) f10937 := by
  apply lratCheckerSound f10937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10937
  · intro a ha; simp [p10937] at ha; subst a; trivial
  · exact checked10937
theorem derived10937 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10937 := by
  apply localUnsat_implies_entails f10937 [c10931, c10929, c10729, c4971, c4737, c10930, c4636, c5031, c3386, c3410, c10936, c9789, c10926, c10933, c10244, c10932, c2629, c10173, c2585, c10899, c10260, c10262, c10715, c2601, c38, c4214, c489, c2573, c4216, c6645, c66, c6659, c7078, c10225, c1043, c1050, c4199] c10937 unsat10937 (by rfl) a
  have h0 : Entails.eval a c10931 := derived10931 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10729 := derived10729 a h
  have h3 : Entails.eval a c4971 := h 4970 (by decide)
  have h4 : Entails.eval a c4737 := h 4736 (by decide)
  have h5 : Entails.eval a c10930 := derived10930 a h
  have h6 : Entails.eval a c4636 := h 4635 (by decide)
  have h7 : Entails.eval a c5031 := h 5030 (by decide)
  have h8 : Entails.eval a c3386 := h 3385 (by decide)
  have h9 : Entails.eval a c3410 := h 3409 (by decide)
  have h10 : Entails.eval a c10936 := derived10936 a h
  have h11 : Entails.eval a c9789 := derived9789 a h
  have h12 : Entails.eval a c10926 := derived10926 a h
  have h13 : Entails.eval a c10933 := derived10933 a h
  have h14 : Entails.eval a c10244 := derived10244 a h
  have h15 : Entails.eval a c10932 := derived10932 a h
  have h16 : Entails.eval a c2629 := h 2628 (by decide)
  have h17 : Entails.eval a c10173 := derived10173 a h
  have h18 : Entails.eval a c2585 := h 2584 (by decide)
  have h19 : Entails.eval a c10899 := derived10899 a h
  have h20 : Entails.eval a c10260 := derived10260 a h
  have h21 : Entails.eval a c10262 := derived10262 a h
  have h22 : Entails.eval a c10715 := derived10715 a h
  have h23 : Entails.eval a c2601 := h 2600 (by decide)
  have h24 : Entails.eval a c38 := h 37 (by decide)
  have h25 : Entails.eval a c4214 := h 4213 (by decide)
  have h26 : Entails.eval a c489 := h 488 (by decide)
  have h27 : Entails.eval a c2573 := h 2572 (by decide)
  have h28 : Entails.eval a c4216 := h 4215 (by decide)
  have h29 : Entails.eval a c6645 := h 6644 (by decide)
  have h30 : Entails.eval a c66 := h 65 (by decide)
  have h31 : Entails.eval a c6659 := h 6658 (by decide)
  have h32 : Entails.eval a c7078 := h 7077 (by decide)
  have h33 : Entails.eval a c10225 := derived10225 a h
  have h34 : Entails.eval a c1043 := h 1042 (by decide)
  have h35 : Entails.eval a c1050 := h 1049 (by decide)
  have h36 : Entails.eval a c4199 := h 4198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10938 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10938 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10930, some c10931, some c10729, some c10926, some c4971, some c4737, some c4636, some c5031, some c9789, some c3386, some c3410, some c10932, some c10933, some c2629, some c10936, some c10173, some c10244, some c2585, some c2601, some c10899, some c10260, some c10937, some c9864, some c9959, some c2595, some c1046, some c1033, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10938 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked10938 : lratChecker f10938 p10938 = .success := by decide +kernel
theorem unsat10938 : Unsatisfiable (PosFin 65) f10938 := by
  apply lratCheckerSound f10938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10938
  · intro a ha; simp [p10938] at ha; subst a; trivial
  · exact checked10938
theorem derived10938 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10938 := by
  apply localUnsat_implies_entails f10938 [c10930, c10931, c10729, c10926, c4971, c4737, c4636, c5031, c9789, c3386, c3410, c10932, c10933, c2629, c10936, c10173, c10244, c2585, c2601, c10899, c10260, c10937, c9864, c9959, c2595, c1046, c1033] c10938 unsat10938 (by rfl) a
  have h0 : Entails.eval a c10930 := derived10930 a h
  have h1 : Entails.eval a c10931 := derived10931 a h
  have h2 : Entails.eval a c10729 := derived10729 a h
  have h3 : Entails.eval a c10926 := derived10926 a h
  have h4 : Entails.eval a c4971 := h 4970 (by decide)
  have h5 : Entails.eval a c4737 := h 4736 (by decide)
  have h6 : Entails.eval a c4636 := h 4635 (by decide)
  have h7 : Entails.eval a c5031 := h 5030 (by decide)
  have h8 : Entails.eval a c9789 := derived9789 a h
  have h9 : Entails.eval a c3386 := h 3385 (by decide)
  have h10 : Entails.eval a c3410 := h 3409 (by decide)
  have h11 : Entails.eval a c10932 := derived10932 a h
  have h12 : Entails.eval a c10933 := derived10933 a h
  have h13 : Entails.eval a c2629 := h 2628 (by decide)
  have h14 : Entails.eval a c10936 := derived10936 a h
  have h15 : Entails.eval a c10173 := derived10173 a h
  have h16 : Entails.eval a c10244 := derived10244 a h
  have h17 : Entails.eval a c2585 := h 2584 (by decide)
  have h18 : Entails.eval a c2601 := h 2600 (by decide)
  have h19 : Entails.eval a c10899 := derived10899 a h
  have h20 : Entails.eval a c10260 := derived10260 a h
  have h21 : Entails.eval a c10937 := derived10937 a h
  have h22 : Entails.eval a c9864 := derived9864 a h
  have h23 : Entails.eval a c9959 := derived9959 a h
  have h24 : Entails.eval a c2595 := h 2594 (by decide)
  have h25 : Entails.eval a c1046 := h 1045 (by decide)
  have h26 : Entails.eval a c1033 := h 1032 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10939 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨56, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10939 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10173, some c4194, some c10244, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10939 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10939 : lratChecker f10939 p10939 = .success := by decide +kernel
theorem unsat10939 : Unsatisfiable (PosFin 65) f10939 := by
  apply lratCheckerSound f10939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10939
  · intro a ha; simp [p10939] at ha; subst a; trivial
  · exact checked10939
theorem derived10939 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10939 := by
  apply localUnsat_implies_entails f10939 [c10173, c4194, c10244] c10939 unsat10939 (by rfl) a
  have h0 : Entails.eval a c10173 := derived10173 a h
  have h1 : Entails.eval a c4194 := h 4193 (by decide)
  have h2 : Entails.eval a c10244 := derived10244 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10940 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10940 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10938, some c5047, some c5032, some c3387, some c3411, some c10939, some c4163, some c3089, some c4134, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10940 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10940 : lratChecker f10940 p10940 = .success := by decide +kernel
theorem unsat10940 : Unsatisfiable (PosFin 65) f10940 := by
  apply lratCheckerSound f10940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10940
  · intro a ha; simp [p10940] at ha; subst a; trivial
  · exact checked10940
theorem derived10940 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10940 := by
  apply localUnsat_implies_entails f10940 [c10929, c10938, c5047, c5032, c3387, c3411, c10939, c4163, c3089, c4134] c10940 unsat10940 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10938 := derived10938 a h
  have h2 : Entails.eval a c5047 := h 5046 (by decide)
  have h3 : Entails.eval a c5032 := h 5031 (by decide)
  have h4 : Entails.eval a c3387 := h 3386 (by decide)
  have h5 : Entails.eval a c3411 := h 3410 (by decide)
  have h6 : Entails.eval a c10939 := derived10939 a h
  have h7 : Entails.eval a c4163 := h 4162 (by decide)
  have h8 : Entails.eval a c3089 := h 3088 (by decide)
  have h9 : Entails.eval a c4134 := h 4133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10941 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨56, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10941 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10173, some c10235, some c10525, some c10233, some c10232, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10941 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10941 : lratChecker f10941 p10941 = .success := by decide +kernel
theorem unsat10941 : Unsatisfiable (PosFin 65) f10941 := by
  apply lratCheckerSound f10941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10941
  · intro a ha; simp [p10941] at ha; subst a; trivial
  · exact checked10941
theorem derived10941 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10941 := by
  apply localUnsat_implies_entails f10941 [c10173, c10235, c10525, c10233, c10232] c10941 unsat10941 (by rfl) a
  have h0 : Entails.eval a c10173 := derived10173 a h
  have h1 : Entails.eval a c10235 := derived10235 a h
  have h2 : Entails.eval a c10525 := derived10525 a h
  have h3 : Entails.eval a c10233 := derived10233 a h
  have h4 : Entails.eval a c10232 := derived10232 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10942 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10942 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10938, some c10940, some c10941, some c4160, some c4120, some c4128, some c4155, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10942 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10942 : lratChecker f10942 p10942 = .success := by decide +kernel
theorem unsat10942 : Unsatisfiable (PosFin 65) f10942 := by
  apply lratCheckerSound f10942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10942
  · intro a ha; simp [p10942] at ha; subst a; trivial
  · exact checked10942
theorem derived10942 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10942 := by
  apply localUnsat_implies_entails f10942 [c10929, c10938, c10940, c10941, c4160, c4120, c4128, c4155] c10942 unsat10942 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10938 := derived10938 a h
  have h2 : Entails.eval a c10940 := derived10940 a h
  have h3 : Entails.eval a c10941 := derived10941 a h
  have h4 : Entails.eval a c4160 := h 4159 (by decide)
  have h5 : Entails.eval a c4120 := h 4119 (by decide)
  have h6 : Entails.eval a c4128 := h 4127 (by decide)
  have h7 : Entails.eval a c4155 := h 4154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10943 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10943 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4160, some c4159, some c4156, some c4155, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p10943 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10943 : lratChecker f10943 p10943 = .success := by decide +kernel
theorem unsat10943 : Unsatisfiable (PosFin 65) f10943 := by
  apply lratCheckerSound f10943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10943
  · intro a ha; simp [p10943] at ha; subst a; trivial
  · exact checked10943
theorem derived10943 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10943 := by
  apply localUnsat_implies_entails f10943 [c4160, c4159, c4156, c4155] c10943 unsat10943 (by rfl) a
  have h0 : Entails.eval a c4160 := h 4159 (by decide)
  have h1 : Entails.eval a c4159 := h 4158 (by decide)
  have h2 : Entails.eval a c4156 := h 4155 (by decide)
  have h3 : Entails.eval a c4155 := h 4154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10944 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10944 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10938, some c10941, some c10943, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10944 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10944 : lratChecker f10944 p10944 = .success := by decide +kernel
theorem unsat10944 : Unsatisfiable (PosFin 65) f10944 := by
  apply lratCheckerSound f10944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10944
  · intro a ha; simp [p10944] at ha; subst a; trivial
  · exact checked10944
theorem derived10944 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10944 := by
  apply localUnsat_implies_entails f10944 [c10929, c10938, c10941, c10943] c10944 unsat10944 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10938 := derived10938 a h
  have h2 : Entails.eval a c10941 := derived10941 a h
  have h3 : Entails.eval a c10943 := derived10943 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10945 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10945 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10942, some c10944, some c2690, some c5073, some c2629, some c10591, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10945 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10945 : lratChecker f10945 p10945 = .success := by decide +kernel
theorem unsat10945 : Unsatisfiable (PosFin 65) f10945 := by
  apply lratCheckerSound f10945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10945
  · intro a ha; simp [p10945] at ha; subst a; trivial
  · exact checked10945
theorem derived10945 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10945 := by
  apply localUnsat_implies_entails f10945 [c10929, c10942, c10944, c2690, c5073, c2629, c10591] c10945 unsat10945 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10942 := derived10942 a h
  have h2 : Entails.eval a c10944 := derived10944 a h
  have h3 : Entails.eval a c2690 := h 2689 (by decide)
  have h4 : Entails.eval a c5073 := h 5072 (by decide)
  have h5 : Entails.eval a c2629 := h 2628 (by decide)
  have h6 : Entails.eval a c10591 := derived10591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10946 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨2, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10946 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c4556, some c2790, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10946 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10946 : lratChecker f10946 p10946 = .success := by decide +kernel
theorem unsat10946 : Unsatisfiable (PosFin 65) f10946 := by
  apply lratCheckerSound f10946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10946
  · intro a ha; simp [p10946] at ha; subst a; trivial
  · exact checked10946
theorem derived10946 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10946 := by
  apply localUnsat_implies_entails f10946 [c10929, c4556, c2790] c10946 unsat10946 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c4556 := h 4555 (by decide)
  have h2 : Entails.eval a c2790 := h 2789 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10947 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10947 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c50, some c511, some c512, some c6536, some c6331, some c4021, some c6720, some c1032, some c4942, some c57, some c1034, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10947 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10947 : lratChecker f10947 p10947 = .success := by decide +kernel
theorem unsat10947 : Unsatisfiable (PosFin 65) f10947 := by
  apply lratCheckerSound f10947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10947
  · intro a ha; simp [p10947] at ha; subst a; trivial
  · exact checked10947
theorem derived10947 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10947 := by
  apply localUnsat_implies_entails f10947 [c10929, c50, c511, c512, c6536, c6331, c4021, c6720, c1032, c4942, c57, c1034] c10947 unsat10947 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c511 := h 510 (by decide)
  have h3 : Entails.eval a c512 := h 511 (by decide)
  have h4 : Entails.eval a c6536 := h 6535 (by decide)
  have h5 : Entails.eval a c6331 := h 6330 (by decide)
  have h6 : Entails.eval a c4021 := h 4020 (by decide)
  have h7 : Entails.eval a c6720 := h 6719 (by decide)
  have h8 : Entails.eval a c1032 := h 1031 (by decide)
  have h9 : Entails.eval a c4942 := h 4941 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c1034 := h 1033 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10948 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨35, by decide⟩, false), (⟨52, by decide⟩, false), (⟨13, by decide⟩, false), (⟨60, by decide⟩, false), (⟨4, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10948 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c945, some c8235, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10948 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10948 : lratChecker f10948 p10948 = .success := by decide +kernel
theorem unsat10948 : Unsatisfiable (PosFin 65) f10948 := by
  apply lratCheckerSound f10948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10948
  · intro a ha; simp [p10948] at ha; subst a; trivial
  · exact checked10948
theorem derived10948 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10948 := by
  apply localUnsat_implies_entails f10948 [c945, c8235] c10948 unsat10948 (by rfl) a
  have h0 : Entails.eval a c945 := h 944 (by decide)
  have h1 : Entails.eval a c8235 := derived8235 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10949 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨39, by decide⟩, true), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨62, by decide⟩, false), (⟨5, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10949 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c6673, some c992, some c464, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10949 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10949 : lratChecker f10949 p10949 = .success := by decide +kernel
theorem unsat10949 : Unsatisfiable (PosFin 65) f10949 := by
  apply lratCheckerSound f10949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10949
  · intro a ha; simp [p10949] at ha; subst a; trivial
  · exact checked10949
theorem derived10949 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10949 := by
  apply localUnsat_implies_entails f10949 [c10929, c6673, c992, c464] c10949 unsat10949 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c6673 := h 6672 (by decide)
  have h2 : Entails.eval a c992 := h 991 (by decide)
  have h3 : Entails.eval a c464 := h 463 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10950 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10950 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10945, some c10929, some c4637, some c5099, some c3423, some c3387, some c2486, some c10946, some c10938, some c2926, some c10939, some c3014, some c2791, some c4101, some c2757, some c3684, some c10860, some c4670, some c3687, some c2739, some c8366, some c10947, some c10948, some c10949, some c1031, some c6306, some c6360, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10950 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked10950 : lratChecker f10950 p10950 = .success := by decide +kernel
theorem unsat10950 : Unsatisfiable (PosFin 65) f10950 := by
  apply lratCheckerSound f10950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10950
  · intro a ha; simp [p10950] at ha; subst a; trivial
  · exact checked10950
theorem derived10950 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10950 := by
  apply localUnsat_implies_entails f10950 [c10945, c10929, c4637, c5099, c3423, c3387, c2486, c10946, c10938, c2926, c10939, c3014, c2791, c4101, c2757, c3684, c10860, c4670, c3687, c2739, c8366, c10947, c10948, c10949, c1031, c6306, c6360] c10950 unsat10950 (by rfl) a
  have h0 : Entails.eval a c10945 := derived10945 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c4637 := h 4636 (by decide)
  have h3 : Entails.eval a c5099 := h 5098 (by decide)
  have h4 : Entails.eval a c3423 := h 3422 (by decide)
  have h5 : Entails.eval a c3387 := h 3386 (by decide)
  have h6 : Entails.eval a c2486 := h 2485 (by decide)
  have h7 : Entails.eval a c10946 := derived10946 a h
  have h8 : Entails.eval a c10938 := derived10938 a h
  have h9 : Entails.eval a c2926 := h 2925 (by decide)
  have h10 : Entails.eval a c10939 := derived10939 a h
  have h11 : Entails.eval a c3014 := h 3013 (by decide)
  have h12 : Entails.eval a c2791 := h 2790 (by decide)
  have h13 : Entails.eval a c4101 := h 4100 (by decide)
  have h14 : Entails.eval a c2757 := h 2756 (by decide)
  have h15 : Entails.eval a c3684 := h 3683 (by decide)
  have h16 : Entails.eval a c10860 := derived10860 a h
  have h17 : Entails.eval a c4670 := h 4669 (by decide)
  have h18 : Entails.eval a c3687 := h 3686 (by decide)
  have h19 : Entails.eval a c2739 := h 2738 (by decide)
  have h20 : Entails.eval a c8366 := derived8366 a h
  have h21 : Entails.eval a c10947 := derived10947 a h
  have h22 : Entails.eval a c10948 := derived10948 a h
  have h23 : Entails.eval a c10949 := derived10949 a h
  have h24 : Entails.eval a c1031 := h 1030 (by decide)
  have h25 : Entails.eval a c6306 := h 6305 (by decide)
  have h26 : Entails.eval a c6360 := h 6359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived10950

end CochromaticTwenty.Certificates.FixedCore0
