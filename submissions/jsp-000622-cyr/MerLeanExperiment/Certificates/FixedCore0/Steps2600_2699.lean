import MerLeanExperiment.Certificates.FixedCore0.Steps2500_2599

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10151 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨57, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10151 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10150, some c4304, some c1795, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10151 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10151 : lratChecker f10151 p10151 = .success := by decide +kernel
theorem unsat10151 : Unsatisfiable (PosFin 65) f10151 := by
  apply lratCheckerSound f10151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10151
  · intro a ha; simp [p10151] at ha; subst a; trivial
  · exact checked10151
theorem derived10151 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10151 := by
  apply localUnsat_implies_entails f10151 [c9748, c10150, c4304, c1795] c10151 unsat10151 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10150 := derived10150 a h
  have h2 : Entails.eval a c4304 := h 4303 (by decide)
  have h3 : Entails.eval a c1795 := h 1794 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10152 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨61, by decide⟩, false), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10152 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4313, some c4312, some c4299, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10152 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10152 : lratChecker f10152 p10152 = .success := by decide +kernel
theorem unsat10152 : Unsatisfiable (PosFin 65) f10152 := by
  apply lratCheckerSound f10152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10152
  · intro a ha; simp [p10152] at ha; subst a; trivial
  · exact checked10152
theorem derived10152 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10152 := by
  apply localUnsat_implies_entails f10152 [c4313, c4312, c4299] c10152 unsat10152 (by rfl) a
  have h0 : Entails.eval a c4313 := h 4312 (by decide)
  have h1 : Entails.eval a c4312 := h 4311 (by decide)
  have h2 : Entails.eval a c4299 := h 4298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10153 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10153 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10021, some c10113, some c10149, some c4687, some c2255, some c2364, some c5086, some c3205, some c2924, some c9664, some c10151, some c10152, some c1808, some c2954, some c2944, some c4498, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10153 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked10153 : lratChecker f10153 p10153 = .success := by decide +kernel
theorem unsat10153 : Unsatisfiable (PosFin 65) f10153 := by
  apply lratCheckerSound f10153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10153
  · intro a ha; simp [p10153] at ha; subst a; trivial
  · exact checked10153
theorem derived10153 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10153 := by
  apply localUnsat_implies_entails f10153 [c9748, c10021, c10113, c10149, c4687, c2255, c2364, c5086, c3205, c2924, c9664, c10151, c10152, c1808, c2954, c2944, c4498] c10153 unsat10153 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10021 := derived10021 a h
  have h2 : Entails.eval a c10113 := derived10113 a h
  have h3 : Entails.eval a c10149 := derived10149 a h
  have h4 : Entails.eval a c4687 := h 4686 (by decide)
  have h5 : Entails.eval a c2255 := h 2254 (by decide)
  have h6 : Entails.eval a c2364 := h 2363 (by decide)
  have h7 : Entails.eval a c5086 := h 5085 (by decide)
  have h8 : Entails.eval a c3205 := h 3204 (by decide)
  have h9 : Entails.eval a c2924 := h 2923 (by decide)
  have h10 : Entails.eval a c9664 := derived9664 a h
  have h11 : Entails.eval a c10151 := derived10151 a h
  have h12 : Entails.eval a c10152 := derived10152 a h
  have h13 : Entails.eval a c1808 := h 1807 (by decide)
  have h14 : Entails.eval a c2954 := h 2953 (by decide)
  have h15 : Entails.eval a c2944 := h 2943 (by decide)
  have h16 : Entails.eval a c4498 := h 4497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10154 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨55, by decide⟩, true), (⟨57, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10154 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2440, some c2535, some c2557, some c3094, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p10154 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10154 : lratChecker f10154 p10154 = .success := by decide +kernel
theorem unsat10154 : Unsatisfiable (PosFin 65) f10154 := by
  apply lratCheckerSound f10154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10154
  · intro a ha; simp [p10154] at ha; subst a; trivial
  · exact checked10154
theorem derived10154 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10154 := by
  apply localUnsat_implies_entails f10154 [c2440, c2535, c2557, c3094] c10154 unsat10154 (by rfl) a
  have h0 : Entails.eval a c2440 := h 2439 (by decide)
  have h1 : Entails.eval a c2535 := h 2534 (by decide)
  have h2 : Entails.eval a c2557 := h 2556 (by decide)
  have h3 : Entails.eval a c3094 := h 3093 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10155 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨63, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10155 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2432, some c2554, some c2533, some c3090, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10155 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10155 : lratChecker f10155 p10155 = .success := by decide +kernel
theorem unsat10155 : Unsatisfiable (PosFin 65) f10155 := by
  apply lratCheckerSound f10155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10155
  · intro a ha; simp [p10155] at ha; subst a; trivial
  · exact checked10155
theorem derived10155 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10155 := by
  apply localUnsat_implies_entails f10155 [c2432, c2554, c2533, c3090] c10155 unsat10155 (by rfl) a
  have h0 : Entails.eval a c2432 := h 2431 (by decide)
  have h1 : Entails.eval a c2554 := h 2553 (by decide)
  have h2 : Entails.eval a c2533 := h 2532 (by decide)
  have h3 : Entails.eval a c3090 := h 3089 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10156 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨57, by decide⟩, false), (⟨4, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10156 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c1940, some c2003, some c3645, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10156 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10156 : lratChecker f10156 p10156 = .success := by decide +kernel
theorem unsat10156 : Unsatisfiable (PosFin 65) f10156 := by
  apply lratCheckerSound f10156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10156
  · intro a ha; simp [p10156] at ha; subst a; trivial
  · exact checked10156
theorem derived10156 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10156 := by
  apply localUnsat_implies_entails f10156 [c9748, c8269, c1940, c2003, c3645] c10156 unsat10156 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c1940 := h 1939 (by decide)
  have h3 : Entails.eval a c2003 := h 2002 (by decide)
  have h4 : Entails.eval a c3645 := h 3644 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10157 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, true), (⟨57, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10157 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3635, some c3637, some c3658, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10157 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10157 : lratChecker f10157 p10157 = .success := by decide +kernel
theorem unsat10157 : Unsatisfiable (PosFin 65) f10157 := by
  apply lratCheckerSound f10157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10157
  · intro a ha; simp [p10157] at ha; subst a; trivial
  · exact checked10157
theorem derived10157 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10157 := by
  apply localUnsat_implies_entails f10157 [c3635, c3637, c3658] c10157 unsat10157 (by rfl) a
  have h0 : Entails.eval a c3635 := h 3634 (by decide)
  have h1 : Entails.eval a c3637 := h 3636 (by decide)
  have h2 : Entails.eval a c3658 := h 3657 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10158 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨64, by decide⟩, true), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10158 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1959, some c1957, some c1967, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10158 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10158 : lratChecker f10158 p10158 = .success := by decide +kernel
theorem unsat10158 : Unsatisfiable (PosFin 65) f10158 := by
  apply lratCheckerSound f10158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10158
  · intro a ha; simp [p10158] at ha; subst a; trivial
  · exact checked10158
theorem derived10158 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10158 := by
  apply localUnsat_implies_entails f10158 [c9748, c1959, c1957, c1967] c10158 unsat10158 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1959 := h 1958 (by decide)
  have h2 : Entails.eval a c1957 := h 1956 (by decide)
  have h3 : Entails.eval a c1967 := h 1966 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10159 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10159 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10156, some c10158, some c10157, some c2029, some c2010, some c2024, some c2013, some c2794, some c1534, some c2028, some c2016, some c1911, some c2748, some c4633, some c3878, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10159 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked10159 : lratChecker f10159 p10159 = .success := by decide +kernel
theorem unsat10159 : Unsatisfiable (PosFin 65) f10159 := by
  apply lratCheckerSound f10159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10159
  · intro a ha; simp [p10159] at ha; subst a; trivial
  · exact checked10159
theorem derived10159 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10159 := by
  apply localUnsat_implies_entails f10159 [c9748, c10156, c10158, c10157, c2029, c2010, c2024, c2013, c2794, c1534, c2028, c2016, c1911, c2748, c4633, c3878] c10159 unsat10159 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10156 := derived10156 a h
  have h2 : Entails.eval a c10158 := derived10158 a h
  have h3 : Entails.eval a c10157 := derived10157 a h
  have h4 : Entails.eval a c2029 := h 2028 (by decide)
  have h5 : Entails.eval a c2010 := h 2009 (by decide)
  have h6 : Entails.eval a c2024 := h 2023 (by decide)
  have h7 : Entails.eval a c2013 := h 2012 (by decide)
  have h8 : Entails.eval a c2794 := h 2793 (by decide)
  have h9 : Entails.eval a c1534 := h 1533 (by decide)
  have h10 : Entails.eval a c2028 := h 2027 (by decide)
  have h11 : Entails.eval a c2016 := h 2015 (by decide)
  have h12 : Entails.eval a c1911 := h 1910 (by decide)
  have h13 : Entails.eval a c2748 := h 2747 (by decide)
  have h14 : Entails.eval a c4633 := h 4632 (by decide)
  have h15 : Entails.eval a c3878 := h 3877 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10160 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨64, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10160 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10158, some c2029, some c2010, some c2024, some c2013, some c2794, some c1534, some c2028, some c2016, some c1911, some c2748, some c4633, some c3878, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10160 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10160 : lratChecker f10160 p10160 = .success := by decide +kernel
theorem unsat10160 : Unsatisfiable (PosFin 65) f10160 := by
  apply lratCheckerSound f10160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10160
  · intro a ha; simp [p10160] at ha; subst a; trivial
  · exact checked10160
theorem derived10160 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10160 := by
  apply localUnsat_implies_entails f10160 [c9748, c10158, c2029, c2010, c2024, c2013, c2794, c1534, c2028, c2016, c1911, c2748, c4633, c3878] c10160 unsat10160 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10158 := derived10158 a h
  have h2 : Entails.eval a c2029 := h 2028 (by decide)
  have h3 : Entails.eval a c2010 := h 2009 (by decide)
  have h4 : Entails.eval a c2024 := h 2023 (by decide)
  have h5 : Entails.eval a c2013 := h 2012 (by decide)
  have h6 : Entails.eval a c2794 := h 2793 (by decide)
  have h7 : Entails.eval a c1534 := h 1533 (by decide)
  have h8 : Entails.eval a c2028 := h 2027 (by decide)
  have h9 : Entails.eval a c2016 := h 2015 (by decide)
  have h10 : Entails.eval a c1911 := h 1910 (by decide)
  have h11 : Entails.eval a c2748 := h 2747 (by decide)
  have h12 : Entails.eval a c4633 := h 4632 (by decide)
  have h13 : Entails.eval a c3878 := h 3877 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10161 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10161 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3635, some c3658, some c9213, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10161 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10161 : lratChecker f10161 p10161 = .success := by decide +kernel
theorem unsat10161 : Unsatisfiable (PosFin 65) f10161 := by
  apply lratCheckerSound f10161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10161
  · intro a ha; simp [p10161] at ha; subst a; trivial
  · exact checked10161
theorem derived10161 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10161 := by
  apply localUnsat_implies_entails f10161 [c3635, c3658, c9213] c10161 unsat10161 (by rfl) a
  have h0 : Entails.eval a c3635 := h 3634 (by decide)
  have h1 : Entails.eval a c3658 := h 3657 (by decide)
  have h2 : Entails.eval a c9213 := derived9213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10162 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10162 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10158, some c10160, some c10161, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10162 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10162 : lratChecker f10162 p10162 = .success := by decide +kernel
theorem unsat10162 : Unsatisfiable (PosFin 65) f10162 := by
  apply lratCheckerSound f10162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10162
  · intro a ha; simp [p10162] at ha; subst a; trivial
  · exact checked10162
theorem derived10162 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10162 := by
  apply localUnsat_implies_entails f10162 [c10158, c10160, c10161] c10162 unsat10162 (by rfl) a
  have h0 : Entails.eval a c10158 := derived10158 a h
  have h1 : Entails.eval a c10160 := derived10160 a h
  have h2 : Entails.eval a c10161 := derived10161 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10163 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10163 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3634, some c3655, some c3631, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10163 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10163 : lratChecker f10163 p10163 = .success := by decide +kernel
theorem unsat10163 : Unsatisfiable (PosFin 65) f10163 := by
  apply lratCheckerSound f10163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10163
  · intro a ha; simp [p10163] at ha; subst a; trivial
  · exact checked10163
theorem derived10163 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10163 := by
  apply localUnsat_implies_entails f10163 [c3634, c3655, c3631] c10163 unsat10163 (by rfl) a
  have h0 : Entails.eval a c3634 := h 3633 (by decide)
  have h1 : Entails.eval a c3655 := h 3654 (by decide)
  have h2 : Entails.eval a c3631 := h 3630 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10164 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨63, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10164 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1956, some c1950, some c1951, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10164 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10164 : lratChecker f10164 p10164 = .success := by decide +kernel
theorem unsat10164 : Unsatisfiable (PosFin 65) f10164 := by
  apply lratCheckerSound f10164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10164
  · intro a ha; simp [p10164] at ha; subst a; trivial
  · exact checked10164
theorem derived10164 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10164 := by
  apply localUnsat_implies_entails f10164 [c9748, c1956, c1950, c1951] c10164 unsat10164 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1956 := h 1955 (by decide)
  have h2 : Entails.eval a c1950 := h 1949 (by decide)
  have h3 : Entails.eval a c1951 := h 1950 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10165 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨64, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10165 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c7994, some c2002, some c2030, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10165 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10165 : lratChecker f10165 p10165 = .success := by decide +kernel
theorem unsat10165 : Unsatisfiable (PosFin 65) f10165 := by
  apply lratCheckerSound f10165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10165
  · intro a ha; simp [p10165] at ha; subst a; trivial
  · exact checked10165
theorem derived10165 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10165 := by
  apply localUnsat_implies_entails f10165 [c9748, c8269, c7994, c2002, c2030] c10165 unsat10165 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c2002 := h 2001 (by decide)
  have h4 : Entails.eval a c2030 := h 2029 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10166 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨61, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10166 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10159, some c10162, some c7994, some c8269, some c10164, some c10165, some c10163, some c3634, some c8380, some c3667, some c9282, some c2745, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10166 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10166 : lratChecker f10166 p10166 = .success := by decide +kernel
theorem unsat10166 : Unsatisfiable (PosFin 65) f10166 := by
  apply lratCheckerSound f10166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10166
  · intro a ha; simp [p10166] at ha; subst a; trivial
  · exact checked10166
theorem derived10166 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10166 := by
  apply localUnsat_implies_entails f10166 [c10159, c10162, c7994, c8269, c10164, c10165, c10163, c3634, c8380, c3667, c9282, c2745] c10166 unsat10166 (by rfl) a
  have h0 : Entails.eval a c10159 := derived10159 a h
  have h1 : Entails.eval a c10162 := derived10162 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c10164 := derived10164 a h
  have h5 : Entails.eval a c10165 := derived10165 a h
  have h6 : Entails.eval a c10163 := derived10163 a h
  have h7 : Entails.eval a c3634 := h 3633 (by decide)
  have h8 : Entails.eval a c8380 := derived8380 a h
  have h9 : Entails.eval a c3667 := h 3666 (by decide)
  have h10 : Entails.eval a c9282 := derived9282 a h
  have h11 : Entails.eval a c2745 := h 2744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10167 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨8, by decide⟩, false), (⟨63, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10167 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2744, some c2786, some c4495, some c4631, some c2625, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10167 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10167 : lratChecker f10167 p10167 = .success := by decide +kernel
theorem unsat10167 : Unsatisfiable (PosFin 65) f10167 := by
  apply lratCheckerSound f10167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10167
  · intro a ha; simp [p10167] at ha; subst a; trivial
  · exact checked10167
theorem derived10167 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10167 := by
  apply localUnsat_implies_entails f10167 [c2744, c2786, c4495, c4631, c2625] c10167 unsat10167 (by rfl) a
  have h0 : Entails.eval a c2744 := h 2743 (by decide)
  have h1 : Entails.eval a c2786 := h 2785 (by decide)
  have h2 : Entails.eval a c4495 := h 4494 (by decide)
  have h3 : Entails.eval a c4631 := h 4630 (by decide)
  have h4 : Entails.eval a c2625 := h 2624 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10168 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10168 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8300, some c8269, some c7994, some c9185, some c9175, some c9259, some c2630, some c3530, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10168 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10168 : lratChecker f10168 p10168 = .success := by decide +kernel
theorem unsat10168 : Unsatisfiable (PosFin 65) f10168 := by
  apply lratCheckerSound f10168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10168
  · intro a ha; simp [p10168] at ha; subst a; trivial
  · exact checked10168
theorem derived10168 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10168 := by
  apply localUnsat_implies_entails f10168 [c8380, c8300, c8269, c7994, c9185, c9175, c9259, c2630, c3530] c10168 unsat10168 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8300 := derived8300 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c9185 := derived9185 a h
  have h5 : Entails.eval a c9175 := derived9175 a h
  have h6 : Entails.eval a c9259 := derived9259 a h
  have h7 : Entails.eval a c2630 := h 2629 (by decide)
  have h8 : Entails.eval a c3530 := h 3529 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10169 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10169 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c10167, some c10168, some c4963, some c2747, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10169 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10169 : lratChecker f10169 p10169 = .success := by decide +kernel
theorem unsat10169 : Unsatisfiable (PosFin 65) f10169 := by
  apply lratCheckerSound f10169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10169
  · intro a ha; simp [p10169] at ha; subst a; trivial
  · exact checked10169
theorem derived10169 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10169 := by
  apply localUnsat_implies_entails f10169 [c7994, c10167, c10168, c4963, c2747] c10169 unsat10169 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c10167 := derived10167 a h
  have h2 : Entails.eval a c10168 := derived10168 a h
  have h3 : Entails.eval a c4963 := h 4962 (by decide)
  have h4 : Entails.eval a c2747 := h 2746 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10170 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨64, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10170 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c7994, some c1940, some c10164, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10170 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10170 : lratChecker f10170 p10170 = .success := by decide +kernel
theorem unsat10170 : Unsatisfiable (PosFin 65) f10170 := by
  apply lratCheckerSound f10170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10170
  · intro a ha; simp [p10170] at ha; subst a; trivial
  · exact checked10170
theorem derived10170 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10170 := by
  apply localUnsat_implies_entails f10170 [c9748, c8269, c7994, c1940, c10164] c10170 unsat10170 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c1940 := h 1939 (by decide)
  have h4 : Entails.eval a c10164 := derived10164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10171 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10171 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c7994, some c8269, some c10170, some c10167, some c10169, some c2017, some c2003, some c2030, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10171 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10171 : lratChecker f10171 p10171 = .success := by decide +kernel
theorem unsat10171 : Unsatisfiable (PosFin 65) f10171 := by
  apply lratCheckerSound f10171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10171
  · intro a ha; simp [p10171] at ha; subst a; trivial
  · exact checked10171
theorem derived10171 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10171 := by
  apply localUnsat_implies_entails f10171 [c9748, c7994, c8269, c10170, c10167, c10169, c2017, c2003, c2030] c10171 unsat10171 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c10170 := derived10170 a h
  have h4 : Entails.eval a c10167 := derived10167 a h
  have h5 : Entails.eval a c10169 := derived10169 a h
  have h6 : Entails.eval a c2017 := h 2016 (by decide)
  have h7 : Entails.eval a c2003 := h 2002 (by decide)
  have h8 : Entails.eval a c2030 := h 2029 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10172 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10172 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4028, some c4037, some c4050, some c4026, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p10172 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10172 : lratChecker f10172 p10172 = .success := by decide +kernel
theorem unsat10172 : Unsatisfiable (PosFin 65) f10172 := by
  apply lratCheckerSound f10172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10172
  · intro a ha; simp [p10172] at ha; subst a; trivial
  · exact checked10172
theorem derived10172 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10172 := by
  apply localUnsat_implies_entails f10172 [c4028, c4037, c4050, c4026] c10172 unsat10172 (by rfl) a
  have h0 : Entails.eval a c4028 := h 4027 (by decide)
  have h1 : Entails.eval a c4037 := h 4036 (by decide)
  have h2 : Entails.eval a c4050 := h 4049 (by decide)
  have h3 : Entails.eval a c4026 := h 4025 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10173 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨60, by decide⟩, false), (⟨7, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10173 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1531, some c1536, some c1534, some c1530, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10173 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10173 : lratChecker f10173 p10173 = .success := by decide +kernel
theorem unsat10173 : Unsatisfiable (PosFin 65) f10173 := by
  apply lratCheckerSound f10173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10173
  · intro a ha; simp [p10173] at ha; subst a; trivial
  · exact checked10173
theorem derived10173 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10173 := by
  apply localUnsat_implies_entails f10173 [c9748, c1531, c1536, c1534, c1530] c10173 unsat10173 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1531 := h 1530 (by decide)
  have h2 : Entails.eval a c1536 := h 1535 (by decide)
  have h3 : Entails.eval a c1534 := h 1533 (by decide)
  have h4 : Entails.eval a c1530 := h 1529 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10174 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨61, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10174 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10166, some c10171, some c10158, some c10160, some c10172, some c1526, some c10173, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10174 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10174 : lratChecker f10174 p10174 = .success := by decide +kernel
theorem unsat10174 : Unsatisfiable (PosFin 65) f10174 := by
  apply lratCheckerSound f10174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10174
  · intro a ha; simp [p10174] at ha; subst a; trivial
  · exact checked10174
theorem derived10174 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10174 := by
  apply localUnsat_implies_entails f10174 [c9748, c10166, c10171, c10158, c10160, c10172, c1526, c10173] c10174 unsat10174 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10166 := derived10166 a h
  have h2 : Entails.eval a c10171 := derived10171 a h
  have h3 : Entails.eval a c10158 := derived10158 a h
  have h4 : Entails.eval a c10160 := derived10160 a h
  have h5 : Entails.eval a c10172 := derived10172 a h
  have h6 : Entails.eval a c1526 := h 1525 (by decide)
  have h7 : Entails.eval a c10173 := derived10173 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10175 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨60, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10175 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10173, some c10174, some c10158, some c10172, some c2010, some c2705, some c2702, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10175 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10175 : lratChecker f10175 p10175 = .success := by decide +kernel
theorem unsat10175 : Unsatisfiable (PosFin 65) f10175 := by
  apply lratCheckerSound f10175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10175
  · intro a ha; simp [p10175] at ha; subst a; trivial
  · exact checked10175
theorem derived10175 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10175 := by
  apply localUnsat_implies_entails f10175 [c9748, c10173, c10174, c10158, c10172, c2010, c2705, c2702] c10175 unsat10175 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10173 := derived10173 a h
  have h2 : Entails.eval a c10174 := derived10174 a h
  have h3 : Entails.eval a c10158 := derived10158 a h
  have h4 : Entails.eval a c10172 := derived10172 a h
  have h5 : Entails.eval a c2010 := h 2009 (by decide)
  have h6 : Entails.eval a c2705 := h 2704 (by decide)
  have h7 : Entails.eval a c2702 := h 2701 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10176 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨64, by decide⟩, false), (⟨60, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10176 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c7994, some c2023, some c2002, some c2704, some c2706, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10176 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10176 : lratChecker f10176 p10176 = .success := by decide +kernel
theorem unsat10176 : Unsatisfiable (PosFin 65) f10176 := by
  apply lratCheckerSound f10176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10176
  · intro a ha; simp [p10176] at ha; subst a; trivial
  · exact checked10176
theorem derived10176 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10176 := by
  apply localUnsat_implies_entails f10176 [c9748, c8269, c7994, c2023, c2002, c2704, c2706] c10176 unsat10176 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c2023 := h 2022 (by decide)
  have h4 : Entails.eval a c2002 := h 2001 (by decide)
  have h5 : Entails.eval a c2704 := h 2703 (by decide)
  have h6 : Entails.eval a c2706 := h 2705 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10177 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10177 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10174, some c10173, some c10175, some c7994, some c8269, some c10170, some c10176, some c4024, some c4034, some c2470, some c9689, some c4240, some c4044, some c3045, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10177 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10177 : lratChecker f10177 p10177 = .success := by decide +kernel
theorem unsat10177 : Unsatisfiable (PosFin 65) f10177 := by
  apply lratCheckerSound f10177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10177
  · intro a ha; simp [p10177] at ha; subst a; trivial
  · exact checked10177
theorem derived10177 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10177 := by
  apply localUnsat_implies_entails f10177 [c10174, c10173, c10175, c7994, c8269, c10170, c10176, c4024, c4034, c2470, c9689, c4240, c4044, c3045] c10177 unsat10177 (by rfl) a
  have h0 : Entails.eval a c10174 := derived10174 a h
  have h1 : Entails.eval a c10173 := derived10173 a h
  have h2 : Entails.eval a c10175 := derived10175 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c10170 := derived10170 a h
  have h6 : Entails.eval a c10176 := derived10176 a h
  have h7 : Entails.eval a c4024 := h 4023 (by decide)
  have h8 : Entails.eval a c4034 := h 4033 (by decide)
  have h9 : Entails.eval a c2470 := h 2469 (by decide)
  have h10 : Entails.eval a c9689 := derived9689 a h
  have h11 : Entails.eval a c4240 := h 4239 (by decide)
  have h12 : Entails.eval a c4044 := h 4043 (by decide)
  have h13 : Entails.eval a c3045 := h 3044 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10178 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10178 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c3478, some c3044, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10178 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10178 : lratChecker f10178 p10178 = .success := by decide +kernel
theorem unsat10178 : Unsatisfiable (PosFin 65) f10178 := by
  apply lratCheckerSound f10178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10178
  · intro a ha; simp [p10178] at ha; subst a; trivial
  · exact checked10178
theorem derived10178 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10178 := by
  apply localUnsat_implies_entails f10178 [c8269, c3478, c3044] c10178 unsat10178 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c3478 := h 3477 (by decide)
  have h2 : Entails.eval a c3044 := h 3043 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10179 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨64, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10179 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c2470, some c9689, some c3634, some c4947, some c10178, some c2598, some c4240, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10179 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10179 : lratChecker f10179 p10179 = .success := by decide +kernel
theorem unsat10179 : Unsatisfiable (PosFin 65) f10179 := by
  apply lratCheckerSound f10179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10179
  · intro a ha; simp [p10179] at ha; subst a; trivial
  · exact checked10179
theorem derived10179 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10179 := by
  apply localUnsat_implies_entails f10179 [c7994, c2470, c9689, c3634, c4947, c10178, c2598, c4240] c10179 unsat10179 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c2470 := h 2469 (by decide)
  have h2 : Entails.eval a c9689 := derived9689 a h
  have h3 : Entails.eval a c3634 := h 3633 (by decide)
  have h4 : Entails.eval a c4947 := h 4946 (by decide)
  have h5 : Entails.eval a c10178 := derived10178 a h
  have h6 : Entails.eval a c2598 := h 2597 (by decide)
  have h7 : Entails.eval a c4240 := h 4239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10180 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨64, by decide⟩, false), (⟨60, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10180 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4041, some c4048, some c8300, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10180 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10180 : lratChecker f10180 p10180 = .success := by decide +kernel
theorem unsat10180 : Unsatisfiable (PosFin 65) f10180 := by
  apply lratCheckerSound f10180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10180
  · intro a ha; simp [p10180] at ha; subst a; trivial
  · exact checked10180
theorem derived10180 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10180 := by
  apply localUnsat_implies_entails f10180 [c4041, c4048, c8300] c10180 unsat10180 (by rfl) a
  have h0 : Entails.eval a c4041 := h 4040 (by decide)
  have h1 : Entails.eval a c4048 := h 4047 (by decide)
  have h2 : Entails.eval a c8300 := derived8300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10181 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨64, by decide⟩, false), (⟨60, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10181 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10179, some c10180, some c1514, some c2578, some c2602, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10181 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10181 : lratChecker f10181 p10181 = .success := by decide +kernel
theorem unsat10181 : Unsatisfiable (PosFin 65) f10181 := by
  apply lratCheckerSound f10181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10181
  · intro a ha; simp [p10181] at ha; subst a; trivial
  · exact checked10181
theorem derived10181 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10181 := by
  apply localUnsat_implies_entails f10181 [c9748, c10179, c10180, c1514, c2578, c2602] c10181 unsat10181 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10179 := derived10179 a h
  have h2 : Entails.eval a c10180 := derived10180 a h
  have h3 : Entails.eval a c1514 := h 1513 (by decide)
  have h4 : Entails.eval a c2578 := h 2577 (by decide)
  have h5 : Entails.eval a c2602 := h 2601 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10182 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10182 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10177, some c10174, some c7994, some c8269, some c10170, some c10181, some c2003, some c2002, some c2714, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10182 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10182 : lratChecker f10182 p10182 = .success := by decide +kernel
theorem unsat10182 : Unsatisfiable (PosFin 65) f10182 := by
  apply lratCheckerSound f10182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10182
  · intro a ha; simp [p10182] at ha; subst a; trivial
  · exact checked10182
theorem derived10182 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10182 := by
  apply localUnsat_implies_entails f10182 [c9748, c10177, c10174, c7994, c8269, c10170, c10181, c2003, c2002, c2714] c10182 unsat10182 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10177 := derived10177 a h
  have h2 : Entails.eval a c10174 := derived10174 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c10170 := derived10170 a h
  have h6 : Entails.eval a c10181 := derived10181 a h
  have h7 : Entails.eval a c2003 := h 2002 (by decide)
  have h8 : Entails.eval a c2002 := h 2001 (by decide)
  have h9 : Entails.eval a c2714 := h 2713 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10183 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10183 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10174, some c10177, some c10182, some c10158, some c2713, some c2590, some c4050, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10183 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10183 : lratChecker f10183 p10183 = .success := by decide +kernel
theorem unsat10183 : Unsatisfiable (PosFin 65) f10183 := by
  apply lratCheckerSound f10183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10183
  · intro a ha; simp [p10183] at ha; subst a; trivial
  · exact checked10183
theorem derived10183 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10183 := by
  apply localUnsat_implies_entails f10183 [c10174, c10177, c10182, c10158, c2713, c2590, c4050] c10183 unsat10183 (by rfl) a
  have h0 : Entails.eval a c10174 := derived10174 a h
  have h1 : Entails.eval a c10177 := derived10177 a h
  have h2 : Entails.eval a c10182 := derived10182 a h
  have h3 : Entails.eval a c10158 := derived10158 a h
  have h4 : Entails.eval a c2713 := h 2712 (by decide)
  have h5 : Entails.eval a c2590 := h 2589 (by decide)
  have h6 : Entails.eval a c4050 := h 4049 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10184 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10184 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10174, some c10158, some c10175, some c2712, some c4050, some c1526, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10184 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10184 : lratChecker f10184 p10184 = .success := by decide +kernel
theorem unsat10184 : Unsatisfiable (PosFin 65) f10184 := by
  apply lratCheckerSound f10184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10184
  · intro a ha; simp [p10184] at ha; subst a; trivial
  · exact checked10184
theorem derived10184 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10184 := by
  apply localUnsat_implies_entails f10184 [c9748, c10174, c10158, c10175, c2712, c4050, c1526] c10184 unsat10184 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10174 := derived10174 a h
  have h2 : Entails.eval a c10158 := derived10158 a h
  have h3 : Entails.eval a c10175 := derived10175 a h
  have h4 : Entails.eval a c2712 := h 2711 (by decide)
  have h5 : Entails.eval a c4050 := h 4049 (by decide)
  have h6 : Entails.eval a c1526 := h 1525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10185 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨64, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10185 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10180, some c1514, some c2587, some c1524, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10185 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10185 : lratChecker f10185 p10185 = .success := by decide +kernel
theorem unsat10185 : Unsatisfiable (PosFin 65) f10185 := by
  apply lratCheckerSound f10185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10185
  · intro a ha; simp [p10185] at ha; subst a; trivial
  · exact checked10185
theorem derived10185 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10185 := by
  apply localUnsat_implies_entails f10185 [c9748, c10180, c1514, c2587, c1524] c10185 unsat10185 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10180 := derived10180 a h
  have h2 : Entails.eval a c1514 := h 1513 (by decide)
  have h3 : Entails.eval a c2587 := h 2586 (by decide)
  have h4 : Entails.eval a c1524 := h 1523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10186 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10186 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10184, some c10170, some c8269, some c7994, some c10183, some c10174, some c10185, some c10173, some c4024, some c5079, some c3634, some c3518, some c4411, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10186 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10186 : lratChecker f10186 p10186 = .success := by decide +kernel
theorem unsat10186 : Unsatisfiable (PosFin 65) f10186 := by
  apply lratCheckerSound f10186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10186
  · intro a ha; simp [p10186] at ha; subst a; trivial
  · exact checked10186
theorem derived10186 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10186 := by
  apply localUnsat_implies_entails f10186 [c10184, c10170, c8269, c7994, c10183, c10174, c10185, c10173, c4024, c5079, c3634, c3518, c4411] c10186 unsat10186 (by rfl) a
  have h0 : Entails.eval a c10184 := derived10184 a h
  have h1 : Entails.eval a c10170 := derived10170 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c10183 := derived10183 a h
  have h5 : Entails.eval a c10174 := derived10174 a h
  have h6 : Entails.eval a c10185 := derived10185 a h
  have h7 : Entails.eval a c10173 := derived10173 a h
  have h8 : Entails.eval a c4024 := h 4023 (by decide)
  have h9 : Entails.eval a c5079 := h 5078 (by decide)
  have h10 : Entails.eval a c3634 := h 3633 (by decide)
  have h11 : Entails.eval a c3518 := h 3517 (by decide)
  have h12 : Entails.eval a c4411 := h 4410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10187 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10187 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10174, some c10184, some c7994, some c8269, some c10186, some c2003, some c2002, some c2714, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10187 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10187 : lratChecker f10187 p10187 = .success := by decide +kernel
theorem unsat10187 : Unsatisfiable (PosFin 65) f10187 := by
  apply lratCheckerSound f10187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10187
  · intro a ha; simp [p10187] at ha; subst a; trivial
  · exact checked10187
theorem derived10187 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10187 := by
  apply localUnsat_implies_entails f10187 [c9748, c10174, c10184, c7994, c8269, c10186, c2003, c2002, c2714] c10187 unsat10187 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10174 := derived10174 a h
  have h2 : Entails.eval a c10184 := derived10184 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c10186 := derived10186 a h
  have h6 : Entails.eval a c2003 := h 2002 (by decide)
  have h7 : Entails.eval a c2002 := h 2001 (by decide)
  have h8 : Entails.eval a c2714 := h 2713 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10188 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨56, by decide⟩, true), (⟨2, by decide⟩, true), (⟨13, by decide⟩, true), (⟨63, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10188 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2268, some c2522, some c3170, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p10188 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10188 : lratChecker f10188 p10188 = .success := by decide +kernel
theorem unsat10188 : Unsatisfiable (PosFin 65) f10188 := by
  apply lratCheckerSound f10188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10188
  · intro a ha; simp [p10188] at ha; subst a; trivial
  · exact checked10188
theorem derived10188 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10188 := by
  apply localUnsat_implies_entails f10188 [c9748, c2268, c2522, c3170] c10188 unsat10188 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2268 := h 2267 (by decide)
  have h2 : Entails.eval a c2522 := h 2521 (by decide)
  have h3 : Entails.eval a c3170 := h 3169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10189 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨2, by decide⟩, true), (⟨13, by decide⟩, true), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10189 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c7994, some c10188, some c2240, some c3156, some c4677, some c2518, some c2470, some c2509, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10189 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10189 : lratChecker f10189 p10189 = .success := by decide +kernel
theorem unsat10189 : Unsatisfiable (PosFin 65) f10189 := by
  apply lratCheckerSound f10189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10189
  · intro a ha; simp [p10189] at ha; subst a; trivial
  · exact checked10189
theorem derived10189 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10189 := by
  apply localUnsat_implies_entails f10189 [c9748, c8269, c7994, c10188, c2240, c3156, c4677, c2518, c2470, c2509] c10189 unsat10189 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c10188 := derived10188 a h
  have h4 : Entails.eval a c2240 := h 2239 (by decide)
  have h5 : Entails.eval a c3156 := h 3155 (by decide)
  have h6 : Entails.eval a c4677 := h 4676 (by decide)
  have h7 : Entails.eval a c2518 := h 2517 (by decide)
  have h8 : Entails.eval a c2470 := h 2469 (by decide)
  have h9 : Entails.eval a c2509 := h 2508 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10190 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨13, by decide⟩, true), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10190 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c7994, some c10189, some c2239, some c3155, some c2510, some c2512, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10190 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10190 : lratChecker f10190 p10190 = .success := by decide +kernel
theorem unsat10190 : Unsatisfiable (PosFin 65) f10190 := by
  apply lratCheckerSound f10190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10190
  · intro a ha; simp [p10190] at ha; subst a; trivial
  · exact checked10190
theorem derived10190 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10190 := by
  apply localUnsat_implies_entails f10190 [c9748, c8269, c7994, c10189, c2239, c3155, c2510, c2512] c10190 unsat10190 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c10189 := derived10189 a h
  have h4 : Entails.eval a c2239 := h 2238 (by decide)
  have h5 : Entails.eval a c3155 := h 3154 (by decide)
  have h6 : Entails.eval a c2510 := h 2509 (by decide)
  have h7 : Entails.eval a c2512 := h 2511 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10191 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨7, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10191 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4779, some c3133, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10191 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10191 : lratChecker f10191 p10191 = .success := by decide +kernel
theorem unsat10191 : Unsatisfiable (PosFin 65) f10191 := by
  apply lratCheckerSound f10191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10191
  · intro a ha; simp [p10191] at ha; subst a; trivial
  · exact checked10191
theorem derived10191 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10191 := by
  apply localUnsat_implies_entails f10191 [c4779, c3133] c10191 unsat10191 (by rfl) a
  have h0 : Entails.eval a c4779 := h 4778 (by decide)
  have h1 : Entails.eval a c3133 := h 3132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10192 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, true), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10192 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c7994, some c2239, some c3155, some c3341, some c4158, some c1567, some c4338, some c10191, some c3452, some c2817, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10192 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10192 : lratChecker f10192 p10192 = .success := by decide +kernel
theorem unsat10192 : Unsatisfiable (PosFin 65) f10192 := by
  apply lratCheckerSound f10192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10192
  · intro a ha; simp [p10192] at ha; subst a; trivial
  · exact checked10192
theorem derived10192 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10192 := by
  apply localUnsat_implies_entails f10192 [c9748, c8269, c7994, c2239, c3155, c3341, c4158, c1567, c4338, c10191, c3452, c2817] c10192 unsat10192 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c2239 := h 2238 (by decide)
  have h4 : Entails.eval a c3155 := h 3154 (by decide)
  have h5 : Entails.eval a c3341 := h 3340 (by decide)
  have h6 : Entails.eval a c4158 := h 4157 (by decide)
  have h7 : Entails.eval a c1567 := h 1566 (by decide)
  have h8 : Entails.eval a c4338 := h 4337 (by decide)
  have h9 : Entails.eval a c10191 := derived10191 a h
  have h10 : Entails.eval a c3452 := h 3451 (by decide)
  have h11 : Entails.eval a c2817 := h 2816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10193 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨13, by decide⟩, true), (⟨63, by decide⟩, true), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10193 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3452, some c4777, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10193 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10193 : lratChecker f10193 p10193 = .success := by decide +kernel
theorem unsat10193 : Unsatisfiable (PosFin 65) f10193 := by
  apply lratCheckerSound f10193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10193
  · intro a ha; simp [p10193] at ha; subst a; trivial
  · exact checked10193
theorem derived10193 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10193 := by
  apply localUnsat_implies_entails f10193 [c3452, c4777] c10193 unsat10193 (by rfl) a
  have h0 : Entails.eval a c3452 := h 3451 (by decide)
  have h1 : Entails.eval a c4777 := h 4776 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10194 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨3, by decide⟩, true), (⟨56, by decide⟩, true), (⟨2, by decide⟩, false), (⟨13, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10194 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3352, some c3454, some c2819, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10194 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10194 : lratChecker f10194 p10194 = .success := by decide +kernel
theorem unsat10194 : Unsatisfiable (PosFin 65) f10194 := by
  apply lratCheckerSound f10194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10194
  · intro a ha; simp [p10194] at ha; subst a; trivial
  · exact checked10194
theorem derived10194 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10194 := by
  apply localUnsat_implies_entails f10194 [c3352, c3454, c2819] c10194 unsat10194 (by rfl) a
  have h0 : Entails.eval a c3352 := h 3351 (by decide)
  have h1 : Entails.eval a c3454 := h 3453 (by decide)
  have h2 : Entails.eval a c2819 := h 2818 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10195 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨56, by decide⟩, true), (⟨13, by decide⟩, true), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10195 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c10190, some c7994, some c10194, some c8296, some c3452, some c2250, some c4777, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10195 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10195 : lratChecker f10195 p10195 = .success := by decide +kernel
theorem unsat10195 : Unsatisfiable (PosFin 65) f10195 := by
  apply lratCheckerSound f10195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10195
  · intro a ha; simp [p10195] at ha; subst a; trivial
  · exact checked10195
theorem derived10195 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10195 := by
  apply localUnsat_implies_entails f10195 [c9748, c10190, c7994, c10194, c8296, c3452, c2250, c4777] c10195 unsat10195 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c10190 := derived10190 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c10194 := derived10194 a h
  have h4 : Entails.eval a c8296 := derived8296 a h
  have h5 : Entails.eval a c3452 := h 3451 (by decide)
  have h6 : Entails.eval a c2250 := h 2249 (by decide)
  have h7 : Entails.eval a c4777 := h 4776 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10196 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨3, by decide⟩, false), (⟨13, by decide⟩, true), (⟨63, by decide⟩, true), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10196 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2250, some c3160, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10196 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10196 : lratChecker f10196 p10196 = .success := by decide +kernel
theorem unsat10196 : Unsatisfiable (PosFin 65) f10196 := by
  apply lratCheckerSound f10196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10196
  · intro a ha; simp [p10196] at ha; subst a; trivial
  · exact checked10196
theorem derived10196 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10196 := by
  apply localUnsat_implies_entails f10196 [c9748, c2250, c3160] c10196 unsat10196 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2250 := h 2249 (by decide)
  have h2 : Entails.eval a c3160 := h 3159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10197 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨64, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10197 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c7994, some c10187, some c10190, some c10192, some c10195, some c10196, some c8300, some c8380, some c2265, some c3169, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10197 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10197 : lratChecker f10197 p10197 = .success := by decide +kernel
theorem unsat10197 : Unsatisfiable (PosFin 65) f10197 := by
  apply lratCheckerSound f10197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10197
  · intro a ha; simp [p10197] at ha; subst a; trivial
  · exact checked10197
theorem derived10197 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10197 := by
  apply localUnsat_implies_entails f10197 [c9748, c7994, c10187, c10190, c10192, c10195, c10196, c8300, c8380, c2265, c3169] c10197 unsat10197 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c10187 := derived10187 a h
  have h3 : Entails.eval a c10190 := derived10190 a h
  have h4 : Entails.eval a c10192 := derived10192 a h
  have h5 : Entails.eval a c10195 := derived10195 a h
  have h6 : Entails.eval a c10196 := derived10196 a h
  have h7 : Entails.eval a c8300 := derived8300 a h
  have h8 : Entails.eval a c8380 := derived8380 a h
  have h9 : Entails.eval a c2265 := h 2264 (by decide)
  have h10 : Entails.eval a c3169 := h 3168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10198 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨59, by decide⟩, true), (⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10198 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3169, some c3209, some c2372, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10198 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10198 : lratChecker f10198 p10198 = .success := by decide +kernel
theorem unsat10198 : Unsatisfiable (PosFin 65) f10198 := by
  apply lratCheckerSound f10198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10198
  · intro a ha; simp [p10198] at ha; subst a; trivial
  · exact checked10198
theorem derived10198 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10198 := by
  apply localUnsat_implies_entails f10198 [c9748, c3169, c3209, c2372] c10198 unsat10198 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3169 := h 3168 (by decide)
  have h2 : Entails.eval a c3209 := h 3208 (by decide)
  have h3 : Entails.eval a c2372 := h 2371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10199 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10199 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c8300, some c10198, some c3198, some c3155, some c2363, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10199 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10199 : lratChecker f10199 p10199 = .success := by decide +kernel
theorem unsat10199 : Unsatisfiable (PosFin 65) f10199 := by
  apply lratCheckerSound f10199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10199
  · intro a ha; simp [p10199] at ha; subst a; trivial
  · exact checked10199
theorem derived10199 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10199 := by
  apply localUnsat_implies_entails f10199 [c9748, c8269, c8300, c10198, c3198, c3155, c2363] c10199 unsat10199 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8300 := derived8300 a h
  have h3 : Entails.eval a c10198 := derived10198 a h
  have h4 : Entails.eval a c3198 := h 3197 (by decide)
  have h5 : Entails.eval a c3155 := h 3154 (by decide)
  have h6 : Entails.eval a c2363 := h 2362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10200 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨14, by decide⟩, true), (⟨3, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10200 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c3198, some c2354, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p10200 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10200 : lratChecker f10200 p10200 = .success := by decide +kernel
theorem unsat10200 : Unsatisfiable (PosFin 65) f10200 := by
  apply lratCheckerSound f10200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10200
  · intro a ha; simp [p10200] at ha; subst a; trivial
  · exact checked10200
theorem derived10200 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10200 := by
  apply localUnsat_implies_entails f10200 [c9748, c8269, c3198, c2354] c10200 unsat10200 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c3198 := h 3197 (by decide)
  have h3 : Entails.eval a c2354 := h 2353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10201 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true), (⟨52, by decide⟩, true), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10201 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c7994, some c2362, some c2356, some c2355, some c3959, some c4179, some c4181, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10201 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10201 : lratChecker f10201 p10201 = .success := by decide +kernel
theorem unsat10201 : Unsatisfiable (PosFin 65) f10201 := by
  apply lratCheckerSound f10201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10201
  · intro a ha; simp [p10201] at ha; subst a; trivial
  · exact checked10201
theorem derived10201 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10201 := by
  apply localUnsat_implies_entails f10201 [c9748, c8269, c7994, c2362, c2356, c2355, c3959, c4179, c4181] c10201 unsat10201 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c2362 := h 2361 (by decide)
  have h4 : Entails.eval a c2356 := h 2355 (by decide)
  have h5 : Entails.eval a c2355 := h 2354 (by decide)
  have h6 : Entails.eval a c3959 := h 3958 (by decide)
  have h7 : Entails.eval a c4179 := h 4178 (by decide)
  have h8 : Entails.eval a c4181 := h 4180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10202 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10202 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c8269, some c7994, some c10199, some c3160, some c1797, some c4417, some c10200, some c10201, some c3202, some c3192, some c3189, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10202 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10202 : lratChecker f10202 p10202 = .success := by decide +kernel
theorem unsat10202 : Unsatisfiable (PosFin 65) f10202 := by
  apply lratCheckerSound f10202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10202
  · intro a ha; simp [p10202] at ha; subst a; trivial
  · exact checked10202
theorem derived10202 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10202 := by
  apply localUnsat_implies_entails f10202 [c9748, c8269, c7994, c10199, c3160, c1797, c4417, c10200, c10201, c3202, c3192, c3189] c10202 unsat10202 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c10199 := derived10199 a h
  have h4 : Entails.eval a c3160 := h 3159 (by decide)
  have h5 : Entails.eval a c1797 := h 1796 (by decide)
  have h6 : Entails.eval a c4417 := h 4416 (by decide)
  have h7 : Entails.eval a c10200 := derived10200 a h
  have h8 : Entails.eval a c10201 := derived10201 a h
  have h9 : Entails.eval a c3202 := h 3201 (by decide)
  have h10 : Entails.eval a c3192 := h 3191 (by decide)
  have h11 : Entails.eval a c3189 := h 3188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10203 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨63, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10203 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2476, some c3288, some c3383, some c2786, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p10203 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10203 : lratChecker f10203 p10203 = .success := by decide +kernel
theorem unsat10203 : Unsatisfiable (PosFin 65) f10203 := by
  apply lratCheckerSound f10203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10203
  · intro a ha; simp [p10203] at ha; subst a; trivial
  · exact checked10203
theorem derived10203 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10203 := by
  apply localUnsat_implies_entails f10203 [c2476, c3288, c3383, c2786] c10203 unsat10203 (by rfl) a
  have h0 : Entails.eval a c2476 := h 2475 (by decide)
  have h1 : Entails.eval a c3288 := h 3287 (by decide)
  have h2 : Entails.eval a c3383 := h 3382 (by decide)
  have h3 : Entails.eval a c2786 := h 2785 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10204 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨3, by decide⟩, true), (⟨13, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10204 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c10203, some c10089, some c3589, some c5084, some c4305, some c3523, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10204 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10204 : lratChecker f10204 p10204 = .success := by decide +kernel
theorem unsat10204 : Unsatisfiable (PosFin 65) f10204 := by
  apply lratCheckerSound f10204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10204
  · intro a ha; simp [p10204] at ha; subst a; trivial
  · exact checked10204
theorem derived10204 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10204 := by
  apply localUnsat_implies_entails f10204 [c8269, c7994, c10203, c10089, c3589, c5084, c4305, c3523] c10204 unsat10204 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c10203 := derived10203 a h
  have h3 : Entails.eval a c10089 := derived10089 a h
  have h4 : Entails.eval a c3589 := h 3588 (by decide)
  have h5 : Entails.eval a c5084 := h 5083 (by decide)
  have h6 : Entails.eval a c4305 := h 4304 (by decide)
  have h7 : Entails.eval a c3523 := h 3522 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10205 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨35, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10205 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1873, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p10205 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10205 : lratChecker f10205 p10205 = .success := by decide +kernel
theorem unsat10205 : Unsatisfiable (PosFin 65) f10205 := by
  apply lratCheckerSound f10205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10205
  · intro a ha; simp [p10205] at ha; subst a; trivial
  · exact checked10205
theorem derived10205 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10205 := by
  apply localUnsat_implies_entails f10205 [c9748, c1873] c10205 unsat10205 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1873 := h 1872 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10206 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨16, by decide⟩, true), (⟨63, by decide⟩, true), (⟨13, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10206 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2331, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p10206 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10206 : lratChecker f10206 p10206 = .success := by decide +kernel
theorem unsat10206 : Unsatisfiable (PosFin 65) f10206 := by
  apply lratCheckerSound f10206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10206
  · intro a ha; simp [p10206] at ha; subst a; trivial
  · exact checked10206
theorem derived10206 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10206 := by
  apply localUnsat_implies_entails f10206 [c9748, c2331] c10206 unsat10206 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2331 := h 2330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10207 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10207 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1667, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p10207 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10207 : lratChecker f10207 p10207 = .success := by decide +kernel
theorem unsat10207 : Unsatisfiable (PosFin 65) f10207 := by
  apply lratCheckerSound f10207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10207
  · intro a ha; simp [p10207] at ha; subst a; trivial
  · exact checked10207
theorem derived10207 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10207 := by
  apply localUnsat_implies_entails f10207 [c9748, c1667] c10207 unsat10207 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1667 := h 1666 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10208 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨57, by decide⟩, true), (⟨56, by decide⟩, true), (⟨63, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10208 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2338, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10208 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10208 : lratChecker f10208 p10208 = .success := by decide +kernel
theorem unsat10208 : Unsatisfiable (PosFin 65) f10208 := by
  apply lratCheckerSound f10208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10208
  · intro a ha; simp [p10208] at ha; subst a; trivial
  · exact checked10208
theorem derived10208 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10208 := by
  apply localUnsat_implies_entails f10208 [c9748, c2338] c10208 unsat10208 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2338 := h 2337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10209 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨58, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10209 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2333, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10209 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10209 : lratChecker f10209 p10209 = .success := by decide +kernel
theorem unsat10209 : Unsatisfiable (PosFin 65) f10209 := by
  apply lratCheckerSound f10209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10209
  · intro a ha; simp [p10209] at ha; subst a; trivial
  · exact checked10209
theorem derived10209 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10209 := by
  apply localUnsat_implies_entails f10209 [c9748, c2333] c10209 unsat10209 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2333 := h 2332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10210 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨58, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10210 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2258, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10210 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10210 : lratChecker f10210 p10210 = .success := by decide +kernel
theorem unsat10210 : Unsatisfiable (PosFin 65) f10210 := by
  apply lratCheckerSound f10210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10210
  · intro a ha; simp [p10210] at ha; subst a; trivial
  · exact checked10210
theorem derived10210 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10210 := by
  apply localUnsat_implies_entails f10210 [c9748, c2258] c10210 unsat10210 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2258 := h 2257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10211 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨13, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10211 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2014, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10211 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10211 : lratChecker f10211 p10211 = .success := by decide +kernel
theorem unsat10211 : Unsatisfiable (PosFin 65) f10211 := by
  apply lratCheckerSound f10211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10211
  · intro a ha; simp [p10211] at ha; subst a; trivial
  · exact checked10211
theorem derived10211 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10211 := by
  apply localUnsat_implies_entails f10211 [c9748, c2014] c10211 unsat10211 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2014 := h 2013 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10212 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10212 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2015, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p10212 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10212 : lratChecker f10212 p10212 = .success := by decide +kernel
theorem unsat10212 : Unsatisfiable (PosFin 65) f10212 := by
  apply lratCheckerSound f10212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10212
  · intro a ha; simp [p10212] at ha; subst a; trivial
  · exact checked10212
theorem derived10212 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10212 := by
  apply localUnsat_implies_entails f10212 [c9748, c2015] c10212 unsat10212 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2015 := h 2014 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10213 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10213 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1902, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10213 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10213 : lratChecker f10213 p10213 = .success := by decide +kernel
theorem unsat10213 : Unsatisfiable (PosFin 65) f10213 := by
  apply lratCheckerSound f10213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10213
  · intro a ha; simp [p10213] at ha; subst a; trivial
  · exact checked10213
theorem derived10213 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10213 := by
  apply localUnsat_implies_entails f10213 [c9748, c1902] c10213 unsat10213 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1902 := h 1901 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10214 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨6, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10214 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1905, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p10214 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10214 : lratChecker f10214 p10214 = .success := by decide +kernel
theorem unsat10214 : Unsatisfiable (PosFin 65) f10214 := by
  apply lratCheckerSound f10214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10214
  · intro a ha; simp [p10214] at ha; subst a; trivial
  · exact checked10214
theorem derived10214 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10214 := by
  apply localUnsat_implies_entails f10214 [c9748, c1905] c10214 unsat10214 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1905 := h 1904 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10215 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨60, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10215 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2256, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p10215 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10215 : lratChecker f10215 p10215 = .success := by decide +kernel
theorem unsat10215 : Unsatisfiable (PosFin 65) f10215 := by
  apply lratCheckerSound f10215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10215
  · intro a ha; simp [p10215] at ha; subst a; trivial
  · exact checked10215
theorem derived10215 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10215 := by
  apply localUnsat_implies_entails f10215 [c9748, c2256] c10215 unsat10215 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2256 := h 2255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10216 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨36, by decide⟩, false), (⟨42, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10216 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1880, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10216 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10216 : lratChecker f10216 p10216 = .success := by decide +kernel
theorem unsat10216 : Unsatisfiable (PosFin 65) f10216 := by
  apply lratCheckerSound f10216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10216
  · intro a ha; simp [p10216] at ha; subst a; trivial
  · exact checked10216
theorem derived10216 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10216 := by
  apply localUnsat_implies_entails f10216 [c9748, c1880] c10216 unsat10216 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1880 := h 1879 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10217 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨45, by decide⟩, true), (⟨34, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10217 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1874, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10217 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10217 : lratChecker f10217 p10217 = .success := by decide +kernel
theorem unsat10217 : Unsatisfiable (PosFin 65) f10217 := by
  apply lratCheckerSound f10217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10217
  · intro a ha; simp [p10217] at ha; subst a; trivial
  · exact checked10217
theorem derived10217 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10217 := by
  apply localUnsat_implies_entails f10217 [c9748, c1874] c10217 unsat10217 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1874 := h 1873 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10218 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨37, by decide⟩, false), (⟨16, by decide⟩, true), (⟨35, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10218 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1878, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10218 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10218 : lratChecker f10218 p10218 = .success := by decide +kernel
theorem unsat10218 : Unsatisfiable (PosFin 65) f10218 := by
  apply lratCheckerSound f10218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10218
  · intro a ha; simp [p10218] at ha; subst a; trivial
  · exact checked10218
theorem derived10218 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10218 := by
  apply localUnsat_implies_entails f10218 [c9748, c1878] c10218 unsat10218 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1878 := h 1877 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10219 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨15, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10219 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1583, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10219 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10219 : lratChecker f10219 p10219 = .success := by decide +kernel
theorem unsat10219 : Unsatisfiable (PosFin 65) f10219 := by
  apply lratCheckerSound f10219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10219
  · intro a ha; simp [p10219] at ha; subst a; trivial
  · exact checked10219
theorem derived10219 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10219 := by
  apply localUnsat_implies_entails f10219 [c9748, c1583] c10219 unsat10219 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1583 := h 1582 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10220 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10220 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1580, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10220 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10220 : lratChecker f10220 p10220 = .success := by decide +kernel
theorem unsat10220 : Unsatisfiable (PosFin 65) f10220 := by
  apply lratCheckerSound f10220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10220
  · intro a ha; simp [p10220] at ha; subst a; trivial
  · exact checked10220
theorem derived10220 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10220 := by
  apply localUnsat_implies_entails f10220 [c9748, c1580] c10220 unsat10220 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1580 := h 1579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10221 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true), (⟨61, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10221 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1575, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10221 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10221 : lratChecker f10221 p10221 = .success := by decide +kernel
theorem unsat10221 : Unsatisfiable (PosFin 65) f10221 := by
  apply lratCheckerSound f10221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10221
  · intro a ha; simp [p10221] at ha; subst a; trivial
  · exact checked10221
theorem derived10221 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10221 := by
  apply localUnsat_implies_entails f10221 [c9748, c1575] c10221 unsat10221 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1575 := h 1574 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10222 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10222 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1510, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10222 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10222 : lratChecker f10222 p10222 = .success := by decide +kernel
theorem unsat10222 : Unsatisfiable (PosFin 65) f10222 := by
  apply lratCheckerSound f10222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10222
  · intro a ha; simp [p10222] at ha; subst a; trivial
  · exact checked10222
theorem derived10222 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10222 := by
  apply localUnsat_implies_entails f10222 [c9748, c1510] c10222 unsat10222 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1510 := h 1509 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10223 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨51, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10223 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1651, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p10223 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10223 : lratChecker f10223 p10223 = .success := by decide +kernel
theorem unsat10223 : Unsatisfiable (PosFin 65) f10223 := by
  apply lratCheckerSound f10223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10223
  · intro a ha; simp [p10223] at ha; subst a; trivial
  · exact checked10223
theorem derived10223 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10223 := by
  apply localUnsat_implies_entails f10223 [c9748, c1651] c10223 unsat10223 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1651 := h 1650 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10224 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨40, by decide⟩, true), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10224 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1559, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p10224 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10224 : lratChecker f10224 p10224 = .success := by decide +kernel
theorem unsat10224 : Unsatisfiable (PosFin 65) f10224 := by
  apply lratCheckerSound f10224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10224
  · intro a ha; simp [p10224] at ha; subst a; trivial
  · exact checked10224
theorem derived10224 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10224 := by
  apply localUnsat_implies_entails f10224 [c9748, c1559] c10224 unsat10224 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1559 := h 1558 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10225 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10225 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1639, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10225 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10225 : lratChecker f10225 p10225 = .success := by decide +kernel
theorem unsat10225 : Unsatisfiable (PosFin 65) f10225 := by
  apply lratCheckerSound f10225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10225
  · intro a ha; simp [p10225] at ha; subst a; trivial
  · exact checked10225
theorem derived10225 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10225 := by
  apply localUnsat_implies_entails f10225 [c9748, c1639] c10225 unsat10225 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1639 := h 1638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10226 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨5, by decide⟩, true), (⟨59, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10226 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1525, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10226 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10226 : lratChecker f10226 p10226 = .success := by decide +kernel
theorem unsat10226 : Unsatisfiable (PosFin 65) f10226 := by
  apply lratCheckerSound f10226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10226
  · intro a ha; simp [p10226] at ha; subst a; trivial
  · exact checked10226
theorem derived10226 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10226 := by
  apply localUnsat_implies_entails f10226 [c9748, c1525] c10226 unsat10226 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1525 := h 1524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10227 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10227 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1643, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p10227 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10227 : lratChecker f10227 p10227 = .success := by decide +kernel
theorem unsat10227 : Unsatisfiable (PosFin 65) f10227 := by
  apply lratCheckerSound f10227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10227
  · intro a ha; simp [p10227] at ha; subst a; trivial
  · exact checked10227
theorem derived10227 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10227 := by
  apply localUnsat_implies_entails f10227 [c9748, c1643] c10227 unsat10227 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1643 := h 1642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10228 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨63, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10228 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1654, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p10228 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10228 : lratChecker f10228 p10228 = .success := by decide +kernel
theorem unsat10228 : Unsatisfiable (PosFin 65) f10228 := by
  apply lratCheckerSound f10228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10228
  · intro a ha; simp [p10228] at ha; subst a; trivial
  · exact checked10228
theorem derived10228 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10228 := by
  apply localUnsat_implies_entails f10228 [c9748, c1654] c10228 unsat10228 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1654 := h 1653 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10229 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨38, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10229 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1493, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p10229 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10229 : lratChecker f10229 p10229 = .success := by decide +kernel
theorem unsat10229 : Unsatisfiable (PosFin 65) f10229 := by
  apply lratCheckerSound f10229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10229
  · intro a ha; simp [p10229] at ha; subst a; trivial
  · exact checked10229
theorem derived10229 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10229 := by
  apply localUnsat_implies_entails f10229 [c9748, c1493] c10229 unsat10229 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1493 := h 1492 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10230 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨63, by decide⟩, false), (⟨61, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10230 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1527, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10230 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10230 : lratChecker f10230 p10230 = .success := by decide +kernel
theorem unsat10230 : Unsatisfiable (PosFin 65) f10230 := by
  apply lratCheckerSound f10230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10230
  · intro a ha; simp [p10230] at ha; subst a; trivial
  · exact checked10230
theorem derived10230 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10230 := by
  apply localUnsat_implies_entails f10230 [c9748, c1527] c10230 unsat10230 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1527 := h 1526 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10231 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨58, by decide⟩, false), (⟨15, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10231 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1581, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10231 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10231 : lratChecker f10231 p10231 = .success := by decide +kernel
theorem unsat10231 : Unsatisfiable (PosFin 65) f10231 := by
  apply lratCheckerSound f10231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10231
  · intro a ha; simp [p10231] at ha; subst a; trivial
  · exact checked10231
theorem derived10231 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10231 := by
  apply localUnsat_implies_entails f10231 [c9748, c1581] c10231 unsat10231 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1581 := h 1580 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10232 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10232 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1520, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10232 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10232 : lratChecker f10232 p10232 = .success := by decide +kernel
theorem unsat10232 : Unsatisfiable (PosFin 65) f10232 := by
  apply lratCheckerSound f10232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10232
  · intro a ha; simp [p10232] at ha; subst a; trivial
  · exact checked10232
theorem derived10232 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10232 := by
  apply localUnsat_implies_entails f10232 [c9748, c1520] c10232 unsat10232 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1520 := h 1519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10233 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10233 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1526, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10233 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10233 : lratChecker f10233 p10233 = .success := by decide +kernel
theorem unsat10233 : Unsatisfiable (PosFin 65) f10233 := by
  apply lratCheckerSound f10233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10233
  · intro a ha; simp [p10233] at ha; subst a; trivial
  · exact checked10233
theorem derived10233 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10233 := by
  apply localUnsat_implies_entails f10233 [c9748, c1526] c10233 unsat10233 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1526 := h 1525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10234 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10234 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1524, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10234 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10234 : lratChecker f10234 p10234 = .success := by decide +kernel
theorem unsat10234 : Unsatisfiable (PosFin 65) f10234 := by
  apply lratCheckerSound f10234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10234
  · intro a ha; simp [p10234] at ha; subst a; trivial
  · exact checked10234
theorem derived10234 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10234 := by
  apply localUnsat_implies_entails f10234 [c9748, c1524] c10234 unsat10234 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1524 := h 1523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10235 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10235 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1522, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10235 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10235 : lratChecker f10235 p10235 = .success := by decide +kernel
theorem unsat10235 : Unsatisfiable (PosFin 65) f10235 := by
  apply lratCheckerSound f10235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10235
  · intro a ha; simp [p10235] at ha; subst a; trivial
  · exact checked10235
theorem derived10235 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10235 := by
  apply localUnsat_implies_entails f10235 [c9748, c1522] c10235 unsat10235 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1522 := h 1521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10236 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨63, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10236 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1528, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p10236 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10236 : lratChecker f10236 p10236 = .success := by decide +kernel
theorem unsat10236 : Unsatisfiable (PosFin 65) f10236 := by
  apply lratCheckerSound f10236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10236
  · intro a ha; simp [p10236] at ha; subst a; trivial
  · exact checked10236
theorem derived10236 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10236 := by
  apply localUnsat_implies_entails f10236 [c9748, c1528] c10236 unsat10236 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1528 := h 1527 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10237 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨58, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10237 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1503, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p10237 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10237 : lratChecker f10237 p10237 = .success := by decide +kernel
theorem unsat10237 : Unsatisfiable (PosFin 65) f10237 := by
  apply lratCheckerSound f10237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10237
  · intro a ha; simp [p10237] at ha; subst a; trivial
  · exact checked10237
theorem derived10237 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10237 := by
  apply localUnsat_implies_entails f10237 [c9748, c1503] c10237 unsat10237 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1503 := h 1502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10238 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10238 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1501, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10238 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10238 : lratChecker f10238 p10238 = .success := by decide +kernel
theorem unsat10238 : Unsatisfiable (PosFin 65) f10238 := by
  apply lratCheckerSound f10238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10238
  · intro a ha; simp [p10238] at ha; subst a; trivial
  · exact checked10238
theorem derived10238 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10238 := by
  apply localUnsat_implies_entails f10238 [c9748, c1501] c10238 unsat10238 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1501 := h 1500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10239 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨64, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10239 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1502, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10239 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10239 : lratChecker f10239 p10239 = .success := by decide +kernel
theorem unsat10239 : Unsatisfiable (PosFin 65) f10239 := by
  apply lratCheckerSound f10239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10239
  · intro a ha; simp [p10239] at ha; subst a; trivial
  · exact checked10239
theorem derived10239 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10239 := by
  apply localUnsat_implies_entails f10239 [c9748, c1502] c10239 unsat10239 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1502 := h 1501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10240 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10240 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1499, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10240 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10240 : lratChecker f10240 p10240 = .success := by decide +kernel
theorem unsat10240 : Unsatisfiable (PosFin 65) f10240 := by
  apply lratCheckerSound f10240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10240
  · intro a ha; simp [p10240] at ha; subst a; trivial
  · exact checked10240
theorem derived10240 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10240 := by
  apply localUnsat_implies_entails f10240 [c9748, c1499] c10240 unsat10240 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1499 := h 1498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10241 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10241 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1512, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10241 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10241 : lratChecker f10241 p10241 = .success := by decide +kernel
theorem unsat10241 : Unsatisfiable (PosFin 65) f10241 := by
  apply lratCheckerSound f10241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10241
  · intro a ha; simp [p10241] at ha; subst a; trivial
  · exact checked10241
theorem derived10241 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10241 := by
  apply localUnsat_implies_entails f10241 [c9748, c1512] c10241 unsat10241 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1512 := h 1511 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10242 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨46, by decide⟩, false), (⟨35, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10242 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1491, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10242 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10242 : lratChecker f10242 p10242 = .success := by decide +kernel
theorem unsat10242 : Unsatisfiable (PosFin 65) f10242 := by
  apply lratCheckerSound f10242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10242
  · intro a ha; simp [p10242] at ha; subst a; trivial
  · exact checked10242
theorem derived10242 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10242 := by
  apply localUnsat_implies_entails f10242 [c9748, c1491] c10242 unsat10242 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1491 := h 1490 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10243 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨44, by decide⟩, true), (⟨36, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10243 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1492, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10243 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10243 : lratChecker f10243 p10243 = .success := by decide +kernel
theorem unsat10243 : Unsatisfiable (PosFin 65) f10243 := by
  apply lratCheckerSound f10243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10243
  · intro a ha; simp [p10243] at ha; subst a; trivial
  · exact checked10243
theorem derived10243 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10243 := by
  apply localUnsat_implies_entails f10243 [c9748, c1492] c10243 unsat10243 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1492 := h 1491 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10244 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨61, by decide⟩, false), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10244 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1516, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10244 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10244 : lratChecker f10244 p10244 = .success := by decide +kernel
theorem unsat10244 : Unsatisfiable (PosFin 65) f10244 := by
  apply lratCheckerSound f10244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10244
  · intro a ha; simp [p10244] at ha; subst a; trivial
  · exact checked10244
theorem derived10244 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10244 := by
  apply localUnsat_implies_entails f10244 [c9748, c1516] c10244 unsat10244 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1516 := h 1515 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10245 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨60, by decide⟩, true), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10245 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1579, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p10245 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10245 : lratChecker f10245 p10245 = .success := by decide +kernel
theorem unsat10245 : Unsatisfiable (PosFin 65) f10245 := by
  apply lratCheckerSound f10245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10245
  · intro a ha; simp [p10245] at ha; subst a; trivial
  · exact checked10245
theorem derived10245 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10245 := by
  apply localUnsat_implies_entails f10245 [c9748, c1579] c10245 unsat10245 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1579 := h 1578 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10246 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨60, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10246 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1584, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10246 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10246 : lratChecker f10246 p10246 = .success := by decide +kernel
theorem unsat10246 : Unsatisfiable (PosFin 65) f10246 := by
  apply lratCheckerSound f10246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10246
  · intro a ha; simp [p10246] at ha; subst a; trivial
  · exact checked10246
theorem derived10246 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10246 := by
  apply localUnsat_implies_entails f10246 [c9748, c1584] c10246 unsat10246 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1584 := h 1583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10247 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10247 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1582, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10247 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10247 : lratChecker f10247 p10247 = .success := by decide +kernel
theorem unsat10247 : Unsatisfiable (PosFin 65) f10247 := by
  apply lratCheckerSound f10247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10247
  · intro a ha; simp [p10247] at ha; subst a; trivial
  · exact checked10247
theorem derived10247 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10247 := by
  apply localUnsat_implies_entails f10247 [c9748, c1582] c10247 unsat10247 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1582 := h 1581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10248 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨59, by decide⟩, true), (⟨55, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10248 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1586, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10248 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10248 : lratChecker f10248 p10248 = .success := by decide +kernel
theorem unsat10248 : Unsatisfiable (PosFin 65) f10248 := by
  apply lratCheckerSound f10248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10248
  · intro a ha; simp [p10248] at ha; subst a; trivial
  · exact checked10248
theorem derived10248 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10248 := by
  apply localUnsat_implies_entails f10248 [c9748, c1586] c10248 unsat10248 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1586 := h 1585 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10249 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨40, by decide⟩, false), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10249 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1482, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10249 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10249 : lratChecker f10249 p10249 = .success := by decide +kernel
theorem unsat10249 : Unsatisfiable (PosFin 65) f10249 := by
  apply lratCheckerSound f10249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10249
  · intro a ha; simp [p10249] at ha; subst a; trivial
  · exact checked10249
theorem derived10249 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10249 := by
  apply localUnsat_implies_entails f10249 [c9748, c1482] c10249 unsat10249 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1482 := h 1481 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10250 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨61, by decide⟩, false), (⟨60, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10250 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1589, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10250 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10250 : lratChecker f10250 p10250 = .success := by decide +kernel
theorem unsat10250 : Unsatisfiable (PosFin 65) f10250 := by
  apply lratCheckerSound f10250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10250
  · intro a ha; simp [p10250] at ha; subst a; trivial
  · exact checked10250
theorem derived10250 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10250 := by
  apply localUnsat_implies_entails f10250 [c9748, c1589] c10250 unsat10250 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1589 := h 1588 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived10250

end CochromaticTwenty.Certificates.FixedCore0
