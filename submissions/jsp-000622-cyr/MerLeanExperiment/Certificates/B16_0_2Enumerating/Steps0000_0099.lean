import MerLeanExperiment.Certificates.B16_0_2Enumerating.Inputs

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c414 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨45, by decide⟩, true), (⟨44, by decide⟩, true), (⟨46, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c138, some c294, some c193, some c307, some c136, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked414 : lratChecker f414 p414 = .success := by decide +kernel
theorem unsat414 : Unsatisfiable (PosFin 57) f414 := by
  apply lratCheckerSound f414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p414
  · intro a ha; simp [p414] at ha; subst a; trivial
  · exact checked414
theorem derived414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c414 := by
  apply localUnsat_implies_entails f414 [c138, c294, c193, c307, c136] c414 unsat414 (by rfl) a
  have h0 : Entails.eval a c138 := h 137 (by decide)
  have h1 : Entails.eval a c294 := h 293 (by decide)
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c307 := h 306 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c415 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨46, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c414, some c308, some c136, some c192, some c193, some c178, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked415 : lratChecker f415 p415 = .success := by decide +kernel
theorem unsat415 : Unsatisfiable (PosFin 57) f415 := by
  apply lratCheckerSound f415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p415
  · intro a ha; simp [p415] at ha; subst a; trivial
  · exact checked415
theorem derived415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c415 := by
  apply localUnsat_implies_entails f415 [c414, c308, c136, c192, c193, c178] c415 unsat415 (by rfl) a
  have h0 : Entails.eval a c414 := derived414 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c136 := h 135 (by decide)
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c416 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c368, some c354, some c355, some c371, some c369, some c373, some c415, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked416 : lratChecker f416 p416 = .success := by decide +kernel
theorem unsat416 : Unsatisfiable (PosFin 57) f416 := by
  apply lratCheckerSound f416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p416
  · intro a ha; simp [p416] at ha; subst a; trivial
  · exact checked416
theorem derived416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c416 := by
  apply localUnsat_implies_entails f416 [c368, c354, c355, c371, c369, c373, c415] c416 unsat416 (by rfl) a
  have h0 : Entails.eval a c368 := h 367 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c373 := h 372 (by decide)
  have h6 : Entails.eval a c415 := derived415 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c417 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨14, by decide⟩, false), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c195, some c193, some c308, some c310, some c149, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked417 : lratChecker f417 p417 = .success := by decide +kernel
theorem unsat417 : Unsatisfiable (PosFin 57) f417 := by
  apply lratCheckerSound f417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p417
  · intro a ha; simp [p417] at ha; subst a; trivial
  · exact checked417
theorem derived417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c417 := by
  apply localUnsat_implies_entails f417 [c195, c193, c308, c310, c149] c417 unsat417 (by rfl) a
  have h0 : Entails.eval a c195 := h 194 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c308 := h 307 (by decide)
  have h3 : Entails.eval a c310 := h 309 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c418 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c193, some c195, some c417, some c296, some c309, some c311, some c151, some c120, some c194, some c260, some c259, some c128, some c214, some c256, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked418 : lratChecker f418 p418 = .success := by decide +kernel
theorem unsat418 : Unsatisfiable (PosFin 57) f418 := by
  apply lratCheckerSound f418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p418
  · intro a ha; simp [p418] at ha; subst a; trivial
  · exact checked418
theorem derived418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c418 := by
  apply localUnsat_implies_entails f418 [c193, c195, c417, c296, c309, c311, c151, c120, c194, c260, c259, c128, c214, c256] c418 unsat418 (by rfl) a
  have h0 : Entails.eval a c193 := h 192 (by decide)
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c417 := derived417 a h
  have h3 : Entails.eval a c296 := h 295 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c151 := h 150 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c260 := h 259 (by decide)
  have h10 : Entails.eval a c259 := h 258 (by decide)
  have h11 : Entails.eval a c128 := h 127 (by decide)
  have h12 : Entails.eval a c214 := h 213 (by decide)
  have h13 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c419 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c418, some c138, some c180, some c308, some c310, some c196, some c194, some c120, some c151, some c260, some c259, some c309, some c212, some c130, some c256, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked419 : lratChecker f419 p419 = .success := by decide +kernel
theorem unsat419 : Unsatisfiable (PosFin 57) f419 := by
  apply lratCheckerSound f419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p419
  · intro a ha; simp [p419] at ha; subst a; trivial
  · exact checked419
theorem derived419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c419 := by
  apply localUnsat_implies_entails f419 [c418, c138, c180, c308, c310, c196, c194, c120, c151, c260, c259, c309, c212, c130, c256] c419 unsat419 (by rfl) a
  have h0 : Entails.eval a c418 := derived418 a h
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c308 := h 307 (by decide)
  have h4 : Entails.eval a c310 := h 309 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c260 := h 259 (by decide)
  have h10 : Entails.eval a c259 := h 258 (by decide)
  have h11 : Entails.eval a c309 := h 308 (by decide)
  have h12 : Entails.eval a c212 := h 211 (by decide)
  have h13 : Entails.eval a c130 := h 129 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c420 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c379, some c376, some c416, some c419, some c367, some c371, some c354, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked420 : lratChecker f420 p420 = .success := by decide +kernel
theorem unsat420 : Unsatisfiable (PosFin 57) f420 := by
  apply lratCheckerSound f420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p420
  · intro a ha; simp [p420] at ha; subst a; trivial
  · exact checked420
theorem derived420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c420 := by
  apply localUnsat_implies_entails f420 [c381, c379, c376, c416, c419, c367, c371, c354] c420 unsat420 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c416 := derived416 a h
  have h4 : Entails.eval a c419 := derived419 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c421 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c420, some c310, some c140, some c196, some c308, some c258, some c256, some c132, some c213, some c259, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked421 : lratChecker f421 p421 = .success := by decide +kernel
theorem unsat421 : Unsatisfiable (PosFin 57) f421 := by
  apply lratCheckerSound f421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p421
  · intro a ha; simp [p421] at ha; subst a; trivial
  · exact checked421
theorem derived421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c421 := by
  apply localUnsat_implies_entails f421 [c420, c310, c140, c196, c308, c258, c256, c132, c213, c259] c421 unsat421 (by rfl) a
  have h0 : Entails.eval a c420 := derived420 a h
  have h1 : Entails.eval a c310 := h 309 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c258 := h 257 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c213 := h 212 (by decide)
  have h9 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c422 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c420, some c310, some c140, some c196, some c139, some c309, some c421, some c215, some c260, some c259, some c132, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked422 : lratChecker f422 p422 = .success := by decide +kernel
theorem unsat422 : Unsatisfiable (PosFin 57) f422 := by
  apply lratCheckerSound f422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p422
  · intro a ha; simp [p422] at ha; subst a; trivial
  · exact checked422
theorem derived422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c422 := by
  apply localUnsat_implies_entails f422 [c420, c310, c140, c196, c139, c309, c421, c215, c260, c259, c132] c422 unsat422 (by rfl) a
  have h0 : Entails.eval a c420 := derived420 a h
  have h1 : Entails.eval a c310 := h 309 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c421 := derived421 a h
  have h7 : Entails.eval a c215 := h 214 (by decide)
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c259 := h 258 (by decide)
  have h10 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c423 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨30, by decide⟩, true), (⟨14, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c150, some c192, some c194, some c139, some c128, some c311, some c258, some c215, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked423 : lratChecker f423 p423 = .success := by decide +kernel
theorem unsat423 : Unsatisfiable (PosFin 57) f423 := by
  apply lratCheckerSound f423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p423
  · intro a ha; simp [p423] at ha; subst a; trivial
  · exact checked423
theorem derived423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c423 := by
  apply localUnsat_implies_entails f423 [c150, c192, c194, c139, c128, c311, c258, c215] c423 unsat423 (by rfl) a
  have h0 : Entails.eval a c150 := h 149 (by decide)
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c128 := h 127 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c424 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨56, by decide⟩, false), (⟨30, by decide⟩, true), (⟨14, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c423, some c307, some c309, some c116, some c139, some c212, some c192, some c196, some c258, some c131, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked424 : lratChecker f424 p424 = .success := by decide +kernel
theorem unsat424 : Unsatisfiable (PosFin 57) f424 := by
  apply lratCheckerSound f424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p424
  · intro a ha; simp [p424] at ha; subst a; trivial
  · exact checked424
theorem derived424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c424 := by
  apply localUnsat_implies_entails f424 [c423, c307, c309, c116, c139, c212, c192, c196, c258, c131] c424 unsat424 (by rfl) a
  have h0 : Entails.eval a c423 := derived423 a h
  have h1 : Entails.eval a c307 := h 306 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c258 := h 257 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c425 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c422, some c118, some c257, some c259, some c424, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked425 : lratChecker f425 p425 = .success := by decide +kernel
theorem unsat425 : Unsatisfiable (PosFin 57) f425 := by
  apply lratCheckerSound f425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p425
  · intro a ha; simp [p425] at ha; subst a; trivial
  · exact checked425
theorem derived425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c425 := by
  apply localUnsat_implies_entails f425 [c422, c118, c257, c259, c424] c425 unsat425 (by rfl) a
  have h0 : Entails.eval a c422 := derived422 a h
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c257 := h 256 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c424 := derived424 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c426 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c129, some c131, some c256, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked426 : lratChecker f426 p426 = .success := by decide +kernel
theorem unsat426 : Unsatisfiable (PosFin 57) f426 := by
  apply lratCheckerSound f426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p426
  · intro a ha; simp [p426] at ha; subst a; trivial
  · exact checked426
theorem derived426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c426 := by
  apply localUnsat_implies_entails f426 [c129, c131, c256] c426 unsat426 (by rfl) a
  have h0 : Entails.eval a c129 := h 128 (by decide)
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c427 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c420, some c425, some c193, some c195, some c417, some c140, some c311, some c139, some c194, some c426, some c260, some c259, some c216, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked427 : lratChecker f427 p427 = .success := by decide +kernel
theorem unsat427 : Unsatisfiable (PosFin 57) f427 := by
  apply lratCheckerSound f427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p427
  · intro a ha; simp [p427] at ha; subst a; trivial
  · exact checked427
theorem derived427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c427 := by
  apply localUnsat_implies_entails f427 [c420, c425, c193, c195, c417, c140, c311, c139, c194, c426, c260, c259, c216] c427 unsat427 (by rfl) a
  have h0 : Entails.eval a c420 := derived420 a h
  have h1 : Entails.eval a c425 := derived425 a h
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c195 := h 194 (by decide)
  have h4 : Entails.eval a c417 := derived417 a h
  have h5 : Entails.eval a c140 := h 139 (by decide)
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c426 := derived426 a h
  have h10 : Entails.eval a c260 := h 259 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  have h12 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c428 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c427, some c420, some c379, some c376, some c193, some c195, some c417, some c140, some c177, some c311, some c370, some c354, some c366, some c179, some c194, some c148, some c119, some c307, some c260, some c258, some c129, some c214, some c257, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked428 : lratChecker f428 p428 = .success := by decide +kernel
theorem unsat428 : Unsatisfiable (PosFin 57) f428 := by
  apply lratCheckerSound f428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p428
  · intro a ha; simp [p428] at ha; subst a; trivial
  · exact checked428
theorem derived428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c428 := by
  apply localUnsat_implies_entails f428 [c427, c420, c379, c376, c193, c195, c417, c140, c177, c311, c370, c354, c366, c179, c194, c148, c119, c307, c260, c258, c129, c214, c257] c428 unsat428 (by rfl) a
  have h0 : Entails.eval a c427 := derived427 a h
  have h1 : Entails.eval a c420 := derived420 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c195 := h 194 (by decide)
  have h6 : Entails.eval a c417 := derived417 a h
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c177 := h 176 (by decide)
  have h9 : Entails.eval a c311 := h 310 (by decide)
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c366 := h 365 (by decide)
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c148 := h 147 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c307 := h 306 (by decide)
  have h18 : Entails.eval a c260 := h 259 (by decide)
  have h19 : Entails.eval a c258 := h 257 (by decide)
  have h20 : Entails.eval a c129 := h 128 (by decide)
  have h21 : Entails.eval a c214 := h 213 (by decide)
  have h22 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c429 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c152, some c257, some c309, some c311, some c128, some c215, some c258, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked429 : lratChecker f429 p429 = .success := by decide +kernel
theorem unsat429 : Unsatisfiable (PosFin 57) f429 := by
  apply lratCheckerSound f429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p429
  · intro a ha; simp [p429] at ha; subst a; trivial
  · exact checked429
theorem derived429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c429 := by
  apply localUnsat_implies_entails f429 [c118, c152, c257, c309, c311, c128, c215, c258] c429 unsat429 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c257 := h 256 (by decide)
  have h3 : Entails.eval a c309 := h 308 (by decide)
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c128 := h 127 (by decide)
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c430 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨56, by decide⟩, false), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c429, some c308, some c310, some c421, some c148, some c215, some c309, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked430 : lratChecker f430 p430 = .success := by decide +kernel
theorem unsat430 : Unsatisfiable (PosFin 57) f430 := by
  apply lratCheckerSound f430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p430
  · intro a ha; simp [p430] at ha; subst a; trivial
  · exact checked430
theorem derived430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c430 := by
  apply localUnsat_implies_entails f430 [c429, c308, c310, c421, c148, c215, c309] c430 unsat430 (by rfl) a
  have h0 : Entails.eval a c429 := derived429 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c310 := h 309 (by decide)
  have h3 : Entails.eval a c421 := derived421 a h
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c215 := h 214 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c431 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨13, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c308, some c310, some c421, some c213, some c130, some c257, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked431 : lratChecker f431 p431 = .success := by decide +kernel
theorem unsat431 : Unsatisfiable (PosFin 57) f431 := by
  apply lratCheckerSound f431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p431
  · intro a ha; simp [p431] at ha; subst a; trivial
  · exact checked431
theorem derived431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c431 := by
  apply localUnsat_implies_entails f431 [c308, c310, c421, c213, c130, c257] c431 unsat431 (by rfl) a
  have h0 : Entails.eval a c308 := h 307 (by decide)
  have h1 : Entails.eval a c310 := h 309 (by decide)
  have h2 : Entails.eval a c421 := derived421 a h
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c432 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c430, some c192, some c431, some c152, some c150, some c309, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked432 : lratChecker f432 p432 = .success := by decide +kernel
theorem unsat432 : Unsatisfiable (PosFin 57) f432 := by
  apply lratCheckerSound f432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p432
  · intro a ha; simp [p432] at ha; subst a; trivial
  · exact checked432
theorem derived432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c432 := by
  apply localUnsat_implies_entails f432 [c430, c192, c431, c152, c150, c309] c432 unsat432 (by rfl) a
  have h0 : Entails.eval a c430 := derived430 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c431 := derived431 a h
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c150 := h 149 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c433 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c373, some c355, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked433 : lratChecker f433 p433 = .success := by decide +kernel
theorem unsat433 : Unsatisfiable (PosFin 57) f433 := by
  apply lratCheckerSound f433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p433
  · intro a ha; simp [p433] at ha; subst a; trivial
  · exact checked433
theorem derived433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c433 := by
  apply localUnsat_implies_entails f433 [c366, c373, c355] c433 unsat433 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c434 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c381, some c427, some c433, some c420, some c179, some c137, some c196, some c309, some c432, some c119, some c260, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked434 : lratChecker f434 p434 = .success := by decide +kernel
theorem unsat434 : Unsatisfiable (PosFin 57) f434 := by
  apply lratCheckerSound f434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p434
  · intro a ha; simp [p434] at ha; subst a; trivial
  · exact checked434
theorem derived434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c434 := by
  apply localUnsat_implies_entails f434 [c376, c381, c427, c433, c420, c179, c137, c196, c309, c432, c119, c260] c434 unsat434 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c427 := derived427 a h
  have h3 : Entails.eval a c433 := derived433 a h
  have h4 : Entails.eval a c420 := derived420 a h
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c137 := h 136 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c432 := derived432 a h
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c435 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c432, some c260, some c259, some c132, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked435 : lratChecker f435 p435 = .success := by decide +kernel
theorem unsat435 : Unsatisfiable (PosFin 57) f435 := by
  apply lratCheckerSound f435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p435
  · intro a ha; simp [p435] at ha; subst a; trivial
  · exact checked435
theorem derived435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c435 := by
  apply localUnsat_implies_entails f435 [c432, c260, c259, c132] c435 unsat435 (by rfl) a
  have h0 : Entails.eval a c432 := derived432 a h
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c259 := h 258 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c436 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c434, some c194, some c435, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked436 : lratChecker f436 p436 = .success := by decide +kernel
theorem unsat436 : Unsatisfiable (PosFin 57) f436 := by
  apply lratCheckerSound f436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p436
  · intro a ha; simp [p436] at ha; subst a; trivial
  · exact checked436
theorem derived436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c436 := by
  apply localUnsat_implies_entails f436 [c434, c194, c435] c436 unsat436 (by rfl) a
  have h0 : Entails.eval a c434 := derived434 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c435 := derived435 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c437 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c376, some c420, some c427, some c433, some c436, some c193, some c195, some c417, some c428, some c140, some c179, some c294, some c311, some c194, some c307, some c148, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked437 : lratChecker f437 p437 = .success := by decide +kernel
theorem unsat437 : Unsatisfiable (PosFin 57) f437 := by
  apply lratCheckerSound f437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p437
  · intro a ha; simp [p437] at ha; subst a; trivial
  · exact checked437
theorem derived437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c437 := by
  apply localUnsat_implies_entails f437 [c381, c376, c420, c427, c433, c436, c193, c195, c417, c428, c140, c179, c294, c311, c194, c307, c148] c437 unsat437 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c420 := derived420 a h
  have h3 : Entails.eval a c427 := derived427 a h
  have h4 : Entails.eval a c433 := derived433 a h
  have h5 : Entails.eval a c436 := derived436 a h
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c417 := derived417 a h
  have h9 : Entails.eval a c428 := derived428 a h
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c179 := h 178 (by decide)
  have h12 : Entails.eval a c294 := h 293 (by decide)
  have h13 : Entails.eval a c311 := h 310 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c307 := h 306 (by decide)
  have h16 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c438 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c94, some c95, some c108, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked438 : lratChecker f438 p438 = .success := by decide +kernel
theorem unsat438 : Unsatisfiable (PosFin 57) f438 := by
  apply lratCheckerSound f438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p438
  · intro a ha; simp [p438] at ha; subst a; trivial
  · exact checked438
theorem derived438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c438 := by
  apply localUnsat_implies_entails f438 [c93, c94, c95, c108] c438 unsat438 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c94 := h 93 (by decide)
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c439 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c108, some c38, some c32, some c13, some c265, some c201, some c129, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked439 : lratChecker f439 p439 = .success := by decide +kernel
theorem unsat439 : Unsatisfiable (PosFin 57) f439 := by
  apply lratCheckerSound f439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p439
  · intro a ha; simp [p439] at ha; subst a; trivial
  · exact checked439
theorem derived439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c439 := by
  apply localUnsat_implies_entails f439 [c111, c108, c38, c32, c13, c265, c201, c129] c439 unsat439 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c440 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨35, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨48, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c58, some c13, some c159, some c157, some c76, some c175, some c329, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked440 : lratChecker f440 p440 = .success := by decide +kernel
theorem unsat440 : Unsatisfiable (PosFin 57) f440 := by
  apply lratCheckerSound f440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p440
  · intro a ha; simp [p440] at ha; subst a; trivial
  · exact checked440
theorem derived440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c440 := by
  apply localUnsat_implies_entails f440 [c58, c13, c159, c157, c76, c175, c329] c440 unsat440 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c441 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨31, by decide⟩, true), (⟨48, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c139, some c433, some c119, some c140, some c439, some c59, some c440, some c48, some c145, some c201, some c177, some c148, some c129, some c82, some c354, some c288, some c231, some c318, some c206, some c205, some c264, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked441 : lratChecker f441 p441 = .success := by decide +kernel
theorem unsat441 : Unsatisfiable (PosFin 57) f441 := by
  apply lratCheckerSound f441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p441
  · intro a ha; simp [p441] at ha; subst a; trivial
  · exact checked441
theorem derived441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c441 := by
  apply localUnsat_implies_entails f441 [c8, c139, c433, c119, c140, c439, c59, c440, c48, c145, c201, c177, c148, c129, c82, c354, c288, c231, c318, c206, c205, c264] c441 unsat441 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c433 := derived433 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c439 := derived439 a h
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c440 := derived440 a h
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c177 := h 176 (by decide)
  have h12 : Entails.eval a c148 := h 147 (by decide)
  have h13 : Entails.eval a c129 := h 128 (by decide)
  have h14 : Entails.eval a c82 := h 81 (by decide)
  have h15 : Entails.eval a c354 := h 353 (by decide)
  have h16 : Entails.eval a c288 := h 287 (by decide)
  have h17 : Entails.eval a c231 := h 230 (by decide)
  have h18 : Entails.eval a c318 := h 317 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c205 := h 204 (by decide)
  have h21 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c442 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c376, some c140, some c311, some c119, some c260, some c258, some c8, some c107, some c44, some c106, some c441, some c16, some c201, some c145, some c13, some c48, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked442 : lratChecker f442 p442 = .success := by decide +kernel
theorem unsat442 : Unsatisfiable (PosFin 57) f442 := by
  apply lratCheckerSound f442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p442
  · intro a ha; simp [p442] at ha; subst a; trivial
  · exact checked442
theorem derived442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c442 := by
  apply localUnsat_implies_entails f442 [c381, c376, c140, c311, c119, c260, c258, c8, c107, c44, c106, c441, c16, c201, c145, c13, c48] c442 unsat442 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c441 := derived441 a h
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c443 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c355, some c356, some c369, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked443 : lratChecker f443 p443 = .success := by decide +kernel
theorem unsat443 : Unsatisfiable (PosFin 57) f443 := by
  apply lratCheckerSound f443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p443
  · intro a ha; simp [p443] at ha; subst a; trivial
  · exact checked443
theorem derived443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c443 := by
  apply localUnsat_implies_entails f443 [c354, c355, c356, c369] c443 unsat443 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c444 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨24, by decide⟩, false), (⟨47, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c236, some c205, some c125, some c201, some c149, some c176, some c316, some c315, some c369, some c290, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked444 : lratChecker f444 p444 = .success := by decide +kernel
theorem unsat444 : Unsatisfiable (PosFin 57) f444 := by
  apply lratCheckerSound f444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p444
  · intro a ha; simp [p444] at ha; subst a; trivial
  · exact checked444
theorem derived444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c444 := by
  apply localUnsat_implies_entails f444 [c236, c205, c125, c201, c149, c176, c316, c315, c369, c290] c444 unsat444 (by rfl) a
  have h0 : Entails.eval a c236 := h 235 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c445 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨43, by decide⟩, true), (⟨28, by decide⟩, false), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c315, some c290, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked445 : lratChecker f445 p445 = .success := by decide +kernel
theorem unsat445 : Unsatisfiable (PosFin 57) f445 := by
  apply lratCheckerSound f445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p445
  · intro a ha; simp [p445] at ha; subst a; trivial
  · exact checked445
theorem derived445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c445 := by
  apply localUnsat_implies_entails f445 [c316, c315, c290] c445 unsat445 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c446 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c214, some c38, some c53, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked446 : lratChecker f446 p446 = .success := by decide +kernel
theorem unsat446 : Unsatisfiable (PosFin 57) f446 := by
  apply lratCheckerSound f446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p446
  · intro a ha; simp [p446] at ha; subst a; trivial
  · exact checked446
theorem derived446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c446 := by
  apply localUnsat_implies_entails f446 [c214, c38, c53] c446 unsat446 (by rfl) a
  have h0 : Entails.eval a c214 := h 213 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c447 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c195, some c376, some c379, some c381, some c437, some c443, some c438, some c442, some c367, some c368, some c80, some c139, some c8, some c309, some c311, some c260, some c259, some c232, some c7, some c43, some c105, some c444, some c173, some c201, some c149, some c176, some c17, some c128, some c446, some c240, some c294, some c288, some c316, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked447 : lratChecker f447 p447 = .success := by decide +kernel
theorem unsat447 : Unsatisfiable (PosFin 57) f447 := by
  apply lratCheckerSound f447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p447
  · intro a ha; simp [p447] at ha; subst a; trivial
  · exact checked447
theorem derived447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c447 := by
  apply localUnsat_implies_entails f447 [c195, c376, c379, c381, c437, c443, c438, c442, c367, c368, c80, c139, c8, c309, c311, c260, c259, c232, c7, c43, c105, c444, c173, c201, c149, c176, c17, c128, c446, c240, c294, c288, c316] c447 unsat447 (by rfl) a
  have h0 : Entails.eval a c195 := h 194 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  have h4 : Entails.eval a c437 := derived437 a h
  have h5 : Entails.eval a c443 := derived443 a h
  have h6 : Entails.eval a c438 := derived438 a h
  have h7 : Entails.eval a c442 := derived442 a h
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c368 := h 367 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c309 := h 308 (by decide)
  have h14 : Entails.eval a c311 := h 310 (by decide)
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c259 := h 258 (by decide)
  have h17 : Entails.eval a c232 := h 231 (by decide)
  have h18 : Entails.eval a c7 := h 6 (by decide)
  have h19 : Entails.eval a c43 := h 42 (by decide)
  have h20 : Entails.eval a c105 := h 104 (by decide)
  have h21 : Entails.eval a c444 := derived444 a h
  have h22 : Entails.eval a c173 := h 172 (by decide)
  have h23 : Entails.eval a c201 := h 200 (by decide)
  have h24 : Entails.eval a c149 := h 148 (by decide)
  have h25 : Entails.eval a c176 := h 175 (by decide)
  have h26 : Entails.eval a c17 := h 16 (by decide)
  have h27 : Entails.eval a c128 := h 127 (by decide)
  have h28 : Entails.eval a c446 := derived446 a h
  have h29 : Entails.eval a c240 := h 239 (by decide)
  have h30 : Entails.eval a c294 := h 293 (by decide)
  have h31 : Entails.eval a c288 := h 287 (by decide)
  have h32 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c448 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c151, some c149, some c80, some c19, some c17, some c52, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked448 : lratChecker f448 p448 = .success := by decide +kernel
theorem unsat448 : Unsatisfiable (PosFin 57) f448 := by
  apply lratCheckerSound f448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p448
  · intro a ha; simp [p448] at ha; subst a; trivial
  · exact checked448
theorem derived448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c448 := by
  apply localUnsat_implies_entails f448 [c140, c151, c149, c80, c19, c17, c52] c448 unsat448 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c149 := h 148 (by decide)
  have h3 : Entails.eval a c80 := h 79 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c449 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c379, some c381, some c437, some c438, some c443, some c195, some c447, some c194, some c448, some c311, some c310, some c179, some c177, some c77, some c5, some c258, some c240, some c216, some c129, some c259, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked449 : lratChecker f449 p449 = .success := by decide +kernel
theorem unsat449 : Unsatisfiable (PosFin 57) f449 := by
  apply lratCheckerSound f449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p449
  · intro a ha; simp [p449] at ha; subst a; trivial
  · exact checked449
theorem derived449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c449 := by
  apply localUnsat_implies_entails f449 [c376, c379, c381, c437, c438, c443, c195, c447, c194, c448, c311, c310, c179, c177, c77, c5, c258, c240, c216, c129, c259] c449 unsat449 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c438 := derived438 a h
  have h5 : Entails.eval a c443 := derived443 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c447 := derived447 a h
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c448 := derived448 a h
  have h10 : Entails.eval a c311 := h 310 (by decide)
  have h11 : Entails.eval a c310 := h 309 (by decide)
  have h12 : Entails.eval a c179 := h 178 (by decide)
  have h13 : Entails.eval a c177 := h 176 (by decide)
  have h14 : Entails.eval a c77 := h 76 (by decide)
  have h15 : Entails.eval a c5 := h 4 (by decide)
  have h16 : Entails.eval a c258 := h 257 (by decide)
  have h17 : Entails.eval a c240 := h 239 (by decide)
  have h18 : Entails.eval a c216 := h 215 (by decide)
  have h19 : Entails.eval a c129 := h 128 (by decide)
  have h20 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c450 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c447, some c194, some c195, some c376, some c379, some c381, some c437, some c443, some c438, some c448, some c310, some c311, some c449, some c367, some c368, some c296, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked450 : lratChecker f450 p450 = .success := by decide +kernel
theorem unsat450 : Unsatisfiable (PosFin 57) f450 := by
  apply lratCheckerSound f450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p450
  · intro a ha; simp [p450] at ha; subst a; trivial
  · exact checked450
theorem derived450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c450 := by
  apply localUnsat_implies_entails f450 [c447, c194, c195, c376, c379, c381, c437, c443, c438, c448, c310, c311, c449, c367, c368, c296] c450 unsat450 (by rfl) a
  have h0 : Entails.eval a c447 := derived447 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c195 := h 194 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c381 := h 380 (by decide)
  have h6 : Entails.eval a c437 := derived437 a h
  have h7 : Entails.eval a c443 := derived443 a h
  have h8 : Entails.eval a c438 := derived438 a h
  have h9 : Entails.eval a c448 := derived448 a h
  have h10 : Entails.eval a c310 := h 309 (by decide)
  have h11 : Entails.eval a c311 := h 310 (by decide)
  have h12 : Entails.eval a c449 := derived449 a h
  have h13 : Entails.eval a c367 := h 366 (by decide)
  have h14 : Entails.eval a c368 := h 367 (by decide)
  have h15 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c451 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c450, some c201, some c447, some c194, some c195, some c376, some c379, some c381, some c437, some c443, some c438, some c367, some c368, some c80, some c19, some c8, some c105, some c77, some c260, some c259, some c232, some c137, some c172, some c40, some c309, some c41, some c236, some c296, some c205, some c33, some c47, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked451 : lratChecker f451 p451 = .success := by decide +kernel
theorem unsat451 : Unsatisfiable (PosFin 57) f451 := by
  apply lratCheckerSound f451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p451
  · intro a ha; simp [p451] at ha; subst a; trivial
  · exact checked451
theorem derived451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c451 := by
  apply localUnsat_implies_entails f451 [c450, c201, c447, c194, c195, c376, c379, c381, c437, c443, c438, c367, c368, c80, c19, c8, c105, c77, c260, c259, c232, c137, c172, c40, c309, c41, c236, c296, c205, c33, c47] c451 unsat451 (by rfl) a
  have h0 : Entails.eval a c450 := derived450 a h
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c447 := derived447 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c195 := h 194 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c437 := derived437 a h
  have h9 : Entails.eval a c443 := derived443 a h
  have h10 : Entails.eval a c438 := derived438 a h
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c77 := h 76 (by decide)
  have h18 : Entails.eval a c260 := h 259 (by decide)
  have h19 : Entails.eval a c259 := h 258 (by decide)
  have h20 : Entails.eval a c232 := h 231 (by decide)
  have h21 : Entails.eval a c137 := h 136 (by decide)
  have h22 : Entails.eval a c172 := h 171 (by decide)
  have h23 : Entails.eval a c40 := h 39 (by decide)
  have h24 : Entails.eval a c309 := h 308 (by decide)
  have h25 : Entails.eval a c41 := h 40 (by decide)
  have h26 : Entails.eval a c236 := h 235 (by decide)
  have h27 : Entails.eval a c296 := h 295 (by decide)
  have h28 : Entails.eval a c205 := h 204 (by decide)
  have h29 : Entails.eval a c33 := h 32 (by decide)
  have h30 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c452 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c379, some c381, some c437, some c443, some c438, some c195, some c447, some c194, some c450, some c201, some c451, some c140, some c179, some c310, some c311, some c366, some c77, some c296, some c5, some c19, some c12, some c78, some c258, some c107, some c48, some c40, some c289, some c209, some c235, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked452 : lratChecker f452 p452 = .success := by decide +kernel
theorem unsat452 : Unsatisfiable (PosFin 57) f452 := by
  apply lratCheckerSound f452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p452
  · intro a ha; simp [p452] at ha; subst a; trivial
  · exact checked452
theorem derived452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c452 := by
  apply localUnsat_implies_entails f452 [c376, c379, c381, c437, c443, c438, c195, c447, c194, c450, c201, c451, c140, c179, c310, c311, c366, c77, c296, c5, c19, c12, c78, c258, c107, c48, c40, c289, c209, c235] c452 unsat452 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c443 := derived443 a h
  have h5 : Entails.eval a c438 := derived438 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c447 := derived447 a h
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c450 := derived450 a h
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c451 := derived451 a h
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c311 := h 310 (by decide)
  have h16 : Entails.eval a c366 := h 365 (by decide)
  have h17 : Entails.eval a c77 := h 76 (by decide)
  have h18 : Entails.eval a c296 := h 295 (by decide)
  have h19 : Entails.eval a c5 := h 4 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c12 := h 11 (by decide)
  have h22 : Entails.eval a c78 := h 77 (by decide)
  have h23 : Entails.eval a c258 := h 257 (by decide)
  have h24 : Entails.eval a c107 := h 106 (by decide)
  have h25 : Entails.eval a c48 := h 47 (by decide)
  have h26 : Entails.eval a c40 := h 39 (by decide)
  have h27 : Entails.eval a c289 := h 288 (by decide)
  have h28 : Entails.eval a c209 := h 208 (by decide)
  have h29 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c453 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c179, some c310, some c77, some c138, some c18, some c78, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked453 : lratChecker f453 p453 = .success := by decide +kernel
theorem unsat453 : Unsatisfiable (PosFin 57) f453 := by
  apply lratCheckerSound f453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p453
  · intro a ha; simp [p453] at ha; subst a; trivial
  · exact checked453
theorem derived453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c453 := by
  apply localUnsat_implies_entails f453 [c140, c179, c310, c77, c138, c18, c78] c453 unsat453 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c310 := h 309 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c454 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨14, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c453, some c367, some c80, some c178, some c19, some c77, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked454 : lratChecker f454 p454 = .success := by decide +kernel
theorem unsat454 : Unsatisfiable (PosFin 57) f454 := by
  apply lratCheckerSound f454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p454
  · intro a ha; simp [p454] at ha; subst a; trivial
  · exact checked454
theorem derived454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c454 := by
  apply localUnsat_implies_entails f454 [c453, c367, c80, c178, c19, c77] c454 unsat454 (by rfl) a
  have h0 : Entails.eval a c453 := derived453 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c455 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c368, some c180, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked455 : lratChecker f455 p455 = .success := by decide +kernel
theorem unsat455 : Unsatisfiable (PosFin 57) f455 := by
  apply lratCheckerSound f455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p455
  · intro a ha; simp [p455] at ha; subst a; trivial
  · exact checked455
theorem derived455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c455 := by
  apply localUnsat_implies_entails f455 [c367, c368, c180] c455 unsat455 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c456 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c452, some c376, some c379, some c381, some c437, some c443, some c438, some c454, some c194, some c455, some c140, some c310, some c311, some c152, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked456 : lratChecker f456 p456 = .success := by decide +kernel
theorem unsat456 : Unsatisfiable (PosFin 57) f456 := by
  apply lratCheckerSound f456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p456
  · intro a ha; simp [p456] at ha; subst a; trivial
  · exact checked456
theorem derived456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c456 := by
  apply localUnsat_implies_entails f456 [c452, c376, c379, c381, c437, c443, c438, c454, c194, c455, c140, c310, c311, c152] c456 unsat456 (by rfl) a
  have h0 : Entails.eval a c452 := derived452 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  have h4 : Entails.eval a c437 := derived437 a h
  have h5 : Entails.eval a c443 := derived443 a h
  have h6 : Entails.eval a c438 := derived438 a h
  have h7 : Entails.eval a c454 := derived454 a h
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c455 := derived455 a h
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c310 := h 309 (by decide)
  have h12 : Entails.eval a c311 := h 310 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c457 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c334, some c335, some c336, some c349, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked457 : lratChecker f457 p457 = .success := by decide +kernel
theorem unsat457 : Unsatisfiable (PosFin 57) f457 := by
  apply lratCheckerSound f457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p457
  · intro a ha; simp [p457] at ha; subst a; trivial
  · exact checked457
theorem derived457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c457 := by
  apply localUnsat_implies_entails f457 [c334, c335, c336, c349] c457 unsat457 (by rfl) a
  have h0 : Entails.eval a c334 := h 333 (by decide)
  have h1 : Entails.eval a c335 := h 334 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  have h3 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c458 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c138, some c118, some c152, some c78, some c230, some c20, some c113, some c43, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked458 : lratChecker f458 p458 = .success := by decide +kernel
theorem unsat458 : Unsatisfiable (PosFin 57) f458 := by
  apply lratCheckerSound f458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p458
  · intro a ha; simp [p458] at ha; subst a; trivial
  · exact checked458
theorem derived458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c458 := by
  apply localUnsat_implies_entails f458 [c138, c118, c152, c78, c230, c20, c113, c43] c458 unsat458 (by rfl) a
  have h0 : Entails.eval a c138 := h 137 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c230 := h 229 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c459 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨38, by decide⟩, true), (⟨33, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c77, some c320, some c180, some c74, some c78, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked459 : lratChecker f459 p459 = .success := by decide +kernel
theorem unsat459 : Unsatisfiable (PosFin 57) f459 := by
  apply lratCheckerSound f459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p459
  · intro a ha; simp [p459] at ha; subst a; trivial
  · exact checked459
theorem derived459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c459 := by
  apply localUnsat_implies_entails f459 [c366, c77, c320, c180, c74, c78] c459 unsat459 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c460 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c379, some c381, some c437, some c457, some c443, some c452, some c456, some c196, some c455, some c438, some c156, some c347, some c458, some c310, some c459, some c295, some c309, some c119, some c139, some c231, some c79, some c113, some c20, some c42, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked460 : lratChecker f460 p460 = .success := by decide +kernel
theorem unsat460 : Unsatisfiable (PosFin 57) f460 := by
  apply lratCheckerSound f460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p460
  · intro a ha; simp [p460] at ha; subst a; trivial
  · exact checked460
theorem derived460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c460 := by
  apply localUnsat_implies_entails f460 [c376, c379, c381, c437, c457, c443, c452, c456, c196, c455, c438, c156, c347, c458, c310, c459, c295, c309, c119, c139, c231, c79, c113, c20, c42] c460 unsat460 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c457 := derived457 a h
  have h5 : Entails.eval a c443 := derived443 a h
  have h6 : Entails.eval a c452 := derived452 a h
  have h7 : Entails.eval a c456 := derived456 a h
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c455 := derived455 a h
  have h10 : Entails.eval a c438 := derived438 a h
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c347 := h 346 (by decide)
  have h13 : Entails.eval a c458 := derived458 a h
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c459 := derived459 a h
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c309 := h 308 (by decide)
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c139 := h 138 (by decide)
  have h20 : Entails.eval a c231 := h 230 (by decide)
  have h21 : Entails.eval a c79 := h 78 (by decide)
  have h22 : Entails.eval a c113 := h 112 (by decide)
  have h23 : Entails.eval a c20 := h 19 (by decide)
  have h24 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c461 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨40, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c78, some c28, some c180, some c260, some c79, some c7, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked461 : lratChecker f461 p461 = .success := by decide +kernel
theorem unsat461 : Unsatisfiable (PosFin 57) f461 := by
  apply lratCheckerSound f461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p461
  · intro a ha; simp [p461] at ha; subst a; trivial
  · exact checked461
theorem derived461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c461 := by
  apply localUnsat_implies_entails f461 [c106, c78, c28, c180, c260, c79, c7] c461 unsat461 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c462 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c376, some c381, some c437, some c438, some c443, some c452, some c456, some c196, some c460, some c461, some c6, some c20, some c259, some c107, some c28, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked462 : lratChecker f462 p462 = .success := by decide +kernel
theorem unsat462 : Unsatisfiable (PosFin 57) f462 := by
  apply lratCheckerSound f462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p462
  · intro a ha; simp [p462] at ha; subst a; trivial
  · exact checked462
theorem derived462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c462 := by
  apply localUnsat_implies_entails f462 [c379, c376, c381, c437, c438, c443, c452, c456, c196, c460, c461, c6, c20, c259, c107, c28] c462 unsat462 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c438 := derived438 a h
  have h5 : Entails.eval a c443 := derived443 a h
  have h6 : Entails.eval a c452 := derived452 a h
  have h7 : Entails.eval a c456 := derived456 a h
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c460 := derived460 a h
  have h10 : Entails.eval a c461 := derived461 a h
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c463 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨41, by decide⟩, false), (⟨40, by decide⟩, true), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c195, some c461, some c6, some c20, some c259, some c107, some c28, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked463 : lratChecker f463 p463 = .success := by decide +kernel
theorem unsat463 : Unsatisfiable (PosFin 57) f463 := by
  apply lratCheckerSound f463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p463
  · intro a ha; simp [p463] at ha; subst a; trivial
  · exact checked463
theorem derived463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c463 := by
  apply localUnsat_implies_entails f463 [c196, c195, c461, c6, c20, c259, c107, c28] c463 unsat463 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c461 := derived461 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c464 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c93, some c94, some c438, some c112, some c108, some c257, some c61, some c18, some c24, some c4, some c164, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked464 : lratChecker f464 p464 = .success := by decide +kernel
theorem unsat464 : Unsatisfiable (PosFin 57) f464 := by
  apply lratCheckerSound f464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p464
  · intro a ha; simp [p464] at ha; subst a; trivial
  · exact checked464
theorem derived464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c464 := by
  apply localUnsat_implies_entails f464 [c6, c93, c94, c438, c112, c108, c257, c61, c18, c24, c4, c164] c464 unsat464 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c438 := derived438 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c257 := h 256 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c465 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨51, by decide⟩, false), (⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c225, some c61, some c18, some c164, some c352, some c128, some c223, some c255, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked465 : lratChecker f465 p465 = .success := by decide +kernel
theorem unsat465 : Unsatisfiable (PosFin 57) f465 := by
  apply lratCheckerSound f465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p465
  · intro a ha; simp [p465] at ha; subst a; trivial
  · exact checked465
theorem derived465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c465 := by
  apply localUnsat_implies_entails f465 [c225, c61, c18, c164, c352, c128, c223, c255] c465 unsat465 (by rfl) a
  have h0 : Entails.eval a c225 := h 224 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c128 := h 127 (by decide)
  have h6 : Entails.eval a c223 := h 222 (by decide)
  have h7 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c466 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true), (⟨41, by decide⟩, false), (⟨40, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c6, some c257, some c465, some c112, some c14, some c189, some c128, some c116, some c255, some c308, some c30, some c138, some c230, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked466 : lratChecker f466 p466 = .success := by decide +kernel
theorem unsat466 : Unsatisfiable (PosFin 57) f466 := by
  apply lratCheckerSound f466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p466
  · intro a ha; simp [p466] at ha; subst a; trivial
  · exact checked466
theorem derived466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c466 := by
  apply localUnsat_implies_entails f466 [c20, c6, c257, c465, c112, c14, c189, c128, c116, c255, c308, c30, c138, c230] c466 unsat466 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c257 := h 256 (by decide)
  have h3 : Entails.eval a c465 := derived465 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c255 := h 254 (by decide)
  have h10 : Entails.eval a c308 := h 307 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c467 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨51, by decide⟩, false), (⟨24, by decide⟩, true), (⟨1, by decide⟩, true), (⟨40, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c225, some c128, some c255, some c223, some c30, some c352, some c261, some c227, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked467 : lratChecker f467 p467 = .success := by decide +kernel
theorem unsat467 : Unsatisfiable (PosFin 57) f467 := by
  apply lratCheckerSound f467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p467
  · intro a ha; simp [p467] at ha; subst a; trivial
  · exact checked467
theorem derived467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c467 := by
  apply localUnsat_implies_entails f467 [c225, c128, c255, c223, c30, c352, c261, c227] c467 unsat467 (by rfl) a
  have h0 : Entails.eval a c225 := h 224 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c255 := h 254 (by decide)
  have h3 : Entails.eval a c223 := h 222 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c352 := h 351 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c468 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨51, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true), (⟨41, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c255, some c30, some c231, some c230, some c180, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked468 : lratChecker f468 p468 = .success := by decide +kernel
theorem unsat468 : Unsatisfiable (PosFin 57) f468 := by
  apply lratCheckerSound f468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p468
  · intro a ha; simp [p468] at ha; subst a; trivial
  · exact checked468
theorem derived468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c468 := by
  apply localUnsat_implies_entails f468 [c255, c30, c231, c230, c180] c468 unsat468 (by rfl) a
  have h0 : Entails.eval a c255 := h 254 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  have h3 : Entails.eval a c230 := h 229 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c469 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨43, by decide⟩, false), (⟨19, by decide⟩, false), (⟨32, by decide⟩, true), (⟨24, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c295, some c215, some c238, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked469 : lratChecker f469 p469 = .success := by decide +kernel
theorem unsat469 : Unsatisfiable (PosFin 57) f469 := by
  apply lratCheckerSound f469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p469
  · intro a ha; simp [p469] at ha; subst a; trivial
  · exact checked469
theorem derived469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c469 := by
  apply localUnsat_implies_entails f469 [c295, c215, c238] c469 unsat469 (by rfl) a
  have h0 : Entails.eval a c295 := h 294 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c470 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨41, by decide⟩, false), (⟨40, by decide⟩, true), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c376, some c463, some c93, some c57, some c196, some c195, some c455, some c462, some c6, some c20, some c259, some c28, some c464, some c466, some c95, some c108, some c14, some c468, some c119, some c306, some c311, some c211, some c291, some c469, some c312, some c54, some c61, some c18, some c465, some c320, some c153, some c346, some c203, some c162, some c265, some c267, some c237, some c357, some c1, some c221, some c143, some c70, some c125, some c176, some c230, some c46, some c280, some c138, some c382, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]]
theorem checked470 : lratChecker f470 p470 = .success := by decide +kernel
theorem unsat470 : Unsatisfiable (PosFin 57) f470 := by
  apply lratCheckerSound f470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p470
  · intro a ha; simp [p470] at ha; subst a; trivial
  · exact checked470
theorem derived470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c470 := by
  apply localUnsat_implies_entails f470 [c379, c376, c463, c93, c57, c196, c195, c455, c462, c6, c20, c259, c28, c464, c466, c95, c108, c14, c468, c119, c306, c311, c211, c291, c469, c312, c54, c61, c18, c465, c320, c153, c346, c203, c162, c265, c267, c237, c357, c1, c221, c143, c70, c125, c176, c230, c46, c280, c138, c382] c470 unsat470 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c455 := derived455 a h
  have h8 : Entails.eval a c462 := derived462 a h
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c20 := h 19 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c464 := derived464 a h
  have h14 : Entails.eval a c466 := derived466 a h
  have h15 : Entails.eval a c95 := h 94 (by decide)
  have h16 : Entails.eval a c108 := h 107 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c468 := derived468 a h
  have h19 : Entails.eval a c119 := h 118 (by decide)
  have h20 : Entails.eval a c306 := h 305 (by decide)
  have h21 : Entails.eval a c311 := h 310 (by decide)
  have h22 : Entails.eval a c211 := h 210 (by decide)
  have h23 : Entails.eval a c291 := h 290 (by decide)
  have h24 : Entails.eval a c469 := derived469 a h
  have h25 : Entails.eval a c312 := h 311 (by decide)
  have h26 : Entails.eval a c54 := h 53 (by decide)
  have h27 : Entails.eval a c61 := h 60 (by decide)
  have h28 : Entails.eval a c18 := h 17 (by decide)
  have h29 : Entails.eval a c465 := derived465 a h
  have h30 : Entails.eval a c320 := h 319 (by decide)
  have h31 : Entails.eval a c153 := h 152 (by decide)
  have h32 : Entails.eval a c346 := h 345 (by decide)
  have h33 : Entails.eval a c203 := h 202 (by decide)
  have h34 : Entails.eval a c162 := h 161 (by decide)
  have h35 : Entails.eval a c265 := h 264 (by decide)
  have h36 : Entails.eval a c267 := h 266 (by decide)
  have h37 : Entails.eval a c237 := h 236 (by decide)
  have h38 : Entails.eval a c357 := h 356 (by decide)
  have h39 : Entails.eval a c1 := h 0 (by decide)
  have h40 : Entails.eval a c221 := h 220 (by decide)
  have h41 : Entails.eval a c143 := h 142 (by decide)
  have h42 : Entails.eval a c70 := h 69 (by decide)
  have h43 : Entails.eval a c125 := h 124 (by decide)
  have h44 : Entails.eval a c176 := h 175 (by decide)
  have h45 : Entails.eval a c230 := h 229 (by decide)
  have h46 : Entails.eval a c46 := h 45 (by decide)
  have h47 : Entails.eval a c280 := h 279 (by decide)
  have h48 : Entails.eval a c138 := h 137 (by decide)
  have h49 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c471 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c195, some c260, some c259, some c132, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked471 : lratChecker f471 p471 = .success := by decide +kernel
theorem unsat471 : Unsatisfiable (PosFin 57) f471 := by
  apply lratCheckerSound f471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p471
  · intro a ha; simp [p471] at ha; subst a; trivial
  · exact checked471
theorem derived471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c471 := by
  apply localUnsat_implies_entails f471 [c196, c195, c260, c259, c132] c471 unsat471 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c260 := h 259 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c472 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c110, some c93, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked472 : lratChecker f472 p472 = .success := by decide +kernel
theorem unsat472 : Unsatisfiable (PosFin 57) f472 := by
  apply lratCheckerSound f472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p472
  · intro a ha; simp [p472] at ha; subst a; trivial
  · exact checked472
theorem derived472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c472 := by
  apply localUnsat_implies_entails f472 [c106, c110, c93] c472 unsat472 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c473 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f473 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c95, some c356, some c82, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p473 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked473 : lratChecker f473 p473 = .success := by decide +kernel
theorem unsat473 : Unsatisfiable (PosFin 57) f473 := by
  apply lratCheckerSound f473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p473
  · intro a ha; simp [p473] at ha; subst a; trivial
  · exact checked473
theorem derived473 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c473 := by
  apply localUnsat_implies_entails f473 [c95, c356, c82] c473 unsat473 (by rfl) a
  have h0 : Entails.eval a c95 := h 94 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c474 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨36, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f474 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c352, some c349, some c337, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p474 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked474 : lratChecker f474 p474 = .success := by decide +kernel
theorem unsat474 : Unsatisfiable (PosFin 57) f474 := by
  apply lratCheckerSound f474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p474
  · intro a ha; simp [p474] at ha; subst a; trivial
  · exact checked474
theorem derived474 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c474 := by
  apply localUnsat_implies_entails f474 [c352, c349, c337] c474 unsat474 (by rfl) a
  have h0 : Entails.eval a c352 := h 351 (by decide)
  have h1 : Entails.eval a c349 := h 348 (by decide)
  have h2 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c475 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f475 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c471, some c196, some c195, some c462, some c379, some c376, some c28, some c472, some c6, some c20, some c470, some c107, some c464, some c354, some c93, some c473, some c257, some c465, some c112, some c14, some c467, some c189, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p475 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked475 : lratChecker f475 p475 = .success := by decide +kernel
theorem unsat475 : Unsatisfiable (PosFin 57) f475 := by
  apply lratCheckerSound f475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p475
  · intro a ha; simp [p475] at ha; subst a; trivial
  · exact checked475
theorem derived475 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c475 := by
  apply localUnsat_implies_entails f475 [c471, c196, c195, c462, c379, c376, c28, c472, c6, c20, c470, c107, c464, c354, c93, c473, c257, c465, c112, c14, c467, c189] c475 unsat475 (by rfl) a
  have h0 : Entails.eval a c471 := derived471 a h
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c195 := h 194 (by decide)
  have h3 : Entails.eval a c462 := derived462 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c472 := derived472 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c470 := derived470 a h
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c464 := derived464 a h
  have h13 : Entails.eval a c354 := h 353 (by decide)
  have h14 : Entails.eval a c93 := h 92 (by decide)
  have h15 : Entails.eval a c473 := derived473 a h
  have h16 : Entails.eval a c257 := h 256 (by decide)
  have h17 : Entails.eval a c465 := derived465 a h
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c467 := derived467 a h
  have h21 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c476 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨9, by decide⟩, true), (⟨51, by decide⟩, false), (⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f476 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c472, some c20, some c107, some c93, some c57, some c354, some c133, some c84, some c473, some c272, some c213, some c304, some c308, some c211, some c291, some c152, some c469, some c312, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p476 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked476 : lratChecker f476 p476 = .success := by decide +kernel
theorem unsat476 : Unsatisfiable (PosFin 57) f476 := by
  apply lratCheckerSound f476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p476
  · intro a ha; simp [p476] at ha; subst a; trivial
  · exact checked476
theorem derived476 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c476 := by
  apply localUnsat_implies_entails f476 [c472, c20, c107, c93, c57, c354, c133, c84, c473, c272, c213, c304, c308, c211, c291, c152, c469, c312] c476 unsat476 (by rfl) a
  have h0 : Entails.eval a c472 := derived472 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c473 := derived473 a h
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c308 := h 307 (by decide)
  have h13 : Entails.eval a c211 := h 210 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c152 := h 151 (by decide)
  have h16 : Entails.eval a c469 := derived469 a h
  have h17 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c477 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨22, by decide⟩, false), (⟨20, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f477 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c195, some c379, some c472, some c20, some c107, some c464, some c57, some c156, some c1, some c476, some c455, some c230, some c138, some c180, some c310, some c366, some c231, some c178, some c295, some c119, some c128, some c319, some c312, some c203, some c142, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p477 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked477 : lratChecker f477 p477 = .success := by decide +kernel
theorem unsat477 : Unsatisfiable (PosFin 57) f477 := by
  apply lratCheckerSound f477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p477
  · intro a ha; simp [p477] at ha; subst a; trivial
  · exact checked477
theorem derived477 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c477 := by
  apply localUnsat_implies_entails f477 [c195, c379, c472, c20, c107, c464, c57, c156, c1, c476, c455, c230, c138, c180, c310, c366, c231, c178, c295, c119, c128, c319, c312, c203, c142] c477 unsat477 (by rfl) a
  have h0 : Entails.eval a c195 := h 194 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c472 := derived472 a h
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c464 := derived464 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c476 := derived476 a h
  have h10 : Entails.eval a c455 := derived455 a h
  have h11 : Entails.eval a c230 := h 229 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c366 := h 365 (by decide)
  have h16 : Entails.eval a c231 := h 230 (by decide)
  have h17 : Entails.eval a c178 := h 177 (by decide)
  have h18 : Entails.eval a c295 := h 294 (by decide)
  have h19 : Entails.eval a c119 := h 118 (by decide)
  have h20 : Entails.eval a c128 := h 127 (by decide)
  have h21 : Entails.eval a c319 := h 318 (by decide)
  have h22 : Entails.eval a c312 := h 311 (by decide)
  have h23 : Entails.eval a c203 := h 202 (by decide)
  have h24 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c478 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f478 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c57, some c93, some c347, some c348, some c109, some c108, some c94, some c35, some c70, some c255, some c474, some c224, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p478 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked478 : lratChecker f478 p478 = .success := by decide +kernel
theorem unsat478 : Unsatisfiable (PosFin 57) f478 := by
  apply lratCheckerSound f478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p478
  · intro a ha; simp [p478] at ha; subst a; trivial
  · exact checked478
theorem derived478 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c478 := by
  apply localUnsat_implies_entails f478 [c37, c57, c93, c347, c348, c109, c108, c94, c35, c70, c255, c474, c224] c478 unsat478 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c255 := h 254 (by decide)
  have h11 : Entails.eval a c474 := derived474 a h
  have h12 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c479 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f479 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c20, some c105, some c96, some c18, some c39, some c108, some c14, some c35, some c203, some c268, some c128, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p479 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked479 : lratChecker f479 p479 = .success := by decide +kernel
theorem unsat479 : Unsatisfiable (PosFin 57) f479 := by
  apply lratCheckerSound f479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p479
  · intro a ha; simp [p479] at ha; subst a; trivial
  · exact checked479
theorem derived479 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c479 := by
  apply localUnsat_implies_entails f479 [c37, c20, c105, c96, c18, c39, c108, c14, c35, c203, c268, c128] c479 unsat479 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c480 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f480 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c478, some c479, some c109, some c58, some c96, some c160, some c105, some c13, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p480 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked480 : lratChecker f480 p480 = .success := by decide +kernel
theorem unsat480 : Unsatisfiable (PosFin 57) f480 := by
  apply lratCheckerSound f480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p480
  · intro a ha; simp [p480] at ha; subst a; trivial
  · exact checked480
theorem derived480 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c480 := by
  apply localUnsat_implies_entails f480 [c37, c478, c479, c109, c58, c96, c160, c105, c13] c480 unsat480 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c478 := derived478 a h
  have h2 : Entails.eval a c479 := derived479 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c481 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f481 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c475, some c471, some c196, some c195, some c462, some c379, some c376, some c480, some c472, some c477, some c6, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p481 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked481 : lratChecker f481 p481 = .success := by decide +kernel
theorem unsat481 : Unsatisfiable (PosFin 57) f481 := by
  apply lratCheckerSound f481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p481
  · intro a ha; simp [p481] at ha; subst a; trivial
  · exact checked481
theorem derived481 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c481 := by
  apply localUnsat_implies_entails f481 [c475, c471, c196, c195, c462, c379, c376, c480, c472, c477, c6] c481 unsat481 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c471 := derived471 a h
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c195 := h 194 (by decide)
  have h4 : Entails.eval a c462 := derived462 a h
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c480 := derived480 a h
  have h8 : Entails.eval a c472 := derived472 a h
  have h9 : Entails.eval a c477 := derived477 a h
  have h10 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c482 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨35, by decide⟩, false), (⟨51, by decide⟩, false), (⟨18, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f482 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c114, some c125, some c276, some c273, some c255, some c211, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p482 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked482 : lratChecker f482 p482 = .success := by decide +kernel
theorem unsat482 : Unsatisfiable (PosFin 57) f482 := by
  apply lratCheckerSound f482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p482
  · intro a ha; simp [p482] at ha; subst a; trivial
  · exact checked482
theorem derived482 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c482 := by
  apply localUnsat_implies_entails f482 [c160, c114, c125, c276, c273, c255, c211] c482 unsat482 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c276 := h 275 (by decide)
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c255 := h 254 (by decide)
  have h6 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c483 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f483 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c472, some c6, some c20, some c257, some c265, some c107, some c464, some c95, some c57, some c93, some c347, some c348, some c108, some c70, some c482, some c221, some c468, some c354, some c473, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p483 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked483 : lratChecker f483 p483 = .success := by decide +kernel
theorem unsat483 : Unsatisfiable (PosFin 57) f483 := by
  apply lratCheckerSound f483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p483
  · intro a ha; simp [p483] at ha; subst a; trivial
  · exact checked483
theorem derived483 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c483 := by
  apply localUnsat_implies_entails f483 [c472, c6, c20, c257, c265, c107, c464, c95, c57, c93, c347, c348, c108, c70, c482, c221, c468, c354, c473] c483 unsat483 (by rfl) a
  have h0 : Entails.eval a c472 := derived472 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c464 := derived464 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c347 := h 346 (by decide)
  have h11 : Entails.eval a c348 := h 347 (by decide)
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c482 := derived482 a h
  have h15 : Entails.eval a c221 := h 220 (by decide)
  have h16 : Entails.eval a c468 := derived468 a h
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c473 := derived473 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c484 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f484 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c57, some c93, some c464, some c95, some c347, some c348, some c108, some c70, some c35, some c482, some c255, some c221, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p484 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked484 : lratChecker f484 p484 = .success := by decide +kernel
theorem unsat484 : Unsatisfiable (PosFin 57) f484 := by
  apply lratCheckerSound f484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p484
  · intro a ha; simp [p484] at ha; subst a; trivial
  · exact checked484
theorem derived484 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c484 := by
  apply localUnsat_implies_entails f484 [c20, c57, c93, c464, c95, c347, c348, c108, c70, c35, c482, c255, c221] c484 unsat484 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c464 := derived464 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c347 := h 346 (by decide)
  have h6 : Entails.eval a c348 := h 347 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c482 := derived482 a h
  have h11 : Entails.eval a c255 := h 254 (by decide)
  have h12 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c485 : DefaultClause 57 := directClause ((⟨42, by decide⟩, false) :: (⟨9, by decide⟩, true) :: (⟨1, by decide⟩, false) :: (⟨2, by decide⟩, false) :: (⟨3, by decide⟩, false) :: (⟨4, by decide⟩, true) :: (⟨7, by decide⟩, false) :: (⟨8, by decide⟩, true) :: (⟨56, by decide⟩, false) :: (⟨6, by decide⟩, true) :: (⟨11, by decide⟩, false) :: (⟨5, by decide⟩, true) :: (⟨13, by decide⟩, false) :: (⟨14, by decide⟩, true) :: (⟨15, by decide⟩, true) :: (⟨16, by decide⟩, false) :: (⟨12, by decide⟩, true) :: (⟨18, by decide⟩, true) :: (⟨19, by decide⟩, true) :: (⟨20, by decide⟩, false) :: (⟨21, by decide⟩, false) :: (⟨22, by decide⟩, false) :: (⟨23, by decide⟩, false) :: (⟨24, by decide⟩, true) :: (⟨25, by decide⟩, false) :: (⟨17, by decide⟩, true) :: (⟨10, by decide⟩, false) :: (⟨28, by decide⟩, false) :: (⟨29, by decide⟩, true) :: (⟨30, by decide⟩, false) :: (⟨31, by decide⟩, true) :: (⟨32, by decide⟩, true) :: (⟨33, by decide⟩, false) :: (⟨34, by decide⟩, true) :: (⟨35, by decide⟩, true) :: (⟨36, by decide⟩, false) :: (⟨37, by decide⟩, false) :: (⟨38, by decide⟩, true) :: (⟨39, by decide⟩, true) :: (⟨40, by decide⟩, false) :: (⟨41, by decide⟩, true) :: (⟨27, by decide⟩, false) :: (⟨43, by decide⟩, true) :: (⟨44, by decide⟩, false) :: (⟨45, by decide⟩, true) :: (⟨26, by decide⟩, true) :: (⟨47, by decide⟩, false) :: (⟨48, by decide⟩, false) :: (⟨49, by decide⟩, true) :: (⟨50, by decide⟩, true) :: (⟨51, by decide⟩, false) :: (⟨52, by decide⟩, true) :: (⟨53, by decide⟩, true) :: (⟨54, by decide⟩, false) :: (⟨55, by decide⟩, false) :: []) (by decide +kernel) (by decide +kernel)
def f485 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c370, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p485 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked485 : lratChecker f485 p485 = .success := by decide +kernel
theorem unsat485 : Unsatisfiable (PosFin 57) f485 := by
  apply lratCheckerSound f485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p485
  · intro a ha; simp [p485] at ha; subst a; trivial
  · exact checked485
theorem derived485 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c485 := by
  apply localUnsat_implies_entails f485 [c383, c370] c485 unsat485 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c486 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f486 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c462, some c195, some c196, some c20, some c376, some c379, some c471, some c475, some c481, some c483, some c6, some c257, some c265, some c484, some c105, some c61, some c18, some c96, some c39, some c267, some c35, some c108, some c60, some c164, some c352, some c334, some c156, some c347, some c348, some c221, some c261, some c113, some c121, some c122, some c43, some c272, some c269, some c152, some c139, some c148, some c211, some c79, some c87, some c242, some c316, some c354, some c443, some c356, some c295, some c485, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p486 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]]
theorem checked486 : lratChecker f486 p486 = .success := by decide +kernel
theorem unsat486 : Unsatisfiable (PosFin 57) f486 := by
  apply lratCheckerSound f486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p486
  · intro a ha; simp [p486] at ha; subst a; trivial
  · exact checked486
theorem derived486 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c486 := by
  apply localUnsat_implies_entails f486 [c462, c195, c196, c20, c376, c379, c471, c475, c481, c483, c6, c257, c265, c484, c105, c61, c18, c96, c39, c267, c35, c108, c60, c164, c352, c334, c156, c347, c348, c221, c261, c113, c121, c122, c43, c272, c269, c152, c139, c148, c211, c79, c87, c242, c316, c354, c443, c356, c295, c485] c486 unsat486 (by rfl) a
  have h0 : Entails.eval a c462 := derived462 a h
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c471 := derived471 a h
  have h7 : Entails.eval a c475 := derived475 a h
  have h8 : Entails.eval a c481 := derived481 a h
  have h9 : Entails.eval a c483 := derived483 a h
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c257 := h 256 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c484 := derived484 a h
  have h14 : Entails.eval a c105 := h 104 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c18 := h 17 (by decide)
  have h17 : Entails.eval a c96 := h 95 (by decide)
  have h18 : Entails.eval a c39 := h 38 (by decide)
  have h19 : Entails.eval a c267 := h 266 (by decide)
  have h20 : Entails.eval a c35 := h 34 (by decide)
  have h21 : Entails.eval a c108 := h 107 (by decide)
  have h22 : Entails.eval a c60 := h 59 (by decide)
  have h23 : Entails.eval a c164 := h 163 (by decide)
  have h24 : Entails.eval a c352 := h 351 (by decide)
  have h25 : Entails.eval a c334 := h 333 (by decide)
  have h26 : Entails.eval a c156 := h 155 (by decide)
  have h27 : Entails.eval a c347 := h 346 (by decide)
  have h28 : Entails.eval a c348 := h 347 (by decide)
  have h29 : Entails.eval a c221 := h 220 (by decide)
  have h30 : Entails.eval a c261 := h 260 (by decide)
  have h31 : Entails.eval a c113 := h 112 (by decide)
  have h32 : Entails.eval a c121 := h 120 (by decide)
  have h33 : Entails.eval a c122 := h 121 (by decide)
  have h34 : Entails.eval a c43 := h 42 (by decide)
  have h35 : Entails.eval a c272 := h 271 (by decide)
  have h36 : Entails.eval a c269 := h 268 (by decide)
  have h37 : Entails.eval a c152 := h 151 (by decide)
  have h38 : Entails.eval a c139 := h 138 (by decide)
  have h39 : Entails.eval a c148 := h 147 (by decide)
  have h40 : Entails.eval a c211 := h 210 (by decide)
  have h41 : Entails.eval a c79 := h 78 (by decide)
  have h42 : Entails.eval a c87 := h 86 (by decide)
  have h43 : Entails.eval a c242 := h 241 (by decide)
  have h44 : Entails.eval a c316 := h 315 (by decide)
  have h45 : Entails.eval a c354 := h 353 (by decide)
  have h46 : Entails.eval a c443 := derived443 a h
  have h47 : Entails.eval a c356 := h 355 (by decide)
  have h48 : Entails.eval a c295 := h 294 (by decide)
  have h49 : Entails.eval a c485 := derived485 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c487 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f487 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c379, some c462, some c195, some c196, some c471, some c475, some c481, some c483, some c6, some c20, some c257, some c265, some c484, some c105, some c96, some c39, some c267, some c35, some c486, some c160, some c114, some c276, some c45, some c211, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p487 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked487 : lratChecker f487 p487 = .success := by decide +kernel
theorem unsat487 : Unsatisfiable (PosFin 57) f487 := by
  apply lratCheckerSound f487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p487
  · intro a ha; simp [p487] at ha; subst a; trivial
  · exact checked487
theorem derived487 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c487 := by
  apply localUnsat_implies_entails f487 [c376, c379, c462, c195, c196, c471, c475, c481, c483, c6, c20, c257, c265, c484, c105, c96, c39, c267, c35, c486, c160, c114, c276, c45, c211] c487 unsat487 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c462 := derived462 a h
  have h3 : Entails.eval a c195 := h 194 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c471 := derived471 a h
  have h6 : Entails.eval a c475 := derived475 a h
  have h7 : Entails.eval a c481 := derived481 a h
  have h8 : Entails.eval a c483 := derived483 a h
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c20 := h 19 (by decide)
  have h11 : Entails.eval a c257 := h 256 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c484 := derived484 a h
  have h14 : Entails.eval a c105 := h 104 (by decide)
  have h15 : Entails.eval a c96 := h 95 (by decide)
  have h16 : Entails.eval a c39 := h 38 (by decide)
  have h17 : Entails.eval a c267 := h 266 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c486 := derived486 a h
  have h20 : Entails.eval a c160 := h 159 (by decide)
  have h21 : Entails.eval a c114 := h 113 (by decide)
  have h22 : Entails.eval a c276 := h 275 (by decide)
  have h23 : Entails.eval a c45 := h 44 (by decide)
  have h24 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c488 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f488 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c114, some c276, some c45, some c211, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p488 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked488 : lratChecker f488 p488 = .success := by decide +kernel
theorem unsat488 : Unsatisfiable (PosFin 57) f488 := by
  apply lratCheckerSound f488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p488
  · intro a ha; simp [p488] at ha; subst a; trivial
  · exact checked488
theorem derived488 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c488 := by
  apply localUnsat_implies_entails f488 [c160, c114, c276, c45, c211] c488 unsat488 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c276 := h 275 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c489 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c96, some c39, some c267, some c35, some c488, some c334, some c156, some c348, some c221, some c261, some c113, some c42, some c43, some c152, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked489 : lratChecker f489 p489 = .success := by decide +kernel
theorem unsat489 : Unsatisfiable (PosFin 57) f489 := by
  apply lratCheckerSound f489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p489
  · intro a ha; simp [p489] at ha; subst a; trivial
  · exact checked489
theorem derived489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c489 := by
  apply localUnsat_implies_entails f489 [c105, c96, c39, c267, c35, c488, c334, c156, c348, c221, c261, c113, c42, c43, c152] c489 unsat489 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c488 := derived488 a h
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c348 := h 347 (by decide)
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c43 := h 42 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c490 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c121, some c122, some c200, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked490 : lratChecker f490 p490 = .success := by decide +kernel
theorem unsat490 : Unsatisfiable (PosFin 57) f490 := by
  apply lratCheckerSound f490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p490
  · intro a ha; simp [p490] at ha; subst a; trivial
  · exact checked490
theorem derived490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c490 := by
  apply localUnsat_implies_entails f490 [c121, c122, c200] c490 unsat490 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c491 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c490, some c261, some c39, some c124, some c117, some c200, some c50, some c115, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked491 : lratChecker f491 p491 = .success := by decide +kernel
theorem unsat491 : Unsatisfiable (PosFin 57) f491 := by
  apply lratCheckerSound f491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p491
  · intro a ha; simp [p491] at ha; subst a; trivial
  · exact checked491
theorem derived491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c491 := by
  apply localUnsat_implies_entails f491 [c490, c261, c39, c124, c117, c200, c50, c115] c491 unsat491 (by rfl) a
  have h0 : Entails.eval a c490 := derived490 a h
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c492 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c491, some c267, some c39, some c124, some c117, some c200, some c50, some c41, some c142, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked492 : lratChecker f492 p492 = .success := by decide +kernel
theorem unsat492 : Unsatisfiable (PosFin 57) f492 := by
  apply lratCheckerSound f492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p492
  · intro a ha; simp [p492] at ha; subst a; trivial
  · exact checked492
theorem derived492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c492 := by
  apply localUnsat_implies_entails f492 [c491, c267, c39, c124, c117, c200, c50, c41, c142] c492 unsat492 (by rfl) a
  have h0 : Entails.eval a c491 := derived491 a h
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c493 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c58, some c334, some c337, some c109, some c156, some c60, some c16, some c352, some c164, some c492, some c35, some c59, some c255, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked493 : lratChecker f493 p493 = .success := by decide +kernel
theorem unsat493 : Unsatisfiable (PosFin 57) f493 := by
  apply lratCheckerSound f493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p493
  · intro a ha; simp [p493] at ha; subst a; trivial
  · exact checked493
theorem derived493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c493 := by
  apply localUnsat_implies_entails f493 [c7, c58, c334, c337, c109, c156, c60, c16, c352, c164, c492, c35, c59, c255] c493 unsat493 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c334 := h 333 (by decide)
  have h3 : Entails.eval a c337 := h 336 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  have h10 : Entails.eval a c492 := derived492 a h
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c494 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c493, some c160, some c13, some c114, some c47, some c138, some c78, some c83, some c354, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked494 : lratChecker f494 p494 = .success := by decide +kernel
theorem unsat494 : Unsatisfiable (PosFin 57) f494 := by
  apply lratCheckerSound f494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p494
  · intro a ha; simp [p494] at ha; subst a; trivial
  · exact checked494
theorem derived494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c494 := by
  apply localUnsat_implies_entails f494 [c489, c493, c160, c13, c114, c47, c138, c78, c83, c354] c494 unsat494 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c493 := derived493 a h
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c495 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c494, some c93, some c95, some c109, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked495 : lratChecker f495 p495 = .success := by decide +kernel
theorem unsat495 : Unsatisfiable (PosFin 57) f495 := by
  apply lratCheckerSound f495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p495
  · intro a ha; simp [p495] at ha; subst a; trivial
  · exact checked495
theorem derived495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c495 := by
  apply localUnsat_implies_entails f495 [c494, c93, c95, c109] c495 unsat495 (by rfl) a
  have h0 : Entails.eval a c494 := derived494 a h
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c496 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c483, some c257, some c265, some c495, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked496 : lratChecker f496 p496 = .success := by decide +kernel
theorem unsat496 : Unsatisfiable (PosFin 57) f496 := by
  apply lratCheckerSound f496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p496
  · intro a ha; simp [p496] at ha; subst a; trivial
  · exact checked496
theorem derived496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c496 := by
  apply localUnsat_implies_entails f496 [c483, c257, c265, c495] c496 unsat496 (by rfl) a
  have h0 : Entails.eval a c483 := derived483 a h
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c495 := derived495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c497 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨22, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c57, some c93, some c156, some c347, some c348, some c109, some c47, some c1, some c11, some c114, some c261, some c200, some c130, some c39, some c226, some c10, some c164, some c112, some c72, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked497 : lratChecker f497 p497 = .success := by decide +kernel
theorem unsat497 : Unsatisfiable (PosFin 57) f497 := by
  apply lratCheckerSound f497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p497
  · intro a ha; simp [p497] at ha; subst a; trivial
  · exact checked497
theorem derived497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c497 := by
  apply localUnsat_implies_entails f497 [c118, c57, c93, c156, c347, c348, c109, c47, c1, c11, c114, c261, c200, c130, c39, c226, c10, c164, c112, c72] c497 unsat497 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c347 := h 346 (by decide)
  have h5 : Entails.eval a c348 := h 347 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c200 := h 199 (by decide)
  have h13 : Entails.eval a c130 := h 129 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c226 := h 225 (by decide)
  have h16 : Entails.eval a c10 := h 9 (by decide)
  have h17 : Entails.eval a c164 := h 163 (by decide)
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c498 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨6, by decide⟩, false), (⟨40, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c118, some c109, some c47, some c16, some c205, some c114, some c261, some c160, some c130, some c334, some c337, some c348, some c164, some c72, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked498 : lratChecker f498 p498 = .success := by decide +kernel
theorem unsat498 : Unsatisfiable (PosFin 57) f498 := by
  apply lratCheckerSound f498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p498
  · intro a ha; simp [p498] at ha; subst a; trivial
  · exact checked498
theorem derived498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c498 := by
  apply localUnsat_implies_entails f498 [c132, c118, c109, c47, c16, c205, c114, c261, c160, c130, c334, c337, c348, c164, c72] c498 unsat498 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c130 := h 129 (by decide)
  have h10 : Entails.eval a c334 := h 333 (by decide)
  have h11 : Entails.eval a c337 := h 336 (by decide)
  have h12 : Entails.eval a c348 := h 347 (by decide)
  have h13 : Entails.eval a c164 := h 163 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c499 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨6, by decide⟩, false), (⟨40, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c498, some c58, some c2, some c160, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked499 : lratChecker f499 p499 = .success := by decide +kernel
theorem unsat499 : Unsatisfiable (PosFin 57) f499 := by
  apply lratCheckerSound f499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p499
  · intro a ha; simp [p499] at ha; subst a; trivial
  · exact checked499
theorem derived499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c499 := by
  apply localUnsat_implies_entails f499 [c498, c58, c2, c160] c499 unsat499 (by rfl) a
  have h0 : Entails.eval a c498 := derived498 a h
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c500 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c118, some c497, some c489, some c42, some c499, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked500 : lratChecker f500 p500 = .success := by decide +kernel
theorem unsat500 : Unsatisfiable (PosFin 57) f500 := by
  apply lratCheckerSound f500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p500
  · intro a ha; simp [p500] at ha; subst a; trivial
  · exact checked500
theorem derived500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c500 := by
  apply localUnsat_implies_entails f500 [c132, c118, c497, c489, c42, c499] c500 unsat500 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c497 := derived497 a h
  have h3 : Entails.eval a c489 := derived489 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c499 := derived499 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c501 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c58, some c13, some c160, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked501 : lratChecker f501 p501 = .success := by decide +kernel
theorem unsat501 : Unsatisfiable (PosFin 57) f501 := by
  apply lratCheckerSound f501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p501
  · intro a ha; simp [p501] at ha; subst a; trivial
  · exact checked501
theorem derived501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c501 := by
  apply localUnsat_implies_entails f501 [c58, c13, c160] c501 unsat501 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c502 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨27, by decide⟩, false), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨40, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c501, some c109, some c47, some c16, some c203, some c200, some c144, some c145, some c319, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked502 : lratChecker f502 p502 = .success := by decide +kernel
theorem unsat502 : Unsatisfiable (PosFin 57) f502 := by
  apply lratCheckerSound f502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p502
  · intro a ha; simp [p502] at ha; subst a; trivial
  · exact checked502
theorem derived502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c502 := by
  apply localUnsat_implies_entails f502 [c501, c109, c47, c16, c203, c200, c144, c145, c319] c502 unsat502 (by rfl) a
  have h0 : Entails.eval a c501 := derived501 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c503 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c462, some c379, some c376, some c195, some c196, some c471, some c475, some c481, some c483, some c487, some c496, some c118, some c132, some c310, some c500, some c264, some c35, some c126, some c211, some c502, some c112, some c51, some c61, some c96, some c39, some c139, some c47, some c242, some c145, some c357, some c160, some c83, some c334, some c178, some c347, some c162, some c222, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked503 : lratChecker f503 p503 = .success := by decide +kernel
theorem unsat503 : Unsatisfiable (PosFin 57) f503 := by
  apply lratCheckerSound f503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p503
  · intro a ha; simp [p503] at ha; subst a; trivial
  · exact checked503
theorem derived503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c503 := by
  apply localUnsat_implies_entails f503 [c462, c379, c376, c195, c196, c471, c475, c481, c483, c487, c496, c118, c132, c310, c500, c264, c35, c126, c211, c502, c112, c51, c61, c96, c39, c139, c47, c242, c145, c357, c160, c83, c334, c178, c347, c162, c222] c503 unsat503 (by rfl) a
  have h0 : Entails.eval a c462 := derived462 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c195 := h 194 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c471 := derived471 a h
  have h6 : Entails.eval a c475 := derived475 a h
  have h7 : Entails.eval a c481 := derived481 a h
  have h8 : Entails.eval a c483 := derived483 a h
  have h9 : Entails.eval a c487 := derived487 a h
  have h10 : Entails.eval a c496 := derived496 a h
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c132 := h 131 (by decide)
  have h13 : Entails.eval a c310 := h 309 (by decide)
  have h14 : Entails.eval a c500 := derived500 a h
  have h15 : Entails.eval a c264 := h 263 (by decide)
  have h16 : Entails.eval a c35 := h 34 (by decide)
  have h17 : Entails.eval a c126 := h 125 (by decide)
  have h18 : Entails.eval a c211 := h 210 (by decide)
  have h19 : Entails.eval a c502 := derived502 a h
  have h20 : Entails.eval a c112 := h 111 (by decide)
  have h21 : Entails.eval a c51 := h 50 (by decide)
  have h22 : Entails.eval a c61 := h 60 (by decide)
  have h23 : Entails.eval a c96 := h 95 (by decide)
  have h24 : Entails.eval a c39 := h 38 (by decide)
  have h25 : Entails.eval a c139 := h 138 (by decide)
  have h26 : Entails.eval a c47 := h 46 (by decide)
  have h27 : Entails.eval a c242 := h 241 (by decide)
  have h28 : Entails.eval a c145 := h 144 (by decide)
  have h29 : Entails.eval a c357 := h 356 (by decide)
  have h30 : Entails.eval a c160 := h 159 (by decide)
  have h31 : Entails.eval a c83 := h 82 (by decide)
  have h32 : Entails.eval a c334 := h 333 (by decide)
  have h33 : Entails.eval a c178 := h 177 (by decide)
  have h34 : Entails.eval a c347 := h 346 (by decide)
  have h35 : Entails.eval a c162 := h 161 (by decide)
  have h36 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c504 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c503, some c379, some c376, some c8, some c120, some c472, some c107, some c310, some c311, some c48, some c57, some c152, some c119, some c139, some c347, some c272, some c201, some c92, some c26, some c177, some c129, some c257, some c265, some c95, some c205, some c82, some c231, some c354, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked504 : lratChecker f504 p504 = .success := by decide +kernel
theorem unsat504 : Unsatisfiable (PosFin 57) f504 := by
  apply lratCheckerSound f504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p504
  · intro a ha; simp [p504] at ha; subst a; trivial
  · exact checked504
theorem derived504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c504 := by
  apply localUnsat_implies_entails f504 [c503, c379, c376, c8, c120, c472, c107, c310, c311, c48, c57, c152, c119, c139, c347, c272, c201, c92, c26, c177, c129, c257, c265, c95, c205, c82, c231, c354] c504 unsat504 (by rfl) a
  have h0 : Entails.eval a c503 := derived503 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c472 := derived472 a h
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c311 := h 310 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c347 := h 346 (by decide)
  have h15 : Entails.eval a c272 := h 271 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c92 := h 91 (by decide)
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c177 := h 176 (by decide)
  have h20 : Entails.eval a c129 := h 128 (by decide)
  have h21 : Entails.eval a c257 := h 256 (by decide)
  have h22 : Entails.eval a c265 := h 264 (by decide)
  have h23 : Entails.eval a c95 := h 94 (by decide)
  have h24 : Entails.eval a c205 := h 204 (by decide)
  have h25 : Entails.eval a c82 := h 81 (by decide)
  have h26 : Entails.eval a c231 := h 230 (by decide)
  have h27 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c505 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c351, some c334, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked505 : lratChecker f505 p505 = .success := by decide +kernel
theorem unsat505 : Unsatisfiable (PosFin 57) f505 := by
  apply lratCheckerSound f505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p505
  · intro a ha; simp [p505] at ha; subst a; trivial
  · exact checked505
theorem derived505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c505 := by
  apply localUnsat_implies_entails f505 [c347, c351, c334] c505 unsat505 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c351 := h 350 (by decide)
  have h2 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c506 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c379, some c505, some c503, some c504, some c260, some c259, some c132, some c201, some c26, some c110, some c109, some c17, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked506 : lratChecker f506 p506 = .success := by decide +kernel
theorem unsat506 : Unsatisfiable (PosFin 57) f506 := by
  apply lratCheckerSound f506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p506
  · intro a ha; simp [p506] at ha; subst a; trivial
  · exact checked506
theorem derived506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c506 := by
  apply localUnsat_implies_entails f506 [c376, c379, c505, c503, c504, c260, c259, c132, c201, c26, c110, c109, c17] c506 unsat506 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c505 := derived505 a h
  have h3 : Entails.eval a c503 := derived503 a h
  have h4 : Entails.eval a c504 := derived504 a h
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c259 := h 258 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c507 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c379, some c505, some c503, some c260, some c259, some c119, some c125, some c228, some c311, some c140, some c236, some c333, some c173, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked507 : lratChecker f507 p507 = .success := by decide +kernel
theorem unsat507 : Unsatisfiable (PosFin 57) f507 := by
  apply lratCheckerSound f507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p507
  · intro a ha; simp [p507] at ha; subst a; trivial
  · exact checked507
theorem derived507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c507 := by
  apply localUnsat_implies_entails f507 [c376, c379, c505, c503, c260, c259, c119, c125, c228, c311, c140, c236, c333, c173] c507 unsat507 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c505 := derived505 a h
  have h3 : Entails.eval a c503 := derived503 a h
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c311 := h 310 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c236 := h 235 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c508 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c503, some c506, some c507, some c8, some c120, some c311, some c48, some c145, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked508 : lratChecker f508 p508 = .success := by decide +kernel
theorem unsat508 : Unsatisfiable (PosFin 57) f508 := by
  apply lratCheckerSound f508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p508
  · intro a ha; simp [p508] at ha; subst a; trivial
  · exact checked508
theorem derived508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c508 := by
  apply localUnsat_implies_entails f508 [c503, c506, c507, c8, c120, c311, c48, c145] c508 unsat508 (by rfl) a
  have h0 : Entails.eval a c503 := derived503 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c507 := derived507 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c509 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c462, some c379, some c376, some c508, some c93, some c96, some c105, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked509 : lratChecker f509 p509 = .success := by decide +kernel
theorem unsat509 : Unsatisfiable (PosFin 57) f509 := by
  apply lratCheckerSound f509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p509
  · intro a ha; simp [p509] at ha; subst a; trivial
  · exact checked509
theorem derived509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c509 := by
  apply localUnsat_implies_entails f509 [c462, c379, c376, c508, c93, c96, c105] c509 unsat509 (by rfl) a
  have h0 : Entails.eval a c462 := derived462 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c508 := derived508 a h
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c510 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c379, some c505, some c503, some c509, some c7, some c260, some c8, some c120, some c472, some c311, some c20, some c76, some c26, some c139, some c348, some c333, some c57, some c334, some c44, some c276, some c145, some c201, some c177, some c129, some c257, some c265, some c336, some c205, some c325, some c231, some c354, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked510 : lratChecker f510 p510 = .success := by decide +kernel
theorem unsat510 : Unsatisfiable (PosFin 57) f510 := by
  apply lratCheckerSound f510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p510
  · intro a ha; simp [p510] at ha; subst a; trivial
  · exact checked510
theorem derived510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c510 := by
  apply localUnsat_implies_entails f510 [c376, c379, c505, c503, c509, c7, c260, c8, c120, c472, c311, c20, c76, c26, c139, c348, c333, c57, c334, c44, c276, c145, c201, c177, c129, c257, c265, c336, c205, c325, c231, c354] c510 unsat510 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c505 := derived505 a h
  have h3 : Entails.eval a c503 := derived503 a h
  have h4 : Entails.eval a c509 := derived509 a h
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c260 := h 259 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c472 := derived472 a h
  have h10 : Entails.eval a c311 := h 310 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c348 := h 347 (by decide)
  have h16 : Entails.eval a c333 := h 332 (by decide)
  have h17 : Entails.eval a c57 := h 56 (by decide)
  have h18 : Entails.eval a c334 := h 333 (by decide)
  have h19 : Entails.eval a c44 := h 43 (by decide)
  have h20 : Entails.eval a c276 := h 275 (by decide)
  have h21 : Entails.eval a c145 := h 144 (by decide)
  have h22 : Entails.eval a c201 := h 200 (by decide)
  have h23 : Entails.eval a c177 := h 176 (by decide)
  have h24 : Entails.eval a c129 := h 128 (by decide)
  have h25 : Entails.eval a c257 := h 256 (by decide)
  have h26 : Entails.eval a c265 := h 264 (by decide)
  have h27 : Entails.eval a c336 := h 335 (by decide)
  have h28 : Entails.eval a c205 := h 204 (by decide)
  have h29 : Entails.eval a c325 := h 324 (by decide)
  have h30 : Entails.eval a c231 := h 230 (by decide)
  have h31 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c511 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c261, some c131, some c197, some c133, some c230, some c231, some c296, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked511 : lratChecker f511 p511 = .success := by decide +kernel
theorem unsat511 : Unsatisfiable (PosFin 57) f511 := by
  apply lratCheckerSound f511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p511
  · intro a ha; simp [p511] at ha; subst a; trivial
  · exact checked511
theorem derived511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c511 := by
  apply localUnsat_implies_entails f511 [c261, c131, c197, c133, c230, c231, c296] c511 unsat511 (by rfl) a
  have h0 : Entails.eval a c261 := h 260 (by decide)
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c197 := h 196 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c230 := h 229 (by decide)
  have h5 : Entails.eval a c231 := h 230 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c512 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨34, by decide⟩, false), (⟨33, by decide⟩, true), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c205, some c265, some c129, some c219, some c158, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked512 : lratChecker f512 p512 = .success := by decide +kernel
theorem unsat512 : Unsatisfiable (PosFin 57) f512 := by
  apply lratCheckerSound f512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p512
  · intro a ha; simp [p512] at ha; subst a; trivial
  · exact checked512
theorem derived512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c512 := by
  apply localUnsat_implies_entails f512 [c205, c265, c129, c219, c158] c512 unsat512 (by rfl) a
  have h0 : Entails.eval a c205 := h 204 (by decide)
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c513 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c510, some c376, some c379, some c505, some c503, some c8, some c120, some c472, some c310, some c311, some c44, some c76, some c26, some c348, some c334, some c276, some c512, some c511, some c209, some c265, some c129, some c212, some c36, some c201, some c200, some c14, some c146, some c49, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked513 : lratChecker f513 p513 = .success := by decide +kernel
theorem unsat513 : Unsatisfiable (PosFin 57) f513 := by
  apply lratCheckerSound f513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p513
  · intro a ha; simp [p513] at ha; subst a; trivial
  · exact checked513
theorem derived513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c513 := by
  apply localUnsat_implies_entails f513 [c510, c376, c379, c505, c503, c8, c120, c472, c310, c311, c44, c76, c26, c348, c334, c276, c512, c511, c209, c265, c129, c212, c36, c201, c200, c14, c146, c49] c513 unsat513 (by rfl) a
  have h0 : Entails.eval a c510 := derived510 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c505 := derived505 a h
  have h4 : Entails.eval a c503 := derived503 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c472 := derived472 a h
  have h8 : Entails.eval a c310 := h 309 (by decide)
  have h9 : Entails.eval a c311 := h 310 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c348 := h 347 (by decide)
  have h14 : Entails.eval a c334 := h 333 (by decide)
  have h15 : Entails.eval a c276 := h 275 (by decide)
  have h16 : Entails.eval a c512 := derived512 a h
  have h17 : Entails.eval a c511 := derived511 a h
  have h18 : Entails.eval a c209 := h 208 (by decide)
  have h19 : Entails.eval a c265 := h 264 (by decide)
  have h20 : Entails.eval a c129 := h 128 (by decide)
  have h21 : Entails.eval a c212 := h 211 (by decide)
  have h22 : Entails.eval a c36 := h 35 (by decide)
  have h23 : Entails.eval a c201 := h 200 (by decide)
  have h24 : Entails.eval a c200 := h 199 (by decide)
  have h25 : Entails.eval a c14 := h 13 (by decide)
  have h26 : Entails.eval a c146 := h 145 (by decide)
  have h27 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived513

end CochromaticTwenty.Certificates.B16_0_2Enumerating
