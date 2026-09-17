import MerLeanExperiment.Certificates.Z12Direct_5_4_12.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_4_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c389 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f389 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c386, some c382, some c128, some c55, some c173, some c218, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p389 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked389 : lratChecker f389 p389 = .success := by decide +kernel
theorem unsat389 : Unsatisfiable (PosFin 31) f389 := by
  apply lratCheckerSound f389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p389
  · intro a ha; simp [p389] at ha; subst a; trivial
  · exact checked389
theorem derived389 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c389 := by
  apply localUnsat_implies_entails f389 [c386, c382, c128, c55, c173, c218] c389 unsat389 (by rfl) a
  have h0 : Entails.eval a c386 := derived386 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c128 := h 127 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c173 := h 172 (by decide)
  have h5 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c390 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨2, by decide⟩, true), (⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f390 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c243, some c89, some c259, some c248, some c67, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p390 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked390 : lratChecker f390 p390 = .success := by decide +kernel
theorem unsat390 : Unsatisfiable (PosFin 31) f390 := by
  apply lratCheckerSound f390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p390
  · intro a ha; simp [p390] at ha; subst a; trivial
  · exact checked390
theorem derived390 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c390 := by
  apply localUnsat_implies_entails f390 [c243, c89, c259, c248, c67] c390 unsat390 (by rfl) a
  have h0 : Entails.eval a c243 := h 242 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c259 := h 258 (by decide)
  have h3 : Entails.eval a c248 := h 247 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c391 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f391 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c389, some c176, some c386, some c388, some c56, some c199, some c218, some c50, some c243, some c390, some c212, some c203, some c24, some c259, some c66, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p391 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked391 : lratChecker f391 p391 = .success := by decide +kernel
theorem unsat391 : Unsatisfiable (PosFin 31) f391 := by
  apply lratCheckerSound f391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p391
  · intro a ha; simp [p391] at ha; subst a; trivial
  · exact checked391
theorem derived391 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c391 := by
  apply localUnsat_implies_entails f391 [c382, c389, c176, c386, c388, c56, c199, c218, c50, c243, c390, c212, c203, c24, c259, c66] c391 unsat391 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c389 := derived389 a h
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c386 := derived386 a h
  have h4 : Entails.eval a c388 := derived388 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c243 := h 242 (by decide)
  have h10 : Entails.eval a c390 := derived390 a h
  have h11 : Entails.eval a c212 := h 211 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c259 := h 258 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c392 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f392 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c389, some c382, some c176, some c56, some c50, some c388, some c386, some c199, some c218, some c243, some c390, some c212, some c391, some c253, some c60, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p392 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked392 : lratChecker f392 p392 = .success := by decide +kernel
theorem unsat392 : Unsatisfiable (PosFin 31) f392 := by
  apply lratCheckerSound f392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p392
  · intro a ha; simp [p392] at ha; subst a; trivial
  · exact checked392
theorem derived392 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c392 := by
  apply localUnsat_implies_entails f392 [c389, c382, c176, c56, c50, c388, c386, c199, c218, c243, c390, c212, c391, c253, c60] c392 unsat392 (by rfl) a
  have h0 : Entails.eval a c389 := derived389 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c388 := derived388 a h
  have h6 : Entails.eval a c386 := derived386 a h
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c243 := h 242 (by decide)
  have h10 : Entails.eval a c390 := derived390 a h
  have h11 : Entails.eval a c212 := h 211 (by decide)
  have h12 : Entails.eval a c391 := derived391 a h
  have h13 : Entails.eval a c253 := h 252 (by decide)
  have h14 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c393 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f393 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c392, some c382, some c389, some c176, some c56, some c386, some c199, some c218, some c50, some c27, some c98, some c189, some c19, some c287, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p393 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked393 : lratChecker f393 p393 = .success := by decide +kernel
theorem unsat393 : Unsatisfiable (PosFin 31) f393 := by
  apply lratCheckerSound f393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p393
  · intro a ha; simp [p393] at ha; subst a; trivial
  · exact checked393
theorem derived393 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c393 := by
  apply localUnsat_implies_entails f393 [c392, c382, c389, c176, c56, c386, c199, c218, c50, c27, c98, c189, c19, c287] c393 unsat393 (by rfl) a
  have h0 : Entails.eval a c392 := derived392 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c389 := derived389 a h
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c386 := derived386 a h
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c189 := h 188 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c394 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f394 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c389, some c382, some c176, some c56, some c392, some c393, some c122, some c19, some c170, some c285, some c140, some c189, some c105, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p394 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked394 : lratChecker f394 p394 = .success := by decide +kernel
theorem unsat394 : Unsatisfiable (PosFin 31) f394 := by
  apply lratCheckerSound f394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p394
  · intro a ha; simp [p394] at ha; subst a; trivial
  · exact checked394
theorem derived394 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c394 := by
  apply localUnsat_implies_entails f394 [c389, c382, c176, c56, c392, c393, c122, c19, c170, c285, c140, c189, c105] c394 unsat394 (by rfl) a
  have h0 : Entails.eval a c389 := derived389 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c392 := derived392 a h
  have h5 : Entails.eval a c393 := derived393 a h
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c170 := h 169 (by decide)
  have h9 : Entails.eval a c285 := h 284 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c189 := h 188 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c395 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f395 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c388, some c394, some c54, some c386, some c382, some c56, some c199, some c218, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p395 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked395 : lratChecker f395 p395 = .success := by decide +kernel
theorem unsat395 : Unsatisfiable (PosFin 31) f395 := by
  apply lratCheckerSound f395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p395
  · intro a ha; simp [p395] at ha; subst a; trivial
  · exact checked395
theorem derived395 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c395 := by
  apply localUnsat_implies_entails f395 [c388, c394, c54, c386, c382, c56, c199, c218] c395 unsat395 (by rfl) a
  have h0 : Entails.eval a c388 := derived388 a h
  have h1 : Entails.eval a c394 := derived394 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c386 := derived386 a h
  have h4 : Entails.eval a c382 := derived382 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c396 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f396 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c388, some c394, some c54, some c395, some c221, some c218, some c389, some c386, some c122, some c139, some c80, some c133, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p396 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked396 : lratChecker f396 p396 = .success := by decide +kernel
theorem unsat396 : Unsatisfiable (PosFin 31) f396 := by
  apply lratCheckerSound f396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p396
  · intro a ha; simp [p396] at ha; subst a; trivial
  · exact checked396
theorem derived396 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c396 := by
  apply localUnsat_implies_entails f396 [c382, c388, c394, c54, c395, c221, c218, c389, c386, c122, c139, c80, c133] c396 unsat396 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c388 := derived388 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c395 := derived395 a h
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  have h7 : Entails.eval a c389 := derived389 a h
  have h8 : Entails.eval a c386 := derived386 a h
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c397 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f397 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c388, some c394, some c395, some c54, some c382, some c221, some c47, some c156, some c218, some c389, some c396, some c311, some c306, some c229, some c279, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p397 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked397 : lratChecker f397 p397 = .success := by decide +kernel
theorem unsat397 : Unsatisfiable (PosFin 31) f397 := by
  apply lratCheckerSound f397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p397
  · intro a ha; simp [p397] at ha; subst a; trivial
  · exact checked397
theorem derived397 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c397 := by
  apply localUnsat_implies_entails f397 [c388, c394, c395, c54, c382, c221, c47, c156, c218, c389, c396, c311, c306, c229, c279] c397 unsat397 (by rfl) a
  have h0 : Entails.eval a c388 := derived388 a h
  have h1 : Entails.eval a c394 := derived394 a h
  have h2 : Entails.eval a c395 := derived395 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c382 := derived382 a h
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c389 := derived389 a h
  have h10 : Entails.eval a c396 := derived396 a h
  have h11 : Entails.eval a c311 := derived311 a h
  have h12 : Entails.eval a c306 := derived306 a h
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c398 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨9, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f398 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c388, some c394, some c395, some c54, some c382, some c221, some c47, some c156, some c218, some c389, some c306, some c229, some c279, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p398 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked398 : lratChecker f398 p398 = .success := by decide +kernel
theorem unsat398 : Unsatisfiable (PosFin 31) f398 := by
  apply lratCheckerSound f398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p398
  · intro a ha; simp [p398] at ha; subst a; trivial
  · exact checked398
theorem derived398 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c398 := by
  apply localUnsat_implies_entails f398 [c388, c394, c395, c54, c382, c221, c47, c156, c218, c389, c306, c229, c279] c398 unsat398 (by rfl) a
  have h0 : Entails.eval a c388 := derived388 a h
  have h1 : Entails.eval a c394 := derived394 a h
  have h2 : Entails.eval a c395 := derived395 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c382 := derived382 a h
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c389 := derived389 a h
  have h10 : Entails.eval a c306 := derived306 a h
  have h11 : Entails.eval a c229 := h 228 (by decide)
  have h12 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c399 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f399 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c386, some c382, some c114, some c92, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p399 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked399 : lratChecker f399 p399 = .success := by decide +kernel
theorem unsat399 : Unsatisfiable (PosFin 31) f399 := by
  apply lratCheckerSound f399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p399
  · intro a ha; simp [p399] at ha; subst a; trivial
  · exact checked399
theorem derived399 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c399 := by
  apply localUnsat_implies_entails f399 [c386, c382, c114, c92] c399 unsat399 (by rfl) a
  have h0 : Entails.eval a c386 := derived386 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c400 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f400 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c397, some c382, some c394, some c395, some c221, some c388, some c398, some c15, some c399, some c204, some c211, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p400 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked400 : lratChecker f400 p400 = .success := by decide +kernel
theorem unsat400 : Unsatisfiable (PosFin 31) f400 := by
  apply lratCheckerSound f400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p400
  · intro a ha; simp [p400] at ha; subst a; trivial
  · exact checked400
theorem derived400 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c400 := by
  apply localUnsat_implies_entails f400 [c397, c382, c394, c395, c221, c388, c398, c15, c399, c204, c211] c400 unsat400 (by rfl) a
  have h0 : Entails.eval a c397 := derived397 a h
  have h1 : Entails.eval a c382 := derived382 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c395 := derived395 a h
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c388 := derived388 a h
  have h6 : Entails.eval a c398 := derived398 a h
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c399 := derived399 a h
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c401 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f401 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c382, some c388, some c389, some c394, some c54, some c395, some c221, some c218, some c47, some c397, some c400, some c160, some c44, some c185, some c187, some c165, some c164, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p401 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked401 : lratChecker f401 p401 = .success := by decide +kernel
theorem unsat401 : Unsatisfiable (PosFin 31) f401 := by
  apply lratCheckerSound f401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p401
  · intro a ha; simp [p401] at ha; subst a; trivial
  · exact checked401
theorem derived401 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c401 := by
  apply localUnsat_implies_entails f401 [c382, c388, c389, c394, c54, c395, c221, c218, c47, c397, c400, c160, c44, c185, c187, c165, c164] c401 unsat401 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c388 := derived388 a h
  have h2 : Entails.eval a c389 := derived389 a h
  have h3 : Entails.eval a c394 := derived394 a h
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c395 := derived395 a h
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c397 := derived397 a h
  have h10 : Entails.eval a c400 := derived400 a h
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c187 := h 186 (by decide)
  have h15 : Entails.eval a c165 := h 164 (by decide)
  have h16 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c402 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f402 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c196, some c200, some c54, some c127, some c242, some c173, some c268, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p402 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked402 : lratChecker f402 p402 = .success := by decide +kernel
theorem unsat402 : Unsatisfiable (PosFin 31) f402 := by
  apply lratCheckerSound f402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p402
  · intro a ha; simp [p402] at ha; subst a; trivial
  · exact checked402
theorem derived402 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c402 := by
  apply localUnsat_implies_entails f402 [c401, c196, c200, c54, c127, c242, c173, c268] c402 unsat402 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c403 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f403 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c221, some c127, some c55, some c130, some c53, some c48, some c354, some c243, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p403 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked403 : lratChecker f403 p403 = .success := by decide +kernel
theorem unsat403 : Unsatisfiable (PosFin 31) f403 := by
  apply lratCheckerSound f403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p403
  · intro a ha; simp [p403] at ha; subst a; trivial
  · exact checked403
theorem derived403 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c403 := by
  apply localUnsat_implies_entails f403 [c401, c221, c127, c55, c130, c53, c48, c354, c243] c403 unsat403 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c354 := derived354 a h
  have h8 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c404 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f404 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c402, some c403, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p404 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked404 : lratChecker f404 p404 = .success := by decide +kernel
theorem unsat404 : Unsatisfiable (PosFin 31) f404 := by
  apply lratCheckerSound f404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p404
  · intro a ha; simp [p404] at ha; subst a; trivial
  · exact checked404
theorem derived404 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c404 := by
  apply localUnsat_implies_entails f404 [c402, c403] c404 unsat404 (by rfl) a
  have h0 : Entails.eval a c402 := derived402 a h
  have h1 : Entails.eval a c403 := derived403 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c405 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f405 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c404, some c127, some c269, some c55, some c52, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p405 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked405 : lratChecker f405 p405 = .success := by decide +kernel
theorem unsat405 : Unsatisfiable (PosFin 31) f405 := by
  apply lratCheckerSound f405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p405
  · intro a ha; simp [p405] at ha; subst a; trivial
  · exact checked405
theorem derived405 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c405 := by
  apply localUnsat_implies_entails f405 [c401, c404, c127, c269, c55, c52] c405 unsat405 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c404 := derived404 a h
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c406 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f406 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c404, some c405, some c152, some c270, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p406 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked406 : lratChecker f406 p406 = .success := by decide +kernel
theorem unsat406 : Unsatisfiable (PosFin 31) f406 := by
  apply lratCheckerSound f406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p406
  · intro a ha; simp [p406] at ha; subst a; trivial
  · exact checked406
theorem derived406 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c406 := by
  apply localUnsat_implies_entails f406 [c401, c404, c405, c152, c270] c406 unsat406 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c404 := derived404 a h
  have h2 : Entails.eval a c405 := derived405 a h
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c407 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f407 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c406, some c404, some c53, some c245, some c153, some c51, some c177, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p407 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked407 : lratChecker f407 p407 = .success := by decide +kernel
theorem unsat407 : Unsatisfiable (PosFin 31) f407 := by
  apply lratCheckerSound f407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p407
  · intro a ha; simp [p407] at ha; subst a; trivial
  · exact checked407
theorem derived407 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c407 := by
  apply localUnsat_implies_entails f407 [c401, c406, c404, c53, c245, c153, c51, c177] c407 unsat407 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c406 := derived406 a h
  have h2 : Entails.eval a c404 := derived404 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c153 := h 152 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c408 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f408 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c196, some c407, some c54, some c127, some c242, some c173, some c268, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p408 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked408 : lratChecker f408 p408 = .success := by decide +kernel
theorem unsat408 : Unsatisfiable (PosFin 31) f408 := by
  apply lratCheckerSound f408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p408
  · intro a ha; simp [p408] at ha; subst a; trivial
  · exact checked408
theorem derived408 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c408 := by
  apply localUnsat_implies_entails f408 [c401, c196, c407, c54, c127, c242, c173, c268] c408 unsat408 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c407 := derived407 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c409 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f409 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c406, some c408, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p409 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked409 : lratChecker f409 p409 = .success := by decide +kernel
theorem unsat409 : Unsatisfiable (PosFin 31) f409 := by
  apply lratCheckerSound f409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p409
  · intro a ha; simp [p409] at ha; subst a; trivial
  · exact checked409
theorem derived409 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c409 := by
  apply localUnsat_implies_entails f409 [c406, c408] c409 unsat409 (by rfl) a
  have h0 : Entails.eval a c406 := derived406 a h
  have h1 : Entails.eval a c408 := derived408 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c410 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨28, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f410 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c401, some c305, some c242, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p410 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked410 : lratChecker f410 p410 = .success := by decide +kernel
theorem unsat410 : Unsatisfiable (PosFin 31) f410 := by
  apply lratCheckerSound f410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p410
  · intro a ha; simp [p410] at ha; subst a; trivial
  · exact checked410
theorem derived410 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c410 := by
  apply localUnsat_implies_entails f410 [c409, c401, c305, c242] c410 unsat410 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c401 := derived401 a h
  have h2 : Entails.eval a c305 := derived305 a h
  have h3 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c411 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨21, by decide⟩, false), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f411 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c409, some c410, some c241, some c57, some c354, some c47, some c177, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p411 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked411 : lratChecker f411 p411 = .success := by decide +kernel
theorem unsat411 : Unsatisfiable (PosFin 31) f411 := by
  apply lratCheckerSound f411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p411
  · intro a ha; simp [p411] at ha; subst a; trivial
  · exact checked411
theorem derived411 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c411 := by
  apply localUnsat_implies_entails f411 [c401, c409, c410, c241, c57, c354, c47, c177] c411 unsat411 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c409 := derived409 a h
  have h2 : Entails.eval a c410 := derived410 a h
  have h3 : Entails.eval a c241 := h 240 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c354 := derived354 a h
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c412 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨2, by decide⟩, false), (⟨21, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f412 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c286, some c81, some c195, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p412 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked412 : lratChecker f412 p412 = .success := by decide +kernel
theorem unsat412 : Unsatisfiable (PosFin 31) f412 := by
  apply lratCheckerSound f412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p412
  · intro a ha; simp [p412] at ha; subst a; trivial
  · exact checked412
theorem derived412 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c412 := by
  apply localUnsat_implies_entails f412 [c286, c81, c195] c412 unsat412 (by rfl) a
  have h0 : Entails.eval a c286 := h 285 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c413 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, true), (⟨19, by decide⟩, true), (⟨21, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f413 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c401, some c370, some c3, some c40, some c412, some c81, some c210, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p413 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked413 : lratChecker f413 p413 = .success := by decide +kernel
theorem unsat413 : Unsatisfiable (PosFin 31) f413 := by
  apply lratCheckerSound f413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p413
  · intro a ha; simp [p413] at ha; subst a; trivial
  · exact checked413
theorem derived413 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c413 := by
  apply localUnsat_implies_entails f413 [c409, c401, c370, c3, c40, c412, c81, c210] c413 unsat413 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c401 := derived401 a h
  have h2 : Entails.eval a c370 := derived370 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c412 := derived412 a h
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c414 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨19, by decide⟩, true), (⟨28, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f414 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c126, some c281, some c282, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p414 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked414 : lratChecker f414 p414 = .success := by decide +kernel
theorem unsat414 : Unsatisfiable (PosFin 31) f414 := by
  apply lratCheckerSound f414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p414
  · intro a ha; simp [p414] at ha; subst a; trivial
  · exact checked414
theorem derived414 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c414 := by
  apply localUnsat_implies_entails f414 [c126, c281, c282] c414 unsat414 (by rfl) a
  have h0 : Entails.eval a c126 := h 125 (by decide)
  have h1 : Entails.eval a c281 := h 280 (by decide)
  have h2 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c415 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f415 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c401, some c411, some c241, some c57, some c354, some c47, some c49, some c413, some c17, some c71, some c414, some c105, some c255, some c281, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p415 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked415 : lratChecker f415 p415 = .success := by decide +kernel
theorem unsat415 : Unsatisfiable (PosFin 31) f415 := by
  apply lratCheckerSound f415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p415
  · intro a ha; simp [p415] at ha; subst a; trivial
  · exact checked415
theorem derived415 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c415 := by
  apply localUnsat_implies_entails f415 [c409, c401, c411, c241, c57, c354, c47, c49, c413, c17, c71, c414, c105, c255, c281] c415 unsat415 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c401 := derived401 a h
  have h2 : Entails.eval a c411 := derived411 a h
  have h3 : Entails.eval a c241 := h 240 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c354 := derived354 a h
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c413 := derived413 a h
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c414 := derived414 a h
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c255 := h 254 (by decide)
  have h14 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c416 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f416 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c409, some c411, some c415, some c242, some c57, some c198, some c153, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p416 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked416 : lratChecker f416 p416 = .success := by decide +kernel
theorem unsat416 : Unsatisfiable (PosFin 31) f416 := by
  apply lratCheckerSound f416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p416
  · intro a ha; simp [p416] at ha; subst a; trivial
  · exact checked416
theorem derived416 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c416 := by
  apply localUnsat_implies_entails f416 [c401, c409, c411, c415, c242, c57, c198, c153] c416 unsat416 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c409 := derived409 a h
  have h2 : Entails.eval a c411 := derived411 a h
  have h3 : Entails.eval a c415 := derived415 a h
  have h4 : Entails.eval a c242 := h 241 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c417 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f417 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c401, some c416, some c154, some c57, some c50, some c241, some c305, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p417 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked417 : lratChecker f417 p417 = .success := by decide +kernel
theorem unsat417 : Unsatisfiable (PosFin 31) f417 := by
  apply lratCheckerSound f417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p417
  · intro a ha; simp [p417] at ha; subst a; trivial
  · exact checked417
theorem derived417 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c417 := by
  apply localUnsat_implies_entails f417 [c409, c401, c416, c154, c57, c50, c241, c305] c417 unsat417 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c401 := derived401 a h
  have h2 : Entails.eval a c416 := derived416 a h
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c241 := h 240 (by decide)
  have h7 : Entails.eval a c305 := derived305 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c418 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨22, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f418 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c401, some c368, some c51, some c241, some c54, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p418 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked418 : lratChecker f418 p418 = .success := by decide +kernel
theorem unsat418 : Unsatisfiable (PosFin 31) f418 := by
  apply lratCheckerSound f418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p418
  · intro a ha; simp [p418] at ha; subst a; trivial
  · exact checked418
theorem derived418 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c418 := by
  apply localUnsat_implies_entails f418 [c409, c401, c368, c51, c241, c54] c418 unsat418 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c401 := derived401 a h
  have h2 : Entails.eval a c368 := derived368 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c419 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f419 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c401, some c219, some c242, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p419 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked419 : lratChecker f419 p419 = .success := by decide +kernel
theorem unsat419 : Unsatisfiable (PosFin 31) f419 := by
  apply lratCheckerSound f419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p419
  · intro a ha; simp [p419] at ha; subst a; trivial
  · exact checked419
theorem derived419 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c419 := by
  apply localUnsat_implies_entails f419 [c409, c401, c219, c242] c419 unsat419 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c401 := derived401 a h
  have h2 : Entails.eval a c219 := h 218 (by decide)
  have h3 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c420 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f420 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c409, some c418, some c419, some c241, some c57, some c131, some c49, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p420 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked420 : lratChecker f420 p420 = .success := by decide +kernel
theorem unsat420 : Unsatisfiable (PosFin 31) f420 := by
  apply lratCheckerSound f420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p420
  · intro a ha; simp [p420] at ha; subst a; trivial
  · exact checked420
theorem derived420 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c420 := by
  apply localUnsat_implies_entails f420 [c401, c409, c418, c419, c241, c57, c131, c49] c420 unsat420 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c409 := derived409 a h
  have h2 : Entails.eval a c418 := derived418 a h
  have h3 : Entails.eval a c419 := derived419 a h
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c131 := h 130 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c421 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f421 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c417, some c420, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p421 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked421 : lratChecker f421 p421 = .success := by decide +kernel
theorem unsat421 : Unsatisfiable (PosFin 31) f421 := by
  apply lratCheckerSound f421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p421
  · intro a ha; simp [p421] at ha; subst a; trivial
  · exact checked421
theorem derived421 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c421 := by
  apply localUnsat_implies_entails f421 [c417, c420] c421 unsat421 (by rfl) a
  have h0 : Entails.eval a c417 := derived417 a h
  have h1 : Entails.eval a c420 := derived420 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c422 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f422 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c409, some c152, some c57, some c368, some c174, some c197, some c55, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p422 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked422 : lratChecker f422 p422 = .success := by decide +kernel
theorem unsat422 : Unsatisfiable (PosFin 31) f422 := by
  apply lratCheckerSound f422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p422
  · intro a ha; simp [p422] at ha; subst a; trivial
  · exact checked422
theorem derived422 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c422 := by
  apply localUnsat_implies_entails f422 [c401, c409, c152, c57, c368, c174, c197, c55] c422 unsat422 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c409 := derived409 a h
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c368 := derived368 a h
  have h5 : Entails.eval a c174 := h 173 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c423 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f423 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c354, some c57, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p423 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked423 : lratChecker f423 p423 = .success := by decide +kernel
theorem unsat423 : Unsatisfiable (PosFin 31) f423 := by
  apply lratCheckerSound f423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p423
  · intro a ha; simp [p423] at ha; subst a; trivial
  · exact checked423
theorem derived423 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c423 := by
  apply localUnsat_implies_entails f423 [c409, c354, c57] c423 unsat423 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c354 := derived354 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c424 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f424 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c130, some c423, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p424 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked424 : lratChecker f424 p424 = .success := by decide +kernel
theorem unsat424 : Unsatisfiable (PosFin 31) f424 := by
  apply lratCheckerSound f424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p424
  · intro a ha; simp [p424] at ha; subst a; trivial
  · exact checked424
theorem derived424 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c424 := by
  apply localUnsat_implies_entails f424 [c401, c130, c423] c424 unsat424 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c130 := h 129 (by decide)
  have h2 : Entails.eval a c423 := derived423 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c425 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f425 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c401, some c421, some c422, some c424, some c55, some c110, some c154, some c24, some c370, some c57, some c59, some c50, some c51, some c29, some c2, some c39, some c166, some c61, some c145, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p425 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked425 : lratChecker f425 p425 = .success := by decide +kernel
theorem unsat425 : Unsatisfiable (PosFin 31) f425 := by
  apply lratCheckerSound f425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p425
  · intro a ha; simp [p425] at ha; subst a; trivial
  · exact checked425
theorem derived425 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c425 := by
  apply localUnsat_implies_entails f425 [c409, c401, c421, c422, c424, c55, c110, c154, c24, c370, c57, c59, c50, c51, c29, c2, c39, c166, c61, c145] c425 unsat425 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c401 := derived401 a h
  have h2 : Entails.eval a c421 := derived421 a h
  have h3 : Entails.eval a c422 := derived422 a h
  have h4 : Entails.eval a c424 := derived424 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c370 := derived370 a h
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c39 := h 38 (by decide)
  have h17 : Entails.eval a c166 := h 165 (by decide)
  have h18 : Entails.eval a c61 := h 60 (by decide)
  have h19 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c426 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f426 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c425, some c401, some c422, some c424, some c55, some c154, some c57, some c93, some c262, some c161, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p426 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked426 : lratChecker f426 p426 = .success := by decide +kernel
theorem unsat426 : Unsatisfiable (PosFin 31) f426 := by
  apply lratCheckerSound f426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p426
  · intro a ha; simp [p426] at ha; subst a; trivial
  · exact checked426
theorem derived426 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c426 := by
  apply localUnsat_implies_entails f426 [c409, c425, c401, c422, c424, c55, c154, c57, c93, c262, c161] c426 unsat426 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c425 := derived425 a h
  have h2 : Entails.eval a c401 := derived401 a h
  have h3 : Entails.eval a c422 := derived422 a h
  have h4 : Entails.eval a c424 := derived424 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c262 := h 261 (by decide)
  have h10 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c427 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f427 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c425, some c401, some c422, some c424, some c55, some c154, some c57, some c51, some c426, some c256, some c115, some c161, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p427 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked427 : lratChecker f427 p427 = .success := by decide +kernel
theorem unsat427 : Unsatisfiable (PosFin 31) f427 := by
  apply lratCheckerSound f427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p427
  · intro a ha; simp [p427] at ha; subst a; trivial
  · exact checked427
theorem derived427 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c427 := by
  apply localUnsat_implies_entails f427 [c409, c425, c401, c422, c424, c55, c154, c57, c51, c426, c256, c115, c161] c427 unsat427 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c425 := derived425 a h
  have h2 : Entails.eval a c401 := derived401 a h
  have h3 : Entails.eval a c422 := derived422 a h
  have h4 : Entails.eval a c424 := derived424 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c426 := derived426 a h
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c428 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f428 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c425, some c409, some c422, some c424, some c55, some c154, some c57, some c50, some c305, some c427, some c251, some c272, some c39, some c44, some c68, some c228, some c191, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p428 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked428 : lratChecker f428 p428 = .success := by decide +kernel
theorem unsat428 : Unsatisfiable (PosFin 31) f428 := by
  apply lratCheckerSound f428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p428
  · intro a ha; simp [p428] at ha; subst a; trivial
  · exact checked428
theorem derived428 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c428 := by
  apply localUnsat_implies_entails f428 [c401, c425, c409, c422, c424, c55, c154, c57, c50, c305, c427, c251, c272, c39, c44, c68, c228, c191] c428 unsat428 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c425 := derived425 a h
  have h2 : Entails.eval a c409 := derived409 a h
  have h3 : Entails.eval a c422 := derived422 a h
  have h4 : Entails.eval a c424 := derived424 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c305 := derived305 a h
  have h10 : Entails.eval a c427 := derived427 a h
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c272 := h 271 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c228 := h 227 (by decide)
  have h17 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c429 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f429 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c425, some c422, some c424, some c428, some c370, some c13, some c111, some c72, some c5, some c74, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p429 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked429 : lratChecker f429 p429 = .success := by decide +kernel
theorem unsat429 : Unsatisfiable (PosFin 31) f429 := by
  apply lratCheckerSound f429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p429
  · intro a ha; simp [p429] at ha; subst a; trivial
  · exact checked429
theorem derived429 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c429 := by
  apply localUnsat_implies_entails f429 [c409, c425, c422, c424, c428, c370, c13, c111, c72, c5, c74] c429 unsat429 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c425 := derived425 a h
  have h2 : Entails.eval a c422 := derived422 a h
  have h3 : Entails.eval a c424 := derived424 a h
  have h4 : Entails.eval a c428 := derived428 a h
  have h5 : Entails.eval a c370 := derived370 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c430 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f430 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c429, some c420, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p430 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked430 : lratChecker f430 p430 = .success := by decide +kernel
theorem unsat430 : Unsatisfiable (PosFin 31) f430 := by
  apply lratCheckerSound f430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p430
  · intro a ha; simp [p430] at ha; subst a; trivial
  · exact checked430
theorem derived430 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c430 := by
  apply localUnsat_implies_entails f430 [c429, c420] c430 unsat430 (by rfl) a
  have h0 : Entails.eval a c429 := derived429 a h
  have h1 : Entails.eval a c420 := derived420 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c431 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f431 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c430, some c424, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p431 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked431 : lratChecker f431 p431 = .success := by decide +kernel
theorem unsat431 : Unsatisfiable (PosFin 31) f431 := by
  apply lratCheckerSound f431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p431
  · intro a ha; simp [p431] at ha; subst a; trivial
  · exact checked431
theorem derived431 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c431 := by
  apply localUnsat_implies_entails f431 [c430, c424] c431 unsat431 (by rfl) a
  have h0 : Entails.eval a c430 := derived430 a h
  have h1 : Entails.eval a c424 := derived424 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c432 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f432 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c409, some c429, some c241, some c198, some c305, some c153, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p432 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked432 : lratChecker f432 p432 = .success := by decide +kernel
theorem unsat432 : Unsatisfiable (PosFin 31) f432 := by
  apply lratCheckerSound f432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p432
  · intro a ha; simp [p432] at ha; subst a; trivial
  · exact checked432
theorem derived432 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c432 := by
  apply localUnsat_implies_entails f432 [c401, c409, c429, c241, c198, c305, c153] c432 unsat432 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c409 := derived409 a h
  have h2 : Entails.eval a c429 := derived429 a h
  have h3 : Entails.eval a c241 := h 240 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c305 := derived305 a h
  have h6 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c433 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f433 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c430, some c401, some c242, some c154, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p433 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked433 : lratChecker f433 p433 = .success := by decide +kernel
theorem unsat433 : Unsatisfiable (PosFin 31) f433 := by
  apply lratCheckerSound f433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p433
  · intro a ha; simp [p433] at ha; subst a; trivial
  · exact checked433
theorem derived433 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c433 := by
  apply localUnsat_implies_entails f433 [c430, c401, c242, c154] c433 unsat433 (by rfl) a
  have h0 : Entails.eval a c430 := derived430 a h
  have h1 : Entails.eval a c401 := derived401 a h
  have h2 : Entails.eval a c242 := h 241 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c434 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f434 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c401, some c429, some c241, some c432, some c433, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p434 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked434 : lratChecker f434 p434 = .success := by decide +kernel
theorem unsat434 : Unsatisfiable (PosFin 31) f434 := by
  apply lratCheckerSound f434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p434
  · intro a ha; simp [p434] at ha; subst a; trivial
  · exact checked434
theorem derived434 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c434 := by
  apply localUnsat_implies_entails f434 [c401, c429, c241, c432, c433] c434 unsat434 (by rfl) a
  have h0 : Entails.eval a c401 := derived401 a h
  have h1 : Entails.eval a c429 := derived429 a h
  have h2 : Entails.eval a c241 := h 240 (by decide)
  have h3 : Entails.eval a c432 := derived432 a h
  have h4 : Entails.eval a c433 := derived433 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c435 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f435 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c434, some c409, some c57, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p435 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked435 : lratChecker f435 p435 = .success := by decide +kernel
theorem unsat435 : Unsatisfiable (PosFin 31) f435 := by
  apply lratCheckerSound f435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p435
  · intro a ha; simp [p435] at ha; subst a; trivial
  · exact checked435
theorem derived435 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c435 := by
  apply localUnsat_implies_entails f435 [c434, c409, c57] c435 unsat435 (by rfl) a
  have h0 : Entails.eval a c434 := derived434 a h
  have h1 : Entails.eval a c409 := derived409 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c436 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f436 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c434, some c425, some c409, some c31, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p436 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked436 : lratChecker f436 p436 = .success := by decide +kernel
theorem unsat436 : Unsatisfiable (PosFin 31) f436 := by
  apply lratCheckerSound f436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p436
  · intro a ha; simp [p436] at ha; subst a; trivial
  · exact checked436
theorem derived436 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c436 := by
  apply localUnsat_implies_entails f436 [c434, c425, c409, c31] c436 unsat436 (by rfl) a
  have h0 : Entails.eval a c434 := derived434 a h
  have h1 : Entails.eval a c425 := derived425 a h
  have h2 : Entails.eval a c409 := derived409 a h
  have h3 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c437 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f437 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c435, some c433, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p437 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked437 : lratChecker f437 p437 = .success := by decide +kernel
theorem unsat437 : Unsatisfiable (PosFin 31) f437 := by
  apply lratCheckerSound f437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p437
  · intro a ha; simp [p437] at ha; subst a; trivial
  · exact checked437
theorem derived437 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c437 := by
  apply localUnsat_implies_entails f437 [c435, c433] c437 unsat437 (by rfl) a
  have h0 : Entails.eval a c435 := derived435 a h
  have h1 : Entails.eval a c433 := derived433 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c438 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f438 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c435, some c429, some c437, some c47, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p438 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked438 : lratChecker f438 p438 = .success := by decide +kernel
theorem unsat438 : Unsatisfiable (PosFin 31) f438 := by
  apply lratCheckerSound f438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p438
  · intro a ha; simp [p438] at ha; subst a; trivial
  · exact checked438
theorem derived438 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c438 := by
  apply localUnsat_implies_entails f438 [c435, c429, c437, c47] c438 unsat438 (by rfl) a
  have h0 : Entails.eval a c435 := derived435 a h
  have h1 : Entails.eval a c429 := derived429 a h
  have h2 : Entails.eval a c437 := derived437 a h
  have h3 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c439 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f439 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c438, some c425, some c434, some c27, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p439 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked439 : lratChecker f439 p439 = .success := by decide +kernel
theorem unsat439 : Unsatisfiable (PosFin 31) f439 := by
  apply lratCheckerSound f439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p439
  · intro a ha; simp [p439] at ha; subst a; trivial
  · exact checked439
theorem derived439 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c439 := by
  apply localUnsat_implies_entails f439 [c438, c425, c434, c27] c439 unsat439 (by rfl) a
  have h0 : Entails.eval a c438 := derived438 a h
  have h1 : Entails.eval a c425 := derived425 a h
  have h2 : Entails.eval a c434 := derived434 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c440 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f440 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c439, some c429, some c437, some c23, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p440 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked440 : lratChecker f440 p440 = .success := by decide +kernel
theorem unsat440 : Unsatisfiable (PosFin 31) f440 := by
  apply lratCheckerSound f440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p440
  · intro a ha; simp [p440] at ha; subst a; trivial
  · exact checked440
theorem derived440 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c440 := by
  apply localUnsat_implies_entails f440 [c439, c429, c437, c23] c440 unsat440 (by rfl) a
  have h0 : Entails.eval a c439 := derived439 a h
  have h1 : Entails.eval a c429 := derived429 a h
  have h2 : Entails.eval a c437 := derived437 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c441 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f441 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c440, some c425, some c409, some c65, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p441 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked441 : lratChecker f441 p441 = .success := by decide +kernel
theorem unsat441 : Unsatisfiable (PosFin 31) f441 := by
  apply lratCheckerSound f441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p441
  · intro a ha; simp [p441] at ha; subst a; trivial
  · exact checked441
theorem derived441 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c441 := by
  apply localUnsat_implies_entails f441 [c440, c425, c409, c65] c441 unsat441 (by rfl) a
  have h0 : Entails.eval a c440 := derived440 a h
  have h1 : Entails.eval a c425 := derived425 a h
  have h2 : Entails.eval a c409 := derived409 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c442 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f442 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c440, some c431, some c425, some c114, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p442 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked442 : lratChecker f442 p442 = .success := by decide +kernel
theorem unsat442 : Unsatisfiable (PosFin 31) f442 := by
  apply lratCheckerSound f442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p442
  · intro a ha; simp [p442] at ha; subst a; trivial
  · exact checked442
theorem derived442 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c442 := by
  apply localUnsat_implies_entails f442 [c440, c431, c425, c114] c442 unsat442 (by rfl) a
  have h0 : Entails.eval a c440 := derived440 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c425 := derived425 a h
  have h3 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c443 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f443 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c441, some c442, some c436, some c5]
def p443 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked443 : lratChecker f443 p443 = .success := by decide +kernel
theorem unsat443 : Unsatisfiable (PosFin 31) f443 := by
  apply lratCheckerSound f443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p443
  · intro a ha; simp [p443] at ha; subst a; trivial
  · exact checked443
theorem derived443 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c443 := by
  apply localUnsat_implies_entails f443 [c441, c442, c436, c5] c443 unsat443 (by rfl) a
  have h0 : Entails.eval a c441 := derived441 a h
  have h1 : Entails.eval a c442 := derived442 a h
  have h2 : Entails.eval a c436 := derived436 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived443

end CochromaticTwenty.Certificates.Z12Direct_5_4_12
