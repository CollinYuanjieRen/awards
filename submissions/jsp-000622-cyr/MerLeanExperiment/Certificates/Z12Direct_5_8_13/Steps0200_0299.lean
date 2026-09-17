import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Steps0100_0199

/-! Generated from the actual pinned z12direct_5_8_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1103 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1103 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1090, some c1064, some c1001, some c1101, some c483, some c79, some c89, some c840, some c33, some c902, some c298, some c822, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1103 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1103 : lratChecker f1103 p1103 = .success := by decide +kernel
theorem unsat1103 : Unsatisfiable (PosFin 31) f1103 := by
  apply lratCheckerSound f1103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1103
  · intro a ha; simp [p1103] at ha; subst a; trivial
  · exact checked1103
theorem derived1103 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1103 := by
  apply localUnsat_implies_entails f1103 [c1090, c1064, c1001, c1101, c483, c79, c89, c840, c33, c902, c298, c822] c1103 unsat1103 (by rfl) a
  have h0 : Entails.eval a c1090 := derived1090 a h
  have h1 : Entails.eval a c1064 := derived1064 a h
  have h2 : Entails.eval a c1001 := derived1001 a h
  have h3 : Entails.eval a c1101 := derived1101 a h
  have h4 : Entails.eval a c483 := h 482 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c840 := h 839 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c902 := h 901 (by decide)
  have h10 : Entails.eval a c298 := h 297 (by decide)
  have h11 : Entails.eval a c822 := h 821 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1104 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1104 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1103, some c1102, some c1100, some c1090, some c1064, some c1001, some c89, some c47, some c33, some c504, some c287, some c258, some c775, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1104 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1104 : lratChecker f1104 p1104 = .success := by decide +kernel
theorem unsat1104 : Unsatisfiable (PosFin 31) f1104 := by
  apply lratCheckerSound f1104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1104
  · intro a ha; simp [p1104] at ha; subst a; trivial
  · exact checked1104
theorem derived1104 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1104 := by
  apply localUnsat_implies_entails f1104 [c1103, c1102, c1100, c1090, c1064, c1001, c89, c47, c33, c504, c287, c258, c775] c1104 unsat1104 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c1102 := derived1102 a h
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c1090 := derived1090 a h
  have h4 : Entails.eval a c1064 := derived1064 a h
  have h5 : Entails.eval a c1001 := derived1001 a h
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c504 := h 503 (by decide)
  have h10 : Entails.eval a c287 := h 286 (by decide)
  have h11 : Entails.eval a c258 := h 257 (by decide)
  have h12 : Entails.eval a c775 := h 774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1105 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1105 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1104, some c1103, some c1102, some c1100, some c1090, some c1001, some c40, some c2, some c266, some c54, some c760, some c842, some c251, some c504, some c166, some c646, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1105 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1105 : lratChecker f1105 p1105 = .success := by decide +kernel
theorem unsat1105 : Unsatisfiable (PosFin 31) f1105 := by
  apply lratCheckerSound f1105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1105
  · intro a ha; simp [p1105] at ha; subst a; trivial
  · exact checked1105
theorem derived1105 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1105 := by
  apply localUnsat_implies_entails f1105 [c1104, c1103, c1102, c1100, c1090, c1001, c40, c2, c266, c54, c760, c842, c251, c504, c166, c646] c1105 unsat1105 (by rfl) a
  have h0 : Entails.eval a c1104 := derived1104 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c1102 := derived1102 a h
  have h3 : Entails.eval a c1100 := derived1100 a h
  have h4 : Entails.eval a c1090 := derived1090 a h
  have h5 : Entails.eval a c1001 := derived1001 a h
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c760 := h 759 (by decide)
  have h11 : Entails.eval a c842 := h 841 (by decide)
  have h12 : Entails.eval a c251 := h 250 (by decide)
  have h13 : Entails.eval a c504 := h 503 (by decide)
  have h14 : Entails.eval a c166 := h 165 (by decide)
  have h15 : Entails.eval a c646 := h 645 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1106 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1106 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1064, some c1001, some c1102, some c1104, some c1105, some c33, some c286, some c251, some c831, some c22, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1106 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1106 : lratChecker f1106 p1106 = .success := by decide +kernel
theorem unsat1106 : Unsatisfiable (PosFin 31) f1106 := by
  apply lratCheckerSound f1106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1106
  · intro a ha; simp [p1106] at ha; subst a; trivial
  · exact checked1106
theorem derived1106 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1106 := by
  apply localUnsat_implies_entails f1106 [c1064, c1001, c1102, c1104, c1105, c33, c286, c251, c831, c22] c1106 unsat1106 (by rfl) a
  have h0 : Entails.eval a c1064 := derived1064 a h
  have h1 : Entails.eval a c1001 := derived1001 a h
  have h2 : Entails.eval a c1102 := derived1102 a h
  have h3 : Entails.eval a c1104 := derived1104 a h
  have h4 : Entails.eval a c1105 := derived1105 a h
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c286 := h 285 (by decide)
  have h7 : Entails.eval a c251 := h 250 (by decide)
  have h8 : Entails.eval a c831 := h 830 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1107 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1107 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c727, some c890, some c338, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1107 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1107 : lratChecker f1107 p1107 = .success := by decide +kernel
theorem unsat1107 : Unsatisfiable (PosFin 31) f1107 := by
  apply lratCheckerSound f1107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1107
  · intro a ha; simp [p1107] at ha; subst a; trivial
  · exact checked1107
theorem derived1107 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1107 := by
  apply localUnsat_implies_entails f1107 [c727, c890, c338] c1107 unsat1107 (by rfl) a
  have h0 : Entails.eval a c727 := h 726 (by decide)
  have h1 : Entails.eval a c890 := h 889 (by decide)
  have h2 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1108 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨22, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1108 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c685, some c1107, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1108 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1108 : lratChecker f1108 p1108 = .success := by decide +kernel
theorem unsat1108 : Unsatisfiable (PosFin 31) f1108 := by
  apply lratCheckerSound f1108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1108
  · intro a ha; simp [p1108] at ha; subst a; trivial
  · exact checked1108
theorem derived1108 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1108 := by
  apply localUnsat_implies_entails f1108 [c685, c1107] c1108 unsat1108 (by rfl) a
  have h0 : Entails.eval a c685 := h 684 (by decide)
  have h1 : Entails.eval a c1107 := derived1107 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1109 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1109 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1090, some c1064, some c1001, some c1106, some c1108, some c525, some c79, some c89, some c882, some c33, some c258, some c885, some c293, some c350, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1109 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1109 : lratChecker f1109 p1109 = .success := by decide +kernel
theorem unsat1109 : Unsatisfiable (PosFin 31) f1109 := by
  apply lratCheckerSound f1109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1109
  · intro a ha; simp [p1109] at ha; subst a; trivial
  · exact checked1109
theorem derived1109 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1109 := by
  apply localUnsat_implies_entails f1109 [c1090, c1064, c1001, c1106, c1108, c525, c79, c89, c882, c33, c258, c885, c293, c350] c1109 unsat1109 (by rfl) a
  have h0 : Entails.eval a c1090 := derived1090 a h
  have h1 : Entails.eval a c1064 := derived1064 a h
  have h2 : Entails.eval a c1001 := derived1001 a h
  have h3 : Entails.eval a c1106 := derived1106 a h
  have h4 : Entails.eval a c1108 := derived1108 a h
  have h5 : Entails.eval a c525 := h 524 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c882 := h 881 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c885 := h 884 (by decide)
  have h12 : Entails.eval a c293 := h 292 (by decide)
  have h13 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1110 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨22, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1110 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c525, some c79, some c144, some c882, some c255, some c864, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1110 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1110 : lratChecker f1110 p1110 = .success := by decide +kernel
theorem unsat1110 : Unsatisfiable (PosFin 31) f1110 := by
  apply lratCheckerSound f1110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1110
  · intro a ha; simp [p1110] at ha; subst a; trivial
  · exact checked1110
theorem derived1110 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1110 := by
  apply localUnsat_implies_entails f1110 [c525, c79, c144, c882, c255, c864] c1110 unsat1110 (by rfl) a
  have h0 : Entails.eval a c525 := h 524 (by decide)
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c144 := h 143 (by decide)
  have h3 : Entails.eval a c882 := h 881 (by decide)
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c864 := h 863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1111 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1111 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1109, some c1090, some c1064, some c79, some c144, some c287, some c255, some c20, some c864, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1111 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1111 : lratChecker f1111 p1111 = .success := by decide +kernel
theorem unsat1111 : Unsatisfiable (PosFin 31) f1111 := by
  apply lratCheckerSound f1111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1111
  · intro a ha; simp [p1111] at ha; subst a; trivial
  · exact checked1111
theorem derived1111 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1111 := by
  apply localUnsat_implies_entails f1111 [c1109, c1090, c1064, c79, c144, c287, c255, c20, c864] c1111 unsat1111 (by rfl) a
  have h0 : Entails.eval a c1109 := derived1109 a h
  have h1 : Entails.eval a c1090 := derived1090 a h
  have h2 : Entails.eval a c1064 := derived1064 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c144 := h 143 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c864 := h 863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1112 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1112 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1109, some c1090, some c1001, some c1111, some c24, some c31, some c864, some c781, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1112 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1112 : lratChecker f1112 p1112 = .success := by decide +kernel
theorem unsat1112 : Unsatisfiable (PosFin 31) f1112 := by
  apply lratCheckerSound f1112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1112
  · intro a ha; simp [p1112] at ha; subst a; trivial
  · exact checked1112
theorem derived1112 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1112 := by
  apply localUnsat_implies_entails f1112 [c1109, c1090, c1001, c1111, c24, c31, c864, c781] c1112 unsat1112 (by rfl) a
  have h0 : Entails.eval a c1109 := derived1109 a h
  have h1 : Entails.eval a c1090 := derived1090 a h
  have h2 : Entails.eval a c1001 := derived1001 a h
  have h3 : Entails.eval a c1111 := derived1111 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c864 := h 863 (by decide)
  have h7 : Entails.eval a c781 := h 780 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1113 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1113 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c274, some c325, some c225, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1113 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1113 : lratChecker f1113 p1113 = .success := by decide +kernel
theorem unsat1113 : Unsatisfiable (PosFin 31) f1113 := by
  apply lratCheckerSound f1113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1113
  · intro a ha; simp [p1113] at ha; subst a; trivial
  · exact checked1113
theorem derived1113 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1113 := by
  apply localUnsat_implies_entails f1113 [c274, c325, c225] c1113 unsat1113 (by rfl) a
  have h0 : Entails.eval a c274 := h 273 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1114 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1114 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1109, some c1100, some c1090, some c1001, some c1112, some c1110, some c549, some c1113, some c864, some c781, some c79, some c760, some c842, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1114 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1114 : lratChecker f1114 p1114 = .success := by decide +kernel
theorem unsat1114 : Unsatisfiable (PosFin 31) f1114 := by
  apply lratCheckerSound f1114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1114
  · intro a ha; simp [p1114] at ha; subst a; trivial
  · exact checked1114
theorem derived1114 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1114 := by
  apply localUnsat_implies_entails f1114 [c1109, c1100, c1090, c1001, c1112, c1110, c549, c1113, c864, c781, c79, c760, c842] c1114 unsat1114 (by rfl) a
  have h0 : Entails.eval a c1109 := derived1109 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1090 := derived1090 a h
  have h3 : Entails.eval a c1001 := derived1001 a h
  have h4 : Entails.eval a c1112 := derived1112 a h
  have h5 : Entails.eval a c1110 := derived1110 a h
  have h6 : Entails.eval a c549 := h 548 (by decide)
  have h7 : Entails.eval a c1113 := derived1113 a h
  have h8 : Entails.eval a c864 := h 863 (by decide)
  have h9 : Entails.eval a c781 := h 780 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c760 := h 759 (by decide)
  have h12 : Entails.eval a c842 := h 841 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1115 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1115 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1090, some c1064, some c1001, some c1109, some c1114, some c338, some c258, some c1107, some c1110, some c1111, some c781, some c22, some c31, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1115 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1115 : lratChecker f1115 p1115 = .success := by decide +kernel
theorem unsat1115 : Unsatisfiable (PosFin 31) f1115 := by
  apply lratCheckerSound f1115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1115
  · intro a ha; simp [p1115] at ha; subst a; trivial
  · exact checked1115
theorem derived1115 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1115 := by
  apply localUnsat_implies_entails f1115 [c1090, c1064, c1001, c1109, c1114, c338, c258, c1107, c1110, c1111, c781, c22, c31] c1115 unsat1115 (by rfl) a
  have h0 : Entails.eval a c1090 := derived1090 a h
  have h1 : Entails.eval a c1064 := derived1064 a h
  have h2 : Entails.eval a c1001 := derived1001 a h
  have h3 : Entails.eval a c1109 := derived1109 a h
  have h4 : Entails.eval a c1114 := derived1114 a h
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c1107 := derived1107 a h
  have h8 : Entails.eval a c1110 := derived1110 a h
  have h9 : Entails.eval a c1111 := derived1111 a h
  have h10 : Entails.eval a c781 := h 780 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1116 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1116 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1115, some c55, some c1001, some c263, some c273, some c309, some c601, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1116 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1116 : lratChecker f1116 p1116 = .success := by decide +kernel
theorem unsat1116 : Unsatisfiable (PosFin 31) f1116 := by
  apply lratCheckerSound f1116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1116
  · intro a ha; simp [p1116] at ha; subst a; trivial
  · exact checked1116
theorem derived1116 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1116 := by
  apply localUnsat_implies_entails f1116 [c1115, c55, c1001, c263, c273, c309, c601] c1116 unsat1116 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c1001 := derived1001 a h
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c601 := h 600 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1117 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1117 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1115, some c1064, some c1001, some c1116, some c172, some c839, some c120, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1117 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1117 : lratChecker f1117 p1117 = .success := by decide +kernel
theorem unsat1117 : Unsatisfiable (PosFin 31) f1117 := by
  apply lratCheckerSound f1117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1117
  · intro a ha; simp [p1117] at ha; subst a; trivial
  · exact checked1117
theorem derived1117 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1117 := by
  apply localUnsat_implies_entails f1117 [c1115, c1064, c1001, c1116, c172, c839, c120] c1117 unsat1117 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c1064 := derived1064 a h
  have h2 : Entails.eval a c1001 := derived1001 a h
  have h3 : Entails.eval a c1116 := derived1116 a h
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c839 := h 838 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1118 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1118 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1115, some c55, some c1100, some c1064, some c1001, some c172, some c258, some c51, some c382, some c24, some c9, some c396, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1118 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1118 : lratChecker f1118 p1118 = .success := by decide +kernel
theorem unsat1118 : Unsatisfiable (PosFin 31) f1118 := by
  apply lratCheckerSound f1118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1118
  · intro a ha; simp [p1118] at ha; subst a; trivial
  · exact checked1118
theorem derived1118 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1118 := by
  apply localUnsat_implies_entails f1118 [c1115, c55, c1100, c1064, c1001, c172, c258, c51, c382, c24, c9, c396] c1118 unsat1118 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c1064 := derived1064 a h
  have h4 : Entails.eval a c1001 := derived1001 a h
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c9 := h 8 (by decide)
  have h11 : Entails.eval a c396 := h 395 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1119 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1119 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1115, some c1100, some c1064, some c1001, some c1117, some c1118, some c263, some c309, some c285, some c1073, some c244, some c592, some c802, some c564, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1119 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1119 : lratChecker f1119 p1119 = .success := by decide +kernel
theorem unsat1119 : Unsatisfiable (PosFin 31) f1119 := by
  apply lratCheckerSound f1119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1119
  · intro a ha; simp [p1119] at ha; subst a; trivial
  · exact checked1119
theorem derived1119 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1119 := by
  apply localUnsat_implies_entails f1119 [c1115, c1100, c1064, c1001, c1117, c1118, c263, c309, c285, c1073, c244, c592, c802, c564] c1119 unsat1119 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1064 := derived1064 a h
  have h3 : Entails.eval a c1001 := derived1001 a h
  have h4 : Entails.eval a c1117 := derived1117 a h
  have h5 : Entails.eval a c1118 := derived1118 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c309 := h 308 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c1073 := derived1073 a h
  have h10 : Entails.eval a c244 := h 243 (by decide)
  have h11 : Entails.eval a c592 := h 591 (by decide)
  have h12 : Entails.eval a c802 := h 801 (by decide)
  have h13 : Entails.eval a c564 := h 563 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1120 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1120 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1115, some c55, some c1100, some c1064, some c1119, some c44, some c51, some c1002, some c309, some c1073, some c287, some c1032, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1120 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1120 : lratChecker f1120 p1120 = .success := by decide +kernel
theorem unsat1120 : Unsatisfiable (PosFin 31) f1120 := by
  apply lratCheckerSound f1120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1120
  · intro a ha; simp [p1120] at ha; subst a; trivial
  · exact checked1120
theorem derived1120 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1120 := by
  apply localUnsat_implies_entails f1120 [c1115, c55, c1100, c1064, c1119, c44, c51, c1002, c309, c1073, c287, c1032] c1120 unsat1120 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c1064 := derived1064 a h
  have h4 : Entails.eval a c1119 := derived1119 a h
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c1002 := derived1002 a h
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c1073 := derived1073 a h
  have h10 : Entails.eval a c287 := h 286 (by decide)
  have h11 : Entails.eval a c1032 := derived1032 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1121 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1121 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1120, some c1115, some c55, some c1090, some c1064, some c1001, some c44, some c79, some c425, some c723, some c719, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1121 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1121 : lratChecker f1121 p1121 = .success := by decide +kernel
theorem unsat1121 : Unsatisfiable (PosFin 31) f1121 := by
  apply lratCheckerSound f1121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1121
  · intro a ha; simp [p1121] at ha; subst a; trivial
  · exact checked1121
theorem derived1121 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1121 := by
  apply localUnsat_implies_entails f1121 [c1120, c1115, c55, c1090, c1064, c1001, c44, c79, c425, c723, c719] c1121 unsat1121 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c1090 := derived1090 a h
  have h4 : Entails.eval a c1064 := derived1064 a h
  have h5 : Entails.eval a c1001 := derived1001 a h
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c425 := h 424 (by decide)
  have h9 : Entails.eval a c723 := h 722 (by decide)
  have h10 : Entails.eval a c719 := h 718 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1122 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1122 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1120, some c1115, some c55, some c1100, some c1090, some c1001, some c1121, some c528, some c420, some c212, some c309, some c723, some c1002, some c173, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1122 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1122 : lratChecker f1122 p1122 = .success := by decide +kernel
theorem unsat1122 : Unsatisfiable (PosFin 31) f1122 := by
  apply lratCheckerSound f1122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1122
  · intro a ha; simp [p1122] at ha; subst a; trivial
  · exact checked1122
theorem derived1122 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1122 := by
  apply localUnsat_implies_entails f1122 [c1120, c1115, c55, c1100, c1090, c1001, c1121, c528, c420, c212, c309, c723, c1002, c173] c1122 unsat1122 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c1100 := derived1100 a h
  have h4 : Entails.eval a c1090 := derived1090 a h
  have h5 : Entails.eval a c1001 := derived1001 a h
  have h6 : Entails.eval a c1121 := derived1121 a h
  have h7 : Entails.eval a c528 := h 527 (by decide)
  have h8 : Entails.eval a c420 := h 419 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c723 := h 722 (by decide)
  have h12 : Entails.eval a c1002 := derived1002 a h
  have h13 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1123 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1123 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1122, some c1120, some c1100, some c1090, some c1001, some c97, some c650, some c246, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1123 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1123 : lratChecker f1123 p1123 = .success := by decide +kernel
theorem unsat1123 : Unsatisfiable (PosFin 31) f1123 := by
  apply lratCheckerSound f1123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1123
  · intro a ha; simp [p1123] at ha; subst a; trivial
  · exact checked1123
theorem derived1123 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1123 := by
  apply localUnsat_implies_entails f1123 [c1122, c1120, c1100, c1090, c1001, c97, c650, c246] c1123 unsat1123 (by rfl) a
  have h0 : Entails.eval a c1122 := derived1122 a h
  have h1 : Entails.eval a c1120 := derived1120 a h
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c1090 := derived1090 a h
  have h4 : Entails.eval a c1001 := derived1001 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c650 := h 649 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1124 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1124 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1122, some c1115, some c1090, some c1064, some c1001, some c1123, some c109, some c662, some c88, some c61, some c784, some c645, some c121, some c209, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1124 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1124 : lratChecker f1124 p1124 = .success := by decide +kernel
theorem unsat1124 : Unsatisfiable (PosFin 31) f1124 := by
  apply lratCheckerSound f1124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1124
  · intro a ha; simp [p1124] at ha; subst a; trivial
  · exact checked1124
theorem derived1124 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1124 := by
  apply localUnsat_implies_entails f1124 [c1122, c1115, c1090, c1064, c1001, c1123, c109, c662, c88, c61, c784, c645, c121, c209] c1124 unsat1124 (by rfl) a
  have h0 : Entails.eval a c1122 := derived1122 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c1090 := derived1090 a h
  have h3 : Entails.eval a c1064 := derived1064 a h
  have h4 : Entails.eval a c1001 := derived1001 a h
  have h5 : Entails.eval a c1123 := derived1123 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c662 := h 661 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c784 := h 783 (by decide)
  have h11 : Entails.eval a c645 := h 644 (by decide)
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1125 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1125 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1064, some c1100, some c1115, some c55, some c1120, some c1124, some c44, some c51, some c1002, some c172, some c309, some c285, some c446, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1125 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1125 : lratChecker f1125 p1125 = .success := by decide +kernel
theorem unsat1125 : Unsatisfiable (PosFin 31) f1125 := by
  apply lratCheckerSound f1125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1125
  · intro a ha; simp [p1125] at ha; subst a; trivial
  · exact checked1125
theorem derived1125 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1125 := by
  apply localUnsat_implies_entails f1125 [c1064, c1100, c1115, c55, c1120, c1124, c44, c51, c1002, c172, c309, c285, c446] c1125 unsat1125 (by rfl) a
  have h0 : Entails.eval a c1064 := derived1064 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1115 := derived1115 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c1120 := derived1120 a h
  have h5 : Entails.eval a c1124 := derived1124 a h
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c1002 := derived1002 a h
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c446 := h 445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1126 : DefaultClause 31 := directClause [(⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨20, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1126 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c51, some c1002, some c172, some c285, some c446, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1126 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1126 : lratChecker f1126 p1126 = .success := by decide +kernel
theorem unsat1126 : Unsatisfiable (PosFin 31) f1126 := by
  apply lratCheckerSound f1126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1126
  · intro a ha; simp [p1126] at ha; subst a; trivial
  · exact checked1126
theorem derived1126 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1126 := by
  apply localUnsat_implies_entails f1126 [c55, c51, c1002, c172, c285, c446] c1126 unsat1126 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c1002 := derived1002 a h
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c446 := h 445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1127 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨20, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1127 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c36, some c1126, some c963, some c884, some c212, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1127 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1127 : lratChecker f1127 p1127 = .success := by decide +kernel
theorem unsat1127 : Unsatisfiable (PosFin 31) f1127 := by
  apply lratCheckerSound f1127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1127
  · intro a ha; simp [p1127] at ha; subst a; trivial
  · exact checked1127
theorem derived1127 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1127 := by
  apply localUnsat_implies_entails f1127 [c55, c36, c1126, c963, c884, c212] c1127 unsat1127 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c1126 := derived1126 a h
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c884 := h 883 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1128 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨15, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1128 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c963, some c76, some c223, some c843, some c148, some c259, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1128 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1128 : lratChecker f1128 p1128 = .success := by decide +kernel
theorem unsat1128 : Unsatisfiable (PosFin 31) f1128 := by
  apply lratCheckerSound f1128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1128
  · intro a ha; simp [p1128] at ha; subst a; trivial
  · exact checked1128
theorem derived1128 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1128 := by
  apply localUnsat_implies_entails f1128 [c963, c76, c223, c843, c148, c259] c1128 unsat1128 (by rfl) a
  have h0 : Entails.eval a c963 := derived963 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c223 := h 222 (by decide)
  have h3 : Entails.eval a c843 := h 842 (by decide)
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1129 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1129 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c44, some c36, some c1127, some c1128, some c51, some c1002, some c139, some c285, some c1073, some c288, some c618, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1129 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1129 : lratChecker f1129 p1129 = .success := by decide +kernel
theorem unsat1129 : Unsatisfiable (PosFin 31) f1129 := by
  apply lratCheckerSound f1129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1129
  · intro a ha; simp [p1129] at ha; subst a; trivial
  · exact checked1129
theorem derived1129 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1129 := by
  apply localUnsat_implies_entails f1129 [c55, c44, c36, c1127, c1128, c51, c1002, c139, c285, c1073, c288, c618] c1129 unsat1129 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c1127 := derived1127 a h
  have h4 : Entails.eval a c1128 := derived1128 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c1002 := derived1002 a h
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c1073 := derived1073 a h
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c618 := h 617 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1130 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1130 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c1125, some c36, some c51, some c1002, some c341, some c343, some c34, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1130 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1130 : lratChecker f1130 p1130 = .success := by decide +kernel
theorem unsat1130 : Unsatisfiable (PosFin 31) f1130 := by
  apply lratCheckerSound f1130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1130
  · intro a ha; simp [p1130] at ha; subst a; trivial
  · exact checked1130
theorem derived1130 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1130 := by
  apply localUnsat_implies_entails f1130 [c55, c1125, c36, c51, c1002, c341, c343, c34] c1130 unsat1130 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c1002 := derived1002 a h
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1131 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1131 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1130, some c1129, some c55, some c356, some c34, some c801, some c41, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1131 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1131 : lratChecker f1131 p1131 = .success := by decide +kernel
theorem unsat1131 : Unsatisfiable (PosFin 31) f1131 := by
  apply lratCheckerSound f1131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1131
  · intro a ha; simp [p1131] at ha; subst a; trivial
  · exact checked1131
theorem derived1131 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1131 := by
  apply localUnsat_implies_entails f1131 [c1130, c1129, c55, c356, c34, c801, c41] c1131 unsat1131 (by rfl) a
  have h0 : Entails.eval a c1130 := derived1130 a h
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c801 := h 800 (by decide)
  have h6 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1132 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, false), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨20, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1132 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c272, some c343, some c70, some c1002, some c270, some c318, some c103, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1132 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1132 : lratChecker f1132 p1132 = .success := by decide +kernel
theorem unsat1132 : Unsatisfiable (PosFin 31) f1132 := by
  apply lratCheckerSound f1132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1132
  · intro a ha; simp [p1132] at ha; subst a; trivial
  · exact checked1132
theorem derived1132 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1132 := by
  apply localUnsat_implies_entails f1132 [c272, c343, c70, c1002, c270, c318, c103] c1132 unsat1132 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c1002 := derived1002 a h
  have h4 : Entails.eval a c270 := h 269 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1133 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨13, by decide⟩, false), (⟨1, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1133 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c26, some c28, some c251, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1133 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1133 : lratChecker f1133 p1133 = .success := by decide +kernel
theorem unsat1133 : Unsatisfiable (PosFin 31) f1133 := by
  apply lratCheckerSound f1133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1133
  · intro a ha; simp [p1133] at ha; subst a; trivial
  · exact checked1133
theorem derived1133 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1133 := by
  apply localUnsat_implies_entails f1133 [c26, c28, c251] c1133 unsat1133 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1134 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨13, by decide⟩, false), (⟨12, by decide⟩, false), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1134 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c272, some c55, some c1133, some c344, some c288, some c579, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1134 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1134 : lratChecker f1134 p1134 = .success := by decide +kernel
theorem unsat1134 : Unsatisfiable (PosFin 31) f1134 := by
  apply lratCheckerSound f1134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1134
  · intro a ha; simp [p1134] at ha; subst a; trivial
  · exact checked1134
theorem derived1134 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1134 := by
  apply localUnsat_implies_entails f1134 [c272, c55, c1133, c344, c288, c579] c1134 unsat1134 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c1133 := derived1133 a h
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c288 := h 287 (by decide)
  have h5 : Entails.eval a c579 := h 578 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1135 : DefaultClause 31 := directClause [(⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1135 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1129, some c55, some c1130, some c1131, some c1132, some c1134, some c1002, some c172, some c288, some c299, some c801, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1135 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1135 : lratChecker f1135 p1135 = .success := by decide +kernel
theorem unsat1135 : Unsatisfiable (PosFin 31) f1135 := by
  apply lratCheckerSound f1135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1135
  · intro a ha; simp [p1135] at ha; subst a; trivial
  · exact checked1135
theorem derived1135 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1135 := by
  apply localUnsat_implies_entails f1135 [c1129, c55, c1130, c1131, c1132, c1134, c1002, c172, c288, c299, c801] c1135 unsat1135 (by rfl) a
  have h0 : Entails.eval a c1129 := derived1129 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c1130 := derived1130 a h
  have h3 : Entails.eval a c1131 := derived1131 a h
  have h4 : Entails.eval a c1132 := derived1132 a h
  have h5 : Entails.eval a c1134 := derived1134 a h
  have h6 : Entails.eval a c1002 := derived1002 a h
  have h7 : Entails.eval a c172 := h 171 (by decide)
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c801 := h 800 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1136 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1136 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c963, some c272, some c805, some c473, some c455, some c229, some c203, some c210, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1136 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1136 : lratChecker f1136 p1136 = .success := by decide +kernel
theorem unsat1136 : Unsatisfiable (PosFin 31) f1136 := by
  apply lratCheckerSound f1136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1136
  · intro a ha; simp [p1136] at ha; subst a; trivial
  · exact checked1136
theorem derived1136 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1136 := by
  apply localUnsat_implies_entails f1136 [c963, c272, c805, c473, c455, c229, c203, c210] c1136 unsat1136 (by rfl) a
  have h0 : Entails.eval a c963 := derived963 a h
  have h1 : Entails.eval a c272 := h 271 (by decide)
  have h2 : Entails.eval a c805 := h 804 (by decide)
  have h3 : Entails.eval a c473 := h 472 (by decide)
  have h4 : Entails.eval a c455 := h 454 (by decide)
  have h5 : Entails.eval a c229 := h 228 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1137 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1137 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c1125, some c1135, some c963, some c486, some c1136, some c36, some c66, some c223, some c843, some c148, some c259, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1137 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1137 : lratChecker f1137 p1137 = .success := by decide +kernel
theorem unsat1137 : Unsatisfiable (PosFin 31) f1137 := by
  apply lratCheckerSound f1137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1137
  · intro a ha; simp [p1137] at ha; subst a; trivial
  · exact checked1137
theorem derived1137 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1137 := by
  apply localUnsat_implies_entails f1137 [c55, c1125, c1135, c963, c486, c1136, c36, c66, c223, c843, c148, c259] c1137 unsat1137 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c1135 := derived1135 a h
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c486 := h 485 (by decide)
  have h5 : Entails.eval a c1136 := derived1136 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c223 := h 222 (by decide)
  have h9 : Entails.eval a c843 := h 842 (by decide)
  have h10 : Entails.eval a c148 := h 147 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1138 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1138 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1137, some c1129, some c55, some c963, some c444, some c883, some c5, some c79, some c21, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1138 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1138 : lratChecker f1138 p1138 = .success := by decide +kernel
theorem unsat1138 : Unsatisfiable (PosFin 31) f1138 := by
  apply lratCheckerSound f1138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1138
  · intro a ha; simp [p1138] at ha; subst a; trivial
  · exact checked1138
theorem derived1138 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1138 := by
  apply localUnsat_implies_entails f1138 [c1137, c1129, c55, c963, c444, c883, c5, c79, c21] c1138 unsat1138 (by rfl) a
  have h0 : Entails.eval a c1137 := derived1137 a h
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c444 := h 443 (by decide)
  have h5 : Entails.eval a c883 := h 882 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1139 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1139 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c79, some c401, some c21, some c203, some c753, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1139 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1139 : lratChecker f1139 p1139 = .success := by decide +kernel
theorem unsat1139 : Unsatisfiable (PosFin 31) f1139 := by
  apply lratCheckerSound f1139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1139
  · intro a ha; simp [p1139] at ha; subst a; trivial
  · exact checked1139
theorem derived1139 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1139 := by
  apply localUnsat_implies_entails f1139 [c79, c401, c21, c203, c753] c1139 unsat1139 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c401 := h 400 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c753 := h 752 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1140 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨6, by decide⟩, false), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1140 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c5, some c6, some c294, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1140 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1140 : lratChecker f1140 p1140 = .success := by decide +kernel
theorem unsat1140 : Unsatisfiable (PosFin 31) f1140 := by
  apply lratCheckerSound f1140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1140
  · intro a ha; simp [p1140] at ha; subst a; trivial
  · exact checked1140
theorem derived1140 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1140 := by
  apply localUnsat_implies_entails f1140 [c55, c5, c6, c294] c1140 unsat1140 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1141 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1141 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c1125, some c1129, some c1137, some c1138, some c1139, some c801, some c883, some c1140, some c21, some c888, some c1113, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1141 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1141 : lratChecker f1141 p1141 = .success := by decide +kernel
theorem unsat1141 : Unsatisfiable (PosFin 31) f1141 := by
  apply lratCheckerSound f1141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1141
  · intro a ha; simp [p1141] at ha; subst a; trivial
  · exact checked1141
theorem derived1141 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1141 := by
  apply localUnsat_implies_entails f1141 [c55, c1125, c1129, c1137, c1138, c1139, c801, c883, c1140, c21, c888, c1113] c1141 unsat1141 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c1129 := derived1129 a h
  have h3 : Entails.eval a c1137 := derived1137 a h
  have h4 : Entails.eval a c1138 := derived1138 a h
  have h5 : Entails.eval a c1139 := derived1139 a h
  have h6 : Entails.eval a c801 := h 800 (by decide)
  have h7 : Entails.eval a c883 := h 882 (by decide)
  have h8 : Entails.eval a c1140 := derived1140 a h
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c888 := h 887 (by decide)
  have h11 : Entails.eval a c1113 := derived1113 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1142 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1142 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c1141, some c304, some c211, some c309, some c1002, some c115, some c175, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1142 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1142 : lratChecker f1142 p1142 = .success := by decide +kernel
theorem unsat1142 : Unsatisfiable (PosFin 31) f1142 := by
  apply lratCheckerSound f1142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1142
  · intro a ha; simp [p1142] at ha; subst a; trivial
  · exact checked1142
theorem derived1142 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1142 := by
  apply localUnsat_implies_entails f1142 [c1125, c1141, c304, c211, c309, c1002, c115, c175] c1142 unsat1142 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c1141 := derived1141 a h
  have h2 : Entails.eval a c304 := h 303 (by decide)
  have h3 : Entails.eval a c211 := h 210 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  have h5 : Entails.eval a c1002 := derived1002 a h
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1143 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1143 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c55, some c1141, some c71, some c309, some c304, some c1002, some c211, some c112, some c1142, some c23, some c60, some c452, some c486, some c28, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1143 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1143 : lratChecker f1143 p1143 = .success := by decide +kernel
theorem unsat1143 : Unsatisfiable (PosFin 31) f1143 := by
  apply lratCheckerSound f1143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1143
  · intro a ha; simp [p1143] at ha; subst a; trivial
  · exact checked1143
theorem derived1143 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1143 := by
  apply localUnsat_implies_entails f1143 [c1125, c55, c1141, c71, c309, c304, c1002, c211, c112, c1142, c23, c60, c452, c486, c28] c1143 unsat1143 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c1141 := derived1141 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c1002 := derived1002 a h
  have h7 : Entails.eval a c211 := h 210 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c1142 := derived1142 a h
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c452 := h 451 (by decide)
  have h13 : Entails.eval a c486 := h 485 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1144 : DefaultClause 31 := directClause [(⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, false), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1144 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c304, some c211, some c112, some c71, some c60, some c17, some c28, some c153, some c355, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1144 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1144 : lratChecker f1144 p1144 = .success := by decide +kernel
theorem unsat1144 : Unsatisfiable (PosFin 31) f1144 := by
  apply lratCheckerSound f1144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1144
  · intro a ha; simp [p1144] at ha; subst a; trivial
  · exact checked1144
theorem derived1144 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1144 := by
  apply localUnsat_implies_entails f1144 [c1125, c304, c211, c112, c71, c60, c17, c28, c153, c355] c1144 unsat1144 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1145 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1145 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c304, some c211, some c112, some c71, some c60, some c17, some c1143, some c1144, some c383, some c114, some c398, some c26, some c967, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1145 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1145 : lratChecker f1145 p1145 = .success := by decide +kernel
theorem unsat1145 : Unsatisfiable (PosFin 31) f1145 := by
  apply lratCheckerSound f1145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1145
  · intro a ha; simp [p1145] at ha; subst a; trivial
  · exact checked1145
theorem derived1145 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1145 := by
  apply localUnsat_implies_entails f1145 [c1125, c304, c211, c112, c71, c60, c17, c1143, c1144, c383, c114, c398, c26, c967] c1145 unsat1145 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c1143 := derived1143 a h
  have h8 : Entails.eval a c1144 := derived1144 a h
  have h9 : Entails.eval a c383 := h 382 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c398 := h 397 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c967 := derived967 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1146 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1146 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c304, some c211, some c112, some c71, some c1143, some c60, some c17, some c1145, some c64, some c68, some c502, some c732, some c221, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1146 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1146 : lratChecker f1146 p1146 = .success := by decide +kernel
theorem unsat1146 : Unsatisfiable (PosFin 31) f1146 := by
  apply lratCheckerSound f1146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1146
  · intro a ha; simp [p1146] at ha; subst a; trivial
  · exact checked1146
theorem derived1146 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1146 := by
  apply localUnsat_implies_entails f1146 [c1125, c304, c211, c112, c71, c1143, c60, c17, c1145, c64, c68, c502, c732, c221] c1146 unsat1146 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c1143 := derived1143 a h
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1145 := derived1145 a h
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c502 := h 501 (by decide)
  have h12 : Entails.eval a c732 := h 731 (by decide)
  have h13 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1147 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨15, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1147 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c112, some c71, some c115, some c144, some c255, some c866, some c701, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1147 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1147 : lratChecker f1147 p1147 = .success := by decide +kernel
theorem unsat1147 : Unsatisfiable (PosFin 31) f1147 := by
  apply lratCheckerSound f1147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1147
  · intro a ha; simp [p1147] at ha; subst a; trivial
  · exact checked1147
theorem derived1147 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1147 := by
  apply localUnsat_implies_entails f1147 [c112, c71, c115, c144, c255, c866, c701] c1147 unsat1147 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c866 := h 865 (by decide)
  have h6 : Entails.eval a c701 := h 700 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1148 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1148 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1143, some c1125, some c304, some c211, some c112, some c1147, some c23, some c1146, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1148 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1148 : lratChecker f1148 p1148 = .success := by decide +kernel
theorem unsat1148 : Unsatisfiable (PosFin 31) f1148 := by
  apply lratCheckerSound f1148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1148
  · intro a ha; simp [p1148] at ha; subst a; trivial
  · exact checked1148
theorem derived1148 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1148 := by
  apply localUnsat_implies_entails f1148 [c1143, c1125, c304, c211, c112, c1147, c23, c1146] c1148 unsat1148 (by rfl) a
  have h0 : Entails.eval a c1143 := derived1143 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c304 := h 303 (by decide)
  have h3 : Entails.eval a c211 := h 210 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1147 := derived1147 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c1146 := derived1146 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1149 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1149 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c846, some c261, some c766, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1149 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1149 : lratChecker f1149 p1149 = .success := by decide +kernel
theorem unsat1149 : Unsatisfiable (PosFin 31) f1149 := by
  apply lratCheckerSound f1149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1149
  · intro a ha; simp [p1149] at ha; subst a; trivial
  · exact checked1149
theorem derived1149 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1149 := by
  apply localUnsat_implies_entails f1149 [c846, c261, c766] c1149 unsat1149 (by rfl) a
  have h0 : Entails.eval a c846 := h 845 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c766 := h 765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1150 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1150 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c701, some c259, some c654, some c1149, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1150 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1150 : lratChecker f1150 p1150 = .success := by decide +kernel
theorem unsat1150 : Unsatisfiable (PosFin 31) f1150 := by
  apply lratCheckerSound f1150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1150
  · intro a ha; simp [p1150] at ha; subst a; trivial
  · exact checked1150
theorem derived1150 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1150 := by
  apply localUnsat_implies_entails f1150 [c701, c259, c654, c1149] c1150 unsat1150 (by rfl) a
  have h0 : Entails.eval a c701 := h 700 (by decide)
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c654 := h 653 (by decide)
  have h3 : Entails.eval a c1149 := derived1149 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1151 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1151 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c259, some c1149, some c502, some c762, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1151 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1151 : lratChecker f1151 p1151 = .success := by decide +kernel
theorem unsat1151 : Unsatisfiable (PosFin 31) f1151 := by
  apply lratCheckerSound f1151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1151
  · intro a ha; simp [p1151] at ha; subst a; trivial
  · exact checked1151
theorem derived1151 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1151 := by
  apply localUnsat_implies_entails f1151 [c259, c1149, c502, c762] c1151 unsat1151 (by rfl) a
  have h0 : Entails.eval a c259 := h 258 (by decide)
  have h1 : Entails.eval a c1149 := derived1149 a h
  have h2 : Entails.eval a c502 := h 501 (by decide)
  have h3 : Entails.eval a c762 := h 761 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1152 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1152 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c60, some c1150, some c206, some c1151, some c690, some c536, some c253, some c554, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1152 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1152 : lratChecker f1152 p1152 = .success := by decide +kernel
theorem unsat1152 : Unsatisfiable (PosFin 31) f1152 := by
  apply lratCheckerSound f1152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1152
  · intro a ha; simp [p1152] at ha; subst a; trivial
  · exact checked1152
theorem derived1152 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1152 := by
  apply localUnsat_implies_entails f1152 [c60, c1150, c206, c1151, c690, c536, c253, c554] c1152 unsat1152 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c1150 := derived1150 a h
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c1151 := derived1151 a h
  have h4 : Entails.eval a c690 := h 689 (by decide)
  have h5 : Entails.eval a c536 := h 535 (by decide)
  have h6 : Entails.eval a c253 := h 252 (by decide)
  have h7 : Entails.eval a c554 := h 553 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1153 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1153 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c679, some c50, some c177, some c963, some c93, some c396, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1153 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1153 : lratChecker f1153 p1153 = .success := by decide +kernel
theorem unsat1153 : Unsatisfiable (PosFin 31) f1153 := by
  apply lratCheckerSound f1153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1153
  · intro a ha; simp [p1153] at ha; subst a; trivial
  · exact checked1153
theorem derived1153 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1153 := by
  apply localUnsat_implies_entails f1153 [c679, c50, c177, c963, c93, c396] c1153 unsat1153 (by rfl) a
  have h0 : Entails.eval a c679 := h 678 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c396 := h 395 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1154 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1154 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c465, some c259, some c656, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p1154 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1154 : lratChecker f1154 p1154 = .success := by decide +kernel
theorem unsat1154 : Unsatisfiable (PosFin 31) f1154 := by
  apply lratCheckerSound f1154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1154
  · intro a ha; simp [p1154] at ha; subst a; trivial
  · exact checked1154
theorem derived1154 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1154 := by
  apply localUnsat_implies_entails f1154 [c465, c259, c656] c1154 unsat1154 (by rfl) a
  have h0 : Entails.eval a c465 := h 464 (by decide)
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c656 := h 655 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1155 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨14, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1155 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1152, some c65, some c1153, some c1154, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1155 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1155 : lratChecker f1155 p1155 = .success := by decide +kernel
theorem unsat1155 : Unsatisfiable (PosFin 31) f1155 := by
  apply lratCheckerSound f1155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1155
  · intro a ha; simp [p1155] at ha; subst a; trivial
  · exact checked1155
theorem derived1155 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1155 := by
  apply localUnsat_implies_entails f1155 [c1152, c65, c1153, c1154] c1155 unsat1155 (by rfl) a
  have h0 : Entails.eval a c1152 := derived1152 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c1153 := derived1153 a h
  have h3 : Entails.eval a c1154 := derived1154 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1156 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1156 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1148, some c1125, some c31, some c967, some c223, some c324, some c427, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1156 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1156 : lratChecker f1156 p1156 = .success := by decide +kernel
theorem unsat1156 : Unsatisfiable (PosFin 31) f1156 := by
  apply lratCheckerSound f1156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1156
  · intro a ha; simp [p1156] at ha; subst a; trivial
  · exact checked1156
theorem derived1156 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1156 := by
  apply localUnsat_implies_entails f1156 [c1148, c1125, c31, c967, c223, c324, c427] c1156 unsat1156 (by rfl) a
  have h0 : Entails.eval a c1148 := derived1148 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c967 := derived967 a h
  have h4 : Entails.eval a c223 := h 222 (by decide)
  have h5 : Entails.eval a c324 := h 323 (by decide)
  have h6 : Entails.eval a c427 := h 426 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1157 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨30, by decide⟩, true), (⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1157 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c30, some c15, some c18, some c489, some c715, some c470, some c689, some c808, some c396, some c889, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1157 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1157 : lratChecker f1157 p1157 = .success := by decide +kernel
theorem unsat1157 : Unsatisfiable (PosFin 31) f1157 := by
  apply lratCheckerSound f1157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1157
  · intro a ha; simp [p1157] at ha; subst a; trivial
  · exact checked1157
theorem derived1157 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1157 := by
  apply localUnsat_implies_entails f1157 [c30, c15, c18, c489, c715, c470, c689, c808, c396, c889] c1157 unsat1157 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c489 := h 488 (by decide)
  have h4 : Entails.eval a c715 := h 714 (by decide)
  have h5 : Entails.eval a c470 := h 469 (by decide)
  have h6 : Entails.eval a c689 := h 688 (by decide)
  have h7 : Entails.eval a c808 := h 807 (by decide)
  have h8 : Entails.eval a c396 := h 395 (by decide)
  have h9 : Entails.eval a c889 := h 888 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1158 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1158 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c470, some c36, some c523, some c182, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1158 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1158 : lratChecker f1158 p1158 = .success := by decide +kernel
theorem unsat1158 : Unsatisfiable (PosFin 31) f1158 := by
  apply lratCheckerSound f1158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1158
  · intro a ha; simp [p1158] at ha; subst a; trivial
  · exact checked1158
theorem derived1158 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1158 := by
  apply localUnsat_implies_entails f1158 [c1125, c470, c36, c523, c182] c1158 unsat1158 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c470 := h 469 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c523 := h 522 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1159 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨30, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1159 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c399, some c690, some c143, some c592, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1159 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1159 : lratChecker f1159 p1159 = .success := by decide +kernel
theorem unsat1159 : Unsatisfiable (PosFin 31) f1159 := by
  apply lratCheckerSound f1159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1159
  · intro a ha; simp [p1159] at ha; subst a; trivial
  · exact checked1159
theorem derived1159 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1159 := by
  apply localUnsat_implies_entails f1159 [c399, c690, c143, c592] c1159 unsat1159 (by rfl) a
  have h0 : Entails.eval a c399 := h 398 (by decide)
  have h1 : Entails.eval a c690 := h 689 (by decide)
  have h2 : Entails.eval a c143 := h 142 (by decide)
  have h3 : Entails.eval a c592 := h 591 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1160 : DefaultClause 31 := directClause [(⟨30, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1160 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1143, some c1148, some c1125, some c1156, some c1155, some c30, some c1157, some c1158, some c554, some c129, some c762, some c1159, some c658, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1160 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1160 : lratChecker f1160 p1160 = .success := by decide +kernel
theorem unsat1160 : Unsatisfiable (PosFin 31) f1160 := by
  apply lratCheckerSound f1160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1160
  · intro a ha; simp [p1160] at ha; subst a; trivial
  · exact checked1160
theorem derived1160 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1160 := by
  apply localUnsat_implies_entails f1160 [c1143, c1148, c1125, c1156, c1155, c30, c1157, c1158, c554, c129, c762, c1159, c658] c1160 unsat1160 (by rfl) a
  have h0 : Entails.eval a c1143 := derived1143 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1156 := derived1156 a h
  have h4 : Entails.eval a c1155 := derived1155 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c1157 := derived1157 a h
  have h7 : Entails.eval a c1158 := derived1158 a h
  have h8 : Entails.eval a c554 := h 553 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c762 := h 761 (by decide)
  have h11 : Entails.eval a c1159 := derived1159 a h
  have h12 : Entails.eval a c658 := h 657 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1161 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1161 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1156, some c1148, some c1143, some c1125, some c1160, some c963, some c1081, some c1150, some c467, some c503, some c399, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1161 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1161 : lratChecker f1161 p1161 = .success := by decide +kernel
theorem unsat1161 : Unsatisfiable (PosFin 31) f1161 := by
  apply lratCheckerSound f1161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1161
  · intro a ha; simp [p1161] at ha; subst a; trivial
  · exact checked1161
theorem derived1161 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1161 := by
  apply localUnsat_implies_entails f1161 [c1156, c1148, c1143, c1125, c1160, c963, c1081, c1150, c467, c503, c399] c1161 unsat1161 (by rfl) a
  have h0 : Entails.eval a c1156 := derived1156 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1143 := derived1143 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c1160 := derived1160 a h
  have h5 : Entails.eval a c963 := derived963 a h
  have h6 : Entails.eval a c1081 := derived1081 a h
  have h7 : Entails.eval a c1150 := derived1150 a h
  have h8 : Entails.eval a c467 := h 466 (by decide)
  have h9 : Entails.eval a c503 := h 502 (by decide)
  have h10 : Entails.eval a c399 := h 398 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1162 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1162 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1081, some c1150, some c467, some c479, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1162 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1162 : lratChecker f1162 p1162 = .success := by decide +kernel
theorem unsat1162 : Unsatisfiable (PosFin 31) f1162 := by
  apply lratCheckerSound f1162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1162
  · intro a ha; simp [p1162] at ha; subst a; trivial
  · exact checked1162
theorem derived1162 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1162 := by
  apply localUnsat_implies_entails f1162 [c1081, c1150, c467, c479] c1162 unsat1162 (by rfl) a
  have h0 : Entails.eval a c1081 := derived1081 a h
  have h1 : Entails.eval a c1150 := derived1150 a h
  have h2 : Entails.eval a c467 := h 466 (by decide)
  have h3 : Entails.eval a c479 := h 478 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1163 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨11, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1163 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c1143, some c1156, some c1161, some c1162, some c1148, some c1150, some c868, some c116, some c258, some c153, some c159, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1163 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1163 : lratChecker f1163 p1163 = .success := by decide +kernel
theorem unsat1163 : Unsatisfiable (PosFin 31) f1163 := by
  apply lratCheckerSound f1163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1163
  · intro a ha; simp [p1163] at ha; subst a; trivial
  · exact checked1163
theorem derived1163 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1163 := by
  apply localUnsat_implies_entails f1163 [c1125, c1143, c1156, c1161, c1162, c1148, c1150, c868, c116, c258, c153, c159] c1163 unsat1163 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c1143 := derived1143 a h
  have h2 : Entails.eval a c1156 := derived1156 a h
  have h3 : Entails.eval a c1161 := derived1161 a h
  have h4 : Entails.eval a c1162 := derived1162 a h
  have h5 : Entails.eval a c1148 := derived1148 a h
  have h6 : Entails.eval a c1150 := derived1150 a h
  have h7 : Entails.eval a c868 := h 867 (by decide)
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c258 := h 257 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1164 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨25, by decide⟩, false), (⟨11, by decide⟩, true), (⟨30, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1164 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1148, some c1143, some c1125, some c14, some c670, some c679, some c577, some c19, some c678, some c185, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1164 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1164 : lratChecker f1164 p1164 = .success := by decide +kernel
theorem unsat1164 : Unsatisfiable (PosFin 31) f1164 := by
  apply lratCheckerSound f1164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1164
  · intro a ha; simp [p1164] at ha; subst a; trivial
  · exact checked1164
theorem derived1164 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1164 := by
  apply localUnsat_implies_entails f1164 [c1148, c1143, c1125, c14, c670, c679, c577, c19, c678, c185] c1164 unsat1164 (by rfl) a
  have h0 : Entails.eval a c1148 := derived1148 a h
  have h1 : Entails.eval a c1143 := derived1143 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c670 := h 669 (by decide)
  have h5 : Entails.eval a c679 := h 678 (by decide)
  have h6 : Entails.eval a c577 := h 576 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c678 := h 677 (by decide)
  have h9 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1165 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1165 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c1143, some c1156, some c1161, some c1162, some c1163, some c1164, some c60, some c536, some c554, some c86, some c1101, some c153, some c159, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1165 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1165 : lratChecker f1165 p1165 = .success := by decide +kernel
theorem unsat1165 : Unsatisfiable (PosFin 31) f1165 := by
  apply lratCheckerSound f1165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1165
  · intro a ha; simp [p1165] at ha; subst a; trivial
  · exact checked1165
theorem derived1165 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1165 := by
  apply localUnsat_implies_entails f1165 [c1125, c1143, c1156, c1161, c1162, c1163, c1164, c60, c536, c554, c86, c1101, c153, c159] c1165 unsat1165 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c1143 := derived1143 a h
  have h2 : Entails.eval a c1156 := derived1156 a h
  have h3 : Entails.eval a c1161 := derived1161 a h
  have h4 : Entails.eval a c1162 := derived1162 a h
  have h5 : Entails.eval a c1163 := derived1163 a h
  have h6 : Entails.eval a c1164 := derived1164 a h
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c536 := h 535 (by decide)
  have h9 : Entails.eval a c554 := h 553 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c1101 := derived1101 a h
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1166 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1166 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1148, some c1143, some c1125, some c1156, some c1161, some c1162, some c1165, some c259, some c1149, some c261, some c762, some c475, some c268, some c305, some c876, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1166 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1166 : lratChecker f1166 p1166 = .success := by decide +kernel
theorem unsat1166 : Unsatisfiable (PosFin 31) f1166 := by
  apply lratCheckerSound f1166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1166
  · intro a ha; simp [p1166] at ha; subst a; trivial
  · exact checked1166
theorem derived1166 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1166 := by
  apply localUnsat_implies_entails f1166 [c1148, c1143, c1125, c1156, c1161, c1162, c1165, c259, c1149, c261, c762, c475, c268, c305, c876] c1166 unsat1166 (by rfl) a
  have h0 : Entails.eval a c1148 := derived1148 a h
  have h1 : Entails.eval a c1143 := derived1143 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1156 := derived1156 a h
  have h4 : Entails.eval a c1161 := derived1161 a h
  have h5 : Entails.eval a c1162 := derived1162 a h
  have h6 : Entails.eval a c1165 := derived1165 a h
  have h7 : Entails.eval a c259 := h 258 (by decide)
  have h8 : Entails.eval a c1149 := derived1149 a h
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c762 := h 761 (by decide)
  have h11 : Entails.eval a c475 := h 474 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c305 := h 304 (by decide)
  have h14 : Entails.eval a c876 := h 875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1167 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨30, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1167 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c259, some c1149, some c261, some c145, some c808, some c754, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1167 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1167 : lratChecker f1167 p1167 = .success := by decide +kernel
theorem unsat1167 : Unsatisfiable (PosFin 31) f1167 := by
  apply lratCheckerSound f1167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1167
  · intro a ha; simp [p1167] at ha; subst a; trivial
  · exact checked1167
theorem derived1167 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1167 := by
  apply localUnsat_implies_entails f1167 [c259, c1149, c261, c145, c808, c754] c1167 unsat1167 (by rfl) a
  have h0 : Entails.eval a c259 := h 258 (by decide)
  have h1 : Entails.eval a c1149 := derived1149 a h
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c808 := h 807 (by decide)
  have h5 : Entails.eval a c754 := h 753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1168 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨30, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1168 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1148, some c1143, some c1125, some c145, some c50, some c868, some c143, some c663, some c808, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1168 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1168 : lratChecker f1168 p1168 = .success := by decide +kernel
theorem unsat1168 : Unsatisfiable (PosFin 31) f1168 := by
  apply lratCheckerSound f1168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1168
  · intro a ha; simp [p1168] at ha; subst a; trivial
  · exact checked1168
theorem derived1168 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1168 := by
  apply localUnsat_implies_entails f1168 [c1148, c1143, c1125, c145, c50, c868, c143, c663, c808] c1168 unsat1168 (by rfl) a
  have h0 : Entails.eval a c1148 := derived1148 a h
  have h1 : Entails.eval a c1143 := derived1143 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c868 := h 867 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c663 := h 662 (by decide)
  have h8 : Entails.eval a c808 := h 807 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1169 : DefaultClause 31 := directClause [(⟨30, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1169 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1166, some c1148, some c1143, some c1125, some c1167, some c1168, some c141, some c363, some c381, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1169 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1169 : lratChecker f1169 p1169 = .success := by decide +kernel
theorem unsat1169 : Unsatisfiable (PosFin 31) f1169 := by
  apply lratCheckerSound f1169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1169
  · intro a ha; simp [p1169] at ha; subst a; trivial
  · exact checked1169
theorem derived1169 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1169 := by
  apply localUnsat_implies_entails f1169 [c1166, c1148, c1143, c1125, c1167, c1168, c141, c363, c381] c1169 unsat1169 (by rfl) a
  have h0 : Entails.eval a c1166 := derived1166 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1143 := derived1143 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c1167 := derived1167 a h
  have h5 : Entails.eval a c1168 := derived1168 a h
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c363 := h 362 (by decide)
  have h8 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1170 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false), (⟨1, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1170 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1081, some c604, some c625, some c436, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1170 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1170 : lratChecker f1170 p1170 = .success := by decide +kernel
theorem unsat1170 : Unsatisfiable (PosFin 31) f1170 := by
  apply lratCheckerSound f1170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1170
  · intro a ha; simp [p1170] at ha; subst a; trivial
  · exact checked1170
theorem derived1170 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1170 := by
  apply localUnsat_implies_entails f1170 [c1081, c604, c625, c436] c1170 unsat1170 (by rfl) a
  have h0 : Entails.eval a c1081 := derived1081 a h
  have h1 : Entails.eval a c604 := h 603 (by decide)
  have h2 : Entails.eval a c625 := h 624 (by decide)
  have h3 : Entails.eval a c436 := h 435 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1171 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1171 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1166, some c1148, some c1143, some c1125, some c1170, some c1167, some c1169, some c1168, some c141, some c553, some c90, some c176, some c296, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1171 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1171 : lratChecker f1171 p1171 = .success := by decide +kernel
theorem unsat1171 : Unsatisfiable (PosFin 31) f1171 := by
  apply lratCheckerSound f1171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1171
  · intro a ha; simp [p1171] at ha; subst a; trivial
  · exact checked1171
theorem derived1171 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1171 := by
  apply localUnsat_implies_entails f1171 [c1166, c1148, c1143, c1125, c1170, c1167, c1169, c1168, c141, c553, c90, c176, c296] c1171 unsat1171 (by rfl) a
  have h0 : Entails.eval a c1166 := derived1166 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1143 := derived1143 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c1170 := derived1170 a h
  have h5 : Entails.eval a c1167 := derived1167 a h
  have h6 : Entails.eval a c1169 := derived1169 a h
  have h7 : Entails.eval a c1168 := derived1168 a h
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c553 := h 552 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c176 := h 175 (by decide)
  have h12 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1172 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1172 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1148, some c1143, some c1125, some c1166, some c1171, some c731, some c145, some c893, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1172 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1172 : lratChecker f1172 p1172 = .success := by decide +kernel
theorem unsat1172 : Unsatisfiable (PosFin 31) f1172 := by
  apply lratCheckerSound f1172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1172
  · intro a ha; simp [p1172] at ha; subst a; trivial
  · exact checked1172
theorem derived1172 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1172 := by
  apply localUnsat_implies_entails f1172 [c1148, c1143, c1125, c1166, c1171, c731, c145, c893] c1172 unsat1172 (by rfl) a
  have h0 : Entails.eval a c1148 := derived1148 a h
  have h1 : Entails.eval a c1143 := derived1143 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1166 := derived1166 a h
  have h4 : Entails.eval a c1171 := derived1171 a h
  have h5 : Entails.eval a c731 := h 730 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c893 := h 892 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1173 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1173 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1172, some c1148, some c1125, some c255, some c967, some c1058, some c324, some c34, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1173 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1173 : lratChecker f1173 p1173 = .success := by decide +kernel
theorem unsat1173 : Unsatisfiable (PosFin 31) f1173 := by
  apply lratCheckerSound f1173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1173
  · intro a ha; simp [p1173] at ha; subst a; trivial
  · exact checked1173
theorem derived1173 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1173 := by
  apply localUnsat_implies_entails f1173 [c1172, c1148, c1125, c255, c967, c1058, c324, c34] c1173 unsat1173 (by rfl) a
  have h0 : Entails.eval a c1172 := derived1172 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c255 := h 254 (by decide)
  have h4 : Entails.eval a c967 := derived967 a h
  have h5 : Entails.eval a c1058 := derived1058 a h
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1174 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1174 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1173, some c1172, some c79, some c1148, some c57, some c34, some c78, some c162, some c843, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1174 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1174 : lratChecker f1174 p1174 = .success := by decide +kernel
theorem unsat1174 : Unsatisfiable (PosFin 31) f1174 := by
  apply lratCheckerSound f1174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1174
  · intro a ha; simp [p1174] at ha; subst a; trivial
  · exact checked1174
theorem derived1174 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1174 := by
  apply localUnsat_implies_entails f1174 [c1173, c1172, c79, c1148, c57, c34, c78, c162, c843] c1174 unsat1174 (by rfl) a
  have h0 : Entails.eval a c1173 := derived1173 a h
  have h1 : Entails.eval a c1172 := derived1172 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1148 := derived1148 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c843 := h 842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1175 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1175 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1173, some c1172, some c79, some c1148, some c1125, some c763, some c1174, some c70, some c109, some c305, some c844, some c843, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1175 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1175 : lratChecker f1175 p1175 = .success := by decide +kernel
theorem unsat1175 : Unsatisfiable (PosFin 31) f1175 := by
  apply lratCheckerSound f1175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1175
  · intro a ha; simp [p1175] at ha; subst a; trivial
  · exact checked1175
theorem derived1175 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1175 := by
  apply localUnsat_implies_entails f1175 [c1173, c1172, c79, c1148, c1125, c763, c1174, c70, c109, c305, c844, c843] c1175 unsat1175 (by rfl) a
  have h0 : Entails.eval a c1173 := derived1173 a h
  have h1 : Entails.eval a c1172 := derived1172 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1148 := derived1148 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c763 := h 762 (by decide)
  have h6 : Entails.eval a c1174 := derived1174 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  have h10 : Entails.eval a c844 := h 843 (by decide)
  have h11 : Entails.eval a c843 := h 842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1176 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1176 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1173, some c1172, some c1125, some c267, some c308, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1176 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1176 : lratChecker f1176 p1176 = .success := by decide +kernel
theorem unsat1176 : Unsatisfiable (PosFin 31) f1176 := by
  apply lratCheckerSound f1176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1176
  · intro a ha; simp [p1176] at ha; subst a; trivial
  · exact checked1176
theorem derived1176 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1176 := by
  apply localUnsat_implies_entails f1176 [c1173, c1172, c1125, c267, c308] c1176 unsat1176 (by rfl) a
  have h0 : Entails.eval a c1173 := derived1173 a h
  have h1 : Entails.eval a c1172 := derived1172 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1177 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1177 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1148, some c1143, some c1125, some c1172, some c79, some c1173, some c1176, some c1175, some c762, some c36, some c761, some c1149, some c577, some c675, some c482, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1177 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1177 : lratChecker f1177 p1177 = .success := by decide +kernel
theorem unsat1177 : Unsatisfiable (PosFin 31) f1177 := by
  apply lratCheckerSound f1177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1177
  · intro a ha; simp [p1177] at ha; subst a; trivial
  · exact checked1177
theorem derived1177 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1177 := by
  apply localUnsat_implies_entails f1177 [c1148, c1143, c1125, c1172, c79, c1173, c1176, c1175, c762, c36, c761, c1149, c577, c675, c482] c1177 unsat1177 (by rfl) a
  have h0 : Entails.eval a c1148 := derived1148 a h
  have h1 : Entails.eval a c1143 := derived1143 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1172 := derived1172 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c1173 := derived1173 a h
  have h6 : Entails.eval a c1176 := derived1176 a h
  have h7 : Entails.eval a c1175 := derived1175 a h
  have h8 : Entails.eval a c762 := h 761 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c761 := h 760 (by decide)
  have h11 : Entails.eval a c1149 := derived1149 a h
  have h12 : Entails.eval a c577 := h 576 (by decide)
  have h13 : Entails.eval a c675 := h 674 (by decide)
  have h14 : Entails.eval a c482 := h 481 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1178 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1178 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c79, some c1177, some c1148, some c1143, some c1125, some c762, some c458, some c547, some c348, some c766, some c332, some c308, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1178 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1178 : lratChecker f1178 p1178 = .success := by decide +kernel
theorem unsat1178 : Unsatisfiable (PosFin 31) f1178 := by
  apply lratCheckerSound f1178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1178
  · intro a ha; simp [p1178] at ha; subst a; trivial
  · exact checked1178
theorem derived1178 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1178 := by
  apply localUnsat_implies_entails f1178 [c79, c1177, c1148, c1143, c1125, c762, c458, c547, c348, c766, c332, c308] c1178 unsat1178 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c1177 := derived1177 a h
  have h2 : Entails.eval a c1148 := derived1148 a h
  have h3 : Entails.eval a c1143 := derived1143 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c762 := h 761 (by decide)
  have h6 : Entails.eval a c458 := h 457 (by decide)
  have h7 : Entails.eval a c547 := h 546 (by decide)
  have h8 : Entails.eval a c348 := h 347 (by decide)
  have h9 : Entails.eval a c766 := h 765 (by decide)
  have h10 : Entails.eval a c332 := h 331 (by decide)
  have h11 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1179 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1179 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c267, some c308, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1179 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1179 : lratChecker f1179 p1179 = .success := by decide +kernel
theorem unsat1179 : Unsatisfiable (PosFin 31) f1179 := by
  apply lratCheckerSound f1179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1179
  · intro a ha; simp [p1179] at ha; subst a; trivial
  · exact checked1179
theorem derived1179 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1179 := by
  apply localUnsat_implies_entails f1179 [c1125, c267, c308] c1179 unsat1179 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1180 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1180 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c328, some c203, some c415, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1180 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1180 : lratChecker f1180 p1180 = .success := by decide +kernel
theorem unsat1180 : Unsatisfiable (PosFin 31) f1180 := by
  apply lratCheckerSound f1180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1180
  · intro a ha; simp [p1180] at ha; subst a; trivial
  · exact checked1180
theorem derived1180 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1180 := by
  apply localUnsat_implies_entails f1180 [c328, c203, c415] c1180 unsat1180 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c415 := h 414 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1181 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1181 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1177, some c1148, some c1125, some c79, some c1178, some c1179, some c763, some c1180, some c888, some c19, some c212, some c843, some c74, some c57, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1181 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1181 : lratChecker f1181 p1181 = .success := by decide +kernel
theorem unsat1181 : Unsatisfiable (PosFin 31) f1181 := by
  apply lratCheckerSound f1181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1181
  · intro a ha; simp [p1181] at ha; subst a; trivial
  · exact checked1181
theorem derived1181 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1181 := by
  apply localUnsat_implies_entails f1181 [c1177, c1148, c1125, c79, c1178, c1179, c763, c1180, c888, c19, c212, c843, c74, c57] c1181 unsat1181 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c1178 := derived1178 a h
  have h5 : Entails.eval a c1179 := derived1179 a h
  have h6 : Entails.eval a c763 := h 762 (by decide)
  have h7 : Entails.eval a c1180 := derived1180 a h
  have h8 : Entails.eval a c888 := h 887 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c843 := h 842 (by decide)
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1182 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1182 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c21, some c805, some c782, some c401, some c898, some c238, some c763, some c82, some c237, some c862, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1182 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1182 : lratChecker f1182 p1182 = .success := by decide +kernel
theorem unsat1182 : Unsatisfiable (PosFin 31) f1182 := by
  apply lratCheckerSound f1182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1182
  · intro a ha; simp [p1182] at ha; subst a; trivial
  · exact checked1182
theorem derived1182 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1182 := by
  apply localUnsat_implies_entails f1182 [c21, c805, c782, c401, c898, c238, c763, c82, c237, c862] c1182 unsat1182 (by rfl) a
  have h0 : Entails.eval a c21 := h 20 (by decide)
  have h1 : Entails.eval a c805 := h 804 (by decide)
  have h2 : Entails.eval a c782 := h 781 (by decide)
  have h3 : Entails.eval a c401 := h 400 (by decide)
  have h4 : Entails.eval a c898 := h 897 (by decide)
  have h5 : Entails.eval a c238 := h 237 (by decide)
  have h6 : Entails.eval a c763 := h 762 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c237 := h 236 (by decide)
  have h9 : Entails.eval a c862 := h 861 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1183 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1183 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1181, some c1177, some c1148, some c1143, some c1125, some c1182, some c328, some c444, some c23, some c401, some c276, some c203, some c210, some c28, some c753, some c579, some c15, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1183 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1183 : lratChecker f1183 p1183 = .success := by decide +kernel
theorem unsat1183 : Unsatisfiable (PosFin 31) f1183 := by
  apply lratCheckerSound f1183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1183
  · intro a ha; simp [p1183] at ha; subst a; trivial
  · exact checked1183
theorem derived1183 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1183 := by
  apply localUnsat_implies_entails f1183 [c1181, c1177, c1148, c1143, c1125, c1182, c328, c444, c23, c401, c276, c203, c210, c28, c753, c579, c15] c1183 unsat1183 (by rfl) a
  have h0 : Entails.eval a c1181 := derived1181 a h
  have h1 : Entails.eval a c1177 := derived1177 a h
  have h2 : Entails.eval a c1148 := derived1148 a h
  have h3 : Entails.eval a c1143 := derived1143 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c1182 := derived1182 a h
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c444 := h 443 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c401 := h 400 (by decide)
  have h10 : Entails.eval a c276 := h 275 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c753 := h 752 (by decide)
  have h15 : Entails.eval a c579 := h 578 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1184 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1184 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1177, some c1125, some c1181, some c1183, some c308, some c21, some c182, some c27, some c25, some c185, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1184 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1184 : lratChecker f1184 p1184 = .success := by decide +kernel
theorem unsat1184 : Unsatisfiable (PosFin 31) f1184 := by
  apply lratCheckerSound f1184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1184
  · intro a ha; simp [p1184] at ha; subst a; trivial
  · exact checked1184
theorem derived1184 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1184 := by
  apply localUnsat_implies_entails f1184 [c1177, c1125, c1181, c1183, c308, c21, c182, c27, c25, c185] c1184 unsat1184 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c1181 := derived1181 a h
  have h3 : Entails.eval a c1183 := derived1183 a h
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c182 := h 181 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1185 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1185 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1177, some c1148, some c1143, some c1125, some c308, some c21, some c182, some c862, some c333, some c693, some c508, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1185 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1185 : lratChecker f1185 p1185 = .success := by decide +kernel
theorem unsat1185 : Unsatisfiable (PosFin 31) f1185 := by
  apply lratCheckerSound f1185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1185
  · intro a ha; simp [p1185] at ha; subst a; trivial
  · exact checked1185
theorem derived1185 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1185 := by
  apply localUnsat_implies_entails f1185 [c1177, c1148, c1143, c1125, c308, c21, c182, c862, c333, c693, c508] c1185 unsat1185 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1143 := derived1143 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c182 := h 181 (by decide)
  have h7 : Entails.eval a c862 := h 861 (by decide)
  have h8 : Entails.eval a c333 := h 332 (by decide)
  have h9 : Entails.eval a c693 := h 692 (by decide)
  have h10 : Entails.eval a c508 := h 507 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1186 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1186 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1185, some c1184, some c1177, some c1148, some c1143, some c860, some c862, some c660, some c739, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1186 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1186 : lratChecker f1186 p1186 = .success := by decide +kernel
theorem unsat1186 : Unsatisfiable (PosFin 31) f1186 := by
  apply lratCheckerSound f1186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1186
  · intro a ha; simp [p1186] at ha; subst a; trivial
  · exact checked1186
theorem derived1186 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1186 := by
  apply localUnsat_implies_entails f1186 [c1185, c1184, c1177, c1148, c1143, c860, c862, c660, c739] c1186 unsat1186 (by rfl) a
  have h0 : Entails.eval a c1185 := derived1185 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1177 := derived1177 a h
  have h3 : Entails.eval a c1148 := derived1148 a h
  have h4 : Entails.eval a c1143 := derived1143 a h
  have h5 : Entails.eval a c860 := h 859 (by decide)
  have h6 : Entails.eval a c862 := h 861 (by decide)
  have h7 : Entails.eval a c660 := h 659 (by decide)
  have h8 : Entails.eval a c739 := h 738 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1187 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1187 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c696, some c863, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1187 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1187 : lratChecker f1187 p1187 = .success := by decide +kernel
theorem unsat1187 : Unsatisfiable (PosFin 31) f1187 := by
  apply lratCheckerSound f1187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1187
  · intro a ha; simp [p1187] at ha; subst a; trivial
  · exact checked1187
theorem derived1187 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1187 := by
  apply localUnsat_implies_entails f1187 [c1125, c696, c863] c1187 unsat1187 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c696 := h 695 (by decide)
  have h2 : Entails.eval a c863 := h 862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1188 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1188 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1177, some c1148, some c1143, some c1125, some c1185, some c1187, some c860, some c862, some c1186, some c660, some c659, some c663, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1188 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1188 : lratChecker f1188 p1188 = .success := by decide +kernel
theorem unsat1188 : Unsatisfiable (PosFin 31) f1188 := by
  apply lratCheckerSound f1188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1188
  · intro a ha; simp [p1188] at ha; subst a; trivial
  · exact checked1188
theorem derived1188 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1188 := by
  apply localUnsat_implies_entails f1188 [c1184, c1177, c1148, c1143, c1125, c1185, c1187, c860, c862, c1186, c660, c659, c663] c1188 unsat1188 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1177 := derived1177 a h
  have h2 : Entails.eval a c1148 := derived1148 a h
  have h3 : Entails.eval a c1143 := derived1143 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c1185 := derived1185 a h
  have h6 : Entails.eval a c1187 := derived1187 a h
  have h7 : Entails.eval a c860 := h 859 (by decide)
  have h8 : Entails.eval a c862 := h 861 (by decide)
  have h9 : Entails.eval a c1186 := derived1186 a h
  have h10 : Entails.eval a c660 := h 659 (by decide)
  have h11 : Entails.eval a c659 := h 658 (by decide)
  have h12 : Entails.eval a c663 := h 662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1189 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1189 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c1148, some c1184, some c1188, some c79, some c255, some c1058, some c57, some c34, some c308, some c262, some c870, some c182, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1189 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1189 : lratChecker f1189 p1189 = .success := by decide +kernel
theorem unsat1189 : Unsatisfiable (PosFin 31) f1189 := by
  apply lratCheckerSound f1189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1189
  · intro a ha; simp [p1189] at ha; subst a; trivial
  · exact checked1189
theorem derived1189 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1189 := by
  apply localUnsat_implies_entails f1189 [c1125, c1148, c1184, c1188, c79, c255, c1058, c57, c34, c308, c262, c870, c182] c1189 unsat1189 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1188 := derived1188 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c255 := h 254 (by decide)
  have h6 : Entails.eval a c1058 := derived1058 a h
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c262 := h 261 (by decide)
  have h11 : Entails.eval a c870 := h 869 (by decide)
  have h12 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1190 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1190 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c308, some c262, some c182, some c55, some c1189, some c873, some c779, some c50, some c386, some c1113, some c605, some c88, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1190 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1190 : lratChecker f1190 p1190 = .success := by decide +kernel
theorem unsat1190 : Unsatisfiable (PosFin 31) f1190 := by
  apply lratCheckerSound f1190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1190
  · intro a ha; simp [p1190] at ha; subst a; trivial
  · exact checked1190
theorem derived1190 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1190 := by
  apply localUnsat_implies_entails f1190 [c1125, c308, c262, c182, c55, c1189, c873, c779, c50, c386, c1113, c605, c88] c1190 unsat1190 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c1189 := derived1189 a h
  have h6 : Entails.eval a c873 := h 872 (by decide)
  have h7 : Entails.eval a c779 := h 778 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c386 := h 385 (by decide)
  have h10 : Entails.eval a c1113 := derived1113 a h
  have h11 : Entails.eval a c605 := h 604 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1191 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1191 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c308, some c262, some c182, some c1189, some c600, some c251, some c27, some c333, some c88, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1191 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1191 : lratChecker f1191 p1191 = .success := by decide +kernel
theorem unsat1191 : Unsatisfiable (PosFin 31) f1191 := by
  apply lratCheckerSound f1191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1191
  · intro a ha; simp [p1191] at ha; subst a; trivial
  · exact checked1191
theorem derived1191 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1191 := by
  apply localUnsat_implies_entails f1191 [c1125, c308, c262, c182, c1189, c600, c251, c27, c333, c88] c1191 unsat1191 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c1189 := derived1189 a h
  have h5 : Entails.eval a c600 := h 599 (by decide)
  have h6 : Entails.eval a c251 := h 250 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c333 := h 332 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1192 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1192 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c308, some c262, some c182, some c55, some c1189, some c1191, some c25, some c751, some c834, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1192 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1192 : lratChecker f1192 p1192 = .success := by decide +kernel
theorem unsat1192 : Unsatisfiable (PosFin 31) f1192 := by
  apply lratCheckerSound f1192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1192
  · intro a ha; simp [p1192] at ha; subst a; trivial
  · exact checked1192
theorem derived1192 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1192 := by
  apply localUnsat_implies_entails f1192 [c1125, c308, c262, c182, c55, c1189, c1191, c25, c751, c834] c1192 unsat1192 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c1189 := derived1189 a h
  have h6 : Entails.eval a c1191 := derived1191 a h
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c751 := h 750 (by decide)
  have h9 : Entails.eval a c834 := h 833 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1193 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1193 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1189, some c1125, some c55, some c308, some c262, some c182, some c1192, some c1190, some c71, some c304, some c211, some c112, some c61, some c24, some c386, some c554, some c27, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1193 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1193 : lratChecker f1193 p1193 = .success := by decide +kernel
theorem unsat1193 : Unsatisfiable (PosFin 31) f1193 := by
  apply lratCheckerSound f1193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1193
  · intro a ha; simp [p1193] at ha; subst a; trivial
  · exact checked1193
theorem derived1193 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1193 := by
  apply localUnsat_implies_entails f1193 [c1189, c1125, c55, c308, c262, c182, c1192, c1190, c71, c304, c211, c112, c61, c24, c386, c554, c27] c1193 unsat1193 (by rfl) a
  have h0 : Entails.eval a c1189 := derived1189 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c308 := h 307 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c1192 := derived1192 a h
  have h7 : Entails.eval a c1190 := derived1190 a h
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c386 := h 385 (by decide)
  have h15 : Entails.eval a c554 := h 553 (by decide)
  have h16 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1194 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨16, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1194 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c24, some c61, some c502, some c554, some c516, some c280, some c709, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1194 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1194 : lratChecker f1194 p1194 = .success := by decide +kernel
theorem unsat1194 : Unsatisfiable (PosFin 31) f1194 := by
  apply lratCheckerSound f1194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1194
  · intro a ha; simp [p1194] at ha; subst a; trivial
  · exact checked1194
theorem derived1194 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1194 := by
  apply localUnsat_implies_entails f1194 [c24, c61, c502, c554, c516, c280, c709] c1194 unsat1194 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c502 := h 501 (by decide)
  have h3 : Entails.eval a c554 := h 553 (by decide)
  have h4 : Entails.eval a c516 := h 515 (by decide)
  have h5 : Entails.eval a c280 := h 279 (by decide)
  have h6 : Entails.eval a c709 := h 708 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1195 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1195 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1193, some c1189, some c1125, some c71, some c304, some c211, some c112, some c61, some c24, some c1194, some c309, some c491, some c1002, some c27, some c452, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1195 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1195 : lratChecker f1195 p1195 = .success := by decide +kernel
theorem unsat1195 : Unsatisfiable (PosFin 31) f1195 := by
  apply lratCheckerSound f1195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1195
  · intro a ha; simp [p1195] at ha; subst a; trivial
  · exact checked1195
theorem derived1195 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1195 := by
  apply localUnsat_implies_entails f1195 [c1193, c1189, c1125, c71, c304, c211, c112, c61, c24, c1194, c309, c491, c1002, c27, c452] c1195 unsat1195 (by rfl) a
  have h0 : Entails.eval a c1193 := derived1193 a h
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c211 := h 210 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c1194 := derived1194 a h
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c491 := h 490 (by decide)
  have h12 : Entails.eval a c1002 := derived1002 a h
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c452 := h 451 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1196 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨18, by decide⟩, false), (⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1196 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1193, some c1195, some c871, some c491, some c27, some c843, some c31, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1196 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1196 : lratChecker f1196 p1196 = .success := by decide +kernel
theorem unsat1196 : Unsatisfiable (PosFin 31) f1196 := by
  apply lratCheckerSound f1196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1196
  · intro a ha; simp [p1196] at ha; subst a; trivial
  · exact checked1196
theorem derived1196 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1196 := by
  apply localUnsat_implies_entails f1196 [c1193, c1195, c871, c491, c27, c843, c31] c1196 unsat1196 (by rfl) a
  have h0 : Entails.eval a c1193 := derived1193 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c871 := h 870 (by decide)
  have h3 : Entails.eval a c491 := h 490 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c843 := h 842 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1197 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1197 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1195, some c1193, some c1189, some c1125, some c1196, some c777, some c595, some c406, some c447, some c461, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1197 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1197 : lratChecker f1197 p1197 = .success := by decide +kernel
theorem unsat1197 : Unsatisfiable (PosFin 31) f1197 := by
  apply lratCheckerSound f1197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1197
  · intro a ha; simp [p1197] at ha; subst a; trivial
  · exact checked1197
theorem derived1197 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1197 := by
  apply localUnsat_implies_entails f1197 [c1195, c1193, c1189, c1125, c1196, c777, c595, c406, c447, c461] c1197 unsat1197 (by rfl) a
  have h0 : Entails.eval a c1195 := derived1195 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c1196 := derived1196 a h
  have h5 : Entails.eval a c777 := h 776 (by decide)
  have h6 : Entails.eval a c595 := h 594 (by decide)
  have h7 : Entails.eval a c406 := h 405 (by decide)
  have h8 : Entails.eval a c447 := h 446 (by decide)
  have h9 : Entails.eval a c461 := h 460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1198 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1198 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1193, some c1195, some c871, some c1189, some c1197, some c36, some c791, some c332, some c167, some c323, some c843, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1198 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1198 : lratChecker f1198 p1198 = .success := by decide +kernel
theorem unsat1198 : Unsatisfiable (PosFin 31) f1198 := by
  apply lratCheckerSound f1198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1198
  · intro a ha; simp [p1198] at ha; subst a; trivial
  · exact checked1198
theorem derived1198 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1198 := by
  apply localUnsat_implies_entails f1198 [c1193, c1195, c871, c1189, c1197, c36, c791, c332, c167, c323, c843] c1198 unsat1198 (by rfl) a
  have h0 : Entails.eval a c1193 := derived1193 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c871 := h 870 (by decide)
  have h3 : Entails.eval a c1189 := derived1189 a h
  have h4 : Entails.eval a c1197 := derived1197 a h
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c791 := h 790 (by decide)
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c167 := h 166 (by decide)
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c843 := h 842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1199 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1199 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c36, some c791, some c54, some c167, some c50, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1199 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1199 : lratChecker f1199 p1199 = .success := by decide +kernel
theorem unsat1199 : Unsatisfiable (PosFin 31) f1199 := by
  apply lratCheckerSound f1199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1199
  · intro a ha; simp [p1199] at ha; subst a; trivial
  · exact checked1199
theorem derived1199 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1199 := by
  apply localUnsat_implies_entails f1199 [c36, c791, c54, c167, c50] c1199 unsat1199 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c791 := h 790 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c167 := h 166 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1200 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1200 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c27, some c50, some c305, some c873, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1200 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1200 : lratChecker f1200 p1200 = .success := by decide +kernel
theorem unsat1200 : Unsatisfiable (PosFin 31) f1200 := by
  apply lratCheckerSound f1200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1200
  · intro a ha; simp [p1200] at ha; subst a; trivial
  · exact checked1200
theorem derived1200 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1200 := by
  apply localUnsat_implies_entails f1200 [c27, c50, c305, c873] c1200 unsat1200 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c873 := h 872 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1201 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1201 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1193, some c1189, some c1125, some c1195, some c1198, some c1199, some c1200, some c888, some c461, some c1113, some c447, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1201 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1201 : lratChecker f1201 p1201 = .success := by decide +kernel
theorem unsat1201 : Unsatisfiable (PosFin 31) f1201 := by
  apply lratCheckerSound f1201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1201
  · intro a ha; simp [p1201] at ha; subst a; trivial
  · exact checked1201
theorem derived1201 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1201 := by
  apply localUnsat_implies_entails f1201 [c1193, c1189, c1125, c1195, c1198, c1199, c1200, c888, c461, c1113, c447] c1201 unsat1201 (by rfl) a
  have h0 : Entails.eval a c1193 := derived1193 a h
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1195 := derived1195 a h
  have h4 : Entails.eval a c1198 := derived1198 a h
  have h5 : Entails.eval a c1199 := derived1199 a h
  have h6 : Entails.eval a c1200 := derived1200 a h
  have h7 : Entails.eval a c888 := h 887 (by decide)
  have h8 : Entails.eval a c461 := h 460 (by decide)
  have h9 : Entails.eval a c1113 := derived1113 a h
  have h10 : Entails.eval a c447 := h 446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1202 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1202 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1193, some c1125, some c888, some c461, some c1113, some c447, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1202 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1202 : lratChecker f1202 p1202 = .success := by decide +kernel
theorem unsat1202 : Unsatisfiable (PosFin 31) f1202 := by
  apply lratCheckerSound f1202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1202
  · intro a ha; simp [p1202] at ha; subst a; trivial
  · exact checked1202
theorem derived1202 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1202 := by
  apply localUnsat_implies_entails f1202 [c1193, c1125, c888, c461, c1113, c447] c1202 unsat1202 (by rfl) a
  have h0 : Entails.eval a c1193 := derived1193 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c888 := h 887 (by decide)
  have h3 : Entails.eval a c461 := h 460 (by decide)
  have h4 : Entails.eval a c1113 := derived1113 a h
  have h5 : Entails.eval a c447 := h 446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1202

end CochromaticTwenty.Certificates.Z12Direct_5_8_13
