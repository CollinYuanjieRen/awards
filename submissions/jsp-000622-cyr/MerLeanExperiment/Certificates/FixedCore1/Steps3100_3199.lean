import MerLeanExperiment.Certificates.FixedCore1.Steps3000_3099

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8981 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨10, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8981 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7343, some c8917, some c1574, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8981 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8981 : lratChecker f8981 p8981 = .success := by decide +kernel
theorem unsat8981 : Unsatisfiable (PosFin 65) f8981 := by
  apply lratCheckerSound f8981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8981
  · intro a ha; simp [p8981] at ha; subst a; trivial
  · exact checked8981
theorem derived8981 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8981 := by
  apply localUnsat_implies_entails f8981 [c7343, c8917, c1574] c8981 unsat8981 (by rfl) a
  have h0 : Entails.eval a c7343 := derived7343 a h
  have h1 : Entails.eval a c8917 := derived8917 a h
  have h2 : Entails.eval a c1574 := h 1573 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8982 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8982 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8919, some c8321, some c8533, some c8490, some c8104, some c8528, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8982 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8982 : lratChecker f8982 p8982 = .success := by decide +kernel
theorem unsat8982 : Unsatisfiable (PosFin 65) f8982 := by
  apply lratCheckerSound f8982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8982
  · intro a ha; simp [p8982] at ha; subst a; trivial
  · exact checked8982
theorem derived8982 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8982 := by
  apply localUnsat_implies_entails f8982 [c8919, c8321, c8533, c8490, c8104, c8528] c8982 unsat8982 (by rfl) a
  have h0 : Entails.eval a c8919 := derived8919 a h
  have h1 : Entails.eval a c8321 := derived8321 a h
  have h2 : Entails.eval a c8533 := derived8533 a h
  have h3 : Entails.eval a c8490 := derived8490 a h
  have h4 : Entails.eval a c8104 := derived8104 a h
  have h5 : Entails.eval a c8528 := derived8528 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8983 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8983 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8959, some c8912, some c8840, some c8970, some c8980, some c8123, some c8919, some c8982, some c8981, some c8920, some c8956, some c8545, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8983 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8983 : lratChecker f8983 p8983 = .success := by decide +kernel
theorem unsat8983 : Unsatisfiable (PosFin 65) f8983 := by
  apply lratCheckerSound f8983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8983
  · intro a ha; simp [p8983] at ha; subst a; trivial
  · exact checked8983
theorem derived8983 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8983 := by
  apply localUnsat_implies_entails f8983 [c8959, c8912, c8840, c8970, c8980, c8123, c8919, c8982, c8981, c8920, c8956, c8545] c8983 unsat8983 (by rfl) a
  have h0 : Entails.eval a c8959 := derived8959 a h
  have h1 : Entails.eval a c8912 := derived8912 a h
  have h2 : Entails.eval a c8840 := derived8840 a h
  have h3 : Entails.eval a c8970 := derived8970 a h
  have h4 : Entails.eval a c8980 := derived8980 a h
  have h5 : Entails.eval a c8123 := derived8123 a h
  have h6 : Entails.eval a c8919 := derived8919 a h
  have h7 : Entails.eval a c8982 := derived8982 a h
  have h8 : Entails.eval a c8981 := derived8981 a h
  have h9 : Entails.eval a c8920 := derived8920 a h
  have h10 : Entails.eval a c8956 := derived8956 a h
  have h11 : Entails.eval a c8545 := derived8545 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8984 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8984 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1280, some c1300, some c1201, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8984 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8984 : lratChecker f8984 p8984 = .success := by decide +kernel
theorem unsat8984 : Unsatisfiable (PosFin 65) f8984 := by
  apply lratCheckerSound f8984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8984
  · intro a ha; simp [p8984] at ha; subst a; trivial
  · exact checked8984
theorem derived8984 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8984 := by
  apply localUnsat_implies_entails f8984 [c1280, c1300, c1201] c8984 unsat8984 (by rfl) a
  have h0 : Entails.eval a c1280 := h 1279 (by decide)
  have h1 : Entails.eval a c1300 := h 1299 (by decide)
  have h2 : Entails.eval a c1201 := h 1200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8985 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8985 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8623, some c8624, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8985 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8985 : lratChecker f8985 p8985 = .success := by decide +kernel
theorem unsat8985 : Unsatisfiable (PosFin 65) f8985 := by
  apply lratCheckerSound f8985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8985
  · intro a ha; simp [p8985] at ha; subst a; trivial
  · exact checked8985
theorem derived8985 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8985 := by
  apply localUnsat_implies_entails f8985 [c8623, c8624] c8985 unsat8985 (by rfl) a
  have h0 : Entails.eval a c8623 := derived8623 a h
  have h1 : Entails.eval a c8624 := derived8624 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8986 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8986 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8984, some c8946, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8986 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8986 : lratChecker f8986 p8986 = .success := by decide +kernel
theorem unsat8986 : Unsatisfiable (PosFin 65) f8986 := by
  apply lratCheckerSound f8986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8986
  · intro a ha; simp [p8986] at ha; subst a; trivial
  · exact checked8986
theorem derived8986 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8986 := by
  apply localUnsat_implies_entails f8986 [c8984, c8946] c8986 unsat8986 (by rfl) a
  have h0 : Entails.eval a c8984 := derived8984 a h
  have h1 : Entails.eval a c8946 := derived8946 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8987 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8987 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8985, some c8986, some c8860, some c8536, some c8514, some c8961, some c1297, some c1193, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8987 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8987 : lratChecker f8987 p8987 = .success := by decide +kernel
theorem unsat8987 : Unsatisfiable (PosFin 65) f8987 := by
  apply lratCheckerSound f8987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8987
  · intro a ha; simp [p8987] at ha; subst a; trivial
  · exact checked8987
theorem derived8987 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8987 := by
  apply localUnsat_implies_entails f8987 [c8985, c8986, c8860, c8536, c8514, c8961, c1297, c1193] c8987 unsat8987 (by rfl) a
  have h0 : Entails.eval a c8985 := derived8985 a h
  have h1 : Entails.eval a c8986 := derived8986 a h
  have h2 : Entails.eval a c8860 := derived8860 a h
  have h3 : Entails.eval a c8536 := derived8536 a h
  have h4 : Entails.eval a c8514 := derived8514 a h
  have h5 : Entails.eval a c8961 := derived8961 a h
  have h6 : Entails.eval a c1297 := h 1296 (by decide)
  have h7 : Entails.eval a c1193 := h 1192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8988 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8988 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8983, some c8912, some c8935, some c8959, some c8985, some c8986, some c8860, some c8670, some c8987, some c8098, some c439, some c434, some c8502, some c8943, some c449, some c8482, some c473, some c477, some c1302, some c8503, some c8481, some c8903, some c1100, some c1458, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8988 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked8988 : lratChecker f8988 p8988 = .success := by decide +kernel
theorem unsat8988 : Unsatisfiable (PosFin 65) f8988 := by
  apply lratCheckerSound f8988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8988
  · intro a ha; simp [p8988] at ha; subst a; trivial
  · exact checked8988
theorem derived8988 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8988 := by
  apply localUnsat_implies_entails f8988 [c8840, c8983, c8912, c8935, c8959, c8985, c8986, c8860, c8670, c8987, c8098, c439, c434, c8502, c8943, c449, c8482, c473, c477, c1302, c8503, c8481, c8903, c1100, c1458] c8988 unsat8988 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8983 := derived8983 a h
  have h2 : Entails.eval a c8912 := derived8912 a h
  have h3 : Entails.eval a c8935 := derived8935 a h
  have h4 : Entails.eval a c8959 := derived8959 a h
  have h5 : Entails.eval a c8985 := derived8985 a h
  have h6 : Entails.eval a c8986 := derived8986 a h
  have h7 : Entails.eval a c8860 := derived8860 a h
  have h8 : Entails.eval a c8670 := derived8670 a h
  have h9 : Entails.eval a c8987 := derived8987 a h
  have h10 : Entails.eval a c8098 := derived8098 a h
  have h11 : Entails.eval a c439 := h 438 (by decide)
  have h12 : Entails.eval a c434 := h 433 (by decide)
  have h13 : Entails.eval a c8502 := derived8502 a h
  have h14 : Entails.eval a c8943 := derived8943 a h
  have h15 : Entails.eval a c449 := h 448 (by decide)
  have h16 : Entails.eval a c8482 := derived8482 a h
  have h17 : Entails.eval a c473 := h 472 (by decide)
  have h18 : Entails.eval a c477 := h 476 (by decide)
  have h19 : Entails.eval a c1302 := h 1301 (by decide)
  have h20 : Entails.eval a c8503 := derived8503 a h
  have h21 : Entails.eval a c8481 := derived8481 a h
  have h22 : Entails.eval a c8903 := derived8903 a h
  have h23 : Entails.eval a c1100 := h 1099 (by decide)
  have h24 : Entails.eval a c1458 := h 1457 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8989 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8989 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8544, some c8336, some c8961, some c8490, some c8418, some c1742, some c1746, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8989 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8989 : lratChecker f8989 p8989 = .success := by decide +kernel
theorem unsat8989 : Unsatisfiable (PosFin 65) f8989 := by
  apply lratCheckerSound f8989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8989
  · intro a ha; simp [p8989] at ha; subst a; trivial
  · exact checked8989
theorem derived8989 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8989 := by
  apply localUnsat_implies_entails f8989 [c8544, c8336, c8961, c8490, c8418, c1742, c1746] c8989 unsat8989 (by rfl) a
  have h0 : Entails.eval a c8544 := derived8544 a h
  have h1 : Entails.eval a c8336 := derived8336 a h
  have h2 : Entails.eval a c8961 := derived8961 a h
  have h3 : Entails.eval a c8490 := derived8490 a h
  have h4 : Entails.eval a c8418 := derived8418 a h
  have h5 : Entails.eval a c1742 := h 1741 (by decide)
  have h6 : Entails.eval a c1746 := h 1745 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8990 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨31, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8990 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1178, some c2552, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8990 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8990 : lratChecker f8990 p8990 = .success := by decide +kernel
theorem unsat8990 : Unsatisfiable (PosFin 65) f8990 := by
  apply lratCheckerSound f8990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8990
  · intro a ha; simp [p8990] at ha; subst a; trivial
  · exact checked8990
theorem derived8990 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8990 := by
  apply localUnsat_implies_entails f8990 [c1178, c2552] c8990 unsat8990 (by rfl) a
  have h0 : Entails.eval a c1178 := h 1177 (by decide)
  have h1 : Entails.eval a c2552 := h 2551 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8991 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8991 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8912, some c8983, some c8935, some c8959, some c8985, some c8986, some c8860, some c8988, some c8989, some c8098, some c1923, some c1917, some c1926, some c1912, some c1892, some c8501, some c8620, some c8482, some c8503, some c2144, some c2168, some c8481, some c8990, some c7817, some c1099, some c1038, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8991 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked8991 : lratChecker f8991 p8991 = .success := by decide +kernel
theorem unsat8991 : Unsatisfiable (PosFin 65) f8991 := by
  apply lratCheckerSound f8991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8991
  · intro a ha; simp [p8991] at ha; subst a; trivial
  · exact checked8991
theorem derived8991 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8991 := by
  apply localUnsat_implies_entails f8991 [c8840, c8912, c8983, c8935, c8959, c8985, c8986, c8860, c8988, c8989, c8098, c1923, c1917, c1926, c1912, c1892, c8501, c8620, c8482, c8503, c2144, c2168, c8481, c8990, c7817, c1099, c1038] c8991 unsat8991 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8912 := derived8912 a h
  have h2 : Entails.eval a c8983 := derived8983 a h
  have h3 : Entails.eval a c8935 := derived8935 a h
  have h4 : Entails.eval a c8959 := derived8959 a h
  have h5 : Entails.eval a c8985 := derived8985 a h
  have h6 : Entails.eval a c8986 := derived8986 a h
  have h7 : Entails.eval a c8860 := derived8860 a h
  have h8 : Entails.eval a c8988 := derived8988 a h
  have h9 : Entails.eval a c8989 := derived8989 a h
  have h10 : Entails.eval a c8098 := derived8098 a h
  have h11 : Entails.eval a c1923 := h 1922 (by decide)
  have h12 : Entails.eval a c1917 := h 1916 (by decide)
  have h13 : Entails.eval a c1926 := h 1925 (by decide)
  have h14 : Entails.eval a c1912 := h 1911 (by decide)
  have h15 : Entails.eval a c1892 := h 1891 (by decide)
  have h16 : Entails.eval a c8501 := derived8501 a h
  have h17 : Entails.eval a c8620 := derived8620 a h
  have h18 : Entails.eval a c8482 := derived8482 a h
  have h19 : Entails.eval a c8503 := derived8503 a h
  have h20 : Entails.eval a c2144 := h 2143 (by decide)
  have h21 : Entails.eval a c2168 := h 2167 (by decide)
  have h22 : Entails.eval a c8481 := derived8481 a h
  have h23 : Entails.eval a c8990 := derived8990 a h
  have h24 : Entails.eval a c7817 := derived7817 a h
  have h25 : Entails.eval a c1099 := h 1098 (by decide)
  have h26 : Entails.eval a c1038 := h 1037 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8992 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8992 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8983, some c8912, some c8840, some c8935, some c8991, some c8546, some c8524, some c8098, some c1926, some c1912, some c1910, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8992 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8992 : lratChecker f8992 p8992 = .success := by decide +kernel
theorem unsat8992 : Unsatisfiable (PosFin 65) f8992 := by
  apply lratCheckerSound f8992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8992
  · intro a ha; simp [p8992] at ha; subst a; trivial
  · exact checked8992
theorem derived8992 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8992 := by
  apply localUnsat_implies_entails f8992 [c8983, c8912, c8840, c8935, c8991, c8546, c8524, c8098, c1926, c1912, c1910] c8992 unsat8992 (by rfl) a
  have h0 : Entails.eval a c8983 := derived8983 a h
  have h1 : Entails.eval a c8912 := derived8912 a h
  have h2 : Entails.eval a c8840 := derived8840 a h
  have h3 : Entails.eval a c8935 := derived8935 a h
  have h4 : Entails.eval a c8991 := derived8991 a h
  have h5 : Entails.eval a c8546 := derived8546 a h
  have h6 : Entails.eval a c8524 := derived8524 a h
  have h7 : Entails.eval a c8098 := derived8098 a h
  have h8 : Entails.eval a c1926 := h 1925 (by decide)
  have h9 : Entails.eval a c1912 := h 1911 (by decide)
  have h10 : Entails.eval a c1910 := h 1909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8993 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8993 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8992, some c8983, some c8959, some c8840, some c8670, some c8580, some c8936, some c8623, some c8581, some c1992, some c89, some c560, some c1352, some c137, some c6748, some c3107, some c3110, some c6749, some c3112, some c94, some c3103, some c3098, some c100, some c3099, some c3100, some c3106, some c3102, some c3105, some c5891, some c3104, some c6464, some c3097, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8993 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked8993 : lratChecker f8993 p8993 = .success := by decide +kernel
theorem unsat8993 : Unsatisfiable (PosFin 65) f8993 := by
  apply lratCheckerSound f8993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8993
  · intro a ha; simp [p8993] at ha; subst a; trivial
  · exact checked8993
theorem derived8993 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8993 := by
  apply localUnsat_implies_entails f8993 [c8992, c8983, c8959, c8840, c8670, c8580, c8936, c8623, c8581, c1992, c89, c560, c1352, c137, c6748, c3107, c3110, c6749, c3112, c94, c3103, c3098, c100, c3099, c3100, c3106, c3102, c3105, c5891, c3104, c6464, c3097] c8993 unsat8993 (by rfl) a
  have h0 : Entails.eval a c8992 := derived8992 a h
  have h1 : Entails.eval a c8983 := derived8983 a h
  have h2 : Entails.eval a c8959 := derived8959 a h
  have h3 : Entails.eval a c8840 := derived8840 a h
  have h4 : Entails.eval a c8670 := derived8670 a h
  have h5 : Entails.eval a c8580 := derived8580 a h
  have h6 : Entails.eval a c8936 := derived8936 a h
  have h7 : Entails.eval a c8623 := derived8623 a h
  have h8 : Entails.eval a c8581 := derived8581 a h
  have h9 : Entails.eval a c1992 := h 1991 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c560 := h 559 (by decide)
  have h12 : Entails.eval a c1352 := h 1351 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c6748 := derived6748 a h
  have h15 : Entails.eval a c3107 := h 3106 (by decide)
  have h16 : Entails.eval a c3110 := h 3109 (by decide)
  have h17 : Entails.eval a c6749 := derived6749 a h
  have h18 : Entails.eval a c3112 := h 3111 (by decide)
  have h19 : Entails.eval a c94 := h 93 (by decide)
  have h20 : Entails.eval a c3103 := h 3102 (by decide)
  have h21 : Entails.eval a c3098 := h 3097 (by decide)
  have h22 : Entails.eval a c100 := h 99 (by decide)
  have h23 : Entails.eval a c3099 := h 3098 (by decide)
  have h24 : Entails.eval a c3100 := h 3099 (by decide)
  have h25 : Entails.eval a c3106 := h 3105 (by decide)
  have h26 : Entails.eval a c3102 := h 3101 (by decide)
  have h27 : Entails.eval a c3105 := h 3104 (by decide)
  have h28 : Entails.eval a c5891 := derived5891 a h
  have h29 : Entails.eval a c3104 := h 3103 (by decide)
  have h30 : Entails.eval a c6464 := derived6464 a h
  have h31 : Entails.eval a c3097 := h 3096 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8994 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8994 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8992, some c8983, some c8840, some c8993, some c8659, some c8595, some c8938, some c8643, some c8577, some c8354, some c8644, some c2178, some c2170, some c8642, some c8640, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8994 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8994 : lratChecker f8994 p8994 = .success := by decide +kernel
theorem unsat8994 : Unsatisfiable (PosFin 65) f8994 := by
  apply lratCheckerSound f8994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8994
  · intro a ha; simp [p8994] at ha; subst a; trivial
  · exact checked8994
theorem derived8994 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8994 := by
  apply localUnsat_implies_entails f8994 [c8992, c8983, c8840, c8993, c8659, c8595, c8938, c8643, c8577, c8354, c8644, c2178, c2170, c8642, c8640] c8994 unsat8994 (by rfl) a
  have h0 : Entails.eval a c8992 := derived8992 a h
  have h1 : Entails.eval a c8983 := derived8983 a h
  have h2 : Entails.eval a c8840 := derived8840 a h
  have h3 : Entails.eval a c8993 := derived8993 a h
  have h4 : Entails.eval a c8659 := derived8659 a h
  have h5 : Entails.eval a c8595 := derived8595 a h
  have h6 : Entails.eval a c8938 := derived8938 a h
  have h7 : Entails.eval a c8643 := derived8643 a h
  have h8 : Entails.eval a c8577 := derived8577 a h
  have h9 : Entails.eval a c8354 := derived8354 a h
  have h10 : Entails.eval a c8644 := derived8644 a h
  have h11 : Entails.eval a c2178 := h 2177 (by decide)
  have h12 : Entails.eval a c2170 := h 2169 (by decide)
  have h13 : Entails.eval a c8642 := derived8642 a h
  have h14 : Entails.eval a c8640 := derived8640 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8995 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8995 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8919, some c8378, some c8500, some c8984, some c2147, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8995 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8995 : lratChecker f8995 p8995 = .success := by decide +kernel
theorem unsat8995 : Unsatisfiable (PosFin 65) f8995 := by
  apply lratCheckerSound f8995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8995
  · intro a ha; simp [p8995] at ha; subst a; trivial
  · exact checked8995
theorem derived8995 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8995 := by
  apply localUnsat_implies_entails f8995 [c8919, c8378, c8500, c8984, c2147] c8995 unsat8995 (by rfl) a
  have h0 : Entails.eval a c8919 := derived8919 a h
  have h1 : Entails.eval a c8378 := derived8378 a h
  have h2 : Entails.eval a c8500 := derived8500 a h
  have h3 : Entails.eval a c8984 := derived8984 a h
  have h4 : Entails.eval a c2147 := h 2146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8996 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8996 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8912, some c8959, some c8983, some c8992, some c8994, some c8919, some c8995, some c8546, some c8524, some c8098, some c8956, some c8957, some c8116, some c1320, some c1106, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8996 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8996 : lratChecker f8996 p8996 = .success := by decide +kernel
theorem unsat8996 : Unsatisfiable (PosFin 65) f8996 := by
  apply lratCheckerSound f8996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8996
  · intro a ha; simp [p8996] at ha; subst a; trivial
  · exact checked8996
theorem derived8996 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8996 := by
  apply localUnsat_implies_entails f8996 [c8840, c8912, c8959, c8983, c8992, c8994, c8919, c8995, c8546, c8524, c8098, c8956, c8957, c8116, c1320, c1106] c8996 unsat8996 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8912 := derived8912 a h
  have h2 : Entails.eval a c8959 := derived8959 a h
  have h3 : Entails.eval a c8983 := derived8983 a h
  have h4 : Entails.eval a c8992 := derived8992 a h
  have h5 : Entails.eval a c8994 := derived8994 a h
  have h6 : Entails.eval a c8919 := derived8919 a h
  have h7 : Entails.eval a c8995 := derived8995 a h
  have h8 : Entails.eval a c8546 := derived8546 a h
  have h9 : Entails.eval a c8524 := derived8524 a h
  have h10 : Entails.eval a c8098 := derived8098 a h
  have h11 : Entails.eval a c8956 := derived8956 a h
  have h12 : Entails.eval a c8957 := derived8957 a h
  have h13 : Entails.eval a c8116 := derived8116 a h
  have h14 : Entails.eval a c1320 := h 1319 (by decide)
  have h15 : Entails.eval a c1106 := h 1105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8997 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨39, by decide⟩, true), (⟨63, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8997 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5519, some c5510, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p8997 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8997 : lratChecker f8997 p8997 = .success := by decide +kernel
theorem unsat8997 : Unsatisfiable (PosFin 65) f8997 := by
  apply lratCheckerSound f8997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8997
  · intro a ha; simp [p8997] at ha; subst a; trivial
  · exact checked8997
theorem derived8997 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8997 := by
  apply localUnsat_implies_entails f8997 [c5519, c5510] c8997 unsat8997 (by rfl) a
  have h0 : Entails.eval a c5519 := h 5518 (by decide)
  have h1 : Entails.eval a c5510 := h 5509 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8998 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨45, by decide⟩, false), (⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8998 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5626, some c6809, some c6942, some c6979, some c5651, some c6658, some c4915, some c5532, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p8998 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8998 : lratChecker f8998 p8998 = .success := by decide +kernel
theorem unsat8998 : Unsatisfiable (PosFin 65) f8998 := by
  apply lratCheckerSound f8998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8998
  · intro a ha; simp [p8998] at ha; subst a; trivial
  · exact checked8998
theorem derived8998 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8998 := by
  apply localUnsat_implies_entails f8998 [c5626, c6809, c6942, c6979, c5651, c6658, c4915, c5532] c8998 unsat8998 (by rfl) a
  have h0 : Entails.eval a c5626 := h 5625 (by decide)
  have h1 : Entails.eval a c6809 := derived6809 a h
  have h2 : Entails.eval a c6942 := derived6942 a h
  have h3 : Entails.eval a c6979 := derived6979 a h
  have h4 : Entails.eval a c5651 := h 5650 (by decide)
  have h5 : Entails.eval a c6658 := derived6658 a h
  have h6 : Entails.eval a c4915 := h 4914 (by decide)
  have h7 : Entails.eval a c5532 := h 5531 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8999 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨63, by decide⟩, false), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8999 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8997, some c8998, some c4448, some c4193, some c3489, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p8999 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8999 : lratChecker f8999 p8999 = .success := by decide +kernel
theorem unsat8999 : Unsatisfiable (PosFin 65) f8999 := by
  apply lratCheckerSound f8999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8999
  · intro a ha; simp [p8999] at ha; subst a; trivial
  · exact checked8999
theorem derived8999 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8999 := by
  apply localUnsat_implies_entails f8999 [c8997, c8998, c4448, c4193, c3489] c8999 unsat8999 (by rfl) a
  have h0 : Entails.eval a c8997 := derived8997 a h
  have h1 : Entails.eval a c8998 := derived8998 a h
  have h2 : Entails.eval a c4448 := h 4447 (by decide)
  have h3 : Entails.eval a c4193 := h 4192 (by decide)
  have h4 : Entails.eval a c3489 := h 3488 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9000 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨39, by decide⟩, false), (⟨63, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9000 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5637, some c4193, some c4118, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9000 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9000 : lratChecker f9000 p9000 = .success := by decide +kernel
theorem unsat9000 : Unsatisfiable (PosFin 65) f9000 := by
  apply lratCheckerSound f9000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9000
  · intro a ha; simp [p9000] at ha; subst a; trivial
  · exact checked9000
theorem derived9000 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9000 := by
  apply localUnsat_implies_entails f9000 [c5637, c4193, c4118] c9000 unsat9000 (by rfl) a
  have h0 : Entails.eval a c5637 := h 5636 (by decide)
  have h1 : Entails.eval a c4193 := h 4192 (by decide)
  have h2 : Entails.eval a c4118 := h 4117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9001 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, false), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9001 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c4213, some c6861, some c4005, some c4285, some c3972, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9001 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9001 : lratChecker f9001 p9001 = .success := by decide +kernel
theorem unsat9001 : Unsatisfiable (PosFin 65) f9001 := by
  apply lratCheckerSound f9001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9001
  · intro a ha; simp [p9001] at ha; subst a; trivial
  · exact checked9001
theorem derived9001 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9001 := by
  apply localUnsat_implies_entails f9001 [c7129, c4213, c6861, c4005, c4285, c3972] c9001 unsat9001 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c4213 := h 4212 (by decide)
  have h2 : Entails.eval a c6861 := derived6861 a h
  have h3 : Entails.eval a c4005 := h 4004 (by decide)
  have h4 : Entails.eval a c4285 := h 4284 (by decide)
  have h5 : Entails.eval a c3972 := h 3971 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9002 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9002 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5651, some c6942, some c5626, some c7129, some c6658, some c4915, some c9001, some c6855, some c4028, some c4334, some c4159, some c4169, some c4200, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9002 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9002 : lratChecker f9002 p9002 = .success := by decide +kernel
theorem unsat9002 : Unsatisfiable (PosFin 65) f9002 := by
  apply lratCheckerSound f9002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9002
  · intro a ha; simp [p9002] at ha; subst a; trivial
  · exact checked9002
theorem derived9002 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9002 := by
  apply localUnsat_implies_entails f9002 [c5651, c6942, c5626, c7129, c6658, c4915, c9001, c6855, c4028, c4334, c4159, c4169, c4200] c9002 unsat9002 (by rfl) a
  have h0 : Entails.eval a c5651 := h 5650 (by decide)
  have h1 : Entails.eval a c6942 := derived6942 a h
  have h2 : Entails.eval a c5626 := h 5625 (by decide)
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c6658 := derived6658 a h
  have h5 : Entails.eval a c4915 := h 4914 (by decide)
  have h6 : Entails.eval a c9001 := derived9001 a h
  have h7 : Entails.eval a c6855 := derived6855 a h
  have h8 : Entails.eval a c4028 := h 4027 (by decide)
  have h9 : Entails.eval a c4334 := h 4333 (by decide)
  have h10 : Entails.eval a c4159 := h 4158 (by decide)
  have h11 : Entails.eval a c4169 := h 4168 (by decide)
  have h12 : Entails.eval a c4200 := h 4199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9003 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨37, by decide⟩, true), (⟨53, by decide⟩, true), (⟨42, by decide⟩, true), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9003 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9002, some c5774, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9003 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9003 : lratChecker f9003 p9003 = .success := by decide +kernel
theorem unsat9003 : Unsatisfiable (PosFin 65) f9003 := by
  apply lratCheckerSound f9003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9003
  · intro a ha; simp [p9003] at ha; subst a; trivial
  · exact checked9003
theorem derived9003 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9003 := by
  apply localUnsat_implies_entails f9003 [c9002, c5774] c9003 unsat9003 (by rfl) a
  have h0 : Entails.eval a c9002 := derived9002 a h
  have h1 : Entails.eval a c5774 := h 5773 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9004 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨35, by decide⟩, true), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9004 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8999, some c9000, some c5626, some c5467, some c6960, some c6872, some c9003, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9004 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9004 : lratChecker f9004 p9004 = .success := by decide +kernel
theorem unsat9004 : Unsatisfiable (PosFin 65) f9004 := by
  apply lratCheckerSound f9004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9004
  · intro a ha; simp [p9004] at ha; subst a; trivial
  · exact checked9004
theorem derived9004 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9004 := by
  apply localUnsat_implies_entails f9004 [c8999, c9000, c5626, c5467, c6960, c6872, c9003] c9004 unsat9004 (by rfl) a
  have h0 : Entails.eval a c8999 := derived8999 a h
  have h1 : Entails.eval a c9000 := derived9000 a h
  have h2 : Entails.eval a c5626 := h 5625 (by decide)
  have h3 : Entails.eval a c5467 := h 5466 (by decide)
  have h4 : Entails.eval a c6960 := derived6960 a h
  have h5 : Entails.eval a c6872 := derived6872 a h
  have h6 : Entails.eval a c9003 := derived9003 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9005 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨63, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9005 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5626, some c6809, some c7037, some c5651, some c8998, some c6979, some c6996, some c6658, some c6477, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9005 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9005 : lratChecker f9005 p9005 = .success := by decide +kernel
theorem unsat9005 : Unsatisfiable (PosFin 65) f9005 := by
  apply lratCheckerSound f9005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9005
  · intro a ha; simp [p9005] at ha; subst a; trivial
  · exact checked9005
theorem derived9005 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9005 := by
  apply localUnsat_implies_entails f9005 [c5626, c6809, c7037, c5651, c8998, c6979, c6996, c6658, c6477] c9005 unsat9005 (by rfl) a
  have h0 : Entails.eval a c5626 := h 5625 (by decide)
  have h1 : Entails.eval a c6809 := derived6809 a h
  have h2 : Entails.eval a c7037 := derived7037 a h
  have h3 : Entails.eval a c5651 := h 5650 (by decide)
  have h4 : Entails.eval a c8998 := derived8998 a h
  have h5 : Entails.eval a c6979 := derived6979 a h
  have h6 : Entails.eval a c6996 := derived6996 a h
  have h7 : Entails.eval a c6658 := derived6658 a h
  have h8 : Entails.eval a c6477 := derived6477 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9006 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨37, by decide⟩, true), (⟨42, by decide⟩, true), (⟨63, by decide⟩, true), (⟨43, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9006 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6658, some c4234, some c4214, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9006 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9006 : lratChecker f9006 p9006 = .success := by decide +kernel
theorem unsat9006 : Unsatisfiable (PosFin 65) f9006 := by
  apply lratCheckerSound f9006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9006
  · intro a ha; simp [p9006] at ha; subst a; trivial
  · exact checked9006
theorem derived9006 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9006 := by
  apply localUnsat_implies_entails f9006 [c6658, c4234, c4214] c9006 unsat9006 (by rfl) a
  have h0 : Entails.eval a c6658 := derived6658 a h
  have h1 : Entails.eval a c4234 := h 4233 (by decide)
  have h2 : Entails.eval a c4214 := h 4213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9007 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨42, by decide⟩, true), (⟨62, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9007 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5772, some c7036, some c5784, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9007 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9007 : lratChecker f9007 p9007 = .success := by decide +kernel
theorem unsat9007 : Unsatisfiable (PosFin 65) f9007 := by
  apply lratCheckerSound f9007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9007
  · intro a ha; simp [p9007] at ha; subst a; trivial
  · exact checked9007
theorem derived9007 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9007 := by
  apply localUnsat_implies_entails f9007 [c5772, c7036, c5784] c9007 unsat9007 (by rfl) a
  have h0 : Entails.eval a c5772 := h 5771 (by decide)
  have h1 : Entails.eval a c7036 := derived7036 a h
  have h2 : Entails.eval a c5784 := h 5783 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9008 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9008 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c5630, some c5629, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9008 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9008 : lratChecker f9008 p9008 = .success := by decide +kernel
theorem unsat9008 : Unsatisfiable (PosFin 65) f9008 := by
  apply lratCheckerSound f9008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9008
  · intro a ha; simp [p9008] at ha; subst a; trivial
  · exact checked9008
theorem derived9008 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9008 := by
  apply localUnsat_implies_entails f9008 [c7129, c5630, c5629] c9008 unsat9008 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c5630 := h 5629 (by decide)
  have h2 : Entails.eval a c5629 := h 5628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9009 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9009 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9007, some c9006, some c6978, some c6977, some c5149, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9009 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9009 : lratChecker f9009 p9009 = .success := by decide +kernel
theorem unsat9009 : Unsatisfiable (PosFin 65) f9009 := by
  apply lratCheckerSound f9009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9009
  · intro a ha; simp [p9009] at ha; subst a; trivial
  · exact checked9009
theorem derived9009 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9009 := by
  apply localUnsat_implies_entails f9009 [c9007, c9006, c6978, c6977, c5149] c9009 unsat9009 (by rfl) a
  have h0 : Entails.eval a c9007 := derived9007 a h
  have h1 : Entails.eval a c9006 := derived9006 a h
  have h2 : Entails.eval a c6978 := derived6978 a h
  have h3 : Entails.eval a c6977 := derived6977 a h
  have h4 : Entails.eval a c5149 := h 5148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9010 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨33, by decide⟩, false), (⟨53, by decide⟩, true), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9010 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9005, some c9008, some c9009, some c3797, some c3805, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9010 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9010 : lratChecker f9010 p9010 = .success := by decide +kernel
theorem unsat9010 : Unsatisfiable (PosFin 65) f9010 := by
  apply lratCheckerSound f9010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9010
  · intro a ha; simp [p9010] at ha; subst a; trivial
  · exact checked9010
theorem derived9010 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9010 := by
  apply localUnsat_implies_entails f9010 [c9005, c9008, c9009, c3797, c3805] c9010 unsat9010 (by rfl) a
  have h0 : Entails.eval a c9005 := derived9005 a h
  have h1 : Entails.eval a c9008 := derived9008 a h
  have h2 : Entails.eval a c9009 := derived9009 a h
  have h3 : Entails.eval a c3797 := h 3796 (by decide)
  have h4 : Entails.eval a c3805 := h 3804 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9011 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9011 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3530, some c6783, some c3547, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9011 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9011 : lratChecker f9011 p9011 = .success := by decide +kernel
theorem unsat9011 : Unsatisfiable (PosFin 65) f9011 := by
  apply lratCheckerSound f9011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9011
  · intro a ha; simp [p9011] at ha; subst a; trivial
  · exact checked9011
theorem derived9011 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9011 := by
  apply localUnsat_implies_entails f9011 [c3530, c6783, c3547] c9011 unsat9011 (by rfl) a
  have h0 : Entails.eval a c3530 := h 3529 (by decide)
  have h1 : Entails.eval a c6783 := derived6783 a h
  have h2 : Entails.eval a c3547 := h 3546 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9012 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨42, by decide⟩, true), (⟨63, by decide⟩, false), (⟨43, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9012 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5637, some c4193, some c5789, some c4219, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9012 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9012 : lratChecker f9012 p9012 = .success := by decide +kernel
theorem unsat9012 : Unsatisfiable (PosFin 65) f9012 := by
  apply lratCheckerSound f9012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9012
  · intro a ha; simp [p9012] at ha; subst a; trivial
  · exact checked9012
theorem derived9012 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9012 := by
  apply localUnsat_implies_entails f9012 [c5637, c4193, c5789, c4219] c9012 unsat9012 (by rfl) a
  have h0 : Entails.eval a c5637 := h 5636 (by decide)
  have h1 : Entails.eval a c4193 := h 4192 (by decide)
  have h2 : Entails.eval a c5789 := h 5788 (by decide)
  have h3 : Entails.eval a c4219 := h 4218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9013 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨33, by decide⟩, false), (⟨53, by decide⟩, true), (⟨48, by decide⟩, true), (⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9013 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9004, some c9011, some c9012, some c6942, some c6779, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p9013 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9013 : lratChecker f9013 p9013 = .success := by decide +kernel
theorem unsat9013 : Unsatisfiable (PosFin 65) f9013 := by
  apply lratCheckerSound f9013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9013
  · intro a ha; simp [p9013] at ha; subst a; trivial
  · exact checked9013
theorem derived9013 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9013 := by
  apply localUnsat_implies_entails f9013 [c9004, c9011, c9012, c6942, c6779] c9013 unsat9013 (by rfl) a
  have h0 : Entails.eval a c9004 := derived9004 a h
  have h1 : Entails.eval a c9011 := derived9011 a h
  have h2 : Entails.eval a c9012 := derived9012 a h
  have h3 : Entails.eval a c6942 := derived6942 a h
  have h4 : Entails.eval a c6779 := derived6779 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9014 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9014 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9010, some c9013, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p9014 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9014 : lratChecker f9014 p9014 = .success := by decide +kernel
theorem unsat9014 : Unsatisfiable (PosFin 65) f9014 := by
  apply lratCheckerSound f9014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9014
  · intro a ha; simp [p9014] at ha; subst a; trivial
  · exact checked9014
theorem derived9014 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9014 := by
  apply localUnsat_implies_entails f9014 [c9010, c9013] c9014 unsat9014 (by rfl) a
  have h0 : Entails.eval a c9010 := derived9010 a h
  have h1 : Entails.eval a c9013 := derived9013 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9015 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9015 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3765, some c3778, some c6434, some c3767, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9015 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9015 : lratChecker f9015 p9015 = .success := by decide +kernel
theorem unsat9015 : Unsatisfiable (PosFin 65) f9015 := by
  apply lratCheckerSound f9015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9015
  · intro a ha; simp [p9015] at ha; subst a; trivial
  · exact checked9015
theorem derived9015 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9015 := by
  apply localUnsat_implies_entails f9015 [c3765, c3778, c6434, c3767] c9015 unsat9015 (by rfl) a
  have h0 : Entails.eval a c3765 := h 3764 (by decide)
  have h1 : Entails.eval a c3778 := h 3777 (by decide)
  have h2 : Entails.eval a c6434 := derived6434 a h
  have h3 : Entails.eval a c3767 := h 3766 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9016 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9016 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9015, some c9014, some c7129, some c9008, some c3838, some c3829, some c3832, some c3846, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9016 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9016 : lratChecker f9016 p9016 = .success := by decide +kernel
theorem unsat9016 : Unsatisfiable (PosFin 65) f9016 := by
  apply lratCheckerSound f9016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9016
  · intro a ha; simp [p9016] at ha; subst a; trivial
  · exact checked9016
theorem derived9016 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9016 := by
  apply localUnsat_implies_entails f9016 [c9015, c9014, c7129, c9008, c3838, c3829, c3832, c3846] c9016 unsat9016 (by rfl) a
  have h0 : Entails.eval a c9015 := derived9015 a h
  have h1 : Entails.eval a c9014 := derived9014 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9008 := derived9008 a h
  have h4 : Entails.eval a c3838 := h 3837 (by decide)
  have h5 : Entails.eval a c3829 := h 3828 (by decide)
  have h6 : Entails.eval a c3832 := h 3831 (by decide)
  have h7 : Entails.eval a c3846 := h 3845 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9017 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9017 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5626, some c3827, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9017 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9017 : lratChecker f9017 p9017 = .success := by decide +kernel
theorem unsat9017 : Unsatisfiable (PosFin 65) f9017 := by
  apply lratCheckerSound f9017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9017
  · intro a ha; simp [p9017] at ha; subst a; trivial
  · exact checked9017
theorem derived9017 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9017 := by
  apply localUnsat_implies_entails f9017 [c5626, c3827] c9017 unsat9017 (by rfl) a
  have h0 : Entails.eval a c5626 := h 5625 (by decide)
  have h1 : Entails.eval a c3827 := h 3826 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9018 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, true), (⟨40, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9018 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9014, some c9017, some c9016, some c3839, some c5637, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p9018 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9018 : lratChecker f9018 p9018 = .success := by decide +kernel
theorem unsat9018 : Unsatisfiable (PosFin 65) f9018 := by
  apply lratCheckerSound f9018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9018
  · intro a ha; simp [p9018] at ha; subst a; trivial
  · exact checked9018
theorem derived9018 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9018 := by
  apply localUnsat_implies_entails f9018 [c9014, c9017, c9016, c3839, c5637] c9018 unsat9018 (by rfl) a
  have h0 : Entails.eval a c9014 := derived9014 a h
  have h1 : Entails.eval a c9017 := derived9017 a h
  have h2 : Entails.eval a c9016 := derived9016 a h
  have h3 : Entails.eval a c3839 := h 3838 (by decide)
  have h4 : Entails.eval a c5637 := h 5636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9019 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9019 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9015, some c9018, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9019 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9019 : lratChecker f9019 p9019 = .success := by decide +kernel
theorem unsat9019 : Unsatisfiable (PosFin 65) f9019 := by
  apply lratCheckerSound f9019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9019
  · intro a ha; simp [p9019] at ha; subst a; trivial
  · exact checked9019
theorem derived9019 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9019 := by
  apply localUnsat_implies_entails f9019 [c9015, c9018] c9019 unsat9019 (by rfl) a
  have h0 : Entails.eval a c9015 := derived9015 a h
  have h1 : Entails.eval a c9018 := derived9018 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9020 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9020 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5624, some c3825, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9020 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9020 : lratChecker f9020 p9020 = .success := by decide +kernel
theorem unsat9020 : Unsatisfiable (PosFin 65) f9020 := by
  apply lratCheckerSound f9020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9020
  · intro a ha; simp [p9020] at ha; subst a; trivial
  · exact checked9020
theorem derived9020 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9020 := by
  apply localUnsat_implies_entails f9020 [c5624, c3825] c9020 unsat9020 (by rfl) a
  have h0 : Entails.eval a c5624 := h 5623 (by decide)
  have h1 : Entails.eval a c3825 := h 3824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9021 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨53, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9021 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6658, some c6652, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p9021 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9021 : lratChecker f9021 p9021 = .success := by decide +kernel
theorem unsat9021 : Unsatisfiable (PosFin 65) f9021 := by
  apply lratCheckerSound f9021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9021
  · intro a ha; simp [p9021] at ha; subst a; trivial
  · exact checked9021
theorem derived9021 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9021 := by
  apply localUnsat_implies_entails f9021 [c6658, c6652] c9021 unsat9021 (by rfl) a
  have h0 : Entails.eval a c6658 := derived6658 a h
  have h1 : Entails.eval a c6652 := derived6652 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9022 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨62, by decide⟩, true), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9022 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6973, some c5108, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p9022 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9022 : lratChecker f9022 p9022 = .success := by decide +kernel
theorem unsat9022 : Unsatisfiable (PosFin 65) f9022 := by
  apply lratCheckerSound f9022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9022
  · intro a ha; simp [p9022] at ha; subst a; trivial
  · exact checked9022
theorem derived9022 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9022 := by
  apply localUnsat_implies_entails f9022 [c6973, c5108] c9022 unsat9022 (by rfl) a
  have h0 : Entails.eval a c6973 := derived6973 a h
  have h1 : Entails.eval a c5108 := h 5107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9023 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨54, by decide⟩, true), (⟨61, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9023 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7022, some c6936, some c4154, some c6826, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p9023 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9023 : lratChecker f9023 p9023 = .success := by decide +kernel
theorem unsat9023 : Unsatisfiable (PosFin 65) f9023 := by
  apply lratCheckerSound f9023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9023
  · intro a ha; simp [p9023] at ha; subst a; trivial
  · exact checked9023
theorem derived9023 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9023 := by
  apply localUnsat_implies_entails f9023 [c7022, c6936, c4154, c6826] c9023 unsat9023 (by rfl) a
  have h0 : Entails.eval a c7022 := derived7022 a h
  have h1 : Entails.eval a c6936 := derived6936 a h
  have h2 : Entails.eval a c4154 := h 4153 (by decide)
  have h3 : Entails.eval a c6826 := derived6826 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9024 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨45, by decide⟩, true), (⟨54, by decide⟩, true), (⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9024 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9023, some c4151, some c5796, some c4812, some c3991, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9024 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9024 : lratChecker f9024 p9024 = .success := by decide +kernel
theorem unsat9024 : Unsatisfiable (PosFin 65) f9024 := by
  apply lratCheckerSound f9024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9024
  · intro a ha; simp [p9024] at ha; subst a; trivial
  · exact checked9024
theorem derived9024 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9024 := by
  apply localUnsat_implies_entails f9024 [c9023, c4151, c5796, c4812, c3991] c9024 unsat9024 (by rfl) a
  have h0 : Entails.eval a c9023 := derived9023 a h
  have h1 : Entails.eval a c4151 := h 4150 (by decide)
  have h2 : Entails.eval a c5796 := h 5795 (by decide)
  have h3 : Entails.eval a c4812 := h 4811 (by decide)
  have h4 : Entails.eval a c3991 := h 3990 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9025 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨57, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨49, by decide⟩, false), (⟨42, by decide⟩, false), (⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9025 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3829, some c9022, some c5725, some c5200, some c3824, some c3845, some c3815, some c2700, some c2861, some c3030, some c3042, some c3281, some c3277, some c3091, some c3161, some c3266, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9025 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9025 : lratChecker f9025 p9025 = .success := by decide +kernel
theorem unsat9025 : Unsatisfiable (PosFin 65) f9025 := by
  apply lratCheckerSound f9025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9025
  · intro a ha; simp [p9025] at ha; subst a; trivial
  · exact checked9025
theorem derived9025 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9025 := by
  apply localUnsat_implies_entails f9025 [c3829, c9022, c5725, c5200, c3824, c3845, c3815, c2700, c2861, c3030, c3042, c3281, c3277, c3091, c3161, c3266] c9025 unsat9025 (by rfl) a
  have h0 : Entails.eval a c3829 := h 3828 (by decide)
  have h1 : Entails.eval a c9022 := derived9022 a h
  have h2 : Entails.eval a c5725 := h 5724 (by decide)
  have h3 : Entails.eval a c5200 := h 5199 (by decide)
  have h4 : Entails.eval a c3824 := h 3823 (by decide)
  have h5 : Entails.eval a c3845 := h 3844 (by decide)
  have h6 : Entails.eval a c3815 := h 3814 (by decide)
  have h7 : Entails.eval a c2700 := h 2699 (by decide)
  have h8 : Entails.eval a c2861 := h 2860 (by decide)
  have h9 : Entails.eval a c3030 := h 3029 (by decide)
  have h10 : Entails.eval a c3042 := h 3041 (by decide)
  have h11 : Entails.eval a c3281 := h 3280 (by decide)
  have h12 : Entails.eval a c3277 := h 3276 (by decide)
  have h13 : Entails.eval a c3091 := h 3090 (by decide)
  have h14 : Entails.eval a c3161 := h 3160 (by decide)
  have h15 : Entails.eval a c3266 := h 3265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9026 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨20, by decide⟩, true), (⟨57, by decide⟩, false), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨60, by decide⟩, false), (⟨41, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9026 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3222, some c3209, some c8619, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p9026 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9026 : lratChecker f9026 p9026 = .success := by decide +kernel
theorem unsat9026 : Unsatisfiable (PosFin 65) f9026 := by
  apply lratCheckerSound f9026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9026
  · intro a ha; simp [p9026] at ha; subst a; trivial
  · exact checked9026
theorem derived9026 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9026 := by
  apply localUnsat_implies_entails f9026 [c3222, c3209, c8619] c9026 unsat9026 (by rfl) a
  have h0 : Entails.eval a c3222 := h 3221 (by decide)
  have h1 : Entails.eval a c3209 := h 3208 (by decide)
  have h2 : Entails.eval a c8619 := derived8619 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9027 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨20, by decide⟩, true), (⟨57, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9027 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8619, some c3293, some c3200, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9027 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9027 : lratChecker f9027 p9027 = .success := by decide +kernel
theorem unsat9027 : Unsatisfiable (PosFin 65) f9027 := by
  apply lratCheckerSound f9027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9027
  · intro a ha; simp [p9027] at ha; subst a; trivial
  · exact checked9027
theorem derived9027 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9027 := by
  apply localUnsat_implies_entails f9027 [c8619, c3293, c3200] c9027 unsat9027 (by rfl) a
  have h0 : Entails.eval a c8619 := derived8619 a h
  have h1 : Entails.eval a c3293 := h 3292 (by decide)
  have h2 : Entails.eval a c3200 := h 3199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9028 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨20, by decide⟩, true), (⟨57, by decide⟩, false), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨60, by decide⟩, false), (⟨41, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9028 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9026, some c9027, some c3229, some c3238, some c3353, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9028 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9028 : lratChecker f9028 p9028 = .success := by decide +kernel
theorem unsat9028 : Unsatisfiable (PosFin 65) f9028 := by
  apply lratCheckerSound f9028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9028
  · intro a ha; simp [p9028] at ha; subst a; trivial
  · exact checked9028
theorem derived9028 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9028 := by
  apply localUnsat_implies_entails f9028 [c9026, c9027, c3229, c3238, c3353] c9028 unsat9028 (by rfl) a
  have h0 : Entails.eval a c9026 := derived9026 a h
  have h1 : Entails.eval a c9027 := derived9027 a h
  have h2 : Entails.eval a c3229 := h 3228 (by decide)
  have h3 : Entails.eval a c3238 := h 3237 (by decide)
  have h4 : Entails.eval a c3353 := h 3352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9029 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨20, by decide⟩, true), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9029 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3229, some c3238, some c3353, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p9029 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9029 : lratChecker f9029 p9029 = .success := by decide +kernel
theorem unsat9029 : Unsatisfiable (PosFin 65) f9029 := by
  apply lratCheckerSound f9029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9029
  · intro a ha; simp [p9029] at ha; subst a; trivial
  · exact checked9029
theorem derived9029 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9029 := by
  apply localUnsat_implies_entails f9029 [c3229, c3238, c3353] c9029 unsat9029 (by rfl) a
  have h0 : Entails.eval a c3229 := h 3228 (by decide)
  have h1 : Entails.eval a c3238 := h 3237 (by decide)
  have h2 : Entails.eval a c3353 := h 3352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9030 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨49, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9030 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3075, some c3283, some c3353, some c3050, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p9030 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9030 : lratChecker f9030 p9030 = .success := by decide +kernel
theorem unsat9030 : Unsatisfiable (PosFin 65) f9030 := by
  apply lratCheckerSound f9030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9030
  · intro a ha; simp [p9030] at ha; subst a; trivial
  · exact checked9030
theorem derived9030 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9030 := by
  apply localUnsat_implies_entails f9030 [c3075, c3283, c3353, c3050] c9030 unsat9030 (by rfl) a
  have h0 : Entails.eval a c3075 := h 3074 (by decide)
  have h1 : Entails.eval a c3283 := h 3282 (by decide)
  have h2 : Entails.eval a c3353 := h 3352 (by decide)
  have h3 : Entails.eval a c3050 := h 3049 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9031 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨45, by decide⟩, true), (⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9031 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3824, some c3845, some c9024, some c3815, some c3819, some c3829, some c9022, some c9020, some c5463, some c5725, some c4175, some c4730, some c5200, some c4460, some c3501, some c9025, some c9028, some c6312, some c9029, some c9030, some c3242, some c3204, some c3323, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9031 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9031 : lratChecker f9031 p9031 = .success := by decide +kernel
theorem unsat9031 : Unsatisfiable (PosFin 65) f9031 := by
  apply lratCheckerSound f9031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9031
  · intro a ha; simp [p9031] at ha; subst a; trivial
  · exact checked9031
theorem derived9031 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9031 := by
  apply localUnsat_implies_entails f9031 [c3824, c3845, c9024, c3815, c3819, c3829, c9022, c9020, c5463, c5725, c4175, c4730, c5200, c4460, c3501, c9025, c9028, c6312, c9029, c9030, c3242, c3204, c3323] c9031 unsat9031 (by rfl) a
  have h0 : Entails.eval a c3824 := h 3823 (by decide)
  have h1 : Entails.eval a c3845 := h 3844 (by decide)
  have h2 : Entails.eval a c9024 := derived9024 a h
  have h3 : Entails.eval a c3815 := h 3814 (by decide)
  have h4 : Entails.eval a c3819 := h 3818 (by decide)
  have h5 : Entails.eval a c3829 := h 3828 (by decide)
  have h6 : Entails.eval a c9022 := derived9022 a h
  have h7 : Entails.eval a c9020 := derived9020 a h
  have h8 : Entails.eval a c5463 := h 5462 (by decide)
  have h9 : Entails.eval a c5725 := h 5724 (by decide)
  have h10 : Entails.eval a c4175 := h 4174 (by decide)
  have h11 : Entails.eval a c4730 := h 4729 (by decide)
  have h12 : Entails.eval a c5200 := h 5199 (by decide)
  have h13 : Entails.eval a c4460 := h 4459 (by decide)
  have h14 : Entails.eval a c3501 := h 3500 (by decide)
  have h15 : Entails.eval a c9025 := derived9025 a h
  have h16 : Entails.eval a c9028 := derived9028 a h
  have h17 : Entails.eval a c6312 := derived6312 a h
  have h18 : Entails.eval a c9029 := derived9029 a h
  have h19 : Entails.eval a c9030 := derived9030 a h
  have h20 : Entails.eval a c3242 := h 3241 (by decide)
  have h21 : Entails.eval a c3204 := h 3203 (by decide)
  have h22 : Entails.eval a c3323 := h 3322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9032 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨55, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨61, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9032 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3248, some c3206, some c3233, some c6766, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9032 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9032 : lratChecker f9032 p9032 = .success := by decide +kernel
theorem unsat9032 : Unsatisfiable (PosFin 65) f9032 := by
  apply lratCheckerSound f9032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9032
  · intro a ha; simp [p9032] at ha; subst a; trivial
  · exact checked9032
theorem derived9032 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9032 := by
  apply localUnsat_implies_entails f9032 [c3248, c3206, c3233, c6766] c9032 unsat9032 (by rfl) a
  have h0 : Entails.eval a c3248 := h 3247 (by decide)
  have h1 : Entails.eval a c3206 := h 3205 (by decide)
  have h2 : Entails.eval a c3233 := h 3232 (by decide)
  have h3 : Entails.eval a c6766 := derived6766 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9033 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨55, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false), (⟨62, by decide⟩, true), (⟨61, by decide⟩, true), (⟨41, by decide⟩, false), (⟨63, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9033 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9032, some c2787, some c2789, some c3255, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9033 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9033 : lratChecker f9033 p9033 = .success := by decide +kernel
theorem unsat9033 : Unsatisfiable (PosFin 65) f9033 := by
  apply lratCheckerSound f9033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9033
  · intro a ha; simp [p9033] at ha; subst a; trivial
  · exact checked9033
theorem derived9033 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9033 := by
  apply localUnsat_implies_entails f9033 [c9032, c2787, c2789, c3255] c9033 unsat9033 (by rfl) a
  have h0 : Entails.eval a c9032 := derived9032 a h
  have h1 : Entails.eval a c2787 := h 2786 (by decide)
  have h2 : Entails.eval a c2789 := h 2788 (by decide)
  have h3 : Entails.eval a c3255 := h 3254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9034 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9034 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9019, some c9020, some c7129, some c3824, some c3831, some c3829, some c3842, some c3845, some c9021, some c9024, some c3815, some c3819, some c9031, some c7010, some c7030, some c4176, some c5553, some c6925, some c3501, some c3441, some c9033, some c2850, some c2861, some c3040, some c3027, some c6764, some c6765, some c3166, some c3089, some c3265, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9034 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked9034 : lratChecker f9034 p9034 = .success := by decide +kernel
theorem unsat9034 : Unsatisfiable (PosFin 65) f9034 := by
  apply lratCheckerSound f9034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9034
  · intro a ha; simp [p9034] at ha; subst a; trivial
  · exact checked9034
theorem derived9034 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9034 := by
  apply localUnsat_implies_entails f9034 [c9019, c9020, c7129, c3824, c3831, c3829, c3842, c3845, c9021, c9024, c3815, c3819, c9031, c7010, c7030, c4176, c5553, c6925, c3501, c3441, c9033, c2850, c2861, c3040, c3027, c6764, c6765, c3166, c3089, c3265] c9034 unsat9034 (by rfl) a
  have h0 : Entails.eval a c9019 := derived9019 a h
  have h1 : Entails.eval a c9020 := derived9020 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c3824 := h 3823 (by decide)
  have h4 : Entails.eval a c3831 := h 3830 (by decide)
  have h5 : Entails.eval a c3829 := h 3828 (by decide)
  have h6 : Entails.eval a c3842 := h 3841 (by decide)
  have h7 : Entails.eval a c3845 := h 3844 (by decide)
  have h8 : Entails.eval a c9021 := derived9021 a h
  have h9 : Entails.eval a c9024 := derived9024 a h
  have h10 : Entails.eval a c3815 := h 3814 (by decide)
  have h11 : Entails.eval a c3819 := h 3818 (by decide)
  have h12 : Entails.eval a c9031 := derived9031 a h
  have h13 : Entails.eval a c7010 := derived7010 a h
  have h14 : Entails.eval a c7030 := derived7030 a h
  have h15 : Entails.eval a c4176 := h 4175 (by decide)
  have h16 : Entails.eval a c5553 := h 5552 (by decide)
  have h17 : Entails.eval a c6925 := derived6925 a h
  have h18 : Entails.eval a c3501 := h 3500 (by decide)
  have h19 : Entails.eval a c3441 := h 3440 (by decide)
  have h20 : Entails.eval a c9033 := derived9033 a h
  have h21 : Entails.eval a c2850 := h 2849 (by decide)
  have h22 : Entails.eval a c2861 := h 2860 (by decide)
  have h23 : Entails.eval a c3040 := h 3039 (by decide)
  have h24 : Entails.eval a c3027 := h 3026 (by decide)
  have h25 : Entails.eval a c6764 := derived6764 a h
  have h26 : Entails.eval a c6765 := derived6765 a h
  have h27 : Entails.eval a c3166 := h 3165 (by decide)
  have h28 : Entails.eval a c3089 := h 3088 (by decide)
  have h29 : Entails.eval a c3265 := h 3264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9035 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9035 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9019, some c9020, some c9034, some c6650, some c5629, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9035 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9035 : lratChecker f9035 p9035 = .success := by decide +kernel
theorem unsat9035 : Unsatisfiable (PosFin 65) f9035 := by
  apply lratCheckerSound f9035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9035
  · intro a ha; simp [p9035] at ha; subst a; trivial
  · exact checked9035
theorem derived9035 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9035 := by
  apply localUnsat_implies_entails f9035 [c9019, c9020, c9034, c6650, c5629] c9035 unsat9035 (by rfl) a
  have h0 : Entails.eval a c9019 := derived9019 a h
  have h1 : Entails.eval a c9020 := derived9020 a h
  have h2 : Entails.eval a c9034 := derived9034 a h
  have h3 : Entails.eval a c6650 := derived6650 a h
  have h4 : Entails.eval a c5629 := h 5628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9036 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9036 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9019, some c6650, some c5624, some c5629, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9036 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9036 : lratChecker f9036 p9036 = .success := by decide +kernel
theorem unsat9036 : Unsatisfiable (PosFin 65) f9036 := by
  apply lratCheckerSound f9036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9036
  · intro a ha; simp [p9036] at ha; subst a; trivial
  · exact checked9036
theorem derived9036 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9036 := by
  apply localUnsat_implies_entails f9036 [c9019, c6650, c5624, c5629] c9036 unsat9036 (by rfl) a
  have h0 : Entails.eval a c9019 := derived9019 a h
  have h1 : Entails.eval a c6650 := derived6650 a h
  have h2 : Entails.eval a c5624 := h 5623 (by decide)
  have h3 : Entails.eval a c5629 := h 5628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9037 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨51, by decide⟩, true), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9037 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4182, some c3455, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9037 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9037 : lratChecker f9037 p9037 = .success := by decide +kernel
theorem unsat9037 : Unsatisfiable (PosFin 65) f9037 := by
  apply lratCheckerSound f9037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9037
  · intro a ha; simp [p9037] at ha; subst a; trivial
  · exact checked9037
theorem derived9037 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9037 := by
  apply localUnsat_implies_entails f9037 [c4182, c3455] c9037 unsat9037 (by rfl) a
  have h0 : Entails.eval a c4182 := h 4181 (by decide)
  have h1 : Entails.eval a c3455 := h 3454 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9038 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨44, by decide⟩, false), (⟨62, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9038 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c4213, some c6861, some c4210, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9038 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9038 : lratChecker f9038 p9038 = .success := by decide +kernel
theorem unsat9038 : Unsatisfiable (PosFin 65) f9038 := by
  apply lratCheckerSound f9038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9038
  · intro a ha; simp [p9038] at ha; subst a; trivial
  · exact checked9038
theorem derived9038 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9038 := by
  apply localUnsat_implies_entails f9038 [c7129, c4213, c6861, c4210] c9038 unsat9038 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c4213 := h 4212 (by decide)
  have h2 : Entails.eval a c6861 := derived6861 a h
  have h3 : Entails.eval a c4210 := h 4209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9039 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨33, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9039 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9035, some c9036, some c9019, some c7129, some c9037, some c3799, some c7095, some c9012, some c5754, some c5139, some c5864, some c9038, some c6855, some c4028, some c4334, some c4159, some c4169, some c4200, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9039 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9039 : lratChecker f9039 p9039 = .success := by decide +kernel
theorem unsat9039 : Unsatisfiable (PosFin 65) f9039 := by
  apply lratCheckerSound f9039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9039
  · intro a ha; simp [p9039] at ha; subst a; trivial
  · exact checked9039
theorem derived9039 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9039 := by
  apply localUnsat_implies_entails f9039 [c9035, c9036, c9019, c7129, c9037, c3799, c7095, c9012, c5754, c5139, c5864, c9038, c6855, c4028, c4334, c4159, c4169, c4200] c9039 unsat9039 (by rfl) a
  have h0 : Entails.eval a c9035 := derived9035 a h
  have h1 : Entails.eval a c9036 := derived9036 a h
  have h2 : Entails.eval a c9019 := derived9019 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9037 := derived9037 a h
  have h5 : Entails.eval a c3799 := h 3798 (by decide)
  have h6 : Entails.eval a c7095 := derived7095 a h
  have h7 : Entails.eval a c9012 := derived9012 a h
  have h8 : Entails.eval a c5754 := h 5753 (by decide)
  have h9 : Entails.eval a c5139 := h 5138 (by decide)
  have h10 : Entails.eval a c5864 := h 5863 (by decide)
  have h11 : Entails.eval a c9038 := derived9038 a h
  have h12 : Entails.eval a c6855 := derived6855 a h
  have h13 : Entails.eval a c4028 := h 4027 (by decide)
  have h14 : Entails.eval a c4334 := h 4333 (by decide)
  have h15 : Entails.eval a c4159 := h 4158 (by decide)
  have h16 : Entails.eval a c4169 := h 4168 (by decide)
  have h17 : Entails.eval a c4200 := h 4199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9040 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9040 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9019, some c9036, some c9035, some c9039, some c9021, some c7095, some c3799, some c4177, some c4174, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9040 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9040 : lratChecker f9040 p9040 = .success := by decide +kernel
theorem unsat9040 : Unsatisfiable (PosFin 65) f9040 := by
  apply lratCheckerSound f9040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9040
  · intro a ha; simp [p9040] at ha; subst a; trivial
  · exact checked9040
theorem derived9040 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9040 := by
  apply localUnsat_implies_entails f9040 [c9019, c9036, c9035, c9039, c9021, c7095, c3799, c4177, c4174] c9040 unsat9040 (by rfl) a
  have h0 : Entails.eval a c9019 := derived9019 a h
  have h1 : Entails.eval a c9036 := derived9036 a h
  have h2 : Entails.eval a c9035 := derived9035 a h
  have h3 : Entails.eval a c9039 := derived9039 a h
  have h4 : Entails.eval a c9021 := derived9021 a h
  have h5 : Entails.eval a c7095 := derived7095 a h
  have h6 : Entails.eval a c3799 := h 3798 (by decide)
  have h7 : Entails.eval a c4177 := h 4176 (by decide)
  have h8 : Entails.eval a c4174 := h 4173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9041 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨42, by decide⟩, false), (⟨45, by decide⟩, true), (⟨43, by decide⟩, true), (⟨41, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9041 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5463, some c5501, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p9041 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9041 : lratChecker f9041 p9041 = .success := by decide +kernel
theorem unsat9041 : Unsatisfiable (PosFin 65) f9041 := by
  apply lratCheckerSound f9041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9041
  · intro a ha; simp [p9041] at ha; subst a; trivial
  · exact checked9041
theorem derived9041 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9041 := by
  apply localUnsat_implies_entails f9041 [c5463, c5501] c9041 unsat9041 (by rfl) a
  have h0 : Entails.eval a c5463 := h 5462 (by decide)
  have h1 : Entails.eval a c5501 := h 5500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9042 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9042 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9036, some c9019, some c7129, some c9035, some c9039, some c9021, some c7095, some c3798, some c3805, some c6810, some c9040, some c3470, some c3471, some c3807, some c9041, some c7010, some c7014, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9042 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9042 : lratChecker f9042 p9042 = .success := by decide +kernel
theorem unsat9042 : Unsatisfiable (PosFin 65) f9042 := by
  apply lratCheckerSound f9042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9042
  · intro a ha; simp [p9042] at ha; subst a; trivial
  · exact checked9042
theorem derived9042 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9042 := by
  apply localUnsat_implies_entails f9042 [c9036, c9019, c7129, c9035, c9039, c9021, c7095, c3798, c3805, c6810, c9040, c3470, c3471, c3807, c9041, c7010, c7014] c9042 unsat9042 (by rfl) a
  have h0 : Entails.eval a c9036 := derived9036 a h
  have h1 : Entails.eval a c9019 := derived9019 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9035 := derived9035 a h
  have h4 : Entails.eval a c9039 := derived9039 a h
  have h5 : Entails.eval a c9021 := derived9021 a h
  have h6 : Entails.eval a c7095 := derived7095 a h
  have h7 : Entails.eval a c3798 := h 3797 (by decide)
  have h8 : Entails.eval a c3805 := h 3804 (by decide)
  have h9 : Entails.eval a c6810 := derived6810 a h
  have h10 : Entails.eval a c9040 := derived9040 a h
  have h11 : Entails.eval a c3470 := h 3469 (by decide)
  have h12 : Entails.eval a c3471 := h 3470 (by decide)
  have h13 : Entails.eval a c3807 := h 3806 (by decide)
  have h14 : Entails.eval a c9041 := derived9041 a h
  have h15 : Entails.eval a c7010 := derived7010 a h
  have h16 : Entails.eval a c7014 := derived7014 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9043 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨34, by decide⟩, false), (⟨42, by decide⟩, false), (⟨59, by decide⟩, false), (⟨54, by decide⟩, true), (⟨62, by decide⟩, true), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨63, by decide⟩, true), (⟨33, by decide⟩, true), (⟨41, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9043 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9021, some c7129, some c7009, some c7030, some c5553, some c4297, some c6804, some c4458, some c3704, some c7013, some c5892, some c5111, some c9033, some c2859, some c2848, some c3039, some c6741, some c3278, some c6765, some c3166, some c3089, some c3264, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9043 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9043 : lratChecker f9043 p9043 = .success := by decide +kernel
theorem unsat9043 : Unsatisfiable (PosFin 65) f9043 := by
  apply lratCheckerSound f9043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9043
  · intro a ha; simp [p9043] at ha; subst a; trivial
  · exact checked9043
theorem derived9043 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9043 := by
  apply localUnsat_implies_entails f9043 [c9021, c7129, c7009, c7030, c5553, c4297, c6804, c4458, c3704, c7013, c5892, c5111, c9033, c2859, c2848, c3039, c6741, c3278, c6765, c3166, c3089, c3264] c9043 unsat9043 (by rfl) a
  have h0 : Entails.eval a c9021 := derived9021 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c7009 := derived7009 a h
  have h3 : Entails.eval a c7030 := derived7030 a h
  have h4 : Entails.eval a c5553 := h 5552 (by decide)
  have h5 : Entails.eval a c4297 := h 4296 (by decide)
  have h6 : Entails.eval a c6804 := derived6804 a h
  have h7 : Entails.eval a c4458 := h 4457 (by decide)
  have h8 : Entails.eval a c3704 := h 3703 (by decide)
  have h9 : Entails.eval a c7013 := derived7013 a h
  have h10 : Entails.eval a c5892 := derived5892 a h
  have h11 : Entails.eval a c5111 := h 5110 (by decide)
  have h12 : Entails.eval a c9033 := derived9033 a h
  have h13 : Entails.eval a c2859 := h 2858 (by decide)
  have h14 : Entails.eval a c2848 := h 2847 (by decide)
  have h15 : Entails.eval a c3039 := h 3038 (by decide)
  have h16 : Entails.eval a c6741 := derived6741 a h
  have h17 : Entails.eval a c3278 := h 3277 (by decide)
  have h18 : Entails.eval a c6765 := derived6765 a h
  have h19 : Entails.eval a c3166 := h 3165 (by decide)
  have h20 : Entails.eval a c3089 := h 3088 (by decide)
  have h21 : Entails.eval a c3264 := h 3263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9044 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨37, by decide⟩, true), (⟨38, by decide⟩, true), (⟨35, by decide⟩, false), (⟨57, by decide⟩, false), (⟨47, by decide⟩, true), (⟨36, by decide⟩, false), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨34, by decide⟩, false), (⟨42, by decide⟩, false), (⟨45, by decide⟩, true), (⟨51, by decide⟩, false), (⟨33, by decide⟩, true), (⟨41, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9044 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2700, some c2860, some c3038, some c3029, some c3278, some c3280, some c3161, some c3085, some c3264, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9044 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9044 : lratChecker f9044 p9044 = .success := by decide +kernel
theorem unsat9044 : Unsatisfiable (PosFin 65) f9044 := by
  apply lratCheckerSound f9044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9044
  · intro a ha; simp [p9044] at ha; subst a; trivial
  · exact checked9044
theorem derived9044 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9044 := by
  apply localUnsat_implies_entails f9044 [c2700, c2860, c3038, c3029, c3278, c3280, c3161, c3085, c3264] c9044 unsat9044 (by rfl) a
  have h0 : Entails.eval a c2700 := h 2699 (by decide)
  have h1 : Entails.eval a c2860 := h 2859 (by decide)
  have h2 : Entails.eval a c3038 := h 3037 (by decide)
  have h3 : Entails.eval a c3029 := h 3028 (by decide)
  have h4 : Entails.eval a c3278 := h 3277 (by decide)
  have h5 : Entails.eval a c3280 := h 3279 (by decide)
  have h6 : Entails.eval a c3161 := h 3160 (by decide)
  have h7 : Entails.eval a c3085 := h 3084 (by decide)
  have h8 : Entails.eval a c3264 := h 3263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9045 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨37, by decide⟩, true), (⟨57, by decide⟩, false), (⟨46, by decide⟩, true), (⟨39, by decide⟩, true), (⟨42, by decide⟩, false), (⟨33, by decide⟩, true), (⟨41, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9045 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3211, some c3232, some c3240, some c3354, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9045 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9045 : lratChecker f9045 p9045 = .success := by decide +kernel
theorem unsat9045 : Unsatisfiable (PosFin 65) f9045 := by
  apply lratCheckerSound f9045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9045
  · intro a ha; simp [p9045] at ha; subst a; trivial
  · exact checked9045
theorem derived9045 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9045 := by
  apply localUnsat_implies_entails f9045 [c3211, c3232, c3240, c3354] c9045 unsat9045 (by rfl) a
  have h0 : Entails.eval a c3211 := h 3210 (by decide)
  have h1 : Entails.eval a c3232 := h 3231 (by decide)
  have h2 : Entails.eval a c3240 := h 3239 (by decide)
  have h3 : Entails.eval a c3354 := h 3353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9046 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨38, by decide⟩, true), (⟨57, by decide⟩, false), (⟨43, by decide⟩, false), (⟨47, by decide⟩, true), (⟨59, by decide⟩, false), (⟨33, by decide⟩, true), (⟨41, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9046 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3074, some c3285, some c3355, some c3047, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9046 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9046 : lratChecker f9046 p9046 = .success := by decide +kernel
theorem unsat9046 : Unsatisfiable (PosFin 65) f9046 := by
  apply lratCheckerSound f9046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9046
  · intro a ha; simp [p9046] at ha; subst a; trivial
  · exact checked9046
theorem derived9046 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9046 := by
  apply localUnsat_implies_entails f9046 [c3074, c3285, c3355, c3047] c9046 unsat9046 (by rfl) a
  have h0 : Entails.eval a c3074 := h 3073 (by decide)
  have h1 : Entails.eval a c3285 := h 3284 (by decide)
  have h2 : Entails.eval a c3355 := h 3354 (by decide)
  have h3 : Entails.eval a c3047 := h 3046 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9047 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9047 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9019, some c9042, some c3762, some c3763, some c6434, some c3773, some c3784, some c9036, some c9021, some c3786, some c9024, some c3788, some c9043, some c5463, some c5725, some c4730, some c5552, some c4296, some c9041, some c6804, some c4460, some c5360, some c9022, some c9044, some c9045, some c9027, some c6312, some c9046, some c3243, some c3205, some c3323, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9047 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked9047 : lratChecker f9047 p9047 = .success := by decide +kernel
theorem unsat9047 : Unsatisfiable (PosFin 65) f9047 := by
  apply lratCheckerSound f9047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9047
  · intro a ha; simp [p9047] at ha; subst a; trivial
  · exact checked9047
theorem derived9047 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9047 := by
  apply localUnsat_implies_entails f9047 [c7129, c9019, c9042, c3762, c3763, c6434, c3773, c3784, c9036, c9021, c3786, c9024, c3788, c9043, c5463, c5725, c4730, c5552, c4296, c9041, c6804, c4460, c5360, c9022, c9044, c9045, c9027, c6312, c9046, c3243, c3205, c3323] c9047 unsat9047 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9019 := derived9019 a h
  have h2 : Entails.eval a c9042 := derived9042 a h
  have h3 : Entails.eval a c3762 := h 3761 (by decide)
  have h4 : Entails.eval a c3763 := h 3762 (by decide)
  have h5 : Entails.eval a c6434 := derived6434 a h
  have h6 : Entails.eval a c3773 := h 3772 (by decide)
  have h7 : Entails.eval a c3784 := h 3783 (by decide)
  have h8 : Entails.eval a c9036 := derived9036 a h
  have h9 : Entails.eval a c9021 := derived9021 a h
  have h10 : Entails.eval a c3786 := h 3785 (by decide)
  have h11 : Entails.eval a c9024 := derived9024 a h
  have h12 : Entails.eval a c3788 := h 3787 (by decide)
  have h13 : Entails.eval a c9043 := derived9043 a h
  have h14 : Entails.eval a c5463 := h 5462 (by decide)
  have h15 : Entails.eval a c5725 := h 5724 (by decide)
  have h16 : Entails.eval a c4730 := h 4729 (by decide)
  have h17 : Entails.eval a c5552 := h 5551 (by decide)
  have h18 : Entails.eval a c4296 := h 4295 (by decide)
  have h19 : Entails.eval a c9041 := derived9041 a h
  have h20 : Entails.eval a c6804 := derived6804 a h
  have h21 : Entails.eval a c4460 := h 4459 (by decide)
  have h22 : Entails.eval a c5360 := h 5359 (by decide)
  have h23 : Entails.eval a c9022 := derived9022 a h
  have h24 : Entails.eval a c9044 := derived9044 a h
  have h25 : Entails.eval a c9045 := derived9045 a h
  have h26 : Entails.eval a c9027 := derived9027 a h
  have h27 : Entails.eval a c6312 := derived6312 a h
  have h28 : Entails.eval a c9046 := derived9046 a h
  have h29 : Entails.eval a c3243 := h 3242 (by decide)
  have h30 : Entails.eval a c3205 := h 3204 (by decide)
  have h31 : Entails.eval a c3323 := h 3322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9048 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9048 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9019, some c9042, some c3763, some c6434, some c9047, some c4177, some c4174, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9048 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9048 : lratChecker f9048 p9048 = .success := by decide +kernel
theorem unsat9048 : Unsatisfiable (PosFin 65) f9048 := by
  apply lratCheckerSound f9048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9048
  · intro a ha; simp [p9048] at ha; subst a; trivial
  · exact checked9048
theorem derived9048 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9048 := by
  apply localUnsat_implies_entails f9048 [c9019, c9042, c3763, c6434, c9047, c4177, c4174] c9048 unsat9048 (by rfl) a
  have h0 : Entails.eval a c9019 := derived9019 a h
  have h1 : Entails.eval a c9042 := derived9042 a h
  have h2 : Entails.eval a c3763 := h 3762 (by decide)
  have h3 : Entails.eval a c6434 := derived6434 a h
  have h4 : Entails.eval a c9047 := derived9047 a h
  have h5 : Entails.eval a c4177 := h 4176 (by decide)
  have h6 : Entails.eval a c4174 := h 4173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9049 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨51, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9049 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c4185, some c4176, some c4175, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9049 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9049 : lratChecker f9049 p9049 = .success := by decide +kernel
theorem unsat9049 : Unsatisfiable (PosFin 65) f9049 := by
  apply lratCheckerSound f9049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9049
  · intro a ha; simp [p9049] at ha; subst a; trivial
  · exact checked9049
theorem derived9049 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9049 := by
  apply localUnsat_implies_entails f9049 [c7129, c4185, c4176, c4175] c9049 unsat9049 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c4185 := h 4184 (by decide)
  have h2 : Entails.eval a c4176 := h 4175 (by decide)
  have h3 : Entails.eval a c4175 := h 4174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9050 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨62, by decide⟩, true), (⟨47, by decide⟩, true), (⟨37, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, true), (⟨45, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9050 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9048, some c7129, some c3775, some c3765, some c3734, some c3625, some c4460, some c4338, some c3695, some c6804, some c3929, some c3594, some c3919, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9050 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9050 : lratChecker f9050 p9050 = .success := by decide +kernel
theorem unsat9050 : Unsatisfiable (PosFin 65) f9050 := by
  apply lratCheckerSound f9050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9050
  · intro a ha; simp [p9050] at ha; subst a; trivial
  · exact checked9050
theorem derived9050 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9050 := by
  apply localUnsat_implies_entails f9050 [c9048, c7129, c3775, c3765, c3734, c3625, c4460, c4338, c3695, c6804, c3929, c3594, c3919] c9050 unsat9050 (by rfl) a
  have h0 : Entails.eval a c9048 := derived9048 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c3775 := h 3774 (by decide)
  have h3 : Entails.eval a c3765 := h 3764 (by decide)
  have h4 : Entails.eval a c3734 := h 3733 (by decide)
  have h5 : Entails.eval a c3625 := h 3624 (by decide)
  have h6 : Entails.eval a c4460 := h 4459 (by decide)
  have h7 : Entails.eval a c4338 := h 4337 (by decide)
  have h8 : Entails.eval a c3695 := h 3694 (by decide)
  have h9 : Entails.eval a c6804 := derived6804 a h
  have h10 : Entails.eval a c3929 := h 3928 (by decide)
  have h11 : Entails.eval a c3594 := h 3593 (by decide)
  have h12 : Entails.eval a c3919 := h 3918 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9051 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨47, by decide⟩, true), (⟨37, by decide⟩, true), (⟨36, by decide⟩, false), (⟨43, by decide⟩, false), (⟨39, by decide⟩, true), (⟨45, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9051 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9048, some c7129, some c9050, some c3460, some c3827, some c3845, some c4460, some c5795, some c3461, some c3563, some c3552, some c3574, some c3536, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9051 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9051 : lratChecker f9051 p9051 = .success := by decide +kernel
theorem unsat9051 : Unsatisfiable (PosFin 65) f9051 := by
  apply lratCheckerSound f9051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9051
  · intro a ha; simp [p9051] at ha; subst a; trivial
  · exact checked9051
theorem derived9051 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9051 := by
  apply localUnsat_implies_entails f9051 [c9048, c7129, c9050, c3460, c3827, c3845, c4460, c5795, c3461, c3563, c3552, c3574, c3536] c9051 unsat9051 (by rfl) a
  have h0 : Entails.eval a c9048 := derived9048 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9050 := derived9050 a h
  have h3 : Entails.eval a c3460 := h 3459 (by decide)
  have h4 : Entails.eval a c3827 := h 3826 (by decide)
  have h5 : Entails.eval a c3845 := h 3844 (by decide)
  have h6 : Entails.eval a c4460 := h 4459 (by decide)
  have h7 : Entails.eval a c5795 := h 5794 (by decide)
  have h8 : Entails.eval a c3461 := h 3460 (by decide)
  have h9 : Entails.eval a c3563 := h 3562 (by decide)
  have h10 : Entails.eval a c3552 := h 3551 (by decide)
  have h11 : Entails.eval a c3574 := h 3573 (by decide)
  have h12 : Entails.eval a c3536 := h 3535 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9052 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9052 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9049, some c7129, some c5619, some c4207, some c4108, some c5502, some c4730, some c5109, some c3991, some c9051, some c3773, some c3834, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9052 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9052 : lratChecker f9052 p9052 = .success := by decide +kernel
theorem unsat9052 : Unsatisfiable (PosFin 65) f9052 := by
  apply lratCheckerSound f9052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9052
  · intro a ha; simp [p9052] at ha; subst a; trivial
  · exact checked9052
theorem derived9052 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9052 := by
  apply localUnsat_implies_entails f9052 [c9049, c7129, c5619, c4207, c4108, c5502, c4730, c5109, c3991, c9051, c3773, c3834] c9052 unsat9052 (by rfl) a
  have h0 : Entails.eval a c9049 := derived9049 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c5619 := h 5618 (by decide)
  have h3 : Entails.eval a c4207 := h 4206 (by decide)
  have h4 : Entails.eval a c4108 := h 4107 (by decide)
  have h5 : Entails.eval a c5502 := h 5501 (by decide)
  have h6 : Entails.eval a c4730 := h 4729 (by decide)
  have h7 : Entails.eval a c5109 := h 5108 (by decide)
  have h8 : Entails.eval a c3991 := h 3990 (by decide)
  have h9 : Entails.eval a c9051 := derived9051 a h
  have h10 : Entails.eval a c3773 := h 3772 (by decide)
  have h11 : Entails.eval a c3834 := h 3833 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9053 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨34, by decide⟩, false), (⟨51, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9053 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3773, some c5630, some c3456, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9053 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9053 : lratChecker f9053 p9053 = .success := by decide +kernel
theorem unsat9053 : Unsatisfiable (PosFin 65) f9053 := by
  apply lratCheckerSound f9053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9053
  · intro a ha; simp [p9053] at ha; subst a; trivial
  · exact checked9053
theorem derived9053 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9053 := by
  apply localUnsat_implies_entails f9053 [c3773, c5630, c3456] c9053 unsat9053 (by rfl) a
  have h0 : Entails.eval a c3773 := h 3772 (by decide)
  have h1 : Entails.eval a c5630 := h 5629 (by decide)
  have h2 : Entails.eval a c3456 := h 3455 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9054 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, false), (⟨62, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9054 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4208, some c6843, some c7015, some c6973, some c6828, some c6981, some c4457, some c7129, some c3460, some c3827, some c3532, some c3828, some c3845, some c3438, some c4335, some c5553, some c3563, some c3807, some c3486, some c3574, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9054 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9054 : lratChecker f9054 p9054 = .success := by decide +kernel
theorem unsat9054 : Unsatisfiable (PosFin 65) f9054 := by
  apply lratCheckerSound f9054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9054
  · intro a ha; simp [p9054] at ha; subst a; trivial
  · exact checked9054
theorem derived9054 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9054 := by
  apply localUnsat_implies_entails f9054 [c4208, c6843, c7015, c6973, c6828, c6981, c4457, c7129, c3460, c3827, c3532, c3828, c3845, c3438, c4335, c5553, c3563, c3807, c3486, c3574] c9054 unsat9054 (by rfl) a
  have h0 : Entails.eval a c4208 := h 4207 (by decide)
  have h1 : Entails.eval a c6843 := derived6843 a h
  have h2 : Entails.eval a c7015 := derived7015 a h
  have h3 : Entails.eval a c6973 := derived6973 a h
  have h4 : Entails.eval a c6828 := derived6828 a h
  have h5 : Entails.eval a c6981 := derived6981 a h
  have h6 : Entails.eval a c4457 := h 4456 (by decide)
  have h7 : Entails.eval a c7129 := derived7129 a h
  have h8 : Entails.eval a c3460 := h 3459 (by decide)
  have h9 : Entails.eval a c3827 := h 3826 (by decide)
  have h10 : Entails.eval a c3532 := h 3531 (by decide)
  have h11 : Entails.eval a c3828 := h 3827 (by decide)
  have h12 : Entails.eval a c3845 := h 3844 (by decide)
  have h13 : Entails.eval a c3438 := h 3437 (by decide)
  have h14 : Entails.eval a c4335 := h 4334 (by decide)
  have h15 : Entails.eval a c5553 := h 5552 (by decide)
  have h16 : Entails.eval a c3563 := h 3562 (by decide)
  have h17 : Entails.eval a c3807 := h 3806 (by decide)
  have h18 : Entails.eval a c3486 := h 3485 (by decide)
  have h19 : Entails.eval a c3574 := h 3573 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9055 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9055 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9048, some c7129, some c9049, some c9052, some c9053, some c5620, some c4208, some c6843, some c7015, some c4457, some c6925, some c6973, some c6828, some c9054, some c3775, some c3765, some c3734, some c3625, some c3695, some c4335, some c6804, some c3704, some c3594, some c3919, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9055 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked9055 : lratChecker f9055 p9055 = .success := by decide +kernel
theorem unsat9055 : Unsatisfiable (PosFin 65) f9055 := by
  apply lratCheckerSound f9055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9055
  · intro a ha; simp [p9055] at ha; subst a; trivial
  · exact checked9055
theorem derived9055 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9055 := by
  apply localUnsat_implies_entails f9055 [c9048, c7129, c9049, c9052, c9053, c5620, c4208, c6843, c7015, c4457, c6925, c6973, c6828, c9054, c3775, c3765, c3734, c3625, c3695, c4335, c6804, c3704, c3594, c3919] c9055 unsat9055 (by rfl) a
  have h0 : Entails.eval a c9048 := derived9048 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9049 := derived9049 a h
  have h3 : Entails.eval a c9052 := derived9052 a h
  have h4 : Entails.eval a c9053 := derived9053 a h
  have h5 : Entails.eval a c5620 := h 5619 (by decide)
  have h6 : Entails.eval a c4208 := h 4207 (by decide)
  have h7 : Entails.eval a c6843 := derived6843 a h
  have h8 : Entails.eval a c7015 := derived7015 a h
  have h9 : Entails.eval a c4457 := h 4456 (by decide)
  have h10 : Entails.eval a c6925 := derived6925 a h
  have h11 : Entails.eval a c6973 := derived6973 a h
  have h12 : Entails.eval a c6828 := derived6828 a h
  have h13 : Entails.eval a c9054 := derived9054 a h
  have h14 : Entails.eval a c3775 := h 3774 (by decide)
  have h15 : Entails.eval a c3765 := h 3764 (by decide)
  have h16 : Entails.eval a c3734 := h 3733 (by decide)
  have h17 : Entails.eval a c3625 := h 3624 (by decide)
  have h18 : Entails.eval a c3695 := h 3694 (by decide)
  have h19 : Entails.eval a c4335 := h 4334 (by decide)
  have h20 : Entails.eval a c6804 := derived6804 a h
  have h21 : Entails.eval a c3704 := h 3703 (by decide)
  have h22 : Entails.eval a c3594 := h 3593 (by decide)
  have h23 : Entails.eval a c3919 := h 3918 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9056 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨62, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9056 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9055, some c9048, some c3775, some c3765, some c6434, some c3766, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9056 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9056 : lratChecker f9056 p9056 = .success := by decide +kernel
theorem unsat9056 : Unsatisfiable (PosFin 65) f9056 := by
  apply lratCheckerSound f9056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9056
  · intro a ha; simp [p9056] at ha; subst a; trivial
  · exact checked9056
theorem derived9056 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9056 := by
  apply localUnsat_implies_entails f9056 [c9055, c9048, c3775, c3765, c6434, c3766] c9056 unsat9056 (by rfl) a
  have h0 : Entails.eval a c9055 := derived9055 a h
  have h1 : Entails.eval a c9048 := derived9048 a h
  have h2 : Entails.eval a c3775 := h 3774 (by decide)
  have h3 : Entails.eval a c3765 := h 3764 (by decide)
  have h4 : Entails.eval a c6434 := derived6434 a h
  have h5 : Entails.eval a c3766 := h 3765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9057 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9057 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5627, some c3478, some c3472, some c3461, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9057 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9057 : lratChecker f9057 p9057 = .success := by decide +kernel
theorem unsat9057 : Unsatisfiable (PosFin 65) f9057 := by
  apply lratCheckerSound f9057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9057
  · intro a ha; simp [p9057] at ha; subst a; trivial
  · exact checked9057
theorem derived9057 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9057 := by
  apply localUnsat_implies_entails f9057 [c5627, c3478, c3472, c3461] c9057 unsat9057 (by rfl) a
  have h0 : Entails.eval a c5627 := h 5626 (by decide)
  have h1 : Entails.eval a c3478 := h 3477 (by decide)
  have h2 : Entails.eval a c3472 := h 3471 (by decide)
  have h3 : Entails.eval a c3461 := h 3460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9058 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9058 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9055, some c5629, some c3455, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9058 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9058 : lratChecker f9058 p9058 = .success := by decide +kernel
theorem unsat9058 : Unsatisfiable (PosFin 65) f9058 := by
  apply lratCheckerSound f9058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9058
  · intro a ha; simp [p9058] at ha; subst a; trivial
  · exact checked9058
theorem derived9058 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9058 := by
  apply localUnsat_implies_entails f9058 [c9055, c5629, c3455] c9058 unsat9058 (by rfl) a
  have h0 : Entails.eval a c9055 := derived9055 a h
  have h1 : Entails.eval a c5629 := h 5628 (by decide)
  have h2 : Entails.eval a c3455 := h 3454 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9059 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9059 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9056, some c9048, some c5632, some c6810, some c6939, some c3434, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9059 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9059 : lratChecker f9059 p9059 = .success := by decide +kernel
theorem unsat9059 : Unsatisfiable (PosFin 65) f9059 := by
  apply lratCheckerSound f9059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9059
  · intro a ha; simp [p9059] at ha; subst a; trivial
  · exact checked9059
theorem derived9059 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9059 := by
  apply localUnsat_implies_entails f9059 [c9056, c9048, c5632, c6810, c6939, c3434] c9059 unsat9059 (by rfl) a
  have h0 : Entails.eval a c9056 := derived9056 a h
  have h1 : Entails.eval a c9048 := derived9048 a h
  have h2 : Entails.eval a c5632 := h 5631 (by decide)
  have h3 : Entails.eval a c6810 := derived6810 a h
  have h4 : Entails.eval a c6939 := derived6939 a h
  have h5 : Entails.eval a c3434 := h 3433 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9060 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9060 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9048, some c7129, some c9056, some c9058, some c9059, some c9057, some c5902, some c5626, some c3461, some c3470, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9060 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9060 : lratChecker f9060 p9060 = .success := by decide +kernel
theorem unsat9060 : Unsatisfiable (PosFin 65) f9060 := by
  apply lratCheckerSound f9060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9060
  · intro a ha; simp [p9060] at ha; subst a; trivial
  · exact checked9060
theorem derived9060 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9060 := by
  apply localUnsat_implies_entails f9060 [c9048, c7129, c9056, c9058, c9059, c9057, c5902, c5626, c3461, c3470] c9060 unsat9060 (by rfl) a
  have h0 : Entails.eval a c9048 := derived9048 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9056 := derived9056 a h
  have h3 : Entails.eval a c9058 := derived9058 a h
  have h4 : Entails.eval a c9059 := derived9059 a h
  have h5 : Entails.eval a c9057 := derived9057 a h
  have h6 : Entails.eval a c5902 := derived5902 a h
  have h7 : Entails.eval a c5626 := h 5625 (by decide)
  have h8 : Entails.eval a c3461 := h 3460 (by decide)
  have h9 : Entails.eval a c3470 := h 3469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9061 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9061 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9060, some c9055, some c7129, some c5623, some c6611, some c3454, some c3470, some c3427, some c3449, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9061 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9061 : lratChecker f9061 p9061 = .success := by decide +kernel
theorem unsat9061 : Unsatisfiable (PosFin 65) f9061 := by
  apply lratCheckerSound f9061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9061
  · intro a ha; simp [p9061] at ha; subst a; trivial
  · exact checked9061
theorem derived9061 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9061 := by
  apply localUnsat_implies_entails f9061 [c9060, c9055, c7129, c5623, c6611, c3454, c3470, c3427, c3449] c9061 unsat9061 (by rfl) a
  have h0 : Entails.eval a c9060 := derived9060 a h
  have h1 : Entails.eval a c9055 := derived9055 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c5623 := h 5622 (by decide)
  have h4 : Entails.eval a c6611 := derived6611 a h
  have h5 : Entails.eval a c3454 := h 3453 (by decide)
  have h6 : Entails.eval a c3470 := h 3469 (by decide)
  have h7 : Entails.eval a c3427 := h 3426 (by decide)
  have h8 : Entails.eval a c3449 := h 3448 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9062 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9062 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9048, some c9058, some c9061, some c9057, some c5632, some c3460, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9062 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9062 : lratChecker f9062 p9062 = .success := by decide +kernel
theorem unsat9062 : Unsatisfiable (PosFin 65) f9062 := by
  apply lratCheckerSound f9062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9062
  · intro a ha; simp [p9062] at ha; subst a; trivial
  · exact checked9062
theorem derived9062 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9062 := by
  apply localUnsat_implies_entails f9062 [c9048, c9058, c9061, c9057, c5632, c3460] c9062 unsat9062 (by rfl) a
  have h0 : Entails.eval a c9048 := derived9048 a h
  have h1 : Entails.eval a c9058 := derived9058 a h
  have h2 : Entails.eval a c9061 := derived9061 a h
  have h3 : Entails.eval a c9057 := derived9057 a h
  have h4 : Entails.eval a c5632 := h 5631 (by decide)
  have h5 : Entails.eval a c3460 := h 3459 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9063 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9063 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9055, some c9048, some c3775, some c6434, some c3761, some c3766, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9063 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9063 : lratChecker f9063 p9063 = .success := by decide +kernel
theorem unsat9063 : Unsatisfiable (PosFin 65) f9063 := by
  apply lratCheckerSound f9063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9063
  · intro a ha; simp [p9063] at ha; subst a; trivial
  · exact checked9063
theorem derived9063 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9063 := by
  apply localUnsat_implies_entails f9063 [c9055, c9048, c3775, c6434, c3761, c3766] c9063 unsat9063 (by rfl) a
  have h0 : Entails.eval a c9055 := derived9055 a h
  have h1 : Entails.eval a c9048 := derived9048 a h
  have h2 : Entails.eval a c3775 := h 3774 (by decide)
  have h3 : Entails.eval a c6434 := derived6434 a h
  have h4 : Entails.eval a c3761 := h 3760 (by decide)
  have h5 : Entails.eval a c3766 := h 3765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9064 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9064 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9048, some c9055, some c9063, some c9062, some c4187, some c4182, some c4205, some c5930, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9064 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9064 : lratChecker f9064 p9064 = .success := by decide +kernel
theorem unsat9064 : Unsatisfiable (PosFin 65) f9064 := by
  apply lratCheckerSound f9064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9064
  · intro a ha; simp [p9064] at ha; subst a; trivial
  · exact checked9064
theorem derived9064 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9064 := by
  apply localUnsat_implies_entails f9064 [c9048, c9055, c9063, c9062, c4187, c4182, c4205, c5930] c9064 unsat9064 (by rfl) a
  have h0 : Entails.eval a c9048 := derived9048 a h
  have h1 : Entails.eval a c9055 := derived9055 a h
  have h2 : Entails.eval a c9063 := derived9063 a h
  have h3 : Entails.eval a c9062 := derived9062 a h
  have h4 : Entails.eval a c4187 := h 4186 (by decide)
  have h5 : Entails.eval a c4182 := h 4181 (by decide)
  have h6 : Entails.eval a c4205 := h 4204 (by decide)
  have h7 : Entails.eval a c5930 := derived5930 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9065 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9065 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5088, some c5058, some c4981, some c5403, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p9065 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9065 : lratChecker f9065 p9065 = .success := by decide +kernel
theorem unsat9065 : Unsatisfiable (PosFin 65) f9065 := by
  apply lratCheckerSound f9065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9065
  · intro a ha; simp [p9065] at ha; subst a; trivial
  · exact checked9065
theorem derived9065 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9065 := by
  apply localUnsat_implies_entails f9065 [c5088, c5058, c4981, c5403] c9065 unsat9065 (by rfl) a
  have h0 : Entails.eval a c5088 := h 5087 (by decide)
  have h1 : Entails.eval a c5058 := h 5057 (by decide)
  have h2 : Entails.eval a c4981 := h 4980 (by decide)
  have h3 : Entails.eval a c5403 := h 5402 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9066 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9066 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5507, some c5772, some c5400, some c5261, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p9066 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9066 : lratChecker f9066 p9066 = .success := by decide +kernel
theorem unsat9066 : Unsatisfiable (PosFin 65) f9066 := by
  apply lratCheckerSound f9066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9066
  · intro a ha; simp [p9066] at ha; subst a; trivial
  · exact checked9066
theorem derived9066 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9066 := by
  apply localUnsat_implies_entails f9066 [c5507, c5772, c5400, c5261] c9066 unsat9066 (by rfl) a
  have h0 : Entails.eval a c5507 := h 5506 (by decide)
  have h1 : Entails.eval a c5772 := h 5771 (by decide)
  have h2 : Entails.eval a c5400 := h 5399 (by decide)
  have h3 : Entails.eval a c5261 := h 5260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9067 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨37, by decide⟩, false), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9067 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5072, some c5053, some c6962, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9067 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9067 : lratChecker f9067 p9067 = .success := by decide +kernel
theorem unsat9067 : Unsatisfiable (PosFin 65) f9067 := by
  apply lratCheckerSound f9067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9067
  · intro a ha; simp [p9067] at ha; subst a; trivial
  · exact checked9067
theorem derived9067 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9067 := by
  apply localUnsat_implies_entails f9067 [c5072, c5053, c6962] c9067 unsat9067 (by rfl) a
  have h0 : Entails.eval a c5072 := h 5071 (by decide)
  have h1 : Entails.eval a c5053 := h 5052 (by decide)
  have h2 : Entails.eval a c6962 := derived6962 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9068 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨45, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9068 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5409, some c4985, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9068 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9068 : lratChecker f9068 p9068 = .success := by decide +kernel
theorem unsat9068 : Unsatisfiable (PosFin 65) f9068 := by
  apply lratCheckerSound f9068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9068
  · intro a ha; simp [p9068] at ha; subst a; trivial
  · exact checked9068
theorem derived9068 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9068 := by
  apply localUnsat_implies_entails f9068 [c5409, c4985] c9068 unsat9068 (by rfl) a
  have h0 : Entails.eval a c5409 := h 5408 (by decide)
  have h1 : Entails.eval a c4985 := h 4984 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9069 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨45, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9069 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9066, some c9068, some c6954, some c7003, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9069 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9069 : lratChecker f9069 p9069 = .success := by decide +kernel
theorem unsat9069 : Unsatisfiable (PosFin 65) f9069 := by
  apply lratCheckerSound f9069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9069
  · intro a ha; simp [p9069] at ha; subst a; trivial
  · exact checked9069
theorem derived9069 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9069 := by
  apply localUnsat_implies_entails f9069 [c7129, c9066, c9068, c6954, c7003] c9069 unsat9069 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9066 := derived9066 a h
  have h2 : Entails.eval a c9068 := derived9068 a h
  have h3 : Entails.eval a c6954 := derived6954 a h
  have h4 : Entails.eval a c7003 := derived7003 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9070 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9070 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6968, some c6963, some c9069, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9070 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9070 : lratChecker f9070 p9070 = .success := by decide +kernel
theorem unsat9070 : Unsatisfiable (PosFin 65) f9070 := by
  apply lratCheckerSound f9070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9070
  · intro a ha; simp [p9070] at ha; subst a; trivial
  · exact checked9070
theorem derived9070 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9070 := by
  apply localUnsat_implies_entails f9070 [c6968, c6963, c9069] c9070 unsat9070 (by rfl) a
  have h0 : Entails.eval a c6968 := derived6968 a h
  have h1 : Entails.eval a c6963 := derived6963 a h
  have h2 : Entails.eval a c9069 := derived9069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9071 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨63, by decide⟩, true), (⟨34, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9071 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c4323, some c4097, some c5321, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9071 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9071 : lratChecker f9071 p9071 = .success := by decide +kernel
theorem unsat9071 : Unsatisfiable (PosFin 65) f9071 := by
  apply lratCheckerSound f9071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9071
  · intro a ha; simp [p9071] at ha; subst a; trivial
  · exact checked9071
theorem derived9071 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9071 := by
  apply localUnsat_implies_entails f9071 [c9064, c4323, c4097, c5321] c9071 unsat9071 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c4323 := h 4322 (by decide)
  have h2 : Entails.eval a c4097 := h 4096 (by decide)
  have h3 : Entails.eval a c5321 := h 5320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9072 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨34, by decide⟩, true), (⟨40, by decide⟩, false), (⟨48, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9072 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4318, some c4094, some c5313, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9072 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9072 : lratChecker f9072 p9072 = .success := by decide +kernel
theorem unsat9072 : Unsatisfiable (PosFin 65) f9072 := by
  apply lratCheckerSound f9072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9072
  · intro a ha; simp [p9072] at ha; subst a; trivial
  · exact checked9072
theorem derived9072 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9072 := by
  apply localUnsat_implies_entails f9072 [c4318, c4094, c5313] c9072 unsat9072 (by rfl) a
  have h0 : Entails.eval a c4318 := h 4317 (by decide)
  have h1 : Entails.eval a c4094 := h 4093 (by decide)
  have h2 : Entails.eval a c5313 := h 5312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9073 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨34, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9073 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c7129, some c9071, some c9072, some c4319, some c4095, some c5314, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9073 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9073 : lratChecker f9073 p9073 = .success := by decide +kernel
theorem unsat9073 : Unsatisfiable (PosFin 65) f9073 := by
  apply lratCheckerSound f9073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9073
  · intro a ha; simp [p9073] at ha; subst a; trivial
  · exact checked9073
theorem derived9073 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9073 := by
  apply localUnsat_implies_entails f9073 [c9064, c7129, c9071, c9072, c4319, c4095, c5314] c9073 unsat9073 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9071 := derived9071 a h
  have h3 : Entails.eval a c9072 := derived9072 a h
  have h4 : Entails.eval a c4319 := h 4318 (by decide)
  have h5 : Entails.eval a c4095 := h 4094 (by decide)
  have h6 : Entails.eval a c5314 := h 5313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9074 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9074 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7028, some c5719, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p9074 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9074 : lratChecker f9074 p9074 = .success := by decide +kernel
theorem unsat9074 : Unsatisfiable (PosFin 65) f9074 := by
  apply lratCheckerSound f9074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9074
  · intro a ha; simp [p9074] at ha; subst a; trivial
  · exact checked9074
theorem derived9074 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9074 := by
  apply localUnsat_implies_entails f9074 [c7028, c5719] c9074 unsat9074 (by rfl) a
  have h0 : Entails.eval a c7028 := derived7028 a h
  have h1 : Entails.eval a c5719 := h 5718 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9075 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨37, by decide⟩, true), (⟨46, by decide⟩, false), (⟨63, by decide⟩, false), (⟨34, by decide⟩, true), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9075 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4509, some c3939, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9075 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9075 : lratChecker f9075 p9075 = .success := by decide +kernel
theorem unsat9075 : Unsatisfiable (PosFin 65) f9075 := by
  apply lratCheckerSound f9075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9075
  · intro a ha; simp [p9075] at ha; subst a; trivial
  · exact checked9075
theorem derived9075 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9075 := by
  apply localUnsat_implies_entails f9075 [c4509, c3939] c9075 unsat9075 (by rfl) a
  have h0 : Entails.eval a c4509 := h 4508 (by decide)
  have h1 : Entails.eval a c3939 := h 3938 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9076 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨63, by decide⟩, false), (⟨34, by decide⟩, true), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9076 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9075, some c6816, some c6890, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9076 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9076 : lratChecker f9076 p9076 = .success := by decide +kernel
theorem unsat9076 : Unsatisfiable (PosFin 65) f9076 := by
  apply lratCheckerSound f9076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9076
  · intro a ha; simp [p9076] at ha; subst a; trivial
  · exact checked9076
theorem derived9076 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9076 := by
  apply localUnsat_implies_entails f9076 [c9075, c6816, c6890] c9076 unsat9076 (by rfl) a
  have h0 : Entails.eval a c9075 := derived9075 a h
  have h1 : Entails.eval a c6816 := derived6816 a h
  have h2 : Entails.eval a c6890 := derived6890 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9077 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨63, by decide⟩, false), (⟨34, by decide⟩, true), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9077 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9074, some c9076, some c9065, some c9067, some c9069, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9077 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9077 : lratChecker f9077 p9077 = .success := by decide +kernel
theorem unsat9077 : Unsatisfiable (PosFin 65) f9077 := by
  apply lratCheckerSound f9077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9077
  · intro a ha; simp [p9077] at ha; subst a; trivial
  · exact checked9077
theorem derived9077 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9077 := by
  apply localUnsat_implies_entails f9077 [c7129, c9074, c9076, c9065, c9067, c9069] c9077 unsat9077 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9074 := derived9074 a h
  have h2 : Entails.eval a c9076 := derived9076 a h
  have h3 : Entails.eval a c9065 := derived9065 a h
  have h4 : Entails.eval a c9067 := derived9067 a h
  have h5 : Entails.eval a c9069 := derived9069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9078 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨34, by decide⟩, true), (⟨60, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9078 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9073, some c9064, some c7129, some c9077, some c4332, some c6836, some c6856, some c9067, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9078 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9078 : lratChecker f9078 p9078 = .success := by decide +kernel
theorem unsat9078 : Unsatisfiable (PosFin 65) f9078 := by
  apply lratCheckerSound f9078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9078
  · intro a ha; simp [p9078] at ha; subst a; trivial
  · exact checked9078
theorem derived9078 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9078 := by
  apply localUnsat_implies_entails f9078 [c9073, c9064, c7129, c9077, c4332, c6836, c6856, c9067] c9078 unsat9078 (by rfl) a
  have h0 : Entails.eval a c9073 := derived9073 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9077 := derived9077 a h
  have h4 : Entails.eval a c4332 := h 4331 (by decide)
  have h5 : Entails.eval a c6836 := derived6836 a h
  have h6 : Entails.eval a c6856 := derived6856 a h
  have h7 : Entails.eval a c9067 := derived9067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9079 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨60, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9079 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c7129, some c9078, some c4096, some c4321, some c5315, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9079 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9079 : lratChecker f9079 p9079 = .success := by decide +kernel
theorem unsat9079 : Unsatisfiable (PosFin 65) f9079 := by
  apply lratCheckerSound f9079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9079
  · intro a ha; simp [p9079] at ha; subst a; trivial
  · exact checked9079
theorem derived9079 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9079 := by
  apply localUnsat_implies_entails f9079 [c9064, c7129, c9078, c4096, c4321, c5315] c9079 unsat9079 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9078 := derived9078 a h
  have h3 : Entails.eval a c4096 := h 4095 (by decide)
  have h4 : Entails.eval a c4321 := h 4320 (by decide)
  have h5 : Entails.eval a c5315 := h 5314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9080 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨49, by decide⟩, false), (⟨60, by decide⟩, false), (⟨58, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9080 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5707, some c5315, some c4495, some c4426, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p9080 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9080 : lratChecker f9080 p9080 = .success := by decide +kernel
theorem unsat9080 : Unsatisfiable (PosFin 65) f9080 := by
  apply lratCheckerSound f9080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9080
  · intro a ha; simp [p9080] at ha; subst a; trivial
  · exact checked9080
theorem derived9080 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9080 := by
  apply localUnsat_implies_entails f9080 [c5707, c5315, c4495, c4426] c9080 unsat9080 (by rfl) a
  have h0 : Entails.eval a c5707 := h 5706 (by decide)
  have h1 : Entails.eval a c5315 := h 5314 (by decide)
  have h2 : Entails.eval a c4495 := h 4494 (by decide)
  have h3 : Entails.eval a c4426 := h 4425 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9080

end CochromaticTwenty.Certificates.FixedCore1
