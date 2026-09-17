import MerLeanExperiment.Certificates.FixedCore0.Steps3300_3399

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10951 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false), (⟨13, by decide⟩, false), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, false), (⟨5, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨56, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10951 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8366, some c10949, some c6798, some c6306, some c6360, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10951 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10951 : lratChecker f10951 p10951 = .success := by decide +kernel
theorem unsat10951 : Unsatisfiable (PosFin 65) f10951 := by
  apply lratCheckerSound f10951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10951
  · intro a ha; simp [p10951] at ha; subst a; trivial
  · exact checked10951
theorem derived10951 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10951 := by
  apply localUnsat_implies_entails f10951 [c8366, c10949, c6798, c6306, c6360] c10951 unsat10951 (by rfl) a
  have h0 : Entails.eval a c8366 := derived8366 a h
  have h1 : Entails.eval a c10949 := derived10949 a h
  have h2 : Entails.eval a c6798 := h 6797 (by decide)
  have h3 : Entails.eval a c6306 := h 6305 (by decide)
  have h4 : Entails.eval a c6360 := h 6359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10952 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨21, by decide⟩, true), (⟨45, by decide⟩, true), (⟨20, by decide⟩, true), (⟨46, by decide⟩, true), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10952 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4372, some c10736, some c10413, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10952 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10952 : lratChecker f10952 p10952 = .success := by decide +kernel
theorem unsat10952 : Unsatisfiable (PosFin 65) f10952 := by
  apply lratCheckerSound f10952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10952
  · intro a ha; simp [p10952] at ha; subst a; trivial
  · exact checked10952
theorem derived10952 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10952 := by
  apply localUnsat_implies_entails f10952 [c4372, c10736, c10413] c10952 unsat10952 (by rfl) a
  have h0 : Entails.eval a c4372 := h 4371 (by decide)
  have h1 : Entails.eval a c10736 := derived10736 a h
  have h2 : Entails.eval a c10413 := derived10413 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10953 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10953 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10945, some c10929, some c10938, some c4637, some c3423, some c5099, some c3387, some c3014, some c2486, some c2926, some c3826, some c10939, some c10946, some c10950, some c4940, some c10720, some c10780, some c3294, some c4552, some c4934, some c10304, some c4547, some c9053, some c8366, some c10951, some c945, some c823, some c10948, some c50, some c4889, some c3234, some c949, some c57, some c10952, some c3965, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10953 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked10953 : lratChecker f10953 p10953 = .success := by decide +kernel
theorem unsat10953 : Unsatisfiable (PosFin 65) f10953 := by
  apply lratCheckerSound f10953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10953
  · intro a ha; simp [p10953] at ha; subst a; trivial
  · exact checked10953
theorem derived10953 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10953 := by
  apply localUnsat_implies_entails f10953 [c10945, c10929, c10938, c4637, c3423, c5099, c3387, c3014, c2486, c2926, c3826, c10939, c10946, c10950, c4940, c10720, c10780, c3294, c4552, c4934, c10304, c4547, c9053, c8366, c10951, c945, c823, c10948, c50, c4889, c3234, c949, c57, c10952, c3965] c10953 unsat10953 (by rfl) a
  have h0 : Entails.eval a c10945 := derived10945 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10938 := derived10938 a h
  have h3 : Entails.eval a c4637 := h 4636 (by decide)
  have h4 : Entails.eval a c3423 := h 3422 (by decide)
  have h5 : Entails.eval a c5099 := h 5098 (by decide)
  have h6 : Entails.eval a c3387 := h 3386 (by decide)
  have h7 : Entails.eval a c3014 := h 3013 (by decide)
  have h8 : Entails.eval a c2486 := h 2485 (by decide)
  have h9 : Entails.eval a c2926 := h 2925 (by decide)
  have h10 : Entails.eval a c3826 := h 3825 (by decide)
  have h11 : Entails.eval a c10939 := derived10939 a h
  have h12 : Entails.eval a c10946 := derived10946 a h
  have h13 : Entails.eval a c10950 := derived10950 a h
  have h14 : Entails.eval a c4940 := h 4939 (by decide)
  have h15 : Entails.eval a c10720 := derived10720 a h
  have h16 : Entails.eval a c10780 := derived10780 a h
  have h17 : Entails.eval a c3294 := h 3293 (by decide)
  have h18 : Entails.eval a c4552 := h 4551 (by decide)
  have h19 : Entails.eval a c4934 := h 4933 (by decide)
  have h20 : Entails.eval a c10304 := derived10304 a h
  have h21 : Entails.eval a c4547 := h 4546 (by decide)
  have h22 : Entails.eval a c9053 := derived9053 a h
  have h23 : Entails.eval a c8366 := derived8366 a h
  have h24 : Entails.eval a c10951 := derived10951 a h
  have h25 : Entails.eval a c945 := h 944 (by decide)
  have h26 : Entails.eval a c823 := h 822 (by decide)
  have h27 : Entails.eval a c10948 := derived10948 a h
  have h28 : Entails.eval a c50 := h 49 (by decide)
  have h29 : Entails.eval a c4889 := h 4888 (by decide)
  have h30 : Entails.eval a c3234 := h 3233 (by decide)
  have h31 : Entails.eval a c949 := h 948 (by decide)
  have h32 : Entails.eval a c57 := h 56 (by decide)
  have h33 : Entails.eval a c10952 := derived10952 a h
  have h34 : Entails.eval a c3965 := h 3964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10954 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨55, by decide⟩, true), (⟨64, by decide⟩, false), (⟨11, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, true), (⟨58, by decide⟩, true), (⟨60, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨59, by decide⟩, true), (⟨56, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10954 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c9053, some c8642, some c8366, some c51, some c4890, some c4889, some c8644, some c6534, some c18, some c815, some c6339, some c6726, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10954 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked10954 : lratChecker f10954 p10954 = .success := by decide +kernel
theorem unsat10954 : Unsatisfiable (PosFin 65) f10954 := by
  apply lratCheckerSound f10954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10954
  · intro a ha; simp [p10954] at ha; subst a; trivial
  · exact checked10954
theorem derived10954 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10954 := by
  apply localUnsat_implies_entails f10954 [c10929, c9053, c8642, c8366, c51, c4890, c4889, c8644, c6534, c18, c815, c6339, c6726] c10954 unsat10954 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c9053 := derived9053 a h
  have h2 : Entails.eval a c8642 := derived8642 a h
  have h3 : Entails.eval a c8366 := derived8366 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c4890 := h 4889 (by decide)
  have h6 : Entails.eval a c4889 := h 4888 (by decide)
  have h7 : Entails.eval a c8644 := derived8644 a h
  have h8 : Entails.eval a c6534 := h 6533 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c815 := h 814 (by decide)
  have h11 : Entails.eval a c6339 := h 6338 (by decide)
  have h12 : Entails.eval a c6726 := h 6725 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10955 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, false), (⟨55, by decide⟩, true), (⟨64, by decide⟩, false), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, true), (⟨58, by decide⟩, true), (⟨60, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨56, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10955 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4934, some c8644, some c10661, some c4924, some c4887, some c5914, some c5618, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10955 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10955 : lratChecker f10955 p10955 = .success := by decide +kernel
theorem unsat10955 : Unsatisfiable (PosFin 65) f10955 := by
  apply lratCheckerSound f10955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10955
  · intro a ha; simp [p10955] at ha; subst a; trivial
  · exact checked10955
theorem derived10955 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10955 := by
  apply localUnsat_implies_entails f10955 [c4934, c8644, c10661, c4924, c4887, c5914, c5618] c10955 unsat10955 (by rfl) a
  have h0 : Entails.eval a c4934 := h 4933 (by decide)
  have h1 : Entails.eval a c8644 := derived8644 a h
  have h2 : Entails.eval a c10661 := derived10661 a h
  have h3 : Entails.eval a c4924 := h 4923 (by decide)
  have h4 : Entails.eval a c4887 := h 4886 (by decide)
  have h5 : Entails.eval a c5914 := h 5913 (by decide)
  have h6 : Entails.eval a c5618 := h 5617 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10956 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨3, by decide⟩, true), (⟨59, by decide⟩, true), (⟨56, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10956 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10656, some c4641, some c5126, some c3020, some c3799, some c2491, some c10941, some c10929, some c4940, some c10720, some c10780, some c3294, some c4552, some c4934, some c10532, some c10533, some c4247, some c4547, some c9053, some c10531, some c8366, some c8642, some c10954, some c10955, some c8664, some c7112, some c6985, some c6616, some c4568, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10956 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked10956 : lratChecker f10956 p10956 = .success := by decide +kernel
theorem unsat10956 : Unsatisfiable (PosFin 65) f10956 := by
  apply lratCheckerSound f10956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10956
  · intro a ha; simp [p10956] at ha; subst a; trivial
  · exact checked10956
theorem derived10956 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10956 := by
  apply localUnsat_implies_entails f10956 [c10656, c4641, c5126, c3020, c3799, c2491, c10941, c10929, c4940, c10720, c10780, c3294, c4552, c4934, c10532, c10533, c4247, c4547, c9053, c10531, c8366, c8642, c10954, c10955, c8664, c7112, c6985, c6616, c4568] c10956 unsat10956 (by rfl) a
  have h0 : Entails.eval a c10656 := derived10656 a h
  have h1 : Entails.eval a c4641 := h 4640 (by decide)
  have h2 : Entails.eval a c5126 := h 5125 (by decide)
  have h3 : Entails.eval a c3020 := h 3019 (by decide)
  have h4 : Entails.eval a c3799 := h 3798 (by decide)
  have h5 : Entails.eval a c2491 := h 2490 (by decide)
  have h6 : Entails.eval a c10941 := derived10941 a h
  have h7 : Entails.eval a c10929 := derived10929 a h
  have h8 : Entails.eval a c4940 := h 4939 (by decide)
  have h9 : Entails.eval a c10720 := derived10720 a h
  have h10 : Entails.eval a c10780 := derived10780 a h
  have h11 : Entails.eval a c3294 := h 3293 (by decide)
  have h12 : Entails.eval a c4552 := h 4551 (by decide)
  have h13 : Entails.eval a c4934 := h 4933 (by decide)
  have h14 : Entails.eval a c10532 := derived10532 a h
  have h15 : Entails.eval a c10533 := derived10533 a h
  have h16 : Entails.eval a c4247 := h 4246 (by decide)
  have h17 : Entails.eval a c4547 := h 4546 (by decide)
  have h18 : Entails.eval a c9053 := derived9053 a h
  have h19 : Entails.eval a c10531 := derived10531 a h
  have h20 : Entails.eval a c8366 := derived8366 a h
  have h21 : Entails.eval a c8642 := derived8642 a h
  have h22 : Entails.eval a c10954 := derived10954 a h
  have h23 : Entails.eval a c10955 := derived10955 a h
  have h24 : Entails.eval a c8664 := derived8664 a h
  have h25 : Entails.eval a c7112 := h 7111 (by decide)
  have h26 : Entails.eval a c6985 := h 6984 (by decide)
  have h27 : Entails.eval a c6616 := h 6615 (by decide)
  have h28 : Entails.eval a c4568 := h 4567 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10957 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨35, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, true), (⟨4, by decide⟩, false), (⟨59, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10957 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c48, some c8664, some c6616, some c7112, some c6985, some c6656, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10957 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10957 : lratChecker f10957 p10957 = .success := by decide +kernel
theorem unsat10957 : Unsatisfiable (PosFin 65) f10957 := by
  apply lratCheckerSound f10957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10957
  · intro a ha; simp [p10957] at ha; subst a; trivial
  · exact checked10957
theorem derived10957 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10957 := by
  apply localUnsat_implies_entails f10957 [c48, c8664, c6616, c7112, c6985, c6656] c10957 unsat10957 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c8664 := derived8664 a h
  have h2 : Entails.eval a c6616 := h 6615 (by decide)
  have h3 : Entails.eval a c7112 := h 7111 (by decide)
  have h4 : Entails.eval a c6985 := h 6984 (by decide)
  have h5 : Entails.eval a c6656 := h 6655 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10958 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10958 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10938, some c10953, some c10941, some c10945, some c10656, some c3091, some c3020, some c3799, some c4641, some c2491, some c3390, some c10956, some c2791, some c4101, some c3694, some c2757, some c3684, some c10172, some c3687, some c2753, some c4024, some c8018, some c2739, some c8642, some c8366, some c10957, some c8644, some c249, some c5914, some c5855, some c5613, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10958 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked10958 : lratChecker f10958 p10958 = .success := by decide +kernel
theorem unsat10958 : Unsatisfiable (PosFin 65) f10958 := by
  apply lratCheckerSound f10958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10958
  · intro a ha; simp [p10958] at ha; subst a; trivial
  · exact checked10958
theorem derived10958 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10958 := by
  apply localUnsat_implies_entails f10958 [c10929, c10938, c10953, c10941, c10945, c10656, c3091, c3020, c3799, c4641, c2491, c3390, c10956, c2791, c4101, c3694, c2757, c3684, c10172, c3687, c2753, c4024, c8018, c2739, c8642, c8366, c10957, c8644, c249, c5914, c5855, c5613] c10958 unsat10958 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10938 := derived10938 a h
  have h2 : Entails.eval a c10953 := derived10953 a h
  have h3 : Entails.eval a c10941 := derived10941 a h
  have h4 : Entails.eval a c10945 := derived10945 a h
  have h5 : Entails.eval a c10656 := derived10656 a h
  have h6 : Entails.eval a c3091 := h 3090 (by decide)
  have h7 : Entails.eval a c3020 := h 3019 (by decide)
  have h8 : Entails.eval a c3799 := h 3798 (by decide)
  have h9 : Entails.eval a c4641 := h 4640 (by decide)
  have h10 : Entails.eval a c2491 := h 2490 (by decide)
  have h11 : Entails.eval a c3390 := h 3389 (by decide)
  have h12 : Entails.eval a c10956 := derived10956 a h
  have h13 : Entails.eval a c2791 := h 2790 (by decide)
  have h14 : Entails.eval a c4101 := h 4100 (by decide)
  have h15 : Entails.eval a c3694 := h 3693 (by decide)
  have h16 : Entails.eval a c2757 := h 2756 (by decide)
  have h17 : Entails.eval a c3684 := h 3683 (by decide)
  have h18 : Entails.eval a c10172 := derived10172 a h
  have h19 : Entails.eval a c3687 := h 3686 (by decide)
  have h20 : Entails.eval a c2753 := h 2752 (by decide)
  have h21 : Entails.eval a c4024 := h 4023 (by decide)
  have h22 : Entails.eval a c8018 := derived8018 a h
  have h23 : Entails.eval a c2739 := h 2738 (by decide)
  have h24 : Entails.eval a c8642 := derived8642 a h
  have h25 : Entails.eval a c8366 := derived8366 a h
  have h26 : Entails.eval a c10957 := derived10957 a h
  have h27 : Entails.eval a c8644 := derived8644 a h
  have h28 : Entails.eval a c249 := h 248 (by decide)
  have h29 : Entails.eval a c5914 := h 5913 (by decide)
  have h30 : Entails.eval a c5855 := h 5854 (by decide)
  have h31 : Entails.eval a c5613 := h 5612 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10959 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10959 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10945, some c10958, some c4640, some c4556, some c4974, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10959 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10959 : lratChecker f10959 p10959 = .success := by decide +kernel
theorem unsat10959 : Unsatisfiable (PosFin 65) f10959 := by
  apply lratCheckerSound f10959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10959
  · intro a ha; simp [p10959] at ha; subst a; trivial
  · exact checked10959
theorem derived10959 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10959 := by
  apply localUnsat_implies_entails f10959 [c10929, c10945, c10958, c4640, c4556, c4974] c10959 unsat10959 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10945 := derived10945 a h
  have h2 : Entails.eval a c10958 := derived10958 a h
  have h3 : Entails.eval a c4640 := h 4639 (by decide)
  have h4 : Entails.eval a c4556 := h 4555 (by decide)
  have h5 : Entails.eval a c4974 := h 4973 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10960 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨7, by decide⟩, false), (⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10960 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3167, some c4785, some c4690, some c3389, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p10960 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10960 : lratChecker f10960 p10960 = .success := by decide +kernel
theorem unsat10960 : Unsatisfiable (PosFin 65) f10960 := by
  apply lratCheckerSound f10960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10960
  · intro a ha; simp [p10960] at ha; subst a; trivial
  · exact checked10960
theorem derived10960 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10960 := by
  apply localUnsat_implies_entails f10960 [c3167, c4785, c4690, c3389] c10960 unsat10960 (by rfl) a
  have h0 : Entails.eval a c3167 := h 3166 (by decide)
  have h1 : Entails.eval a c4785 := h 4784 (by decide)
  have h2 : Entails.eval a c4690 := h 4689 (by decide)
  have h3 : Entails.eval a c3389 := h 3388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10961 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10961 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10959, some c10960, some c10938, some c3390, some c3387, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10961 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10961 : lratChecker f10961 p10961 = .success := by decide +kernel
theorem unsat10961 : Unsatisfiable (PosFin 65) f10961 := by
  apply lratCheckerSound f10961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10961
  · intro a ha; simp [p10961] at ha; subst a; trivial
  · exact checked10961
theorem derived10961 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10961 := by
  apply localUnsat_implies_entails f10961 [c10929, c10959, c10960, c10938, c3390, c3387] c10961 unsat10961 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10959 := derived10959 a h
  have h2 : Entails.eval a c10960 := derived10960 a h
  have h3 : Entails.eval a c10938 := derived10938 a h
  have h4 : Entails.eval a c3390 := h 3389 (by decide)
  have h5 : Entails.eval a c3387 := h 3386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10962 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10962 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10959, some c10960, some c10938, some c4786, some c4782, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10962 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10962 : lratChecker f10962 p10962 = .success := by decide +kernel
theorem unsat10962 : Unsatisfiable (PosFin 65) f10962 := by
  apply lratCheckerSound f10962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10962
  · intro a ha; simp [p10962] at ha; subst a; trivial
  · exact checked10962
theorem derived10962 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10962 := by
  apply localUnsat_implies_entails f10962 [c10929, c10959, c10960, c10938, c4786, c4782] c10962 unsat10962 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10959 := derived10959 a h
  have h2 : Entails.eval a c10960 := derived10960 a h
  have h3 : Entails.eval a c10938 := derived10938 a h
  have h4 : Entails.eval a c4786 := h 4785 (by decide)
  have h5 : Entails.eval a c4782 := h 4781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10963 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨14, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10963 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10959, some c10960, some c10938, some c3163, some c10198, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10963 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10963 : lratChecker f10963 p10963 = .success := by decide +kernel
theorem unsat10963 : Unsatisfiable (PosFin 65) f10963 := by
  apply lratCheckerSound f10963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10963
  · intro a ha; simp [p10963] at ha; subst a; trivial
  · exact checked10963
theorem derived10963 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10963 := by
  apply localUnsat_implies_entails f10963 [c10929, c10959, c10960, c10938, c3163, c10198] c10963 unsat10963 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10959 := derived10959 a h
  have h2 : Entails.eval a c10960 := derived10960 a h
  have h3 : Entails.eval a c10938 := derived10938 a h
  have h4 : Entails.eval a c3163 := h 3162 (by decide)
  have h5 : Entails.eval a c10198 := derived10198 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10964 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10964 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10938, some c10959, some c10960, some c10962, some c10963, some c10961, some c4692, some c4689, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10964 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10964 : lratChecker f10964 p10964 = .success := by decide +kernel
theorem unsat10964 : Unsatisfiable (PosFin 65) f10964 := by
  apply lratCheckerSound f10964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10964
  · intro a ha; simp [p10964] at ha; subst a; trivial
  · exact checked10964
theorem derived10964 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10964 := by
  apply localUnsat_implies_entails f10964 [c10938, c10959, c10960, c10962, c10963, c10961, c4692, c4689] c10964 unsat10964 (by rfl) a
  have h0 : Entails.eval a c10938 := derived10938 a h
  have h1 : Entails.eval a c10959 := derived10959 a h
  have h2 : Entails.eval a c10960 := derived10960 a h
  have h3 : Entails.eval a c10962 := derived10962 a h
  have h4 : Entails.eval a c10963 := derived10963 a h
  have h5 : Entails.eval a c10961 := derived10961 a h
  have h6 : Entails.eval a c4692 := h 4691 (by decide)
  have h7 : Entails.eval a c4689 := h 4688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10965 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10965 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c10301, some c4242, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10965 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10965 : lratChecker f10965 p10965 = .success := by decide +kernel
theorem unsat10965 : Unsatisfiable (PosFin 65) f10965 := by
  apply lratCheckerSound f10965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10965
  · intro a ha; simp [p10965] at ha; subst a; trivial
  · exact checked10965
theorem derived10965 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10965 := by
  apply localUnsat_implies_entails f10965 [c8269, c10301, c4242] c10965 unsat10965 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c10301 := derived10301 a h
  have h2 : Entails.eval a c4242 := h 4241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10966 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨59, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10966 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10965, some c10172, some c10286, some c10297, some c3456, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10966 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10966 : lratChecker f10966 p10966 = .success := by decide +kernel
theorem unsat10966 : Unsatisfiable (PosFin 65) f10966 := by
  apply lratCheckerSound f10966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10966
  · intro a ha; simp [p10966] at ha; subst a; trivial
  · exact checked10966
theorem derived10966 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10966 := by
  apply localUnsat_implies_entails f10966 [c10965, c10172, c10286, c10297, c3456] c10966 unsat10966 (by rfl) a
  have h0 : Entails.eval a c10965 := derived10965 a h
  have h1 : Entails.eval a c10172 := derived10172 a h
  have h2 : Entails.eval a c10286 := derived10286 a h
  have h3 : Entails.eval a c10297 := derived10297 a h
  have h4 : Entails.eval a c3456 := h 3455 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10967 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10967 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10173, some c10234, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10967 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10967 : lratChecker f10967 p10967 = .success := by decide +kernel
theorem unsat10967 : Unsatisfiable (PosFin 65) f10967 := by
  apply lratCheckerSound f10967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10967
  · intro a ha; simp [p10967] at ha; subst a; trivial
  · exact checked10967
theorem derived10967 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10967 := by
  apply localUnsat_implies_entails f10967 [c10173, c10234] c10967 unsat10967 (by rfl) a
  have h0 : Entails.eval a c10173 := derived10173 a h
  have h1 : Entails.eval a c10234 := derived10234 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10968 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10968 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10591, some c4311, some c10964, some c10709, some c2647, some c2690, some c4396, some c3014, some c10967, some c10965, some c10966, some c10519, some c9624, some c10653, some c3268, some c4552, some c4655, some c4410, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10968 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked10968 : lratChecker f10968 p10968 = .success := by decide +kernel
theorem unsat10968 : Unsatisfiable (PosFin 65) f10968 := by
  apply lratCheckerSound f10968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10968
  · intro a ha; simp [p10968] at ha; subst a; trivial
  · exact checked10968
theorem derived10968 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10968 := by
  apply localUnsat_implies_entails f10968 [c10929, c10591, c4311, c10964, c10709, c2647, c2690, c4396, c3014, c10967, c10965, c10966, c10519, c9624, c10653, c3268, c4552, c4655, c4410] c10968 unsat10968 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10591 := derived10591 a h
  have h2 : Entails.eval a c4311 := h 4310 (by decide)
  have h3 : Entails.eval a c10964 := derived10964 a h
  have h4 : Entails.eval a c10709 := derived10709 a h
  have h5 : Entails.eval a c2647 := h 2646 (by decide)
  have h6 : Entails.eval a c2690 := h 2689 (by decide)
  have h7 : Entails.eval a c4396 := h 4395 (by decide)
  have h8 : Entails.eval a c3014 := h 3013 (by decide)
  have h9 : Entails.eval a c10967 := derived10967 a h
  have h10 : Entails.eval a c10965 := derived10965 a h
  have h11 : Entails.eval a c10966 := derived10966 a h
  have h12 : Entails.eval a c10519 := derived10519 a h
  have h13 : Entails.eval a c9624 := derived9624 a h
  have h14 : Entails.eval a c10653 := derived10653 a h
  have h15 : Entails.eval a c3268 := h 3267 (by decide)
  have h16 : Entails.eval a c4552 := h 4551 (by decide)
  have h17 : Entails.eval a c4655 := h 4654 (by decide)
  have h18 : Entails.eval a c4410 := h 4409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10969 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10969 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10591, some c4311, some c4396, some c3014, some c10968, some c10021, some c8269, some c10301, some c4413, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10969 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10969 : lratChecker f10969 p10969 = .success := by decide +kernel
theorem unsat10969 : Unsatisfiable (PosFin 65) f10969 := by
  apply lratCheckerSound f10969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10969
  · intro a ha; simp [p10969] at ha; subst a; trivial
  · exact checked10969
theorem derived10969 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10969 := by
  apply localUnsat_implies_entails f10969 [c10929, c10591, c4311, c4396, c3014, c10968, c10021, c8269, c10301, c4413] c10969 unsat10969 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10591 := derived10591 a h
  have h2 : Entails.eval a c4311 := h 4310 (by decide)
  have h3 : Entails.eval a c4396 := h 4395 (by decide)
  have h4 : Entails.eval a c3014 := h 3013 (by decide)
  have h5 : Entails.eval a c10968 := derived10968 a h
  have h6 : Entails.eval a c10021 := derived10021 a h
  have h7 : Entails.eval a c8269 := derived8269 a h
  have h8 : Entails.eval a c10301 := derived10301 a h
  have h9 : Entails.eval a c4413 := h 4412 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10970 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨56, by decide⟩, true), (⟨10, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10970 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8269, some c10914, some c4425, some c4414, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10970 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10970 : lratChecker f10970 p10970 = .success := by decide +kernel
theorem unsat10970 : Unsatisfiable (PosFin 65) f10970 := by
  apply lratCheckerSound f10970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10970
  · intro a ha; simp [p10970] at ha; subst a; trivial
  · exact checked10970
theorem derived10970 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10970 := by
  apply localUnsat_implies_entails f10970 [c7994, c8269, c10914, c4425, c4414] c10970 unsat10970 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c10914 := derived10914 a h
  have h3 : Entails.eval a c4425 := h 4424 (by decide)
  have h4 : Entails.eval a c4414 := h 4413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10971 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨56, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10971 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10970, some c10789, some c10021, some c2552, some c3013, some c9931, some c2655, some c9789, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10971 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10971 : lratChecker f10971 p10971 = .success := by decide +kernel
theorem unsat10971 : Unsatisfiable (PosFin 65) f10971 := by
  apply lratCheckerSound f10971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10971
  · intro a ha; simp [p10971] at ha; subst a; trivial
  · exact checked10971
theorem derived10971 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10971 := by
  apply localUnsat_implies_entails f10971 [c10929, c10964, c10970, c10789, c10021, c2552, c3013, c9931, c2655, c9789] c10971 unsat10971 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10970 := derived10970 a h
  have h3 : Entails.eval a c10789 := derived10789 a h
  have h4 : Entails.eval a c10021 := derived10021 a h
  have h5 : Entails.eval a c2552 := h 2551 (by decide)
  have h6 : Entails.eval a c3013 := h 3012 (by decide)
  have h7 : Entails.eval a c9931 := derived9931 a h
  have h8 : Entails.eval a c2655 := h 2654 (by decide)
  have h9 : Entails.eval a c9789 := derived9789 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10972 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨56, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10972 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10970, some c10971, some c10967, some c10654, some c10655, some c3960, some c3963, some c10172, some c4528, some c10720, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10972 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked10972 : lratChecker f10972 p10972 = .success := by decide +kernel
theorem unsat10972 : Unsatisfiable (PosFin 65) f10972 := by
  apply lratCheckerSound f10972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10972
  · intro a ha; simp [p10972] at ha; subst a; trivial
  · exact checked10972
theorem derived10972 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10972 := by
  apply localUnsat_implies_entails f10972 [c10929, c10964, c10970, c10971, c10967, c10654, c10655, c3960, c3963, c10172, c4528, c10720] c10972 unsat10972 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10970 := derived10970 a h
  have h3 : Entails.eval a c10971 := derived10971 a h
  have h4 : Entails.eval a c10967 := derived10967 a h
  have h5 : Entails.eval a c10654 := derived10654 a h
  have h6 : Entails.eval a c10655 := derived10655 a h
  have h7 : Entails.eval a c3960 := h 3959 (by decide)
  have h8 : Entails.eval a c3963 := h 3962 (by decide)
  have h9 : Entails.eval a c10172 := derived10172 a h
  have h10 : Entails.eval a c4528 := h 4527 (by decide)
  have h11 : Entails.eval a c10720 := derived10720 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10973 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨7, by decide⟩, true), (⟨56, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10973 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10967, some c10654, some c10721, some c4041, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10973 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10973 : lratChecker f10973 p10973 = .success := by decide +kernel
theorem unsat10973 : Unsatisfiable (PosFin 65) f10973 := by
  apply lratCheckerSound f10973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10973
  · intro a ha; simp [p10973] at ha; subst a; trivial
  · exact checked10973
theorem derived10973 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10973 := by
  apply localUnsat_implies_entails f10973 [c10929, c10964, c10967, c10654, c10721, c4041] c10973 unsat10973 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10967 := derived10967 a h
  have h3 : Entails.eval a c10654 := derived10654 a h
  have h4 : Entails.eval a c10721 := derived10721 a h
  have h5 : Entails.eval a c4041 := h 4040 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10974 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10974 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10969, some c10929, some c10964, some c10972, some c10344, some c3136, some c10586, some c10599, some c10569, some c10349, some c10590, some c10973, some c10729, some c10566, some c3455, some c4046, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10974 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked10974 : lratChecker f10974 p10974 = .success := by decide +kernel
theorem unsat10974 : Unsatisfiable (PosFin 65) f10974 := by
  apply lratCheckerSound f10974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10974
  · intro a ha; simp [p10974] at ha; subst a; trivial
  · exact checked10974
theorem derived10974 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10974 := by
  apply localUnsat_implies_entails f10974 [c10969, c10929, c10964, c10972, c10344, c3136, c10586, c10599, c10569, c10349, c10590, c10973, c10729, c10566, c3455, c4046] c10974 unsat10974 (by rfl) a
  have h0 : Entails.eval a c10969 := derived10969 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c10972 := derived10972 a h
  have h4 : Entails.eval a c10344 := derived10344 a h
  have h5 : Entails.eval a c3136 := h 3135 (by decide)
  have h6 : Entails.eval a c10586 := derived10586 a h
  have h7 : Entails.eval a c10599 := derived10599 a h
  have h8 : Entails.eval a c10569 := derived10569 a h
  have h9 : Entails.eval a c10349 := derived10349 a h
  have h10 : Entails.eval a c10590 := derived10590 a h
  have h11 : Entails.eval a c10973 := derived10973 a h
  have h12 : Entails.eval a c10729 := derived10729 a h
  have h13 : Entails.eval a c10566 := derived10566 a h
  have h14 : Entails.eval a c3455 := h 3454 (by decide)
  have h15 : Entails.eval a c4046 := h 4045 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10975 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10975 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10789, some c245, some c255, some c8918, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10975 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked10975 : lratChecker f10975 p10975 = .success := by decide +kernel
theorem unsat10975 : Unsatisfiable (PosFin 65) f10975 := by
  apply lratCheckerSound f10975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10975
  · intro a ha; simp [p10975] at ha; subst a; trivial
  · exact checked10975
theorem derived10975 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10975 := by
  apply localUnsat_implies_entails f10975 [c10929, c10964, c10789, c245, c255, c8918] c10975 unsat10975 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10789 := derived10789 a h
  have h3 : Entails.eval a c245 := h 244 (by decide)
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c8918 := derived8918 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10976 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10976 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10789, some c10975, some c5582, some c987, some c818, some c8480, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10976 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10976 : lratChecker f10976 p10976 = .success := by decide +kernel
theorem unsat10976 : Unsatisfiable (PosFin 65) f10976 := by
  apply lratCheckerSound f10976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10976
  · intro a ha; simp [p10976] at ha; subst a; trivial
  · exact checked10976
theorem derived10976 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10976 := by
  apply localUnsat_implies_entails f10976 [c10929, c10964, c10789, c10975, c5582, c987, c818, c8480] c10976 unsat10976 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10789 := derived10789 a h
  have h3 : Entails.eval a c10975 := derived10975 a h
  have h4 : Entails.eval a c5582 := h 5581 (by decide)
  have h5 : Entails.eval a c987 := h 986 (by decide)
  have h6 : Entails.eval a c818 := h 817 (by decide)
  have h7 : Entails.eval a c8480 := derived8480 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10977 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10977 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10599, some c10586, some c10349, some c10929, some c8480, some c10571, some c5749, some c3515, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10977 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10977 : lratChecker f10977 p10977 = .success := by decide +kernel
theorem unsat10977 : Unsatisfiable (PosFin 65) f10977 := by
  apply lratCheckerSound f10977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10977
  · intro a ha; simp [p10977] at ha; subst a; trivial
  · exact checked10977
theorem derived10977 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10977 := by
  apply localUnsat_implies_entails f10977 [c10599, c10586, c10349, c10929, c8480, c10571, c5749, c3515] c10977 unsat10977 (by rfl) a
  have h0 : Entails.eval a c10599 := derived10599 a h
  have h1 : Entails.eval a c10586 := derived10586 a h
  have h2 : Entails.eval a c10349 := derived10349 a h
  have h3 : Entails.eval a c10929 := derived10929 a h
  have h4 : Entails.eval a c8480 := derived8480 a h
  have h5 : Entails.eval a c10571 := derived10571 a h
  have h6 : Entails.eval a c5749 := h 5748 (by decide)
  have h7 : Entails.eval a c3515 := h 3514 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10978 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨10, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10978 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10599, some c10569, some c10590, some c10586, some c10349, some c10977, some c1036, some c5606, some c813, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10978 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10978 : lratChecker f10978 p10978 = .success := by decide +kernel
theorem unsat10978 : Unsatisfiable (PosFin 65) f10978 := by
  apply lratCheckerSound f10978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10978
  · intro a ha; simp [p10978] at ha; subst a; trivial
  · exact checked10978
theorem derived10978 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10978 := by
  apply localUnsat_implies_entails f10978 [c10599, c10569, c10590, c10586, c10349, c10977, c1036, c5606, c813] c10978 unsat10978 (by rfl) a
  have h0 : Entails.eval a c10599 := derived10599 a h
  have h1 : Entails.eval a c10569 := derived10569 a h
  have h2 : Entails.eval a c10590 := derived10590 a h
  have h3 : Entails.eval a c10586 := derived10586 a h
  have h4 : Entails.eval a c10349 := derived10349 a h
  have h5 : Entails.eval a c10977 := derived10977 a h
  have h6 : Entails.eval a c1036 := h 1035 (by decide)
  have h7 : Entails.eval a c5606 := h 5605 (by decide)
  have h8 : Entails.eval a c813 := h 812 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10979 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10979 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10599, some c10586, some c10349, some c3123, some c10569, some c10590, some c10929, some c10964, some c10789, some c10566, some c3455, some c5110, some c4046, some c2434, some c3023, some c5086, some c10976, some c10978, some c22, some c8474, some c10063, some c1041, some c4371, some c6751, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10979 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked10979 : lratChecker f10979 p10979 = .success := by decide +kernel
theorem unsat10979 : Unsatisfiable (PosFin 65) f10979 := by
  apply lratCheckerSound f10979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10979
  · intro a ha; simp [p10979] at ha; subst a; trivial
  · exact checked10979
theorem derived10979 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10979 := by
  apply localUnsat_implies_entails f10979 [c10599, c10586, c10349, c3123, c10569, c10590, c10929, c10964, c10789, c10566, c3455, c5110, c4046, c2434, c3023, c5086, c10976, c10978, c22, c8474, c10063, c1041, c4371, c6751] c10979 unsat10979 (by rfl) a
  have h0 : Entails.eval a c10599 := derived10599 a h
  have h1 : Entails.eval a c10586 := derived10586 a h
  have h2 : Entails.eval a c10349 := derived10349 a h
  have h3 : Entails.eval a c3123 := h 3122 (by decide)
  have h4 : Entails.eval a c10569 := derived10569 a h
  have h5 : Entails.eval a c10590 := derived10590 a h
  have h6 : Entails.eval a c10929 := derived10929 a h
  have h7 : Entails.eval a c10964 := derived10964 a h
  have h8 : Entails.eval a c10789 := derived10789 a h
  have h9 : Entails.eval a c10566 := derived10566 a h
  have h10 : Entails.eval a c3455 := h 3454 (by decide)
  have h11 : Entails.eval a c5110 := h 5109 (by decide)
  have h12 : Entails.eval a c4046 := h 4045 (by decide)
  have h13 : Entails.eval a c2434 := h 2433 (by decide)
  have h14 : Entails.eval a c3023 := h 3022 (by decide)
  have h15 : Entails.eval a c5086 := h 5085 (by decide)
  have h16 : Entails.eval a c10976 := derived10976 a h
  have h17 : Entails.eval a c10978 := derived10978 a h
  have h18 : Entails.eval a c22 := h 21 (by decide)
  have h19 : Entails.eval a c8474 := derived8474 a h
  have h20 : Entails.eval a c10063 := derived10063 a h
  have h21 : Entails.eval a c1041 := h 1040 (by decide)
  have h22 : Entails.eval a c4371 := h 4370 (by decide)
  have h23 : Entails.eval a c6751 := h 6750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10980 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, true), (⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨10, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10980 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c252, some c244, some c20, some c6185, some c8918, some c10063, some c1037, some c5903, some c58, some c820, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10980 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked10980 : lratChecker f10980 p10980 = .success := by decide +kernel
theorem unsat10980 : Unsatisfiable (PosFin 65) f10980 := by
  apply lratCheckerSound f10980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10980
  · intro a ha; simp [p10980] at ha; subst a; trivial
  · exact checked10980
theorem derived10980 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10980 := by
  apply localUnsat_implies_entails f10980 [c252, c244, c20, c6185, c8918, c10063, c1037, c5903, c58, c820] c10980 unsat10980 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c244 := h 243 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c6185 := h 6184 (by decide)
  have h4 : Entails.eval a c8918 := derived8918 a h
  have h5 : Entails.eval a c10063 := derived10063 a h
  have h6 : Entails.eval a c1037 := h 1036 (by decide)
  have h7 : Entails.eval a c5903 := h 5902 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c820 := h 819 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10981 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, true), (⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false), (⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10981 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10980, some c8537, some c8516, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p10981 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10981 : lratChecker f10981 p10981 = .success := by decide +kernel
theorem unsat10981 : Unsatisfiable (PosFin 65) f10981 := by
  apply lratCheckerSound f10981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10981
  · intro a ha; simp [p10981] at ha; subst a; trivial
  · exact checked10981
theorem derived10981 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10981 := by
  apply localUnsat_implies_entails f10981 [c10980, c8537, c8516] c10981 unsat10981 (by rfl) a
  have h0 : Entails.eval a c10980 := derived10980 a h
  have h1 : Entails.eval a c8537 := derived8537 a h
  have h2 : Entails.eval a c8516 := derived8516 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10982 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10982 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10974, some c10969, some c10929, some c10964, some c10344, some c3136, some c10586, some c10599, some c10569, some c10349, some c3131, some c10590, some c3123, some c10330, some c10636, some c9998, some c10979, some c10654, some c10577, some c10655, some c2418, some c3001, some c10172, some c10981, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10982 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked10982 : lratChecker f10982 p10982 = .success := by decide +kernel
theorem unsat10982 : Unsatisfiable (PosFin 65) f10982 := by
  apply lratCheckerSound f10982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10982
  · intro a ha; simp [p10982] at ha; subst a; trivial
  · exact checked10982
theorem derived10982 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10982 := by
  apply localUnsat_implies_entails f10982 [c10974, c10969, c10929, c10964, c10344, c3136, c10586, c10599, c10569, c10349, c3131, c10590, c3123, c10330, c10636, c9998, c10979, c10654, c10577, c10655, c2418, c3001, c10172, c10981] c10982 unsat10982 (by rfl) a
  have h0 : Entails.eval a c10974 := derived10974 a h
  have h1 : Entails.eval a c10969 := derived10969 a h
  have h2 : Entails.eval a c10929 := derived10929 a h
  have h3 : Entails.eval a c10964 := derived10964 a h
  have h4 : Entails.eval a c10344 := derived10344 a h
  have h5 : Entails.eval a c3136 := h 3135 (by decide)
  have h6 : Entails.eval a c10586 := derived10586 a h
  have h7 : Entails.eval a c10599 := derived10599 a h
  have h8 : Entails.eval a c10569 := derived10569 a h
  have h9 : Entails.eval a c10349 := derived10349 a h
  have h10 : Entails.eval a c3131 := h 3130 (by decide)
  have h11 : Entails.eval a c10590 := derived10590 a h
  have h12 : Entails.eval a c3123 := h 3122 (by decide)
  have h13 : Entails.eval a c10330 := derived10330 a h
  have h14 : Entails.eval a c10636 := derived10636 a h
  have h15 : Entails.eval a c9998 := derived9998 a h
  have h16 : Entails.eval a c10979 := derived10979 a h
  have h17 : Entails.eval a c10654 := derived10654 a h
  have h18 : Entails.eval a c10577 := derived10577 a h
  have h19 : Entails.eval a c10655 := derived10655 a h
  have h20 : Entails.eval a c2418 := h 2417 (by decide)
  have h21 : Entails.eval a c3001 := h 3000 (by decide)
  have h22 : Entails.eval a c10172 := derived10172 a h
  have h23 : Entails.eval a c10981 := derived10981 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10983 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10983 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8537, some c8516, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p10983 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10983 : lratChecker f10983 p10983 = .success := by decide +kernel
theorem unsat10983 : Unsatisfiable (PosFin 65) f10983 := by
  apply lratCheckerSound f10983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10983
  · intro a ha; simp [p10983] at ha; subst a; trivial
  · exact checked10983
theorem derived10983 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10983 := by
  apply localUnsat_implies_entails f10983 [c8537, c8516] c10983 unsat10983 (by rfl) a
  have h0 : Entails.eval a c8537 := derived8537 a h
  have h1 : Entails.eval a c8516 := derived8516 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10984 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10984 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10982, some c10974, some c10969, some c10929, some c10964, some c3596, some c10654, some c10577, some c10655, some c2433, some c3020, some c5087, some c4424, some c3963, some c2652, some c4357, some c4349, some c3871, some c2628, some c5106, some c4307, some c4298, some c3955, some c9664, some c10983, some c252, some c244, some c20, some c6185, some c4280, some c8550, some c1037, some c4387, some c4401, some c1059, some c991, some c6077, some c79, some c314, some c315, some c208, some c344, some c343, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10984 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]]
theorem checked10984 : lratChecker f10984 p10984 = .success := by decide +kernel
theorem unsat10984 : Unsatisfiable (PosFin 65) f10984 := by
  apply lratCheckerSound f10984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10984
  · intro a ha; simp [p10984] at ha; subst a; trivial
  · exact checked10984
theorem derived10984 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10984 := by
  apply localUnsat_implies_entails f10984 [c10982, c10974, c10969, c10929, c10964, c3596, c10654, c10577, c10655, c2433, c3020, c5087, c4424, c3963, c2652, c4357, c4349, c3871, c2628, c5106, c4307, c4298, c3955, c9664, c10983, c252, c244, c20, c6185, c4280, c8550, c1037, c4387, c4401, c1059, c991, c6077, c79, c314, c315, c208, c344, c343] c10984 unsat10984 (by rfl) a
  have h0 : Entails.eval a c10982 := derived10982 a h
  have h1 : Entails.eval a c10974 := derived10974 a h
  have h2 : Entails.eval a c10969 := derived10969 a h
  have h3 : Entails.eval a c10929 := derived10929 a h
  have h4 : Entails.eval a c10964 := derived10964 a h
  have h5 : Entails.eval a c3596 := h 3595 (by decide)
  have h6 : Entails.eval a c10654 := derived10654 a h
  have h7 : Entails.eval a c10577 := derived10577 a h
  have h8 : Entails.eval a c10655 := derived10655 a h
  have h9 : Entails.eval a c2433 := h 2432 (by decide)
  have h10 : Entails.eval a c3020 := h 3019 (by decide)
  have h11 : Entails.eval a c5087 := h 5086 (by decide)
  have h12 : Entails.eval a c4424 := h 4423 (by decide)
  have h13 : Entails.eval a c3963 := h 3962 (by decide)
  have h14 : Entails.eval a c2652 := h 2651 (by decide)
  have h15 : Entails.eval a c4357 := h 4356 (by decide)
  have h16 : Entails.eval a c4349 := h 4348 (by decide)
  have h17 : Entails.eval a c3871 := h 3870 (by decide)
  have h18 : Entails.eval a c2628 := h 2627 (by decide)
  have h19 : Entails.eval a c5106 := h 5105 (by decide)
  have h20 : Entails.eval a c4307 := h 4306 (by decide)
  have h21 : Entails.eval a c4298 := h 4297 (by decide)
  have h22 : Entails.eval a c3955 := h 3954 (by decide)
  have h23 : Entails.eval a c9664 := derived9664 a h
  have h24 : Entails.eval a c10983 := derived10983 a h
  have h25 : Entails.eval a c252 := h 251 (by decide)
  have h26 : Entails.eval a c244 := h 243 (by decide)
  have h27 : Entails.eval a c20 := h 19 (by decide)
  have h28 : Entails.eval a c6185 := h 6184 (by decide)
  have h29 : Entails.eval a c4280 := h 4279 (by decide)
  have h30 : Entails.eval a c8550 := derived8550 a h
  have h31 : Entails.eval a c1037 := h 1036 (by decide)
  have h32 : Entails.eval a c4387 := h 4386 (by decide)
  have h33 : Entails.eval a c4401 := h 4400 (by decide)
  have h34 : Entails.eval a c1059 := h 1058 (by decide)
  have h35 : Entails.eval a c991 := h 990 (by decide)
  have h36 : Entails.eval a c6077 := h 6076 (by decide)
  have h37 : Entails.eval a c79 := h 78 (by decide)
  have h38 : Entails.eval a c314 := h 313 (by decide)
  have h39 : Entails.eval a c315 := h 314 (by decide)
  have h40 : Entails.eval a c208 := h 207 (by decide)
  have h41 : Entails.eval a c344 := h 343 (by decide)
  have h42 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10985 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨57, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false), (⟨58, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10985 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10789, some c22, some c245, some c255, some c8474, some c1049, some c8947, some c1037, some c4387, some c819, some c822, some c991, some c6080, some c1020, some c314, some c553, some c5285, some c528, some c5287, some c5267, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10985 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked10985 : lratChecker f10985 p10985 = .success := by decide +kernel
theorem unsat10985 : Unsatisfiable (PosFin 65) f10985 := by
  apply lratCheckerSound f10985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10985
  · intro a ha; simp [p10985] at ha; subst a; trivial
  · exact checked10985
theorem derived10985 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10985 := by
  apply localUnsat_implies_entails f10985 [c10929, c10964, c10789, c22, c245, c255, c8474, c1049, c8947, c1037, c4387, c819, c822, c991, c6080, c1020, c314, c553, c5285, c528, c5287, c5267] c10985 unsat10985 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10789 := derived10789 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c255 := h 254 (by decide)
  have h6 : Entails.eval a c8474 := derived8474 a h
  have h7 : Entails.eval a c1049 := h 1048 (by decide)
  have h8 : Entails.eval a c8947 := derived8947 a h
  have h9 : Entails.eval a c1037 := h 1036 (by decide)
  have h10 : Entails.eval a c4387 := h 4386 (by decide)
  have h11 : Entails.eval a c819 := h 818 (by decide)
  have h12 : Entails.eval a c822 := h 821 (by decide)
  have h13 : Entails.eval a c991 := h 990 (by decide)
  have h14 : Entails.eval a c6080 := h 6079 (by decide)
  have h15 : Entails.eval a c1020 := h 1019 (by decide)
  have h16 : Entails.eval a c314 := h 313 (by decide)
  have h17 : Entails.eval a c553 := h 552 (by decide)
  have h18 : Entails.eval a c5285 := h 5284 (by decide)
  have h19 : Entails.eval a c528 := h 527 (by decide)
  have h20 : Entails.eval a c5287 := h 5286 (by decide)
  have h21 : Entails.eval a c5267 := h 5266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10986 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10986 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10969, some c10974, some c10982, some c10984, some c10789, some c3593, some c2552, some c3013, some c4354, some c2650, some c2652, some c4357, some c4349, some c10566, some c10602, some c3871, some c2628, some c4307, some c4288, some c10976, some c10985, some c8480, some c10066, some c1021, some c1038, some c5678, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10986 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked10986 : lratChecker f10986 p10986 = .success := by decide +kernel
theorem unsat10986 : Unsatisfiable (PosFin 65) f10986 := by
  apply lratCheckerSound f10986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10986
  · intro a ha; simp [p10986] at ha; subst a; trivial
  · exact checked10986
theorem derived10986 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10986 := by
  apply localUnsat_implies_entails f10986 [c10929, c10964, c10969, c10974, c10982, c10984, c10789, c3593, c2552, c3013, c4354, c2650, c2652, c4357, c4349, c10566, c10602, c3871, c2628, c4307, c4288, c10976, c10985, c8480, c10066, c1021, c1038, c5678] c10986 unsat10986 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10969 := derived10969 a h
  have h3 : Entails.eval a c10974 := derived10974 a h
  have h4 : Entails.eval a c10982 := derived10982 a h
  have h5 : Entails.eval a c10984 := derived10984 a h
  have h6 : Entails.eval a c10789 := derived10789 a h
  have h7 : Entails.eval a c3593 := h 3592 (by decide)
  have h8 : Entails.eval a c2552 := h 2551 (by decide)
  have h9 : Entails.eval a c3013 := h 3012 (by decide)
  have h10 : Entails.eval a c4354 := h 4353 (by decide)
  have h11 : Entails.eval a c2650 := h 2649 (by decide)
  have h12 : Entails.eval a c2652 := h 2651 (by decide)
  have h13 : Entails.eval a c4357 := h 4356 (by decide)
  have h14 : Entails.eval a c4349 := h 4348 (by decide)
  have h15 : Entails.eval a c10566 := derived10566 a h
  have h16 : Entails.eval a c10602 := derived10602 a h
  have h17 : Entails.eval a c3871 := h 3870 (by decide)
  have h18 : Entails.eval a c2628 := h 2627 (by decide)
  have h19 : Entails.eval a c4307 := h 4306 (by decide)
  have h20 : Entails.eval a c4288 := h 4287 (by decide)
  have h21 : Entails.eval a c10976 := derived10976 a h
  have h22 : Entails.eval a c10985 := derived10985 a h
  have h23 : Entails.eval a c8480 := derived8480 a h
  have h24 : Entails.eval a c10066 := derived10066 a h
  have h25 : Entails.eval a c1021 := h 1020 (by decide)
  have h26 : Entails.eval a c1038 := h 1037 (by decide)
  have h27 : Entails.eval a c5678 := h 5677 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10987 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10987 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10986, some c10929, some c10964, some c10789, some c4836, some c2925, some c5119, some c10972, some c2690, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10987 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10987 : lratChecker f10987 p10987 = .success := by decide +kernel
theorem unsat10987 : Unsatisfiable (PosFin 65) f10987 := by
  apply lratCheckerSound f10987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10987
  · intro a ha; simp [p10987] at ha; subst a; trivial
  · exact checked10987
theorem derived10987 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10987 := by
  apply localUnsat_implies_entails f10987 [c10986, c10929, c10964, c10789, c4836, c2925, c5119, c10972, c2690] c10987 unsat10987 (by rfl) a
  have h0 : Entails.eval a c10986 := derived10986 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c10789 := derived10789 a h
  have h4 : Entails.eval a c4836 := h 4835 (by decide)
  have h5 : Entails.eval a c2925 := h 2924 (by decide)
  have h6 : Entails.eval a c5119 := h 5118 (by decide)
  have h7 : Entails.eval a c10972 := derived10972 a h
  have h8 : Entails.eval a c2690 := h 2689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10988 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨10, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10988 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10709, some c4311, some c2926, some c5120, some c2690, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10988 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked10988 : lratChecker f10988 p10988 = .success := by decide +kernel
theorem unsat10988 : Unsatisfiable (PosFin 65) f10988 := by
  apply lratCheckerSound f10988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10988
  · intro a ha; simp [p10988] at ha; subst a; trivial
  · exact checked10988
theorem derived10988 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10988 := by
  apply localUnsat_implies_entails f10988 [c10929, c10964, c10709, c4311, c2926, c5120, c2690] c10988 unsat10988 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10709 := derived10709 a h
  have h3 : Entails.eval a c4311 := h 4310 (by decide)
  have h4 : Entails.eval a c2926 := h 2925 (by decide)
  have h5 : Entails.eval a c5120 := h 5119 (by decide)
  have h6 : Entails.eval a c2690 := h 2689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10989 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10989 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10986, some c10929, some c10964, some c10987, some c10988, some c10972, some c10655, some c4838, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10989 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10989 : lratChecker f10989 p10989 = .success := by decide +kernel
theorem unsat10989 : Unsatisfiable (PosFin 65) f10989 := by
  apply lratCheckerSound f10989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10989
  · intro a ha; simp [p10989] at ha; subst a; trivial
  · exact checked10989
theorem derived10989 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10989 := by
  apply localUnsat_implies_entails f10989 [c10986, c10929, c10964, c10987, c10988, c10972, c10655, c4838] c10989 unsat10989 (by rfl) a
  have h0 : Entails.eval a c10986 := derived10986 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c10987 := derived10987 a h
  have h4 : Entails.eval a c10988 := derived10988 a h
  have h5 : Entails.eval a c10972 := derived10972 a h
  have h6 : Entails.eval a c10655 := derived10655 a h
  have h7 : Entails.eval a c4838 := h 4837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10990 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨60, by decide⟩, true), (⟨16, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10990 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c4836, some c4840, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10990 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked10990 : lratChecker f10990 p10990 = .success := by decide +kernel
theorem unsat10990 : Unsatisfiable (PosFin 65) f10990 := by
  apply lratCheckerSound f10990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10990
  · intro a ha; simp [p10990] at ha; subst a; trivial
  · exact checked10990
theorem derived10990 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10990 := by
  apply localUnsat_implies_entails f10990 [c10929, c4836, c4840] c10990 unsat10990 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c4836 := h 4835 (by decide)
  have h2 : Entails.eval a c4840 := h 4839 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c10991 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨57, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10991 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10757, some c10753, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10991 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked10991 : lratChecker f10991 p10991 = .success := by decide +kernel
theorem unsat10991 : Unsatisfiable (PosFin 65) f10991 := by
  apply lratCheckerSound f10991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10991
  · intro a ha; simp [p10991] at ha; subst a; trivial
  · exact checked10991
theorem derived10991 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10991 := by
  apply localUnsat_implies_entails f10991 [c10929, c10964, c10757, c10753] c10991 unsat10991 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10757 := derived10757 a h
  have h3 : Entails.eval a c10753 := derived10753 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c10992 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10992 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10986, some c10989, some c10347, some c10344, some c10336, some c10648, some c10754, some c10364, some c10991, some c10990, some c10973, some c2927, some c2589, some c10652, some c4047, some c10729, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10992 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked10992 : lratChecker f10992 p10992 = .success := by decide +kernel
theorem unsat10992 : Unsatisfiable (PosFin 65) f10992 := by
  apply lratCheckerSound f10992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10992
  · intro a ha; simp [p10992] at ha; subst a; trivial
  · exact checked10992
theorem derived10992 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10992 := by
  apply localUnsat_implies_entails f10992 [c10929, c10964, c10986, c10989, c10347, c10344, c10336, c10648, c10754, c10364, c10991, c10990, c10973, c2927, c2589, c10652, c4047, c10729] c10992 unsat10992 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10986 := derived10986 a h
  have h3 : Entails.eval a c10989 := derived10989 a h
  have h4 : Entails.eval a c10347 := derived10347 a h
  have h5 : Entails.eval a c10344 := derived10344 a h
  have h6 : Entails.eval a c10336 := derived10336 a h
  have h7 : Entails.eval a c10648 := derived10648 a h
  have h8 : Entails.eval a c10754 := derived10754 a h
  have h9 : Entails.eval a c10364 := derived10364 a h
  have h10 : Entails.eval a c10991 := derived10991 a h
  have h11 : Entails.eval a c10990 := derived10990 a h
  have h12 : Entails.eval a c10973 := derived10973 a h
  have h13 : Entails.eval a c2927 := h 2926 (by decide)
  have h14 : Entails.eval a c2589 := h 2588 (by decide)
  have h15 : Entails.eval a c10652 := derived10652 a h
  have h16 : Entails.eval a c4047 := h 4046 (by decide)
  have h17 : Entails.eval a c10729 := derived10729 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10993 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10993 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10347, some c10344, some c10648, some c10754, some c10364, some c10991, some c10336, some c10990, some c10973, some c2927, some c2589, some c10652, some c4047, some c10729, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10993 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked10993 : lratChecker f10993 p10993 = .success := by decide +kernel
theorem unsat10993 : Unsatisfiable (PosFin 65) f10993 := by
  apply lratCheckerSound f10993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10993
  · intro a ha; simp [p10993] at ha; subst a; trivial
  · exact checked10993
theorem derived10993 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10993 := by
  apply localUnsat_implies_entails f10993 [c10929, c10964, c10347, c10344, c10648, c10754, c10364, c10991, c10336, c10990, c10973, c2927, c2589, c10652, c4047, c10729] c10993 unsat10993 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10347 := derived10347 a h
  have h3 : Entails.eval a c10344 := derived10344 a h
  have h4 : Entails.eval a c10648 := derived10648 a h
  have h5 : Entails.eval a c10754 := derived10754 a h
  have h6 : Entails.eval a c10364 := derived10364 a h
  have h7 : Entails.eval a c10991 := derived10991 a h
  have h8 : Entails.eval a c10336 := derived10336 a h
  have h9 : Entails.eval a c10990 := derived10990 a h
  have h10 : Entails.eval a c10973 := derived10973 a h
  have h11 : Entails.eval a c2927 := h 2926 (by decide)
  have h12 : Entails.eval a c2589 := h 2588 (by decide)
  have h13 : Entails.eval a c10652 := derived10652 a h
  have h14 : Entails.eval a c4047 := h 4046 (by decide)
  have h15 : Entails.eval a c10729 := derived10729 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10994 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10994 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10993, some c10929, some c10964, some c10347, some c10344, some c10648, some c10754, some c10364, some c10336, some c10973, some c10566, some c10602, some c4047, some c10729, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10994 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked10994 : lratChecker f10994 p10994 = .success := by decide +kernel
theorem unsat10994 : Unsatisfiable (PosFin 65) f10994 := by
  apply lratCheckerSound f10994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10994
  · intro a ha; simp [p10994] at ha; subst a; trivial
  · exact checked10994
theorem derived10994 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10994 := by
  apply localUnsat_implies_entails f10994 [c10993, c10929, c10964, c10347, c10344, c10648, c10754, c10364, c10336, c10973, c10566, c10602, c4047, c10729] c10994 unsat10994 (by rfl) a
  have h0 : Entails.eval a c10993 := derived10993 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c10347 := derived10347 a h
  have h4 : Entails.eval a c10344 := derived10344 a h
  have h5 : Entails.eval a c10648 := derived10648 a h
  have h6 : Entails.eval a c10754 := derived10754 a h
  have h7 : Entails.eval a c10364 := derived10364 a h
  have h8 : Entails.eval a c10336 := derived10336 a h
  have h9 : Entails.eval a c10973 := derived10973 a h
  have h10 : Entails.eval a c10566 := derived10566 a h
  have h11 : Entails.eval a c10602 := derived10602 a h
  have h12 : Entails.eval a c4047 := h 4046 (by decide)
  have h13 : Entails.eval a c10729 := derived10729 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10995 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10995 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10347, some c10344, some c10648, some c10754, some c10364, some c10991, some c10994, some c10198, some c3210, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10995 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked10995 : lratChecker f10995 p10995 = .success := by decide +kernel
theorem unsat10995 : Unsatisfiable (PosFin 65) f10995 := by
  apply lratCheckerSound f10995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10995
  · intro a ha; simp [p10995] at ha; subst a; trivial
  · exact checked10995
theorem derived10995 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10995 := by
  apply localUnsat_implies_entails f10995 [c10929, c10964, c10347, c10344, c10648, c10754, c10364, c10991, c10994, c10198, c3210] c10995 unsat10995 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10347 := derived10347 a h
  have h3 : Entails.eval a c10344 := derived10344 a h
  have h4 : Entails.eval a c10648 := derived10648 a h
  have h5 : Entails.eval a c10754 := derived10754 a h
  have h6 : Entails.eval a c10364 := derived10364 a h
  have h7 : Entails.eval a c10991 := derived10991 a h
  have h8 : Entails.eval a c10994 := derived10994 a h
  have h9 : Entails.eval a c10198 := derived10198 a h
  have h10 : Entails.eval a c3210 := h 3209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10996 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10996 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10992, some c10995, some c10929, some c10964, some c4311, some c10198, some c10789, some c3206, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10996 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked10996 : lratChecker f10996 p10996 = .success := by decide +kernel
theorem unsat10996 : Unsatisfiable (PosFin 65) f10996 := by
  apply lratCheckerSound f10996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10996
  · intro a ha; simp [p10996] at ha; subst a; trivial
  · exact checked10996
theorem derived10996 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10996 := by
  apply localUnsat_implies_entails f10996 [c10992, c10995, c10929, c10964, c4311, c10198, c10789, c3206] c10996 unsat10996 (by rfl) a
  have h0 : Entails.eval a c10992 := derived10992 a h
  have h1 : Entails.eval a c10995 := derived10995 a h
  have h2 : Entails.eval a c10929 := derived10929 a h
  have h3 : Entails.eval a c10964 := derived10964 a h
  have h4 : Entails.eval a c4311 := h 4310 (by decide)
  have h5 : Entails.eval a c10198 := derived10198 a h
  have h6 : Entails.eval a c10789 := derived10789 a h
  have h7 : Entails.eval a c3206 := h 3205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c10997 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨54, by decide⟩, false), (⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10997 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9931, some c2689, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10997 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10997 : lratChecker f10997 p10997 = .success := by decide +kernel
theorem unsat10997 : Unsatisfiable (PosFin 65) f10997 := by
  apply lratCheckerSound f10997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10997
  · intro a ha; simp [p10997] at ha; subst a; trivial
  · exact checked10997
theorem derived10997 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10997 := by
  apply localUnsat_implies_entails f10997 [c9931, c2689] c10997 unsat10997 (by rfl) a
  have h0 : Entails.eval a c9931 := derived9931 a h
  have h1 : Entails.eval a c2689 := h 2688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10998 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10998 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10789, some c3410, some c10997, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10998 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10998 : lratChecker f10998 p10998 = .success := by decide +kernel
theorem unsat10998 : Unsatisfiable (PosFin 65) f10998 := by
  apply lratCheckerSound f10998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10998
  · intro a ha; simp [p10998] at ha; subst a; trivial
  · exact checked10998
theorem derived10998 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10998 := by
  apply localUnsat_implies_entails f10998 [c10929, c10964, c10789, c3410, c10997] c10998 unsat10998 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10789 := derived10789 a h
  have h3 : Entails.eval a c3410 := h 3409 (by decide)
  have h4 : Entails.eval a c10997 := derived10997 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c10999 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10999 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10992, some c10996, some c10998, some c10929, some c10964, some c2690, some c2917, some c2555, some c3799, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10999 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked10999 : lratChecker f10999 p10999 = .success := by decide +kernel
theorem unsat10999 : Unsatisfiable (PosFin 65) f10999 := by
  apply lratCheckerSound f10999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10999
  · intro a ha; simp [p10999] at ha; subst a; trivial
  · exact checked10999
theorem derived10999 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10999 := by
  apply localUnsat_implies_entails f10999 [c10992, c10996, c10998, c10929, c10964, c2690, c2917, c2555, c3799] c10999 unsat10999 (by rfl) a
  have h0 : Entails.eval a c10992 := derived10992 a h
  have h1 : Entails.eval a c10996 := derived10996 a h
  have h2 : Entails.eval a c10998 := derived10998 a h
  have h3 : Entails.eval a c10929 := derived10929 a h
  have h4 : Entails.eval a c10964 := derived10964 a h
  have h5 : Entails.eval a c2690 := h 2689 (by decide)
  have h6 : Entails.eval a c2917 := h 2916 (by decide)
  have h7 : Entails.eval a c2555 := h 2554 (by decide)
  have h8 : Entails.eval a c3799 := h 3798 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11000 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11000 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10996, some c10992, some c10998, some c10967, some c10995, some c10929, some c10964, some c2647, some c10970, some c10654, some c3960, some c2655, some c10172, some c4528, some c10720, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11000 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11000 : lratChecker f11000 p11000 = .success := by decide +kernel
theorem unsat11000 : Unsatisfiable (PosFin 65) f11000 := by
  apply lratCheckerSound f11000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11000
  · intro a ha; simp [p11000] at ha; subst a; trivial
  · exact checked11000
theorem derived11000 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11000 := by
  apply localUnsat_implies_entails f11000 [c10996, c10992, c10998, c10967, c10995, c10929, c10964, c2647, c10970, c10654, c3960, c2655, c10172, c4528, c10720] c11000 unsat11000 (by rfl) a
  have h0 : Entails.eval a c10996 := derived10996 a h
  have h1 : Entails.eval a c10992 := derived10992 a h
  have h2 : Entails.eval a c10998 := derived10998 a h
  have h3 : Entails.eval a c10967 := derived10967 a h
  have h4 : Entails.eval a c10995 := derived10995 a h
  have h5 : Entails.eval a c10929 := derived10929 a h
  have h6 : Entails.eval a c10964 := derived10964 a h
  have h7 : Entails.eval a c2647 := h 2646 (by decide)
  have h8 : Entails.eval a c10970 := derived10970 a h
  have h9 : Entails.eval a c10654 := derived10654 a h
  have h10 : Entails.eval a c3960 := h 3959 (by decide)
  have h11 : Entails.eval a c2655 := h 2654 (by decide)
  have h12 : Entails.eval a c10172 := derived10172 a h
  have h13 : Entails.eval a c4528 := h 4527 (by decide)
  have h14 : Entails.eval a c10720 := derived10720 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11001 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11001 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10709, some c10655, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11001 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11001 : lratChecker f11001 p11001 = .success := by decide +kernel
theorem unsat11001 : Unsatisfiable (PosFin 65) f11001 := by
  apply lratCheckerSound f11001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11001
  · intro a ha; simp [p11001] at ha; subst a; trivial
  · exact checked11001
theorem derived11001 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11001 := by
  apply localUnsat_implies_entails f11001 [c10929, c10964, c10709, c10655] c11001 unsat11001 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10709 := derived10709 a h
  have h3 : Entails.eval a c10655 := derived10655 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11002 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11002 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c10992, some c10996, some c10998, some c11001, some c11000, some c10999, some c3411, some c10654, some c2555, some c3799, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11002 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11002 : lratChecker f11002 p11002 = .success := by decide +kernel
theorem unsat11002 : Unsatisfiable (PosFin 65) f11002 := by
  apply lratCheckerSound f11002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11002
  · intro a ha; simp [p11002] at ha; subst a; trivial
  · exact checked11002
theorem derived11002 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11002 := by
  apply localUnsat_implies_entails f11002 [c10929, c10964, c10992, c10996, c10998, c11001, c11000, c10999, c3411, c10654, c2555, c3799] c11002 unsat11002 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c10992 := derived10992 a h
  have h3 : Entails.eval a c10996 := derived10996 a h
  have h4 : Entails.eval a c10998 := derived10998 a h
  have h5 : Entails.eval a c11001 := derived11001 a h
  have h6 : Entails.eval a c11000 := derived11000 a h
  have h7 : Entails.eval a c10999 := derived10999 a h
  have h8 : Entails.eval a c3411 := h 3410 (by decide)
  have h9 : Entails.eval a c10654 := derived10654 a h
  have h10 : Entails.eval a c2555 := h 2554 (by decide)
  have h11 : Entails.eval a c3799 := h 3798 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11003 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨59, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11003 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10654, some c3960, some c2555, some c3963, some c4528, some c3662, some c10720, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11003 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11003 : lratChecker f11003 p11003 = .success := by decide +kernel
theorem unsat11003 : Unsatisfiable (PosFin 65) f11003 := by
  apply lratCheckerSound f11003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11003
  · intro a ha; simp [p11003] at ha; subst a; trivial
  · exact checked11003
theorem derived11003 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11003 := by
  apply localUnsat_implies_entails f11003 [c10654, c3960, c2555, c3963, c4528, c3662, c10720] c11003 unsat11003 (by rfl) a
  have h0 : Entails.eval a c10654 := derived10654 a h
  have h1 : Entails.eval a c3960 := h 3959 (by decide)
  have h2 : Entails.eval a c2555 := h 2554 (by decide)
  have h3 : Entails.eval a c3963 := h 3962 (by decide)
  have h4 : Entails.eval a c4528 := h 4527 (by decide)
  have h5 : Entails.eval a c3662 := h 3661 (by decide)
  have h6 : Entails.eval a c10720 := derived10720 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11004 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11004 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11001, some c10967, some c10994, some c11002, some c10929, some c10964, some c11003, some c2486, some c3411, some c2690, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11004 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11004 : lratChecker f11004 p11004 = .success := by decide +kernel
theorem unsat11004 : Unsatisfiable (PosFin 65) f11004 := by
  apply lratCheckerSound f11004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11004
  · intro a ha; simp [p11004] at ha; subst a; trivial
  · exact checked11004
theorem derived11004 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11004 := by
  apply localUnsat_implies_entails f11004 [c11001, c10967, c10994, c11002, c10929, c10964, c11003, c2486, c3411, c2690] c11004 unsat11004 (by rfl) a
  have h0 : Entails.eval a c11001 := derived11001 a h
  have h1 : Entails.eval a c10967 := derived10967 a h
  have h2 : Entails.eval a c10994 := derived10994 a h
  have h3 : Entails.eval a c11002 := derived11002 a h
  have h4 : Entails.eval a c10929 := derived10929 a h
  have h5 : Entails.eval a c10964 := derived10964 a h
  have h6 : Entails.eval a c11003 := derived11003 a h
  have h7 : Entails.eval a c2486 := h 2485 (by decide)
  have h8 : Entails.eval a c3411 := h 3410 (by decide)
  have h9 : Entails.eval a c2690 := h 2689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11005 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11005 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10994, some c10929, some c10964, some c10967, some c11001, some c11004, some c2647, some c10654, some c3960, some c2655, some c4528, some c4049, some c10720, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11005 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11005 : lratChecker f11005 p11005 = .success := by decide +kernel
theorem unsat11005 : Unsatisfiable (PosFin 65) f11005 := by
  apply lratCheckerSound f11005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11005
  · intro a ha; simp [p11005] at ha; subst a; trivial
  · exact checked11005
theorem derived11005 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11005 := by
  apply localUnsat_implies_entails f11005 [c10994, c10929, c10964, c10967, c11001, c11004, c2647, c10654, c3960, c2655, c4528, c4049, c10720] c11005 unsat11005 (by rfl) a
  have h0 : Entails.eval a c10994 := derived10994 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c10967 := derived10967 a h
  have h4 : Entails.eval a c11001 := derived11001 a h
  have h5 : Entails.eval a c11004 := derived11004 a h
  have h6 : Entails.eval a c2647 := h 2646 (by decide)
  have h7 : Entails.eval a c10654 := derived10654 a h
  have h8 : Entails.eval a c3960 := h 3959 (by decide)
  have h9 : Entails.eval a c2655 := h 2654 (by decide)
  have h10 : Entails.eval a c4528 := h 4527 (by decide)
  have h11 : Entails.eval a c4049 := h 4048 (by decide)
  have h12 : Entails.eval a c10720 := derived10720 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11006 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11006 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11002, some c10929, some c10964, some c11005, some c10789, some c10997, some c10998, some c3386, some c5119, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11006 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11006 : lratChecker f11006 p11006 = .success := by decide +kernel
theorem unsat11006 : Unsatisfiable (PosFin 65) f11006 := by
  apply lratCheckerSound f11006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11006
  · intro a ha; simp [p11006] at ha; subst a; trivial
  · exact checked11006
theorem derived11006 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11006 := by
  apply localUnsat_implies_entails f11006 [c11002, c10929, c10964, c11005, c10789, c10997, c10998, c3386, c5119] c11006 unsat11006 (by rfl) a
  have h0 : Entails.eval a c11002 := derived11002 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c11005 := derived11005 a h
  have h4 : Entails.eval a c10789 := derived10789 a h
  have h5 : Entails.eval a c10997 := derived10997 a h
  have h6 : Entails.eval a c10998 := derived10998 a h
  have h7 : Entails.eval a c3386 := h 3385 (by decide)
  have h8 : Entails.eval a c5119 := h 5118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11007 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11007 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11006, some c11002, some c10929, some c10964, some c10789, some c4836, some c3206, some c3386, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11007 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11007 : lratChecker f11007 p11007 = .success := by decide +kernel
theorem unsat11007 : Unsatisfiable (PosFin 65) f11007 := by
  apply lratCheckerSound f11007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11007
  · intro a ha; simp [p11007] at ha; subst a; trivial
  · exact checked11007
theorem derived11007 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11007 := by
  apply localUnsat_implies_entails f11007 [c11006, c11002, c10929, c10964, c10789, c4836, c3206, c3386] c11007 unsat11007 (by rfl) a
  have h0 : Entails.eval a c11006 := derived11006 a h
  have h1 : Entails.eval a c11002 := derived11002 a h
  have h2 : Entails.eval a c10929 := derived10929 a h
  have h3 : Entails.eval a c10964 := derived10964 a h
  have h4 : Entails.eval a c10789 := derived10789 a h
  have h5 : Entails.eval a c4836 := h 4835 (by decide)
  have h6 : Entails.eval a c3206 := h 3205 (by decide)
  have h7 : Entails.eval a c3386 := h 3385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11008 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11008 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11007, some c11002, some c10929, some c3387, some c3390, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11008 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11008 : lratChecker f11008 p11008 = .success := by decide +kernel
theorem unsat11008 : Unsatisfiable (PosFin 65) f11008 := by
  apply lratCheckerSound f11008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11008
  · intro a ha; simp [p11008] at ha; subst a; trivial
  · exact checked11008
theorem derived11008 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11008 := by
  apply localUnsat_implies_entails f11008 [c11007, c11002, c10929, c3387, c3390] c11008 unsat11008 (by rfl) a
  have h0 : Entails.eval a c11007 := derived11007 a h
  have h1 : Entails.eval a c11002 := derived11002 a h
  have h2 : Entails.eval a c10929 := derived10929 a h
  have h3 : Entails.eval a c3387 := h 3386 (by decide)
  have h4 : Entails.eval a c3390 := h 3389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11009 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11009 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11007, some c11001, some c11006, some c10929, some c4838, some c4837, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11009 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11009 : lratChecker f11009 p11009 = .success := by decide +kernel
theorem unsat11009 : Unsatisfiable (PosFin 65) f11009 := by
  apply lratCheckerSound f11009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11009
  · intro a ha; simp [p11009] at ha; subst a; trivial
  · exact checked11009
theorem derived11009 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11009 := by
  apply localUnsat_implies_entails f11009 [c11007, c11001, c11006, c10929, c4838, c4837] c11009 unsat11009 (by rfl) a
  have h0 : Entails.eval a c11007 := derived11007 a h
  have h1 : Entails.eval a c11001 := derived11001 a h
  have h2 : Entails.eval a c11006 := derived11006 a h
  have h3 : Entails.eval a c10929 := derived10929 a h
  have h4 : Entails.eval a c4838 := h 4837 (by decide)
  have h5 : Entails.eval a c4837 := h 4836 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11010 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11010 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c11006, some c11007, some c11001, some c11009, some c11008, some c3207, some c3209, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11010 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11010 : lratChecker f11010 p11010 = .success := by decide +kernel
theorem unsat11010 : Unsatisfiable (PosFin 65) f11010 := by
  apply lratCheckerSound f11010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11010
  · intro a ha; simp [p11010] at ha; subst a; trivial
  · exact checked11010
theorem derived11010 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11010 := by
  apply localUnsat_implies_entails f11010 [c10929, c11006, c11007, c11001, c11009, c11008, c3207, c3209] c11010 unsat11010 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c11006 := derived11006 a h
  have h2 : Entails.eval a c11007 := derived11007 a h
  have h3 : Entails.eval a c11001 := derived11001 a h
  have h4 : Entails.eval a c11009 := derived11009 a h
  have h5 : Entails.eval a c11008 := derived11008 a h
  have h6 : Entails.eval a c3207 := h 3206 (by decide)
  have h7 : Entails.eval a c3209 := h 3208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11011 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨3, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11011 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11010, some c10929, some c10964, some c10345, some c10755, some c4352, some c3439, some c4640, some c4397, some c2649, some c10941, some c3884, some c3878, some c3868, some c3882, some c9416, some c3407, some c2914, some c5102, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11011 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked11011 : lratChecker f11011 p11011 = .success := by decide +kernel
theorem unsat11011 : Unsatisfiable (PosFin 65) f11011 := by
  apply lratCheckerSound f11011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11011
  · intro a ha; simp [p11011] at ha; subst a; trivial
  · exact checked11011
theorem derived11011 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11011 := by
  apply localUnsat_implies_entails f11011 [c11010, c10929, c10964, c10345, c10755, c4352, c3439, c4640, c4397, c2649, c10941, c3884, c3878, c3868, c3882, c9416, c3407, c2914, c5102] c11011 unsat11011 (by rfl) a
  have h0 : Entails.eval a c11010 := derived11010 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c10345 := derived10345 a h
  have h4 : Entails.eval a c10755 := derived10755 a h
  have h5 : Entails.eval a c4352 := h 4351 (by decide)
  have h6 : Entails.eval a c3439 := h 3438 (by decide)
  have h7 : Entails.eval a c4640 := h 4639 (by decide)
  have h8 : Entails.eval a c4397 := h 4396 (by decide)
  have h9 : Entails.eval a c2649 := h 2648 (by decide)
  have h10 : Entails.eval a c10941 := derived10941 a h
  have h11 : Entails.eval a c3884 := h 3883 (by decide)
  have h12 : Entails.eval a c3878 := h 3877 (by decide)
  have h13 : Entails.eval a c3868 := h 3867 (by decide)
  have h14 : Entails.eval a c3882 := h 3881 (by decide)
  have h15 : Entails.eval a c9416 := derived9416 a h
  have h16 : Entails.eval a c3407 := h 3406 (by decide)
  have h17 : Entails.eval a c2914 := h 2913 (by decide)
  have h18 : Entails.eval a c5102 := h 5101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11012 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11012 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11010, some c10929, some c10964, some c10345, some c10755, some c4352, some c2649, some c11011, some c3411, some c2690, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11012 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11012 : lratChecker f11012 p11012 = .success := by decide +kernel
theorem unsat11012 : Unsatisfiable (PosFin 65) f11012 := by
  apply lratCheckerSound f11012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11012
  · intro a ha; simp [p11012] at ha; subst a; trivial
  · exact checked11012
theorem derived11012 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11012 := by
  apply localUnsat_implies_entails f11012 [c11010, c10929, c10964, c10345, c10755, c4352, c2649, c11011, c3411, c2690] c11012 unsat11012 (by rfl) a
  have h0 : Entails.eval a c11010 := derived11010 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c10345 := derived10345 a h
  have h4 : Entails.eval a c10755 := derived10755 a h
  have h5 : Entails.eval a c4352 := h 4351 (by decide)
  have h6 : Entails.eval a c2649 := h 2648 (by decide)
  have h7 : Entails.eval a c11011 := derived11011 a h
  have h8 : Entails.eval a c3411 := h 3410 (by decide)
  have h9 : Entails.eval a c2690 := h 2689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11013 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨56, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11013 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c10964, some c11010, some c10345, some c10755, some c2649, some c4352, some c2690, some c10730, some c10965, some c10172, some c10286, some c10288, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11013 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11013 : lratChecker f11013 p11013 = .success := by decide +kernel
theorem unsat11013 : Unsatisfiable (PosFin 65) f11013 := by
  apply lratCheckerSound f11013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11013
  · intro a ha; simp [p11013] at ha; subst a; trivial
  · exact checked11013
theorem derived11013 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11013 := by
  apply localUnsat_implies_entails f11013 [c10929, c10964, c11010, c10345, c10755, c2649, c4352, c2690, c10730, c10965, c10172, c10286, c10288] c11013 unsat11013 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c10964 := derived10964 a h
  have h2 : Entails.eval a c11010 := derived11010 a h
  have h3 : Entails.eval a c10345 := derived10345 a h
  have h4 : Entails.eval a c10755 := derived10755 a h
  have h5 : Entails.eval a c2649 := h 2648 (by decide)
  have h6 : Entails.eval a c4352 := h 4351 (by decide)
  have h7 : Entails.eval a c2690 := h 2689 (by decide)
  have h8 : Entails.eval a c10730 := derived10730 a h
  have h9 : Entails.eval a c10965 := derived10965 a h
  have h10 : Entails.eval a c10172 := derived10172 a h
  have h11 : Entails.eval a c10286 := derived10286 a h
  have h12 : Entails.eval a c10288 := derived10288 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11014 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11014 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11010, some c10929, some c10964, some c10345, some c10755, some c4352, some c11013, some c10173, some c10525, some c10244, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11014 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11014 : lratChecker f11014 p11014 = .success := by decide +kernel
theorem unsat11014 : Unsatisfiable (PosFin 65) f11014 := by
  apply lratCheckerSound f11014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11014
  · intro a ha; simp [p11014] at ha; subst a; trivial
  · exact checked11014
theorem derived11014 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11014 := by
  apply localUnsat_implies_entails f11014 [c11010, c10929, c10964, c10345, c10755, c4352, c11013, c10173, c10525, c10244] c11014 unsat11014 (by rfl) a
  have h0 : Entails.eval a c11010 := derived11010 a h
  have h1 : Entails.eval a c10929 := derived10929 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c10345 := derived10345 a h
  have h4 : Entails.eval a c10755 := derived10755 a h
  have h5 : Entails.eval a c4352 := h 4351 (by decide)
  have h6 : Entails.eval a c11013 := derived11013 a h
  have h7 : Entails.eval a c10173 := derived10173 a h
  have h8 : Entails.eval a c10525 := derived10525 a h
  have h9 : Entails.eval a c10244 := derived10244 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11015 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11015 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c11010, some c10964, some c10345, some c10755, some c4352, some c10730, some c2649, some c11012, some c2488, some c11014, some c10970, some c10941, some c10172, some c10286, some c10288, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11015 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11015 : lratChecker f11015 p11015 = .success := by decide +kernel
theorem unsat11015 : Unsatisfiable (PosFin 65) f11015 := by
  apply lratCheckerSound f11015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11015
  · intro a ha; simp [p11015] at ha; subst a; trivial
  · exact checked11015
theorem derived11015 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11015 := by
  apply localUnsat_implies_entails f11015 [c10929, c11010, c10964, c10345, c10755, c4352, c10730, c2649, c11012, c2488, c11014, c10970, c10941, c10172, c10286, c10288] c11015 unsat11015 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c11010 := derived11010 a h
  have h2 : Entails.eval a c10964 := derived10964 a h
  have h3 : Entails.eval a c10345 := derived10345 a h
  have h4 : Entails.eval a c10755 := derived10755 a h
  have h5 : Entails.eval a c4352 := h 4351 (by decide)
  have h6 : Entails.eval a c10730 := derived10730 a h
  have h7 : Entails.eval a c2649 := h 2648 (by decide)
  have h8 : Entails.eval a c11012 := derived11012 a h
  have h9 : Entails.eval a c2488 := h 2487 (by decide)
  have h10 : Entails.eval a c11014 := derived11014 a h
  have h11 : Entails.eval a c10970 := derived10970 a h
  have h12 : Entails.eval a c10941 := derived10941 a h
  have h13 : Entails.eval a c10172 := derived10172 a h
  have h14 : Entails.eval a c10286 := derived10286 a h
  have h15 : Entails.eval a c10288 := derived10288 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11016 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11016 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10345, some c10755, some c2649, some c4352, some c2553, some c11015, some c10998, some c2485, some c10021, some c8269, some c10914, some c10970, some c4517, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11016 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11016 : lratChecker f11016 p11016 = .success := by decide +kernel
theorem unsat11016 : Unsatisfiable (PosFin 65) f11016 := by
  apply lratCheckerSound f11016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11016
  · intro a ha; simp [p11016] at ha; subst a; trivial
  · exact checked11016
theorem derived11016 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11016 := by
  apply localUnsat_implies_entails f11016 [c10345, c10755, c2649, c4352, c2553, c11015, c10998, c2485, c10021, c8269, c10914, c10970, c4517] c11016 unsat11016 (by rfl) a
  have h0 : Entails.eval a c10345 := derived10345 a h
  have h1 : Entails.eval a c10755 := derived10755 a h
  have h2 : Entails.eval a c2649 := h 2648 (by decide)
  have h3 : Entails.eval a c4352 := h 4351 (by decide)
  have h4 : Entails.eval a c2553 := h 2552 (by decide)
  have h5 : Entails.eval a c11015 := derived11015 a h
  have h6 : Entails.eval a c10998 := derived10998 a h
  have h7 : Entails.eval a c2485 := h 2484 (by decide)
  have h8 : Entails.eval a c10021 := derived10021 a h
  have h9 : Entails.eval a c8269 := derived8269 a h
  have h10 : Entails.eval a c10914 := derived10914 a h
  have h11 : Entails.eval a c10970 := derived10970 a h
  have h12 : Entails.eval a c4517 := h 4516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11017 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11017 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10964, some c11010, some c11016, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11017 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11017 : lratChecker f11017 p11017 = .success := by decide +kernel
theorem unsat11017 : Unsatisfiable (PosFin 65) f11017 := by
  apply lratCheckerSound f11017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11017
  · intro a ha; simp [p11017] at ha; subst a; trivial
  · exact checked11017
theorem derived11017 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11017 := by
  apply localUnsat_implies_entails f11017 [c10964, c11010, c11016] c11017 unsat11017 (by rfl) a
  have h0 : Entails.eval a c10964 := derived10964 a h
  have h1 : Entails.eval a c11010 := derived11010 a h
  have h2 : Entails.eval a c11016 := derived11016 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11018 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11018 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10929, some c11017, some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p11018 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11018 : lratChecker f11018 p11018 = .success := by decide +kernel
theorem unsat11018 : Unsatisfiable (PosFin 65) f11018 := by
  apply lratCheckerSound f11018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11018
  · intro a ha; simp [p11018] at ha; subst a; trivial
  · exact checked11018
theorem derived11018 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11018 := by
  apply localUnsat_implies_entails f11018 [c10929, c11017] c11018 unsat11018 (by rfl) a
  have h0 : Entails.eval a c10929 := derived10929 a h
  have h1 : Entails.eval a c11017 := derived11017 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11019 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨13, by decide⟩, false), (⟨56, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11019 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c10761, some c10332, some c4517, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p11019 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11019 : lratChecker f11019 p11019 = .success := by decide +kernel
theorem unsat11019 : Unsatisfiable (PosFin 65) f11019 := by
  apply lratCheckerSound f11019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11019
  · intro a ha; simp [p11019] at ha; subst a; trivial
  · exact checked11019
theorem derived11019 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11019 := by
  apply localUnsat_implies_entails f11019 [c8269, c10761, c10332, c4517] c11019 unsat11019 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c10761 := derived10761 a h
  have h2 : Entails.eval a c10332 := derived10332 a h
  have h3 : Entails.eval a c4517 := h 4516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11020 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨64, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11020 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c4524, some c4519, some c10394, some c10253, some c2646, some c2683, some c4243, some c3956, some c2551, some c3825, some c9989, some c4514, some c4042, some c3392, some c3042, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11020 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11020 : lratChecker f11020 p11020 = .success := by decide +kernel
theorem unsat11020 : Unsatisfiable (PosFin 65) f11020 := by
  apply lratCheckerSound f11020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11020
  · intro a ha; simp [p11020] at ha; subst a; trivial
  · exact checked11020
theorem derived11020 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11020 := by
  apply localUnsat_implies_entails f11020 [c11018, c4524, c4519, c10394, c10253, c2646, c2683, c4243, c3956, c2551, c3825, c9989, c4514, c4042, c3392, c3042] c11020 unsat11020 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c4524 := h 4523 (by decide)
  have h2 : Entails.eval a c4519 := h 4518 (by decide)
  have h3 : Entails.eval a c10394 := derived10394 a h
  have h4 : Entails.eval a c10253 := derived10253 a h
  have h5 : Entails.eval a c2646 := h 2645 (by decide)
  have h6 : Entails.eval a c2683 := h 2682 (by decide)
  have h7 : Entails.eval a c4243 := h 4242 (by decide)
  have h8 : Entails.eval a c3956 := h 3955 (by decide)
  have h9 : Entails.eval a c2551 := h 2550 (by decide)
  have h10 : Entails.eval a c3825 := h 3824 (by decide)
  have h11 : Entails.eval a c9989 := derived9989 a h
  have h12 : Entails.eval a c4514 := h 4513 (by decide)
  have h13 : Entails.eval a c4042 := h 4041 (by decide)
  have h14 : Entails.eval a c3392 := h 3391 (by decide)
  have h15 : Entails.eval a c3042 := h 3041 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11021 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨64, by decide⟩, true), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11021 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10388, some c10642, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11021 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11021 : lratChecker f11021 p11021 = .success := by decide +kernel
theorem unsat11021 : Unsatisfiable (PosFin 65) f11021 := by
  apply lratCheckerSound f11021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11021
  · intro a ha; simp [p11021] at ha; subst a; trivial
  · exact checked11021
theorem derived11021 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11021 := by
  apply localUnsat_implies_entails f11021 [c11018, c10388, c10642] c11021 unsat11021 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10388 := derived10388 a h
  have h2 : Entails.eval a c10642 := derived10642 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11022 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨64, by decide⟩, true), (⟨53, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11022 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11020, some c10320, some c10645, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p11022 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11022 : lratChecker f11022 p11022 = .success := by decide +kernel
theorem unsat11022 : Unsatisfiable (PosFin 65) f11022 := by
  apply lratCheckerSound f11022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11022
  · intro a ha; simp [p11022] at ha; subst a; trivial
  · exact checked11022
theorem derived11022 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11022 := by
  apply localUnsat_implies_entails f11022 [c11018, c11020, c10320, c10645] c11022 unsat11022 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11020 := derived11020 a h
  have h2 : Entails.eval a c10320 := derived10320 a h
  have h3 : Entails.eval a c10645 := derived10645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11023 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨56, by decide⟩, false), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11023 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11019, some c11021, some c11022, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11023 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11023 : lratChecker f11023 p11023 = .success := by decide +kernel
theorem unsat11023 : Unsatisfiable (PosFin 65) f11023 := by
  apply lratCheckerSound f11023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11023
  · intro a ha; simp [p11023] at ha; subst a; trivial
  · exact checked11023
theorem derived11023 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11023 := by
  apply localUnsat_implies_entails f11023 [c11019, c11021, c11022] c11023 unsat11023 (by rfl) a
  have h0 : Entails.eval a c11019 := derived11019 a h
  have h1 : Entails.eval a c11021 := derived11021 a h
  have h2 : Entails.eval a c11022 := derived11022 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11024 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11024 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11023, some c10715, some c10288, some c10914, some c10388, some c10394, some c10253, some c10320, some c2646, some c2683, some c2708, some c2915, some c2551, some c3825, some c9989, some c2911, some c2916, some c3392, some c3042, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11024 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked11024 : lratChecker f11024 p11024 = .success := by decide +kernel
theorem unsat11024 : Unsatisfiable (PosFin 65) f11024 := by
  apply lratCheckerSound f11024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11024
  · intro a ha; simp [p11024] at ha; subst a; trivial
  · exact checked11024
theorem derived11024 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11024 := by
  apply localUnsat_implies_entails f11024 [c11018, c11023, c10715, c10288, c10914, c10388, c10394, c10253, c10320, c2646, c2683, c2708, c2915, c2551, c3825, c9989, c2911, c2916, c3392, c3042] c11024 unsat11024 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11023 := derived11023 a h
  have h2 : Entails.eval a c10715 := derived10715 a h
  have h3 : Entails.eval a c10288 := derived10288 a h
  have h4 : Entails.eval a c10914 := derived10914 a h
  have h5 : Entails.eval a c10388 := derived10388 a h
  have h6 : Entails.eval a c10394 := derived10394 a h
  have h7 : Entails.eval a c10253 := derived10253 a h
  have h8 : Entails.eval a c10320 := derived10320 a h
  have h9 : Entails.eval a c2646 := h 2645 (by decide)
  have h10 : Entails.eval a c2683 := h 2682 (by decide)
  have h11 : Entails.eval a c2708 := h 2707 (by decide)
  have h12 : Entails.eval a c2915 := h 2914 (by decide)
  have h13 : Entails.eval a c2551 := h 2550 (by decide)
  have h14 : Entails.eval a c3825 := h 3824 (by decide)
  have h15 : Entails.eval a c9989 := derived9989 a h
  have h16 : Entails.eval a c2911 := h 2910 (by decide)
  have h17 : Entails.eval a c2916 := h 2915 (by decide)
  have h18 : Entails.eval a c3392 := h 3391 (by decide)
  have h19 : Entails.eval a c3042 := h 3041 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11025 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11025 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10756, some c10317, some c10390, some c10342, some c4344, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11025 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11025 : lratChecker f11025 p11025 = .success := by decide +kernel
theorem unsat11025 : Unsatisfiable (PosFin 65) f11025 := by
  apply lratCheckerSound f11025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11025
  · intro a ha; simp [p11025] at ha; subst a; trivial
  · exact checked11025
theorem derived11025 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11025 := by
  apply localUnsat_implies_entails f11025 [c11018, c10756, c10317, c10390, c10342, c4344] c11025 unsat11025 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10756 := derived10756 a h
  have h2 : Entails.eval a c10317 := derived10317 a h
  have h3 : Entails.eval a c10390 := derived10390 a h
  have h4 : Entails.eval a c10342 := derived10342 a h
  have h5 : Entails.eval a c4344 := h 4343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11026 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨15, by decide⟩, false), (⟨64, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11026 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c4519, some c4347, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11026 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11026 : lratChecker f11026 p11026 = .success := by decide +kernel
theorem unsat11026 : Unsatisfiable (PosFin 65) f11026 := by
  apply lratCheckerSound f11026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11026
  · intro a ha; simp [p11026] at ha; subst a; trivial
  · exact checked11026
theorem derived11026 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11026 := by
  apply localUnsat_implies_entails f11026 [c11018, c4519, c4347] c11026 unsat11026 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c4519 := h 4518 (by decide)
  have h2 : Entails.eval a c4347 := h 4346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11027 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11027 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11024, some c11025, some c11019, some c11021, some c11026, some c10320, some c10645, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p11027 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11027 : lratChecker f11027 p11027 = .success := by decide +kernel
theorem unsat11027 : Unsatisfiable (PosFin 65) f11027 := by
  apply lratCheckerSound f11027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11027
  · intro a ha; simp [p11027] at ha; subst a; trivial
  · exact checked11027
theorem derived11027 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11027 := by
  apply localUnsat_implies_entails f11027 [c11018, c11024, c11025, c11019, c11021, c11026, c10320, c10645] c11027 unsat11027 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11024 := derived11024 a h
  have h2 : Entails.eval a c11025 := derived11025 a h
  have h3 : Entails.eval a c11019 := derived11019 a h
  have h4 : Entails.eval a c11021 := derived11021 a h
  have h5 : Entails.eval a c11026 := derived11026 a h
  have h6 : Entails.eval a c10320 := derived10320 a h
  have h7 : Entails.eval a c10645 := derived10645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11028 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11028 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10366, some c10645, some c10342, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p11028 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11028 : lratChecker f11028 p11028 = .success := by decide +kernel
theorem unsat11028 : Unsatisfiable (PosFin 65) f11028 := by
  apply lratCheckerSound f11028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11028
  · intro a ha; simp [p11028] at ha; subst a; trivial
  · exact checked11028
theorem derived11028 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11028 := by
  apply localUnsat_implies_entails f11028 [c11018, c10366, c10645, c10342] c11028 unsat11028 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10366 := derived10366 a h
  have h2 : Entails.eval a c10645 := derived10645 a h
  have h3 : Entails.eval a c10342 := derived10342 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11029 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨56, by decide⟩, true), (⟨6, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11029 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4524, some c4519, some c4521, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11029 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11029 : lratChecker f11029 p11029 = .success := by decide +kernel
theorem unsat11029 : Unsatisfiable (PosFin 65) f11029 := by
  apply lratCheckerSound f11029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11029
  · intro a ha; simp [p11029] at ha; subst a; trivial
  · exact checked11029
theorem derived11029 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11029 := by
  apply localUnsat_implies_entails f11029 [c4524, c4519, c4521] c11029 unsat11029 (by rfl) a
  have h0 : Entails.eval a c4524 := h 4523 (by decide)
  have h1 : Entails.eval a c4519 := h 4518 (by decide)
  have h2 : Entails.eval a c4521 := h 4520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11030 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11030 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10757, some c10642, some c10390, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11030 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11030 : lratChecker f11030 p11030 = .success := by decide +kernel
theorem unsat11030 : Unsatisfiable (PosFin 65) f11030 := by
  apply lratCheckerSound f11030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11030
  · intro a ha; simp [p11030] at ha; subst a; trivial
  · exact checked11030
theorem derived11030 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11030 := by
  apply localUnsat_implies_entails f11030 [c11018, c10757, c10642, c10390] c11030 unsat11030 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10757 := derived10757 a h
  have h2 : Entails.eval a c10642 := derived10642 a h
  have h3 : Entails.eval a c10390 := derived10390 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11031 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11031 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11028, some c11027, some c11030, some c11029, some c10756, some c10317, some c10758, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11031 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11031 : lratChecker f11031 p11031 = .success := by decide +kernel
theorem unsat11031 : Unsatisfiable (PosFin 65) f11031 := by
  apply lratCheckerSound f11031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11031
  · intro a ha; simp [p11031] at ha; subst a; trivial
  · exact checked11031
theorem derived11031 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11031 := by
  apply localUnsat_implies_entails f11031 [c11028, c11027, c11030, c11029, c10756, c10317, c10758] c11031 unsat11031 (by rfl) a
  have h0 : Entails.eval a c11028 := derived11028 a h
  have h1 : Entails.eval a c11027 := derived11027 a h
  have h2 : Entails.eval a c11030 := derived11030 a h
  have h3 : Entails.eval a c11029 := derived11029 a h
  have h4 : Entails.eval a c10756 := derived10756 a h
  have h5 : Entails.eval a c10317 := derived10317 a h
  have h6 : Entails.eval a c10758 := derived10758 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11032 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11032 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10390, some c2644, some c4344, some c2549, some c9991, some c2883, some c8300, some c3813, some c10291, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p11032 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11032 : lratChecker f11032 p11032 = .success := by decide +kernel
theorem unsat11032 : Unsatisfiable (PosFin 65) f11032 := by
  apply lratCheckerSound f11032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11032
  · intro a ha; simp [p11032] at ha; subst a; trivial
  · exact checked11032
theorem derived11032 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11032 := by
  apply localUnsat_implies_entails f11032 [c11018, c10390, c2644, c4344, c2549, c9991, c2883, c8300, c3813, c10291] c11032 unsat11032 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10390 := derived10390 a h
  have h2 : Entails.eval a c2644 := h 2643 (by decide)
  have h3 : Entails.eval a c4344 := h 4343 (by decide)
  have h4 : Entails.eval a c2549 := h 2548 (by decide)
  have h5 : Entails.eval a c9991 := derived9991 a h
  have h6 : Entails.eval a c2883 := h 2882 (by decide)
  have h7 : Entails.eval a c8300 := derived8300 a h
  have h8 : Entails.eval a c3813 := h 3812 (by decide)
  have h9 : Entails.eval a c10291 := derived10291 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11033 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨14, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11033 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11028, some c10714, some c10307, some c4524, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11033 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11033 : lratChecker f11033 p11033 = .success := by decide +kernel
theorem unsat11033 : Unsatisfiable (PosFin 65) f11033 := by
  apply lratCheckerSound f11033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11033
  · intro a ha; simp [p11033] at ha; subst a; trivial
  · exact checked11033
theorem derived11033 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11033 := by
  apply localUnsat_implies_entails f11033 [c11028, c10714, c10307, c4524] c11033 unsat11033 (by rfl) a
  have h0 : Entails.eval a c11028 := derived11028 a h
  have h1 : Entails.eval a c10714 := derived10714 a h
  have h2 : Entails.eval a c10307 := derived10307 a h
  have h3 : Entails.eval a c4524 := h 4523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11034 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11034 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11028, some c11031, some c11033, some c11032, some c10317, some c10642, some c4341, some c11023, some c11029, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11034 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11034 : lratChecker f11034 p11034 = .success := by decide +kernel
theorem unsat11034 : Unsatisfiable (PosFin 65) f11034 := by
  apply lratCheckerSound f11034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11034
  · intro a ha; simp [p11034] at ha; subst a; trivial
  · exact checked11034
theorem derived11034 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11034 := by
  apply localUnsat_implies_entails f11034 [c11028, c11031, c11033, c11032, c10317, c10642, c4341, c11023, c11029] c11034 unsat11034 (by rfl) a
  have h0 : Entails.eval a c11028 := derived11028 a h
  have h1 : Entails.eval a c11031 := derived11031 a h
  have h2 : Entails.eval a c11033 := derived11033 a h
  have h3 : Entails.eval a c11032 := derived11032 a h
  have h4 : Entails.eval a c10317 := derived10317 a h
  have h5 : Entails.eval a c10642 := derived10642 a h
  have h6 : Entails.eval a c4341 := h 4340 (by decide)
  have h7 : Entails.eval a c11023 := derived11023 a h
  have h8 : Entails.eval a c11029 := derived11029 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11035 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨64, by decide⟩, false), (⟨9, by decide⟩, false), (⟨56, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11035 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4158, some c8269, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p11035 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11035 : lratChecker f11035 p11035 = .success := by decide +kernel
theorem unsat11035 : Unsatisfiable (PosFin 65) f11035 := by
  apply lratCheckerSound f11035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11035
  · intro a ha; simp [p11035] at ha; subst a; trivial
  · exact checked11035
theorem derived11035 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11035 := by
  apply localUnsat_implies_entails f11035 [c4158, c8269] c11035 unsat11035 (by rfl) a
  have h0 : Entails.eval a c4158 := h 4157 (by decide)
  have h1 : Entails.eval a c8269 := derived8269 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11036 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11036 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10943, some c10172, some c11035, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p11036 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11036 : lratChecker f11036 p11036 = .success := by decide +kernel
theorem unsat11036 : Unsatisfiable (PosFin 65) f11036 := by
  apply lratCheckerSound f11036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11036
  · intro a ha; simp [p11036] at ha; subst a; trivial
  · exact checked11036
theorem derived11036 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11036 := by
  apply localUnsat_implies_entails f11036 [c10943, c10172, c11035] c11036 unsat11036 (by rfl) a
  have h0 : Entails.eval a c10943 := derived10943 a h
  have h1 : Entails.eval a c10172 := derived10172 a h
  have h2 : Entails.eval a c11035 := derived11035 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11037 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨16, by decide⟩, true), (⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨14, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11037 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11036, some c10223, some c4252, some c3503, some c4225, some c10220, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p11037 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11037 : lratChecker f11037 p11037 = .success := by decide +kernel
theorem unsat11037 : Unsatisfiable (PosFin 65) f11037 := by
  apply lratCheckerSound f11037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11037
  · intro a ha; simp [p11037] at ha; subst a; trivial
  · exact checked11037
theorem derived11037 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11037 := by
  apply localUnsat_implies_entails f11037 [c11036, c10223, c4252, c3503, c4225, c10220] c11037 unsat11037 (by rfl) a
  have h0 : Entails.eval a c11036 := derived11036 a h
  have h1 : Entails.eval a c10223 := derived10223 a h
  have h2 : Entails.eval a c4252 := h 4251 (by decide)
  have h3 : Entails.eval a c3503 := h 3502 (by decide)
  have h4 : Entails.eval a c4225 := h 4224 (by decide)
  have h5 : Entails.eval a c10220 := derived10220 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11038 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨2, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨51, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11038 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c4252, some c10534, some c2529, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p11038 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11038 : lratChecker f11038 p11038 = .success := by decide +kernel
theorem unsat11038 : Unsatisfiable (PosFin 65) f11038 := by
  apply lratCheckerSound f11038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11038
  · intro a ha; simp [p11038] at ha; subst a; trivial
  · exact checked11038
theorem derived11038 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11038 := by
  apply localUnsat_implies_entails f11038 [c11018, c4252, c10534, c2529] c11038 unsat11038 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c4252 := h 4251 (by decide)
  have h2 : Entails.eval a c10534 := derived10534 a h
  have h3 : Entails.eval a c2529 := h 2528 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11039 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, false), (⟨6, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11039 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11034, some c4519, some c4415, some c10710, some c4955, some c3648, some c5005, some c3731, some c2621, some c10154, some c11037, some c10155, some c11038, some c3941, some c4038, some c3946, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11039 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11039 : lratChecker f11039 p11039 = .success := by decide +kernel
theorem unsat11039 : Unsatisfiable (PosFin 65) f11039 := by
  apply lratCheckerSound f11039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11039
  · intro a ha; simp [p11039] at ha; subst a; trivial
  · exact checked11039
theorem derived11039 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11039 := by
  apply localUnsat_implies_entails f11039 [c11018, c11034, c4519, c4415, c10710, c4955, c3648, c5005, c3731, c2621, c10154, c11037, c10155, c11038, c3941, c4038, c3946] c11039 unsat11039 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11034 := derived11034 a h
  have h2 : Entails.eval a c4519 := h 4518 (by decide)
  have h3 : Entails.eval a c4415 := h 4414 (by decide)
  have h4 : Entails.eval a c10710 := derived10710 a h
  have h5 : Entails.eval a c4955 := h 4954 (by decide)
  have h6 : Entails.eval a c3648 := h 3647 (by decide)
  have h7 : Entails.eval a c5005 := h 5004 (by decide)
  have h8 : Entails.eval a c3731 := h 3730 (by decide)
  have h9 : Entails.eval a c2621 := h 2620 (by decide)
  have h10 : Entails.eval a c10154 := derived10154 a h
  have h11 : Entails.eval a c11037 := derived11037 a h
  have h12 : Entails.eval a c10155 := derived10155 a h
  have h13 : Entails.eval a c11038 := derived11038 a h
  have h14 : Entails.eval a c3941 := h 3940 (by decide)
  have h15 : Entails.eval a c4038 := h 4037 (by decide)
  have h16 : Entails.eval a c3946 := h 3945 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11040 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11040 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11034, some c10288, some c10620, some c4775, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11040 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11040 : lratChecker f11040 p11040 = .success := by decide +kernel
theorem unsat11040 : Unsatisfiable (PosFin 65) f11040 := by
  apply lratCheckerSound f11040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11040
  · intro a ha; simp [p11040] at ha; subst a; trivial
  · exact checked11040
theorem derived11040 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11040 := by
  apply localUnsat_implies_entails f11040 [c11034, c10288, c10620, c4775] c11040 unsat11040 (by rfl) a
  have h0 : Entails.eval a c11034 := derived11034 a h
  have h1 : Entails.eval a c10288 := derived10288 a h
  have h2 : Entails.eval a c10620 := derived10620 a h
  have h3 : Entails.eval a c4775 := h 4774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11041 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨13, by decide⟩, false), (⟨51, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11041 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c3941, some c3086, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p11041 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11041 : lratChecker f11041 p11041 = .success := by decide +kernel
theorem unsat11041 : Unsatisfiable (PosFin 65) f11041 := by
  apply lratCheckerSound f11041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11041
  · intro a ha; simp [p11041] at ha; subst a; trivial
  · exact checked11041
theorem derived11041 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11041 := by
  apply localUnsat_implies_entails f11041 [c11018, c3941, c3086] c11041 unsat11041 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c3941 := h 3940 (by decide)
  have h2 : Entails.eval a c3086 := h 3085 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11042 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨6, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11042 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11034, some c11040, some c4519, some c4415, some c11039, some c10710, some c3656, some c4972, some c5012, some c3388, some c3731, some c3164, some c2621, some c10329, some c11041, some c4218, some c4183, some c11038, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11042 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked11042 : lratChecker f11042 p11042 = .success := by decide +kernel
theorem unsat11042 : Unsatisfiable (PosFin 65) f11042 := by
  apply lratCheckerSound f11042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11042
  · intro a ha; simp [p11042] at ha; subst a; trivial
  · exact checked11042
theorem derived11042 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11042 := by
  apply localUnsat_implies_entails f11042 [c11018, c11034, c11040, c4519, c4415, c11039, c10710, c3656, c4972, c5012, c3388, c3731, c3164, c2621, c10329, c11041, c4218, c4183, c11038] c11042 unsat11042 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11034 := derived11034 a h
  have h2 : Entails.eval a c11040 := derived11040 a h
  have h3 : Entails.eval a c4519 := h 4518 (by decide)
  have h4 : Entails.eval a c4415 := h 4414 (by decide)
  have h5 : Entails.eval a c11039 := derived11039 a h
  have h6 : Entails.eval a c10710 := derived10710 a h
  have h7 : Entails.eval a c3656 := h 3655 (by decide)
  have h8 : Entails.eval a c4972 := h 4971 (by decide)
  have h9 : Entails.eval a c5012 := h 5011 (by decide)
  have h10 : Entails.eval a c3388 := h 3387 (by decide)
  have h11 : Entails.eval a c3731 := h 3730 (by decide)
  have h12 : Entails.eval a c3164 := h 3163 (by decide)
  have h13 : Entails.eval a c2621 := h 2620 (by decide)
  have h14 : Entails.eval a c10329 := derived10329 a h
  have h15 : Entails.eval a c11041 := derived11041 a h
  have h16 : Entails.eval a c4218 := h 4217 (by decide)
  have h17 : Entails.eval a c4183 := h 4182 (by decide)
  have h18 : Entails.eval a c11038 := derived11038 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11043 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11043 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11042, some c11034, some c4524, some c4421, some c4938, some c5012, some c3388, some c3164, some c10329, some c10221, some c4091, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11043 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11043 : lratChecker f11043 p11043 = .success := by decide +kernel
theorem unsat11043 : Unsatisfiable (PosFin 65) f11043 := by
  apply lratCheckerSound f11043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11043
  · intro a ha; simp [p11043] at ha; subst a; trivial
  · exact checked11043
theorem derived11043 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11043 := by
  apply localUnsat_implies_entails f11043 [c11018, c11042, c11034, c4524, c4421, c4938, c5012, c3388, c3164, c10329, c10221, c4091] c11043 unsat11043 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11042 := derived11042 a h
  have h2 : Entails.eval a c11034 := derived11034 a h
  have h3 : Entails.eval a c4524 := h 4523 (by decide)
  have h4 : Entails.eval a c4421 := h 4420 (by decide)
  have h5 : Entails.eval a c4938 := h 4937 (by decide)
  have h6 : Entails.eval a c5012 := h 5011 (by decide)
  have h7 : Entails.eval a c3388 := h 3387 (by decide)
  have h8 : Entails.eval a c3164 := h 3163 (by decide)
  have h9 : Entails.eval a c10329 := derived10329 a h
  have h10 : Entails.eval a c10221 := derived10221 a h
  have h11 : Entails.eval a c4091 := h 4090 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11044 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11044 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11043, some c11042, some c11034, some c3953, some c4087, some c8300, some c10394, some c10391, some c11026, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11044 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11044 : lratChecker f11044 p11044 = .success := by decide +kernel
theorem unsat11044 : Unsatisfiable (PosFin 65) f11044 := by
  apply lratCheckerSound f11044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11044
  · intro a ha; simp [p11044] at ha; subst a; trivial
  · exact checked11044
theorem derived11044 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11044 := by
  apply localUnsat_implies_entails f11044 [c11018, c11043, c11042, c11034, c3953, c4087, c8300, c10394, c10391, c11026] c11044 unsat11044 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11043 := derived11043 a h
  have h2 : Entails.eval a c11042 := derived11042 a h
  have h3 : Entails.eval a c11034 := derived11034 a h
  have h4 : Entails.eval a c3953 := h 3952 (by decide)
  have h5 : Entails.eval a c4087 := h 4086 (by decide)
  have h6 : Entails.eval a c8300 := derived8300 a h
  have h7 : Entails.eval a c10394 := derived10394 a h
  have h8 : Entails.eval a c10391 := derived10391 a h
  have h9 : Entails.eval a c11026 := derived11026 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11045 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11045 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11042, some c11043, some c11044, some c10253, some c10272, some c4344, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11045 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11045 : lratChecker f11045 p11045 = .success := by decide +kernel
theorem unsat11045 : Unsatisfiable (PosFin 65) f11045 := by
  apply lratCheckerSound f11045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11045
  · intro a ha; simp [p11045] at ha; subst a; trivial
  · exact checked11045
theorem derived11045 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11045 := by
  apply localUnsat_implies_entails f11045 [c11018, c11042, c11043, c11044, c10253, c10272, c4344] c11045 unsat11045 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11042 := derived11042 a h
  have h2 : Entails.eval a c11043 := derived11043 a h
  have h3 : Entails.eval a c11044 := derived11044 a h
  have h4 : Entails.eval a c10253 := derived10253 a h
  have h5 : Entails.eval a c10272 := derived10272 a h
  have h6 : Entails.eval a c4344 := h 4343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11046 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11046 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10391, some c10272, some c4087, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p11046 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11046 : lratChecker f11046 p11046 = .success := by decide +kernel
theorem unsat11046 : Unsatisfiable (PosFin 65) f11046 := by
  apply lratCheckerSound f11046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11046
  · intro a ha; simp [p11046] at ha; subst a; trivial
  · exact checked11046
theorem derived11046 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11046 := by
  apply localUnsat_implies_entails f11046 [c11018, c10391, c10272, c4087] c11046 unsat11046 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10391 := derived10391 a h
  have h2 : Entails.eval a c10272 := derived10272 a h
  have h3 : Entails.eval a c4087 := h 4086 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11047 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11047 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11046, some c4344, some c10394, some c10253, some c4087, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p11047 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11047 : lratChecker f11047 p11047 = .success := by decide +kernel
theorem unsat11047 : Unsatisfiable (PosFin 65) f11047 := by
  apply lratCheckerSound f11047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11047
  · intro a ha; simp [p11047] at ha; subst a; trivial
  · exact checked11047
theorem derived11047 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11047 := by
  apply localUnsat_implies_entails f11047 [c11018, c11046, c4344, c10394, c10253, c4087] c11047 unsat11047 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11046 := derived11046 a h
  have h2 : Entails.eval a c4344 := h 4343 (by decide)
  have h3 : Entails.eval a c10394 := derived10394 a h
  have h4 : Entails.eval a c10253 := derived10253 a h
  have h5 : Entails.eval a c4087 := h 4086 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11048 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11048 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11034, some c11042, some c11045, some c11047, some c10302, some c10609, some c4783, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11048 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11048 : lratChecker f11048 p11048 = .success := by decide +kernel
theorem unsat11048 : Unsatisfiable (PosFin 65) f11048 := by
  apply lratCheckerSound f11048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11048
  · intro a ha; simp [p11048] at ha; subst a; trivial
  · exact checked11048
theorem derived11048 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11048 := by
  apply localUnsat_implies_entails f11048 [c11034, c11042, c11045, c11047, c10302, c10609, c4783] c11048 unsat11048 (by rfl) a
  have h0 : Entails.eval a c11034 := derived11034 a h
  have h1 : Entails.eval a c11042 := derived11042 a h
  have h2 : Entails.eval a c11045 := derived11045 a h
  have h3 : Entails.eval a c11047 := derived11047 a h
  have h4 : Entails.eval a c10302 := derived10302 a h
  have h5 : Entails.eval a c10609 := derived10609 a h
  have h6 : Entails.eval a c4783 := h 4782 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11049 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11049 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11048, some c11034, some c10338, some c10575, some c5012, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p11049 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11049 : lratChecker f11049 p11049 = .success := by decide +kernel
theorem unsat11049 : Unsatisfiable (PosFin 65) f11049 := by
  apply lratCheckerSound f11049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11049
  · intro a ha; simp [p11049] at ha; subst a; trivial
  · exact checked11049
theorem derived11049 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11049 := by
  apply localUnsat_implies_entails f11049 [c11048, c11034, c10338, c10575, c5012] c11049 unsat11049 (by rfl) a
  have h0 : Entails.eval a c11048 := derived11048 a h
  have h1 : Entails.eval a c11034 := derived11034 a h
  have h2 : Entails.eval a c10338 := derived10338 a h
  have h3 : Entails.eval a c10575 := derived10575 a h
  have h4 : Entails.eval a c5012 := h 5011 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11050 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨57, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11050 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10393, some c10568, some c5006, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p11050 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11050 : lratChecker f11050 p11050 = .success := by decide +kernel
theorem unsat11050 : Unsatisfiable (PosFin 65) f11050 := by
  apply lratCheckerSound f11050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11050
  · intro a ha; simp [p11050] at ha; subst a; trivial
  · exact checked11050
theorem derived11050 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11050 := by
  apply localUnsat_implies_entails f11050 [c11018, c10393, c10568, c5006] c11050 unsat11050 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10393 := derived10393 a h
  have h2 : Entails.eval a c10568 := derived10568 a h
  have h3 : Entails.eval a c5006 := h 5005 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived11050

end CochromaticTwenty.Certificates.FixedCore0
