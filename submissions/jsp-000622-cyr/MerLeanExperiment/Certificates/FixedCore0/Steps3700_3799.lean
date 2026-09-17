import MerLeanExperiment.Certificates.FixedCore0.Steps3600_3699

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c11251 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11251 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11249, some c11244, some c11221, some c11250, some c10615, some c10617, some c11175, some c10417, some c10407, some c10610, some c10630, some c10494, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11251 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11251 : lratChecker f11251 p11251 = .success := by decide +kernel
theorem unsat11251 : Unsatisfiable (PosFin 65) f11251 := by
  apply lratCheckerSound f11251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11251
  · intro a ha; simp [p11251] at ha; subst a; trivial
  · exact checked11251
theorem derived11251 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11251 := by
  apply localUnsat_implies_entails f11251 [c11249, c11244, c11221, c11250, c10615, c10617, c11175, c10417, c10407, c10610, c10630, c10494] c11251 unsat11251 (by rfl) a
  have h0 : Entails.eval a c11249 := derived11249 a h
  have h1 : Entails.eval a c11244 := derived11244 a h
  have h2 : Entails.eval a c11221 := derived11221 a h
  have h3 : Entails.eval a c11250 := derived11250 a h
  have h4 : Entails.eval a c10615 := derived10615 a h
  have h5 : Entails.eval a c10617 := derived10617 a h
  have h6 : Entails.eval a c11175 := derived11175 a h
  have h7 : Entails.eval a c10417 := derived10417 a h
  have h8 : Entails.eval a c10407 := derived10407 a h
  have h9 : Entails.eval a c10610 := derived10610 a h
  have h10 : Entails.eval a c10630 := derived10630 a h
  have h11 : Entails.eval a c10494 := derived10494 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11252 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11252 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10411, some c10612, some c10447, some c10630, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11252 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11252 : lratChecker f11252 p11252 = .success := by decide +kernel
theorem unsat11252 : Unsatisfiable (PosFin 65) f11252 := by
  apply lratCheckerSound f11252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11252
  · intro a ha; simp [p11252] at ha; subst a; trivial
  · exact checked11252
theorem derived11252 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11252 := by
  apply localUnsat_implies_entails f11252 [c10411, c10612, c10447, c10630] c11252 unsat11252 (by rfl) a
  have h0 : Entails.eval a c10411 := derived10411 a h
  have h1 : Entails.eval a c10612 := derived10612 a h
  have h2 : Entails.eval a c10447 := derived10447 a h
  have h3 : Entails.eval a c10630 := derived10630 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11253 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11253 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11244, some c11251, some c11252, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11253 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11253 : lratChecker f11253 p11253 = .success := by decide +kernel
theorem unsat11253 : Unsatisfiable (PosFin 65) f11253 := by
  apply lratCheckerSound f11253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11253
  · intro a ha; simp [p11253] at ha; subst a; trivial
  · exact checked11253
theorem derived11253 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11253 := by
  apply localUnsat_implies_entails f11253 [c11244, c11251, c11252] c11253 unsat11253 (by rfl) a
  have h0 : Entails.eval a c11244 := derived11244 a h
  have h1 : Entails.eval a c11251 := derived11251 a h
  have h2 : Entails.eval a c11252 := derived11252 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11254 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11254 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11253, some c11249, some c11244, some c11221, some c11215, some c11223, some c3904, some c3898, some c11222, some c4402, some c4501, some c4927, some c10741, some c4056, some c4063, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11254 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11254 : lratChecker f11254 p11254 = .success := by decide +kernel
theorem unsat11254 : Unsatisfiable (PosFin 65) f11254 := by
  apply lratCheckerSound f11254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11254
  · intro a ha; simp [p11254] at ha; subst a; trivial
  · exact checked11254
theorem derived11254 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11254 := by
  apply localUnsat_implies_entails f11254 [c11170, c11253, c11249, c11244, c11221, c11215, c11223, c3904, c3898, c11222, c4402, c4501, c4927, c10741, c4056, c4063] c11254 unsat11254 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11253 := derived11253 a h
  have h2 : Entails.eval a c11249 := derived11249 a h
  have h3 : Entails.eval a c11244 := derived11244 a h
  have h4 : Entails.eval a c11221 := derived11221 a h
  have h5 : Entails.eval a c11215 := derived11215 a h
  have h6 : Entails.eval a c11223 := derived11223 a h
  have h7 : Entails.eval a c3904 := h 3903 (by decide)
  have h8 : Entails.eval a c3898 := h 3897 (by decide)
  have h9 : Entails.eval a c11222 := derived11222 a h
  have h10 : Entails.eval a c4402 := h 4401 (by decide)
  have h11 : Entails.eval a c4501 := h 4500 (by decide)
  have h12 : Entails.eval a c4927 := h 4926 (by decide)
  have h13 : Entails.eval a c10741 := derived10741 a h
  have h14 : Entails.eval a c4056 := h 4055 (by decide)
  have h15 : Entails.eval a c4063 := h 4062 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11255 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11255 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11253, some c11221, some c11254, some c11195, some c11249, some c11244, some c11215, some c3922, some c3899, some c4404, some c4510, some c4925, some c10776, some c4061, some c4063, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11255 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11255 : lratChecker f11255 p11255 = .success := by decide +kernel
theorem unsat11255 : Unsatisfiable (PosFin 65) f11255 := by
  apply lratCheckerSound f11255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11255
  · intro a ha; simp [p11255] at ha; subst a; trivial
  · exact checked11255
theorem derived11255 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11255 := by
  apply localUnsat_implies_entails f11255 [c11170, c11253, c11221, c11254, c11195, c11249, c11244, c11215, c3922, c3899, c4404, c4510, c4925, c10776, c4061, c4063] c11255 unsat11255 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11253 := derived11253 a h
  have h2 : Entails.eval a c11221 := derived11221 a h
  have h3 : Entails.eval a c11254 := derived11254 a h
  have h4 : Entails.eval a c11195 := derived11195 a h
  have h5 : Entails.eval a c11249 := derived11249 a h
  have h6 : Entails.eval a c11244 := derived11244 a h
  have h7 : Entails.eval a c11215 := derived11215 a h
  have h8 : Entails.eval a c3922 := h 3921 (by decide)
  have h9 : Entails.eval a c3899 := h 3898 (by decide)
  have h10 : Entails.eval a c4404 := h 4403 (by decide)
  have h11 : Entails.eval a c4510 := h 4509 (by decide)
  have h12 : Entails.eval a c4925 := h 4924 (by decide)
  have h13 : Entails.eval a c10776 := derived10776 a h
  have h14 : Entails.eval a c4061 := h 4060 (by decide)
  have h15 : Entails.eval a c4063 := h 4062 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11256 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11256 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11221, some c11244, some c11249, some c11253, some c11254, some c11195, some c11255, some c3921, some c4505, some c4408, some c4929, some c3909, some c4001, some c4006, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p11256 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked11256 : lratChecker f11256 p11256 = .success := by decide +kernel
theorem unsat11256 : Unsatisfiable (PosFin 65) f11256 := by
  apply lratCheckerSound f11256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11256
  · intro a ha; simp [p11256] at ha; subst a; trivial
  · exact checked11256
theorem derived11256 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11256 := by
  apply localUnsat_implies_entails f11256 [c11170, c11221, c11244, c11249, c11253, c11254, c11195, c11255, c3921, c4505, c4408, c4929, c3909, c4001, c4006] c11256 unsat11256 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11221 := derived11221 a h
  have h2 : Entails.eval a c11244 := derived11244 a h
  have h3 : Entails.eval a c11249 := derived11249 a h
  have h4 : Entails.eval a c11253 := derived11253 a h
  have h5 : Entails.eval a c11254 := derived11254 a h
  have h6 : Entails.eval a c11195 := derived11195 a h
  have h7 : Entails.eval a c11255 := derived11255 a h
  have h8 : Entails.eval a c3921 := h 3920 (by decide)
  have h9 : Entails.eval a c4505 := h 4504 (by decide)
  have h10 : Entails.eval a c4408 := h 4407 (by decide)
  have h11 : Entails.eval a c4929 := h 4928 (by decide)
  have h12 : Entails.eval a c3909 := h 3908 (by decide)
  have h13 : Entails.eval a c4001 := h 4000 (by decide)
  have h14 : Entails.eval a c4006 := h 4005 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11257 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11257 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3904, some c11200, some c3912, some c11195, some c3909, some c3902, some c4505, some c4408, some c3916, some c10452, some c4925, some c4066, some c4059, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11257 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11257 : lratChecker f11257 p11257 = .success := by decide +kernel
theorem unsat11257 : Unsatisfiable (PosFin 65) f11257 := by
  apply lratCheckerSound f11257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11257
  · intro a ha; simp [p11257] at ha; subst a; trivial
  · exact checked11257
theorem derived11257 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11257 := by
  apply localUnsat_implies_entails f11257 [c11170, c3904, c11200, c3912, c11195, c3909, c3902, c4505, c4408, c3916, c10452, c4925, c4066, c4059] c11257 unsat11257 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3904 := h 3903 (by decide)
  have h2 : Entails.eval a c11200 := derived11200 a h
  have h3 : Entails.eval a c3912 := h 3911 (by decide)
  have h4 : Entails.eval a c11195 := derived11195 a h
  have h5 : Entails.eval a c3909 := h 3908 (by decide)
  have h6 : Entails.eval a c3902 := h 3901 (by decide)
  have h7 : Entails.eval a c4505 := h 4504 (by decide)
  have h8 : Entails.eval a c4408 := h 4407 (by decide)
  have h9 : Entails.eval a c3916 := h 3915 (by decide)
  have h10 : Entails.eval a c10452 := derived10452 a h
  have h11 : Entails.eval a c4925 := h 4924 (by decide)
  have h12 : Entails.eval a c4066 := h 4065 (by decide)
  have h13 : Entails.eval a c4059 := h 4058 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11258 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11258 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c4000, some c4004, some c4005, some c4001, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p11258 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11258 : lratChecker f11258 p11258 = .success := by decide +kernel
theorem unsat11258 : Unsatisfiable (PosFin 65) f11258 := by
  apply lratCheckerSound f11258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11258
  · intro a ha; simp [p11258] at ha; subst a; trivial
  · exact checked11258
theorem derived11258 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11258 := by
  apply localUnsat_implies_entails f11258 [c11170, c4000, c4004, c4005, c4001] c11258 unsat11258 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c4000 := h 3999 (by decide)
  have h2 : Entails.eval a c4004 := h 4003 (by decide)
  have h3 : Entails.eval a c4005 := h 4004 (by decide)
  have h4 : Entails.eval a c4001 := h 4000 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11259 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11259 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11257, some c11258, some c10426, some c10446, some c10820, some c10464, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p11259 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11259 : lratChecker f11259 p11259 = .success := by decide +kernel
theorem unsat11259 : Unsatisfiable (PosFin 65) f11259 := by
  apply lratCheckerSound f11259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11259
  · intro a ha; simp [p11259] at ha; subst a; trivial
  · exact checked11259
theorem derived11259 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11259 := by
  apply localUnsat_implies_entails f11259 [c11257, c11258, c10426, c10446, c10820, c10464] c11259 unsat11259 (by rfl) a
  have h0 : Entails.eval a c11257 := derived11257 a h
  have h1 : Entails.eval a c11258 := derived11258 a h
  have h2 : Entails.eval a c10426 := derived10426 a h
  have h3 : Entails.eval a c10446 := derived10446 a h
  have h4 : Entails.eval a c10820 := derived10820 a h
  have h5 : Entails.eval a c10464 := derived10464 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11260 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11260 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11259, some c11195, some c10814, some c10464, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11260 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11260 : lratChecker f11260 p11260 = .success := by decide +kernel
theorem unsat11260 : Unsatisfiable (PosFin 65) f11260 := by
  apply lratCheckerSound f11260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11260
  · intro a ha; simp [p11260] at ha; subst a; trivial
  · exact checked11260
theorem derived11260 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11260 := by
  apply localUnsat_implies_entails f11260 [c11259, c11195, c10814, c10464] c11260 unsat11260 (by rfl) a
  have h0 : Entails.eval a c11259 := derived11259 a h
  have h1 : Entails.eval a c11195 := derived11195 a h
  have h2 : Entails.eval a c10814 := derived10814 a h
  have h3 : Entails.eval a c10464 := derived10464 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11261 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11261 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10446, some c10440, some c4505, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11261 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11261 : lratChecker f11261 p11261 = .success := by decide +kernel
theorem unsat11261 : Unsatisfiable (PosFin 65) f11261 := by
  apply lratCheckerSound f11261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11261
  · intro a ha; simp [p11261] at ha; subst a; trivial
  · exact checked11261
theorem derived11261 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11261 := by
  apply localUnsat_implies_entails f11261 [c10446, c10440, c4505] c11261 unsat11261 (by rfl) a
  have h0 : Entails.eval a c10446 := derived10446 a h
  have h1 : Entails.eval a c10440 := derived10440 a h
  have h2 : Entails.eval a c4505 := h 4504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11262 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11262 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11260, some c10515, some c10413, some c4502, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p11262 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11262 : lratChecker f11262 p11262 = .success := by decide +kernel
theorem unsat11262 : Unsatisfiable (PosFin 65) f11262 := by
  apply lratCheckerSound f11262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11262
  · intro a ha; simp [p11262] at ha; subst a; trivial
  · exact checked11262
theorem derived11262 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11262 := by
  apply localUnsat_implies_entails f11262 [c11260, c10515, c10413, c4502] c11262 unsat11262 (by rfl) a
  have h0 : Entails.eval a c11260 := derived11260 a h
  have h1 : Entails.eval a c10515 := derived10515 a h
  have h2 : Entails.eval a c10413 := derived10413 a h
  have h3 : Entails.eval a c4502 := h 4501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11263 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11263 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11261, some c11262, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p11263 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11263 : lratChecker f11263 p11263 = .success := by decide +kernel
theorem unsat11263 : Unsatisfiable (PosFin 65) f11263 := by
  apply lratCheckerSound f11263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11263
  · intro a ha; simp [p11263] at ha; subst a; trivial
  · exact checked11263
theorem derived11263 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11263 := by
  apply localUnsat_implies_entails f11263 [c11261, c11262] c11263 unsat11263 (by rfl) a
  have h0 : Entails.eval a c11261 := derived11261 a h
  have h1 : Entails.eval a c11262 := derived11262 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11264 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11264 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c4008, some c4009, some c3995, some c3999, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11264 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11264 : lratChecker f11264 p11264 = .success := by decide +kernel
theorem unsat11264 : Unsatisfiable (PosFin 65) f11264 := by
  apply lratCheckerSound f11264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11264
  · intro a ha; simp [p11264] at ha; subst a; trivial
  · exact checked11264
theorem derived11264 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11264 := by
  apply localUnsat_implies_entails f11264 [c11170, c4008, c4009, c3995, c3999] c11264 unsat11264 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c4008 := h 4007 (by decide)
  have h2 : Entails.eval a c4009 := h 4008 (by decide)
  have h3 : Entails.eval a c3995 := h 3994 (by decide)
  have h4 : Entails.eval a c3999 := h 3998 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11265 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11265 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11259, some c11263, some c11264, some c4984, some c10405, some c10452, some c4505, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11265 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11265 : lratChecker f11265 p11265 = .success := by decide +kernel
theorem unsat11265 : Unsatisfiable (PosFin 65) f11265 := by
  apply lratCheckerSound f11265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11265
  · intro a ha; simp [p11265] at ha; subst a; trivial
  · exact checked11265
theorem derived11265 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11265 := by
  apply localUnsat_implies_entails f11265 [c11256, c11259, c11263, c11264, c4984, c10405, c10452, c4505] c11265 unsat11265 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11259 := derived11259 a h
  have h2 : Entails.eval a c11263 := derived11263 a h
  have h3 : Entails.eval a c11264 := derived11264 a h
  have h4 : Entails.eval a c4984 := h 4983 (by decide)
  have h5 : Entails.eval a c10405 := derived10405 a h
  have h6 : Entails.eval a c10452 := derived10452 a h
  have h7 : Entails.eval a c4505 := h 4504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11266 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11266 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11265, some c4510, some c4507, some c3920, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11266 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11266 : lratChecker f11266 p11266 = .success := by decide +kernel
theorem unsat11266 : Unsatisfiable (PosFin 65) f11266 := by
  apply lratCheckerSound f11266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11266
  · intro a ha; simp [p11266] at ha; subst a; trivial
  · exact checked11266
theorem derived11266 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11266 := by
  apply localUnsat_implies_entails f11266 [c11170, c11265, c4510, c4507, c3920] c11266 unsat11266 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11265 := derived11265 a h
  have h2 : Entails.eval a c4510 := h 4509 (by decide)
  have h3 : Entails.eval a c4507 := h 4506 (by decide)
  have h4 : Entails.eval a c3920 := h 3919 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11267 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true), (⟨8, by decide⟩, false), (⟨20, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11267 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c4013, some c3920, some c3927, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11267 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11267 : lratChecker f11267 p11267 = .success := by decide +kernel
theorem unsat11267 : Unsatisfiable (PosFin 65) f11267 := by
  apply lratCheckerSound f11267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11267
  · intro a ha; simp [p11267] at ha; subst a; trivial
  · exact checked11267
theorem derived11267 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11267 := by
  apply localUnsat_implies_entails f11267 [c11170, c4013, c3920, c3927] c11267 unsat11267 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c4013 := h 4012 (by decide)
  have h2 : Entails.eval a c3920 := h 3919 (by decide)
  have h3 : Entails.eval a c3927 := h 3926 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11268 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨28, by decide⟩, true), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11268 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11265, some c11266, some c11267, some c4015, some c3628, some c10776, some c3760, some c4985, some c5064, some c5065, some c5062, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11268 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11268 : lratChecker f11268 p11268 = .success := by decide +kernel
theorem unsat11268 : Unsatisfiable (PosFin 65) f11268 := by
  apply lratCheckerSound f11268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11268
  · intro a ha; simp [p11268] at ha; subst a; trivial
  · exact checked11268
theorem derived11268 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11268 := by
  apply localUnsat_implies_entails f11268 [c11170, c11256, c11265, c11266, c11267, c4015, c3628, c10776, c3760, c4985, c5064, c5065, c5062] c11268 unsat11268 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11265 := derived11265 a h
  have h3 : Entails.eval a c11266 := derived11266 a h
  have h4 : Entails.eval a c11267 := derived11267 a h
  have h5 : Entails.eval a c4015 := h 4014 (by decide)
  have h6 : Entails.eval a c3628 := h 3627 (by decide)
  have h7 : Entails.eval a c10776 := derived10776 a h
  have h8 : Entails.eval a c3760 := h 3759 (by decide)
  have h9 : Entails.eval a c4985 := h 4984 (by decide)
  have h10 : Entails.eval a c5064 := h 5063 (by decide)
  have h11 : Entails.eval a c5065 := h 5064 (by decide)
  have h12 : Entails.eval a c5062 := h 5061 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11269 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨28, by decide⟩, true), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11269 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11268, some c11265, some c4015, some c3628, some c10777, some c2938, some c4985, some c3068, some c4065, some c4987, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11269 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11269 : lratChecker f11269 p11269 = .success := by decide +kernel
theorem unsat11269 : Unsatisfiable (PosFin 65) f11269 := by
  apply lratCheckerSound f11269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11269
  · intro a ha; simp [p11269] at ha; subst a; trivial
  · exact checked11269
theorem derived11269 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11269 := by
  apply localUnsat_implies_entails f11269 [c11170, c11256, c11268, c11265, c4015, c3628, c10777, c2938, c4985, c3068, c4065, c4987] c11269 unsat11269 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11268 := derived11268 a h
  have h3 : Entails.eval a c11265 := derived11265 a h
  have h4 : Entails.eval a c4015 := h 4014 (by decide)
  have h5 : Entails.eval a c3628 := h 3627 (by decide)
  have h6 : Entails.eval a c10777 := derived10777 a h
  have h7 : Entails.eval a c2938 := h 2937 (by decide)
  have h8 : Entails.eval a c4985 := h 4984 (by decide)
  have h9 : Entails.eval a c3068 := h 3067 (by decide)
  have h10 : Entails.eval a c4065 := h 4064 (by decide)
  have h11 : Entails.eval a c4987 := h 4986 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11270 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11270 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11265, some c11269, some c4013, some c4012, some c4017, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11270 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11270 : lratChecker f11270 p11270 = .success := by decide +kernel
theorem unsat11270 : Unsatisfiable (PosFin 65) f11270 := by
  apply lratCheckerSound f11270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11270
  · intro a ha; simp [p11270] at ha; subst a; trivial
  · exact checked11270
theorem derived11270 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11270 := by
  apply localUnsat_implies_entails f11270 [c11170, c11265, c11269, c4013, c4012, c4017] c11270 unsat11270 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11265 := derived11265 a h
  have h2 : Entails.eval a c11269 := derived11269 a h
  have h3 : Entails.eval a c4013 := h 4012 (by decide)
  have h4 : Entails.eval a c4012 := h 4011 (by decide)
  have h5 : Entails.eval a c4017 := h 4016 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11271 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11271 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11270, some c11264, some c11265, some c4013, some c4012, some c11200, some c4002, some c3994, some c11210, some c4977, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11271 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11271 : lratChecker f11271 p11271 = .success := by decide +kernel
theorem unsat11271 : Unsatisfiable (PosFin 65) f11271 := by
  apply lratCheckerSound f11271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11271
  · intro a ha; simp [p11271] at ha; subst a; trivial
  · exact checked11271
theorem derived11271 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11271 := by
  apply localUnsat_implies_entails f11271 [c11170, c11256, c11270, c11264, c11265, c4013, c4012, c11200, c4002, c3994, c11210, c4977] c11271 unsat11271 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11270 := derived11270 a h
  have h3 : Entails.eval a c11264 := derived11264 a h
  have h4 : Entails.eval a c11265 := derived11265 a h
  have h5 : Entails.eval a c4013 := h 4012 (by decide)
  have h6 : Entails.eval a c4012 := h 4011 (by decide)
  have h7 : Entails.eval a c11200 := derived11200 a h
  have h8 : Entails.eval a c4002 := h 4001 (by decide)
  have h9 : Entails.eval a c3994 := h 3993 (by decide)
  have h10 : Entails.eval a c11210 := derived11210 a h
  have h11 : Entails.eval a c4977 := h 4976 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11272 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11272 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11265, some c11270, some c11264, some c11271, some c4007, some c4011, some c3998, some c4977, some c3625, some c2771, some c2540, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11272 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11272 : lratChecker f11272 p11272 = .success := by decide +kernel
theorem unsat11272 : Unsatisfiable (PosFin 65) f11272 := by
  apply lratCheckerSound f11272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11272
  · intro a ha; simp [p11272] at ha; subst a; trivial
  · exact checked11272
theorem derived11272 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11272 := by
  apply localUnsat_implies_entails f11272 [c11170, c11256, c11265, c11270, c11264, c11271, c4007, c4011, c3998, c4977, c3625, c2771, c2540] c11272 unsat11272 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11265 := derived11265 a h
  have h3 : Entails.eval a c11270 := derived11270 a h
  have h4 : Entails.eval a c11264 := derived11264 a h
  have h5 : Entails.eval a c11271 := derived11271 a h
  have h6 : Entails.eval a c4007 := h 4006 (by decide)
  have h7 : Entails.eval a c4011 := h 4010 (by decide)
  have h8 : Entails.eval a c3998 := h 3997 (by decide)
  have h9 : Entails.eval a c4977 := h 4976 (by decide)
  have h10 : Entails.eval a c3625 := h 3624 (by decide)
  have h11 : Entails.eval a c2771 := h 2770 (by decide)
  have h12 : Entails.eval a c2540 := h 2539 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11273 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11273 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3535, some c3829, some c4501, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11273 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11273 : lratChecker f11273 p11273 = .success := by decide +kernel
theorem unsat11273 : Unsatisfiable (PosFin 65) f11273 := by
  apply lratCheckerSound f11273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11273
  · intro a ha; simp [p11273] at ha; subst a; trivial
  · exact checked11273
theorem derived11273 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11273 := by
  apply localUnsat_implies_entails f11273 [c3535, c3829, c4501] c11273 unsat11273 (by rfl) a
  have h0 : Entails.eval a c3535 := h 3534 (by decide)
  have h1 : Entails.eval a c3829 := h 3828 (by decide)
  have h2 : Entails.eval a c4501 := h 4500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11274 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11274 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11272, some c11273, some c3777, some c3805, some c4870, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11274 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11274 : lratChecker f11274 p11274 = .success := by decide +kernel
theorem unsat11274 : Unsatisfiable (PosFin 65) f11274 := by
  apply lratCheckerSound f11274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11274
  · intro a ha; simp [p11274] at ha; subst a; trivial
  · exact checked11274
theorem derived11274 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11274 := by
  apply localUnsat_implies_entails f11274 [c11272, c11273, c3777, c3805, c4870] c11274 unsat11274 (by rfl) a
  have h0 : Entails.eval a c11272 := derived11272 a h
  have h1 : Entails.eval a c11273 := derived11273 a h
  have h2 : Entails.eval a c3777 := h 3776 (by decide)
  have h3 : Entails.eval a c3805 := h 3804 (by decide)
  have h4 : Entails.eval a c4870 := h 4869 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11275 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11275 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11272, some c10741, some c10412, some c4503, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11275 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11275 : lratChecker f11275 p11275 = .success := by decide +kernel
theorem unsat11275 : Unsatisfiable (PosFin 65) f11275 := by
  apply lratCheckerSound f11275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11275
  · intro a ha; simp [p11275] at ha; subst a; trivial
  · exact checked11275
theorem derived11275 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11275 := by
  apply localUnsat_implies_entails f11275 [c11272, c10741, c10412, c4503] c11275 unsat11275 (by rfl) a
  have h0 : Entails.eval a c11272 := derived11272 a h
  have h1 : Entails.eval a c10741 := derived10741 a h
  have h2 : Entails.eval a c10412 := derived10412 a h
  have h3 : Entails.eval a c4503 := h 4502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11276 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11276 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11272, some c11274, some c11275, some c11195, some c4361, some c4231, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11276 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11276 : lratChecker f11276 p11276 = .success := by decide +kernel
theorem unsat11276 : Unsatisfiable (PosFin 65) f11276 := by
  apply lratCheckerSound f11276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11276
  · intro a ha; simp [p11276] at ha; subst a; trivial
  · exact checked11276
theorem derived11276 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11276 := by
  apply localUnsat_implies_entails f11276 [c11170, c11272, c11274, c11275, c11195, c4361, c4231] c11276 unsat11276 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11272 := derived11272 a h
  have h2 : Entails.eval a c11274 := derived11274 a h
  have h3 : Entails.eval a c11275 := derived11275 a h
  have h4 : Entails.eval a c11195 := derived11195 a h
  have h5 : Entails.eval a c4361 := h 4360 (by decide)
  have h6 : Entails.eval a c4231 := h 4230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11277 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨26, by decide⟩, false), (⟨14, by decide⟩, false), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11277 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c5051, some c4748, some c4533, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p11277 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11277 : lratChecker f11277 p11277 = .success := by decide +kernel
theorem unsat11277 : Unsatisfiable (PosFin 65) f11277 := by
  apply lratCheckerSound f11277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11277
  · intro a ha; simp [p11277] at ha; subst a; trivial
  · exact checked11277
theorem derived11277 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11277 := by
  apply localUnsat_implies_entails f11277 [c11256, c5051, c4748, c4533] c11277 unsat11277 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c5051 := h 5050 (by decide)
  have h2 : Entails.eval a c4748 := h 4747 (by decide)
  have h3 : Entails.eval a c4533 := h 4532 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11278 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11278 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11272, some c11265, some c11195, some c10820, some c10402, some c10467, some c10829, some c11277, some c3060, some c3101, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11278 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11278 : lratChecker f11278 p11278 = .success := by decide +kernel
theorem unsat11278 : Unsatisfiable (PosFin 65) f11278 := by
  apply lratCheckerSound f11278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11278
  · intro a ha; simp [p11278] at ha; subst a; trivial
  · exact checked11278
theorem derived11278 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11278 := by
  apply localUnsat_implies_entails f11278 [c11170, c11272, c11265, c11195, c10820, c10402, c10467, c10829, c11277, c3060, c3101] c11278 unsat11278 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11272 := derived11272 a h
  have h2 : Entails.eval a c11265 := derived11265 a h
  have h3 : Entails.eval a c11195 := derived11195 a h
  have h4 : Entails.eval a c10820 := derived10820 a h
  have h5 : Entails.eval a c10402 := derived10402 a h
  have h6 : Entails.eval a c10467 := derived10467 a h
  have h7 : Entails.eval a c10829 := derived10829 a h
  have h8 : Entails.eval a c11277 := derived11277 a h
  have h9 : Entails.eval a c3060 := h 3059 (by decide)
  have h10 : Entails.eval a c3101 := h 3100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11279 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11279 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11272, some c11276, some c11278, some c10412, some c10733, some c4503, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11279 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11279 : lratChecker f11279 p11279 = .success := by decide +kernel
theorem unsat11279 : Unsatisfiable (PosFin 65) f11279 := by
  apply lratCheckerSound f11279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11279
  · intro a ha; simp [p11279] at ha; subst a; trivial
  · exact checked11279
theorem derived11279 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11279 := by
  apply localUnsat_implies_entails f11279 [c11272, c11276, c11278, c10412, c10733, c4503] c11279 unsat11279 (by rfl) a
  have h0 : Entails.eval a c11272 := derived11272 a h
  have h1 : Entails.eval a c11276 := derived11276 a h
  have h2 : Entails.eval a c11278 := derived11278 a h
  have h3 : Entails.eval a c10412 := derived10412 a h
  have h4 : Entails.eval a c10733 := derived10733 a h
  have h5 : Entails.eval a c4503 := h 4502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11280 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11280 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c4757, some c10410, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p11280 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11280 : lratChecker f11280 p11280 = .success := by decide +kernel
theorem unsat11280 : Unsatisfiable (PosFin 65) f11280 := by
  apply lratCheckerSound f11280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11280
  · intro a ha; simp [p11280] at ha; subst a; trivial
  · exact checked11280
theorem derived11280 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11280 := by
  apply localUnsat_implies_entails f11280 [c11256, c4757, c10410] c11280 unsat11280 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c4757 := h 4756 (by decide)
  have h2 : Entails.eval a c10410 := derived10410 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11281 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11281 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11272, some c11265, some c10480, some c4506, some c10482, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11281 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11281 : lratChecker f11281 p11281 = .success := by decide +kernel
theorem unsat11281 : Unsatisfiable (PosFin 65) f11281 := by
  apply lratCheckerSound f11281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11281
  · intro a ha; simp [p11281] at ha; subst a; trivial
  · exact checked11281
theorem derived11281 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11281 := by
  apply localUnsat_implies_entails f11281 [c11272, c11265, c10480, c4506, c10482] c11281 unsat11281 (by rfl) a
  have h0 : Entails.eval a c11272 := derived11272 a h
  have h1 : Entails.eval a c11265 := derived11265 a h
  have h2 : Entails.eval a c10480 := derived10480 a h
  have h3 : Entails.eval a c4506 := h 4505 (by decide)
  have h4 : Entails.eval a c10482 := derived10482 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11282 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11282 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11272, some c11279, some c11281, some c10404, some c10784, some c4509, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11282 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11282 : lratChecker f11282 p11282 = .success := by decide +kernel
theorem unsat11282 : Unsatisfiable (PosFin 65) f11282 := by
  apply lratCheckerSound f11282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11282
  · intro a ha; simp [p11282] at ha; subst a; trivial
  · exact checked11282
theorem derived11282 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11282 := by
  apply localUnsat_implies_entails f11282 [c11272, c11279, c11281, c10404, c10784, c4509] c11282 unsat11282 (by rfl) a
  have h0 : Entails.eval a c11272 := derived11272 a h
  have h1 : Entails.eval a c11279 := derived11279 a h
  have h2 : Entails.eval a c11281 := derived11281 a h
  have h3 : Entails.eval a c10404 := derived10404 a h
  have h4 : Entails.eval a c10784 := derived10784 a h
  have h5 : Entails.eval a c4509 := h 4508 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11283 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11283 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11272, some c11265, some c3920, some c10659, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11283 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11283 : lratChecker f11283 p11283 = .success := by decide +kernel
theorem unsat11283 : Unsatisfiable (PosFin 65) f11283 := by
  apply lratCheckerSound f11283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11283
  · intro a ha; simp [p11283] at ha; subst a; trivial
  · exact checked11283
theorem derived11283 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11283 := by
  apply localUnsat_implies_entails f11283 [c11170, c11272, c11265, c3920, c10659] c11283 unsat11283 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11272 := derived11272 a h
  have h2 : Entails.eval a c11265 := derived11265 a h
  have h3 : Entails.eval a c3920 := h 3919 (by decide)
  have h4 : Entails.eval a c10659 := derived10659 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11284 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, false), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11284 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c10412, some c10672, some c10820, some c11210, some c10681, some c10402, some c4764, some c5059, some c4543, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p11284 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11284 : lratChecker f11284 p11284 = .success := by decide +kernel
theorem unsat11284 : Unsatisfiable (PosFin 65) f11284 := by
  apply lratCheckerSound f11284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11284
  · intro a ha; simp [p11284] at ha; subst a; trivial
  · exact checked11284
theorem derived11284 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11284 := by
  apply localUnsat_implies_entails f11284 [c11256, c10412, c10672, c10820, c11210, c10681, c10402, c4764, c5059, c4543] c11284 unsat11284 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c10412 := derived10412 a h
  have h2 : Entails.eval a c10672 := derived10672 a h
  have h3 : Entails.eval a c10820 := derived10820 a h
  have h4 : Entails.eval a c11210 := derived11210 a h
  have h5 : Entails.eval a c10681 := derived10681 a h
  have h6 : Entails.eval a c10402 := derived10402 a h
  have h7 : Entails.eval a c4764 := h 4763 (by decide)
  have h8 : Entails.eval a c5059 := h 5058 (by decide)
  have h9 : Entails.eval a c4543 := h 4542 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11285 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11285 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11272, some c11265, some c11282, some c11283, some c11284, some c11195, some c3906, some c3922, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11285 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11285 : lratChecker f11285 p11285 = .success := by decide +kernel
theorem unsat11285 : Unsatisfiable (PosFin 65) f11285 := by
  apply lratCheckerSound f11285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11285
  · intro a ha; simp [p11285] at ha; subst a; trivial
  · exact checked11285
theorem derived11285 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11285 := by
  apply localUnsat_implies_entails f11285 [c11170, c11272, c11265, c11282, c11283, c11284, c11195, c3906, c3922] c11285 unsat11285 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11272 := derived11272 a h
  have h2 : Entails.eval a c11265 := derived11265 a h
  have h3 : Entails.eval a c11282 := derived11282 a h
  have h4 : Entails.eval a c11283 := derived11283 a h
  have h5 : Entails.eval a c11284 := derived11284 a h
  have h6 : Entails.eval a c11195 := derived11195 a h
  have h7 : Entails.eval a c3906 := h 3905 (by decide)
  have h8 : Entails.eval a c3922 := h 3921 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11286 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11286 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11285, some c11272, some c10735, some c4507, some c10737, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11286 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11286 : lratChecker f11286 p11286 = .success := by decide +kernel
theorem unsat11286 : Unsatisfiable (PosFin 65) f11286 := by
  apply lratCheckerSound f11286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11286
  · intro a ha; simp [p11286] at ha; subst a; trivial
  · exact checked11286
theorem derived11286 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11286 := by
  apply localUnsat_implies_entails f11286 [c11285, c11272, c10735, c4507, c10737] c11286 unsat11286 (by rfl) a
  have h0 : Entails.eval a c11285 := derived11285 a h
  have h1 : Entails.eval a c11272 := derived11272 a h
  have h2 : Entails.eval a c10735 := derived10735 a h
  have h3 : Entails.eval a c4507 := h 4506 (by decide)
  have h4 : Entails.eval a c10737 := derived10737 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11287 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11287 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11272, some c11286, some c11281, some c11283, some c10404, some c10784, some c4509, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11287 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11287 : lratChecker f11287 p11287 = .success := by decide +kernel
theorem unsat11287 : Unsatisfiable (PosFin 65) f11287 := by
  apply lratCheckerSound f11287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11287
  · intro a ha; simp [p11287] at ha; subst a; trivial
  · exact checked11287
theorem derived11287 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11287 := by
  apply localUnsat_implies_entails f11287 [c11272, c11286, c11281, c11283, c10404, c10784, c4509] c11287 unsat11287 (by rfl) a
  have h0 : Entails.eval a c11272 := derived11272 a h
  have h1 : Entails.eval a c11286 := derived11286 a h
  have h2 : Entails.eval a c11281 := derived11281 a h
  have h3 : Entails.eval a c11283 := derived11283 a h
  have h4 : Entails.eval a c10404 := derived10404 a h
  have h5 : Entails.eval a c10784 := derived10784 a h
  have h6 : Entails.eval a c4509 := h 4508 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11288 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11288 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11287, some c3913, some c3914, some c4504, some c3903, some c3910, some c4500, some c11188, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11288 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11288 : lratChecker f11288 p11288 = .success := by decide +kernel
theorem unsat11288 : Unsatisfiable (PosFin 65) f11288 := by
  apply lratCheckerSound f11288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11288
  · intro a ha; simp [p11288] at ha; subst a; trivial
  · exact checked11288
theorem derived11288 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11288 := by
  apply localUnsat_implies_entails f11288 [c11170, c11287, c3913, c3914, c4504, c3903, c3910, c4500, c11188] c11288 unsat11288 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11287 := derived11287 a h
  have h2 : Entails.eval a c3913 := h 3912 (by decide)
  have h3 : Entails.eval a c3914 := h 3913 (by decide)
  have h4 : Entails.eval a c4504 := h 4503 (by decide)
  have h5 : Entails.eval a c3903 := h 3902 (by decide)
  have h6 : Entails.eval a c3910 := h 3909 (by decide)
  have h7 : Entails.eval a c4500 := h 4499 (by decide)
  have h8 : Entails.eval a c11188 := derived11188 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11289 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11289 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11287, some c11288, some c11200, some c4508, some c3912, some c3922, some c3919, some c3916, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11289 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11289 : lratChecker f11289 p11289 = .success := by decide +kernel
theorem unsat11289 : Unsatisfiable (PosFin 65) f11289 := by
  apply lratCheckerSound f11289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11289
  · intro a ha; simp [p11289] at ha; subst a; trivial
  · exact checked11289
theorem derived11289 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11289 := by
  apply localUnsat_implies_entails f11289 [c11170, c11287, c11288, c11200, c4508, c3912, c3922, c3919, c3916] c11289 unsat11289 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11287 := derived11287 a h
  have h2 : Entails.eval a c11288 := derived11288 a h
  have h3 : Entails.eval a c11200 := derived11200 a h
  have h4 : Entails.eval a c4508 := h 4507 (by decide)
  have h5 : Entails.eval a c3912 := h 3911 (by decide)
  have h6 : Entails.eval a c3922 := h 3921 (by decide)
  have h7 : Entails.eval a c3919 := h 3918 (by decide)
  have h8 : Entails.eval a c3916 := h 3915 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11290 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11290 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11289, some c11287, some c3916, some c3913, some c3914, some c10696, some c3903, some c3910, some c10516, some c3897, some c11186, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11290 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11290 : lratChecker f11290 p11290 = .success := by decide +kernel
theorem unsat11290 : Unsatisfiable (PosFin 65) f11290 := by
  apply lratCheckerSound f11290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11290
  · intro a ha; simp [p11290] at ha; subst a; trivial
  · exact checked11290
theorem derived11290 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11290 := by
  apply localUnsat_implies_entails f11290 [c11170, c11289, c11287, c3916, c3913, c3914, c10696, c3903, c3910, c10516, c3897, c11186] c11290 unsat11290 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11289 := derived11289 a h
  have h2 : Entails.eval a c11287 := derived11287 a h
  have h3 : Entails.eval a c3916 := h 3915 (by decide)
  have h4 : Entails.eval a c3913 := h 3912 (by decide)
  have h5 : Entails.eval a c3914 := h 3913 (by decide)
  have h6 : Entails.eval a c10696 := derived10696 a h
  have h7 : Entails.eval a c3903 := h 3902 (by decide)
  have h8 : Entails.eval a c3910 := h 3909 (by decide)
  have h9 : Entails.eval a c10516 := derived10516 a h
  have h10 : Entails.eval a c3897 := h 3896 (by decide)
  have h11 : Entails.eval a c11186 := derived11186 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11291 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11291 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11289, some c10482, some c3926, some c10485, some c10456, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11291 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11291 : lratChecker f11291 p11291 = .success := by decide +kernel
theorem unsat11291 : Unsatisfiable (PosFin 65) f11291 := by
  apply lratCheckerSound f11291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11291
  · intro a ha; simp [p11291] at ha; subst a; trivial
  · exact checked11291
theorem derived11291 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11291 := by
  apply localUnsat_implies_entails f11291 [c11170, c11289, c10482, c3926, c10485, c10456] c11291 unsat11291 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11289 := derived11289 a h
  have h2 : Entails.eval a c10482 := derived10482 a h
  have h3 : Entails.eval a c3926 := h 3925 (by decide)
  have h4 : Entails.eval a c10485 := derived10485 a h
  have h5 : Entails.eval a c10456 := derived10456 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11292 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11292 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3920, some c3928, some c3929, some c3923, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11292 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11292 : lratChecker f11292 p11292 = .success := by decide +kernel
theorem unsat11292 : Unsatisfiable (PosFin 65) f11292 := by
  apply lratCheckerSound f11292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11292
  · intro a ha; simp [p11292] at ha; subst a; trivial
  · exact checked11292
theorem derived11292 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11292 := by
  apply localUnsat_implies_entails f11292 [c11170, c3920, c3928, c3929, c3923] c11292 unsat11292 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3920 := h 3919 (by decide)
  have h2 : Entails.eval a c3928 := h 3927 (by decide)
  have h3 : Entails.eval a c3929 := h 3928 (by decide)
  have h4 : Entails.eval a c3923 := h 3922 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11293 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11293 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11290, some c11292, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p11293 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11293 : lratChecker f11293 p11293 = .success := by decide +kernel
theorem unsat11293 : Unsatisfiable (PosFin 65) f11293 := by
  apply lratCheckerSound f11293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11293
  · intro a ha; simp [p11293] at ha; subst a; trivial
  · exact checked11293
theorem derived11293 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11293 := by
  apply localUnsat_implies_entails f11293 [c11290, c11292] c11293 unsat11293 (by rfl) a
  have h0 : Entails.eval a c11290 := derived11290 a h
  have h1 : Entails.eval a c11292 := derived11292 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11294 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11294 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11291, some c11293, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p11294 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11294 : lratChecker f11294 p11294 = .success := by decide +kernel
theorem unsat11294 : Unsatisfiable (PosFin 65) f11294 := by
  apply lratCheckerSound f11294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11294
  · intro a ha; simp [p11294] at ha; subst a; trivial
  · exact checked11294
theorem derived11294 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11294 := by
  apply localUnsat_implies_entails f11294 [c11291, c11293] c11294 unsat11294 (by rfl) a
  have h0 : Entails.eval a c11291 := derived11291 a h
  have h1 : Entails.eval a c11293 := derived11293 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11295 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11295 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10659, some c10375, some c10666, some c10457, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11295 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11295 : lratChecker f11295 p11295 = .success := by decide +kernel
theorem unsat11295 : Unsatisfiable (PosFin 65) f11295 := by
  apply lratCheckerSound f11295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11295
  · intro a ha; simp [p11295] at ha; subst a; trivial
  · exact checked11295
theorem derived11295 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11295 := by
  apply localUnsat_implies_entails f11295 [c10659, c10375, c10666, c10457] c11295 unsat11295 (by rfl) a
  have h0 : Entails.eval a c10659 := derived10659 a h
  have h1 : Entails.eval a c10375 := derived10375 a h
  have h2 : Entails.eval a c10666 := derived10666 a h
  have h3 : Entails.eval a c10457 := derived10457 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11296 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11296 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c10393, some c10358, some c10333, some c10370, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p11296 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11296 : lratChecker f11296 p11296 = .success := by decide +kernel
theorem unsat11296 : Unsatisfiable (PosFin 65) f11296 := by
  apply lratCheckerSound f11296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11296
  · intro a ha; simp [p11296] at ha; subst a; trivial
  · exact checked11296
theorem derived11296 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11296 := by
  apply localUnsat_implies_entails f11296 [c11018, c10393, c10358, c10333, c10370] c11296 unsat11296 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c10393 := derived10393 a h
  have h2 : Entails.eval a c10358 := derived10358 a h
  have h3 : Entails.eval a c10333 := derived10333 a h
  have h4 : Entails.eval a c10370 := derived10370 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11297 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11297 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11296, some c10692, some c10798, some c10376, some c10517, some c10457, some c10638, some c10639, some c10643, some c10354, some c10350, some c10727, some c10726, some c10356, some c10325, some c10731, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p11297 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked11297 : lratChecker f11297 p11297 = .success := by decide +kernel
theorem unsat11297 : Unsatisfiable (PosFin 65) f11297 := by
  apply lratCheckerSound f11297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11297
  · intro a ha; simp [p11297] at ha; subst a; trivial
  · exact checked11297
theorem derived11297 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11297 := by
  apply localUnsat_implies_entails f11297 [c11018, c11296, c10692, c10798, c10376, c10517, c10457, c10638, c10639, c10643, c10354, c10350, c10727, c10726, c10356, c10325, c10731] c11297 unsat11297 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11296 := derived11296 a h
  have h2 : Entails.eval a c10692 := derived10692 a h
  have h3 : Entails.eval a c10798 := derived10798 a h
  have h4 : Entails.eval a c10376 := derived10376 a h
  have h5 : Entails.eval a c10517 := derived10517 a h
  have h6 : Entails.eval a c10457 := derived10457 a h
  have h7 : Entails.eval a c10638 := derived10638 a h
  have h8 : Entails.eval a c10639 := derived10639 a h
  have h9 : Entails.eval a c10643 := derived10643 a h
  have h10 : Entails.eval a c10354 := derived10354 a h
  have h11 : Entails.eval a c10350 := derived10350 a h
  have h12 : Entails.eval a c10727 := derived10727 a h
  have h13 : Entails.eval a c10726 := derived10726 a h
  have h14 : Entails.eval a c10356 := derived10356 a h
  have h15 : Entails.eval a c10325 := derived10325 a h
  have h16 : Entails.eval a c10731 := derived10731 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11298 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨25, by decide⟩, false), (⟨31, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11298 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11287, some c10726, some c10825, some c10824, some c10063, some c342, some c10367, some c10728, some c61, some c10352, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11298 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11298 : lratChecker f11298 p11298 = .success := by decide +kernel
theorem unsat11298 : Unsatisfiable (PosFin 65) f11298 := by
  apply lratCheckerSound f11298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11298
  · intro a ha; simp [p11298] at ha; subst a; trivial
  · exact checked11298
theorem derived11298 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11298 := by
  apply localUnsat_implies_entails f11298 [c11018, c11170, c11287, c10726, c10825, c10824, c10063, c342, c10367, c10728, c61, c10352] c11298 unsat11298 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11287 := derived11287 a h
  have h3 : Entails.eval a c10726 := derived10726 a h
  have h4 : Entails.eval a c10825 := derived10825 a h
  have h5 : Entails.eval a c10824 := derived10824 a h
  have h6 : Entails.eval a c10063 := derived10063 a h
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c10367 := derived10367 a h
  have h9 : Entails.eval a c10728 := derived10728 a h
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c10352 := derived10352 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11299 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11299 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11287, some c11294, some c11295, some c11296, some c11297, some c10829, some c10801, some c10674, some c10480, some c10470, some c10517, some c10457, some c10433, some c11298, some c10361, some c10350, some c10357, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11299 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked11299 : lratChecker f11299 p11299 = .success := by decide +kernel
theorem unsat11299 : Unsatisfiable (PosFin 65) f11299 := by
  apply lratCheckerSound f11299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11299
  · intro a ha; simp [p11299] at ha; subst a; trivial
  · exact checked11299
theorem derived11299 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11299 := by
  apply localUnsat_implies_entails f11299 [c11018, c11287, c11294, c11295, c11296, c11297, c10829, c10801, c10674, c10480, c10470, c10517, c10457, c10433, c11298, c10361, c10350, c10357] c11299 unsat11299 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11287 := derived11287 a h
  have h2 : Entails.eval a c11294 := derived11294 a h
  have h3 : Entails.eval a c11295 := derived11295 a h
  have h4 : Entails.eval a c11296 := derived11296 a h
  have h5 : Entails.eval a c11297 := derived11297 a h
  have h6 : Entails.eval a c10829 := derived10829 a h
  have h7 : Entails.eval a c10801 := derived10801 a h
  have h8 : Entails.eval a c10674 := derived10674 a h
  have h9 : Entails.eval a c10480 := derived10480 a h
  have h10 : Entails.eval a c10470 := derived10470 a h
  have h11 : Entails.eval a c10517 := derived10517 a h
  have h12 : Entails.eval a c10457 := derived10457 a h
  have h13 : Entails.eval a c10433 := derived10433 a h
  have h14 : Entails.eval a c11298 := derived11298 a h
  have h15 : Entails.eval a c10361 := derived10361 a h
  have h16 : Entails.eval a c10350 := derived10350 a h
  have h17 : Entails.eval a c10357 := derived10357 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11300 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11300 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c8269, some c10172, some c4046, some c4045, some c4040, some c4035, some c4038, some c4025, some c4030, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11300 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11300 : lratChecker f11300 p11300 = .success := by decide +kernel
theorem unsat11300 : Unsatisfiable (PosFin 65) f11300 := by
  apply lratCheckerSound f11300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11300
  · intro a ha; simp [p11300] at ha; subst a; trivial
  · exact checked11300
theorem derived11300 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11300 := by
  apply localUnsat_implies_entails f11300 [c11170, c8269, c10172, c4046, c4045, c4040, c4035, c4038, c4025, c4030] c11300 unsat11300 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c10172 := derived10172 a h
  have h3 : Entails.eval a c4046 := h 4045 (by decide)
  have h4 : Entails.eval a c4045 := h 4044 (by decide)
  have h5 : Entails.eval a c4040 := h 4039 (by decide)
  have h6 : Entails.eval a c4035 := h 4034 (by decide)
  have h7 : Entails.eval a c4038 := h 4037 (by decide)
  have h8 : Entails.eval a c4025 := h 4024 (by decide)
  have h9 : Entails.eval a c4030 := h 4029 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11301 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11301 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11256, some c11300, some c10398, some c5004, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11301 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11301 : lratChecker f11301 p11301 = .success := by decide +kernel
theorem unsat11301 : Unsatisfiable (PosFin 65) f11301 := by
  apply lratCheckerSound f11301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11301
  · intro a ha; simp [p11301] at ha; subst a; trivial
  · exact checked11301
theorem derived11301 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11301 := by
  apply localUnsat_implies_entails f11301 [c11018, c11256, c11300, c10398, c5004] c11301 unsat11301 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11300 := derived11300 a h
  have h3 : Entails.eval a c10398 := derived10398 a h
  have h4 : Entails.eval a c5004 := h 5003 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11302 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11302 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11256, some c4999, some c5016, some c4997, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11302 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11302 : lratChecker f11302 p11302 = .success := by decide +kernel
theorem unsat11302 : Unsatisfiable (PosFin 65) f11302 := by
  apply lratCheckerSound f11302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11302
  · intro a ha; simp [p11302] at ha; subst a; trivial
  · exact checked11302
theorem derived11302 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11302 := by
  apply localUnsat_implies_entails f11302 [c11018, c11256, c4999, c5016, c4997] c11302 unsat11302 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c4999 := h 4998 (by decide)
  have h3 : Entails.eval a c5016 := h 5015 (by decide)
  have h4 : Entails.eval a c4997 := h 4996 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11303 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11303 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c4032, some c4034, some c10172, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11303 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11303 : lratChecker f11303 p11303 = .success := by decide +kernel
theorem unsat11303 : Unsatisfiable (PosFin 65) f11303 := by
  apply lratCheckerSound f11303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11303
  · intro a ha; simp [p11303] at ha; subst a; trivial
  · exact checked11303
theorem derived11303 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11303 := by
  apply localUnsat_implies_entails f11303 [c11170, c4032, c4034, c10172] c11303 unsat11303 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c4032 := h 4031 (by decide)
  have h2 : Entails.eval a c4034 := h 4033 (by decide)
  have h3 : Entails.eval a c10172 := derived10172 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11304 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨57, by decide⟩, true), (⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11304 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11302, some c10340, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11304 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11304 : lratChecker f11304 p11304 = .success := by decide +kernel
theorem unsat11304 : Unsatisfiable (PosFin 65) f11304 := by
  apply lratCheckerSound f11304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11304
  · intro a ha; simp [p11304] at ha; subst a; trivial
  · exact checked11304
theorem derived11304 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11304 := by
  apply localUnsat_implies_entails f11304 [c11018, c11302, c10340] c11304 unsat11304 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11302 := derived11302 a h
  have h2 : Entails.eval a c10340 := derived10340 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11305 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11305 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11299, some c11301, some c11303, some c11304, some c10172, some c4033, some c4044, some c3993, some c4045, some c3992, some c4040, some c4004, some c3991, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11305 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked11305 : lratChecker f11305 p11305 = .success := by decide +kernel
theorem unsat11305 : Unsatisfiable (PosFin 65) f11305 := by
  apply lratCheckerSound f11305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11305
  · intro a ha; simp [p11305] at ha; subst a; trivial
  · exact checked11305
theorem derived11305 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11305 := by
  apply localUnsat_implies_entails f11305 [c11170, c11299, c11301, c11303, c11304, c10172, c4033, c4044, c3993, c4045, c3992, c4040, c4004, c3991] c11305 unsat11305 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11299 := derived11299 a h
  have h2 : Entails.eval a c11301 := derived11301 a h
  have h3 : Entails.eval a c11303 := derived11303 a h
  have h4 : Entails.eval a c11304 := derived11304 a h
  have h5 : Entails.eval a c10172 := derived10172 a h
  have h6 : Entails.eval a c4033 := h 4032 (by decide)
  have h7 : Entails.eval a c4044 := h 4043 (by decide)
  have h8 : Entails.eval a c3993 := h 3992 (by decide)
  have h9 : Entails.eval a c4045 := h 4044 (by decide)
  have h10 : Entails.eval a c3992 := h 3991 (by decide)
  have h11 : Entails.eval a c4040 := h 4039 (by decide)
  have h12 : Entails.eval a c4004 := h 4003 (by decide)
  have h13 : Entails.eval a c3991 := h 3990 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11306 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11306 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11299, some c11301, some c11303, some c11304, some c11305, some c7994, some c8380, some c4044, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11306 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11306 : lratChecker f11306 p11306 = .success := by decide +kernel
theorem unsat11306 : Unsatisfiable (PosFin 65) f11306 := by
  apply lratCheckerSound f11306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11306
  · intro a ha; simp [p11306] at ha; subst a; trivial
  · exact checked11306
theorem derived11306 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11306 := by
  apply localUnsat_implies_entails f11306 [c11170, c11299, c11301, c11303, c11304, c11305, c7994, c8380, c4044] c11306 unsat11306 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11299 := derived11299 a h
  have h2 : Entails.eval a c11301 := derived11301 a h
  have h3 : Entails.eval a c11303 := derived11303 a h
  have h4 : Entails.eval a c11304 := derived11304 a h
  have h5 : Entails.eval a c11305 := derived11305 a h
  have h6 : Entails.eval a c7994 := derived7994 a h
  have h7 : Entails.eval a c8380 := derived8380 a h
  have h8 : Entails.eval a c4044 := h 4043 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11307 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨50, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11307 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c11229, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11307 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11307 : lratChecker f11307 p11307 = .success := by decide +kernel
theorem unsat11307 : Unsatisfiable (PosFin 65) f11307 := by
  apply lratCheckerSound f11307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11307
  · intro a ha; simp [p11307] at ha; subst a; trivial
  · exact checked11307
theorem derived11307 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11307 := by
  apply localUnsat_implies_entails f11307 [c7994, c11229] c11307 unsat11307 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c11229 := derived11229 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11308 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11308 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c4015, some c4006, some c11264, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11308 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11308 : lratChecker f11308 p11308 = .success := by decide +kernel
theorem unsat11308 : Unsatisfiable (PosFin 65) f11308 := by
  apply lratCheckerSound f11308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11308
  · intro a ha; simp [p11308] at ha; subst a; trivial
  · exact checked11308
theorem derived11308 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11308 := by
  apply localUnsat_implies_entails f11308 [c11170, c4015, c4006, c11264] c11308 unsat11308 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c4015 := h 4014 (by decide)
  have h2 : Entails.eval a c4006 := h 4005 (by decide)
  have h3 : Entails.eval a c11264 := derived11264 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11309 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11309 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11299, some c11306, some c11292, some c11308, some c11287, some c11303, some c11307, some c10172, some c4033, some c10916, some c331, some c3993, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11309 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11309 : lratChecker f11309 p11309 = .success := by decide +kernel
theorem unsat11309 : Unsatisfiable (PosFin 65) f11309 := by
  apply lratCheckerSound f11309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11309
  · intro a ha; simp [p11309] at ha; subst a; trivial
  · exact checked11309
theorem derived11309 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11309 := by
  apply localUnsat_implies_entails f11309 [c11170, c11299, c11306, c11292, c11308, c11287, c11303, c11307, c10172, c4033, c10916, c331, c3993] c11309 unsat11309 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11299 := derived11299 a h
  have h2 : Entails.eval a c11306 := derived11306 a h
  have h3 : Entails.eval a c11292 := derived11292 a h
  have h4 : Entails.eval a c11308 := derived11308 a h
  have h5 : Entails.eval a c11287 := derived11287 a h
  have h6 : Entails.eval a c11303 := derived11303 a h
  have h7 : Entails.eval a c11307 := derived11307 a h
  have h8 : Entails.eval a c10172 := derived10172 a h
  have h9 : Entails.eval a c4033 := h 4032 (by decide)
  have h10 : Entails.eval a c10916 := derived10916 a h
  have h11 : Entails.eval a c331 := h 330 (by decide)
  have h12 : Entails.eval a c3993 := h 3992 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11310 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11310 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11287, some c11299, some c11306, some c11292, some c11308, some c11309, some c322, some c11300, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11310 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11310 : lratChecker f11310 p11310 = .success := by decide +kernel
theorem unsat11310 : Unsatisfiable (PosFin 65) f11310 := by
  apply lratCheckerSound f11310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11310
  · intro a ha; simp [p11310] at ha; subst a; trivial
  · exact checked11310
theorem derived11310 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11310 := by
  apply localUnsat_implies_entails f11310 [c11018, c11170, c11287, c11299, c11306, c11292, c11308, c11309, c322, c11300] c11310 unsat11310 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11287 := derived11287 a h
  have h3 : Entails.eval a c11299 := derived11299 a h
  have h4 : Entails.eval a c11306 := derived11306 a h
  have h5 : Entails.eval a c11292 := derived11292 a h
  have h6 : Entails.eval a c11308 := derived11308 a h
  have h7 : Entails.eval a c11309 := derived11309 a h
  have h8 : Entails.eval a c322 := h 321 (by decide)
  have h9 : Entails.eval a c11300 := derived11300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11311 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨22, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11311 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11287, some c322, some c11300, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11311 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11311 : lratChecker f11311 p11311 = .success := by decide +kernel
theorem unsat11311 : Unsatisfiable (PosFin 65) f11311 := by
  apply lratCheckerSound f11311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11311
  · intro a ha; simp [p11311] at ha; subst a; trivial
  · exact checked11311
theorem derived11311 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11311 := by
  apply localUnsat_implies_entails f11311 [c11018, c11170, c11287, c322, c11300] c11311 unsat11311 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11287 := derived11287 a h
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c11300 := derived11300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11312 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨22, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11312 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11310, some c11287, some c2772, some c11264, some c4983, some c3673, some c2543, some c2544, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11312 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11312 : lratChecker f11312 p11312 = .success := by decide +kernel
theorem unsat11312 : Unsatisfiable (PosFin 65) f11312 := by
  apply lratCheckerSound f11312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11312
  · intro a ha; simp [p11312] at ha; subst a; trivial
  · exact checked11312
theorem derived11312 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11312 := by
  apply localUnsat_implies_entails f11312 [c11256, c11310, c11287, c2772, c11264, c4983, c3673, c2543, c2544] c11312 unsat11312 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11310 := derived11310 a h
  have h2 : Entails.eval a c11287 := derived11287 a h
  have h3 : Entails.eval a c2772 := h 2771 (by decide)
  have h4 : Entails.eval a c11264 := derived11264 a h
  have h5 : Entails.eval a c4983 := h 4982 (by decide)
  have h6 : Entails.eval a c3673 := h 3672 (by decide)
  have h7 : Entails.eval a c2543 := h 2542 (by decide)
  have h8 : Entails.eval a c2544 := h 2543 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11313 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11313 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11170, some c11310, some c11287, some c11311, some c11303, some c11307, some c332, some c327, some c10172, some c4039, some c3989, some c4002, some c11312, some c11258, some c3899, some c11230, some c3900, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11313 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked11313 : lratChecker f11313 p11313 = .success := by decide +kernel
theorem unsat11313 : Unsatisfiable (PosFin 65) f11313 := by
  apply lratCheckerSound f11313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11313
  · intro a ha; simp [p11313] at ha; subst a; trivial
  · exact checked11313
theorem derived11313 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11313 := by
  apply localUnsat_implies_entails f11313 [c11018, c11170, c11310, c11287, c11311, c11303, c11307, c332, c327, c10172, c4039, c3989, c4002, c11312, c11258, c3899, c11230, c3900] c11313 unsat11313 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11310 := derived11310 a h
  have h3 : Entails.eval a c11287 := derived11287 a h
  have h4 : Entails.eval a c11311 := derived11311 a h
  have h5 : Entails.eval a c11303 := derived11303 a h
  have h6 : Entails.eval a c11307 := derived11307 a h
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c327 := h 326 (by decide)
  have h9 : Entails.eval a c10172 := derived10172 a h
  have h10 : Entails.eval a c4039 := h 4038 (by decide)
  have h11 : Entails.eval a c3989 := h 3988 (by decide)
  have h12 : Entails.eval a c4002 := h 4001 (by decide)
  have h13 : Entails.eval a c11312 := derived11312 a h
  have h14 : Entails.eval a c11258 := derived11258 a h
  have h15 : Entails.eval a c3899 := h 3898 (by decide)
  have h16 : Entails.eval a c11230 := derived11230 a h
  have h17 : Entails.eval a c3900 := h 3899 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11314 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11314 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11313, some c11308, some c11258, some c11200, some c3922, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11314 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11314 : lratChecker f11314 p11314 = .success := by decide +kernel
theorem unsat11314 : Unsatisfiable (PosFin 65) f11314 := by
  apply lratCheckerSound f11314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11314
  · intro a ha; simp [p11314] at ha; subst a; trivial
  · exact checked11314
theorem derived11314 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11314 := by
  apply localUnsat_implies_entails f11314 [c11170, c11313, c11308, c11258, c11200, c3922] c11314 unsat11314 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11313 := derived11313 a h
  have h2 : Entails.eval a c11308 := derived11308 a h
  have h3 : Entails.eval a c11258 := derived11258 a h
  have h4 : Entails.eval a c11200 := derived11200 a h
  have h5 : Entails.eval a c3922 := h 3921 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11315 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11315 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11313, some c11308, some c11314, some c11264, some c4010, some c11267, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11315 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11315 : lratChecker f11315 p11315 = .success := by decide +kernel
theorem unsat11315 : Unsatisfiable (PosFin 65) f11315 := by
  apply lratCheckerSound f11315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11315
  · intro a ha; simp [p11315] at ha; subst a; trivial
  · exact checked11315
theorem derived11315 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11315 := by
  apply localUnsat_implies_entails f11315 [c11170, c11313, c11308, c11314, c11264, c4010, c11267] c11315 unsat11315 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11313 := derived11313 a h
  have h2 : Entails.eval a c11308 := derived11308 a h
  have h3 : Entails.eval a c11314 := derived11314 a h
  have h4 : Entails.eval a c11264 := derived11264 a h
  have h5 : Entails.eval a c4010 := h 4009 (by decide)
  have h6 : Entails.eval a c11267 := derived11267 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11316 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨6, by decide⟩, false), (⟨23, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11316 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c3906, some c11194, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11316 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11316 : lratChecker f11316 p11316 = .success := by decide +kernel
theorem unsat11316 : Unsatisfiable (PosFin 65) f11316 := by
  apply lratCheckerSound f11316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11316
  · intro a ha; simp [p11316] at ha; subst a; trivial
  · exact checked11316
theorem derived11316 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11316 := by
  apply localUnsat_implies_entails f11316 [c11170, c3906, c11194] c11316 unsat11316 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c3906 := h 3905 (by decide)
  have h2 : Entails.eval a c11194 := derived11194 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11317 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11317 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11310, some c11316, some c11315, some c11287, some c4504, some c10696, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11317 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11317 : lratChecker f11317 p11317 = .success := by decide +kernel
theorem unsat11317 : Unsatisfiable (PosFin 65) f11317 := by
  apply lratCheckerSound f11317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11317
  · intro a ha; simp [p11317] at ha; subst a; trivial
  · exact checked11317
theorem derived11317 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11317 := by
  apply localUnsat_implies_entails f11317 [c11310, c11316, c11315, c11287, c4504, c10696] c11317 unsat11317 (by rfl) a
  have h0 : Entails.eval a c11310 := derived11310 a h
  have h1 : Entails.eval a c11316 := derived11316 a h
  have h2 : Entails.eval a c11315 := derived11315 a h
  have h3 : Entails.eval a c11287 := derived11287 a h
  have h4 : Entails.eval a c4504 := h 4503 (by decide)
  have h5 : Entails.eval a c10696 := derived10696 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11318 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨8, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11318 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10700, some c10676, some c10679, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p11318 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11318 : lratChecker f11318 p11318 = .success := by decide +kernel
theorem unsat11318 : Unsatisfiable (PosFin 65) f11318 := by
  apply lratCheckerSound f11318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11318
  · intro a ha; simp [p11318] at ha; subst a; trivial
  · exact checked11318
theorem derived11318 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11318 := by
  apply localUnsat_implies_entails f11318 [c10700, c10676, c10679] c11318 unsat11318 (by rfl) a
  have h0 : Entails.eval a c10700 := derived10700 a h
  have h1 : Entails.eval a c10676 := derived10676 a h
  have h2 : Entails.eval a c10679 := derived10679 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11319 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨30, by decide⟩, true), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11319 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c4804, some c10508, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p11319 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11319 : lratChecker f11319 p11319 = .success := by decide +kernel
theorem unsat11319 : Unsatisfiable (PosFin 65) f11319 := by
  apply lratCheckerSound f11319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11319
  · intro a ha; simp [p11319] at ha; subst a; trivial
  · exact checked11319
theorem derived11319 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11319 := by
  apply localUnsat_implies_entails f11319 [c11256, c4804, c10508] c11319 unsat11319 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c4804 := h 4803 (by decide)
  have h2 : Entails.eval a c10508 := derived10508 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11320 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11320 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11310, some c11287, some c11315, some c11316, some c11317, some c11318, some c4508, some c3925, some c3915, some c11195, some c4511, some c11319, some c10675, some c4810, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11320 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked11320 : lratChecker f11320 p11320 = .success := by decide +kernel
theorem unsat11320 : Unsatisfiable (PosFin 65) f11320 := by
  apply lratCheckerSound f11320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11320
  · intro a ha; simp [p11320] at ha; subst a; trivial
  · exact checked11320
theorem derived11320 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11320 := by
  apply localUnsat_implies_entails f11320 [c11170, c11256, c11310, c11287, c11315, c11316, c11317, c11318, c4508, c3925, c3915, c11195, c4511, c11319, c10675, c4810] c11320 unsat11320 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11310 := derived11310 a h
  have h3 : Entails.eval a c11287 := derived11287 a h
  have h4 : Entails.eval a c11315 := derived11315 a h
  have h5 : Entails.eval a c11316 := derived11316 a h
  have h6 : Entails.eval a c11317 := derived11317 a h
  have h7 : Entails.eval a c11318 := derived11318 a h
  have h8 : Entails.eval a c4508 := h 4507 (by decide)
  have h9 : Entails.eval a c3925 := h 3924 (by decide)
  have h10 : Entails.eval a c3915 := h 3914 (by decide)
  have h11 : Entails.eval a c11195 := derived11195 a h
  have h12 : Entails.eval a c4511 := h 4510 (by decide)
  have h13 : Entails.eval a c11319 := derived11319 a h
  have h14 : Entails.eval a c10675 := derived10675 a h
  have h15 : Entails.eval a c4810 := h 4809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11321 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨27, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11321 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11320, some c11310, some c11287, some c10674, some c10702, some c10681, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11321 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11321 : lratChecker f11321 p11321 = .success := by decide +kernel
theorem unsat11321 : Unsatisfiable (PosFin 65) f11321 := by
  apply lratCheckerSound f11321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11321
  · intro a ha; simp [p11321] at ha; subst a; trivial
  · exact checked11321
theorem derived11321 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11321 := by
  apply localUnsat_implies_entails f11321 [c11320, c11310, c11287, c10674, c10702, c10681] c11321 unsat11321 (by rfl) a
  have h0 : Entails.eval a c11320 := derived11320 a h
  have h1 : Entails.eval a c11310 := derived11310 a h
  have h2 : Entails.eval a c11287 := derived11287 a h
  have h3 : Entails.eval a c10674 := derived10674 a h
  have h4 : Entails.eval a c10702 := derived10702 a h
  have h5 : Entails.eval a c10681 := derived10681 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11322 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11322 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11320, some c11310, some c4068, some c10682, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11322 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11322 : lratChecker f11322 p11322 = .success := by decide +kernel
theorem unsat11322 : Unsatisfiable (PosFin 65) f11322 := by
  apply lratCheckerSound f11322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11322
  · intro a ha; simp [p11322] at ha; subst a; trivial
  · exact checked11322
theorem derived11322 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11322 := by
  apply localUnsat_implies_entails f11322 [c11170, c11320, c11310, c4068, c10682] c11322 unsat11322 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11320 := derived11320 a h
  have h2 : Entails.eval a c11310 := derived11310 a h
  have h3 : Entails.eval a c4068 := h 4067 (by decide)
  have h4 : Entails.eval a c10682 := derived10682 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11323 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11323 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11321, some c11320, some c11287, some c10704, some c4986, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11323 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11323 : lratChecker f11323 p11323 = .success := by decide +kernel
theorem unsat11323 : Unsatisfiable (PosFin 65) f11323 := by
  apply lratCheckerSound f11323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11323
  · intro a ha; simp [p11323] at ha; subst a; trivial
  · exact checked11323
theorem derived11323 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11323 := by
  apply localUnsat_implies_entails f11323 [c11256, c11321, c11320, c11287, c10704, c4986] c11323 unsat11323 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11321 := derived11321 a h
  have h2 : Entails.eval a c11320 := derived11320 a h
  have h3 : Entails.eval a c11287 := derived11287 a h
  have h4 : Entails.eval a c10704 := derived10704 a h
  have h5 : Entails.eval a c4986 := h 4985 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11324 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11324 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11320, some c11287, some c11321, some c11323, some c11322, some c4988, some c10691, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11324 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked11324 : lratChecker f11324 p11324 = .success := by decide +kernel
theorem unsat11324 : Unsatisfiable (PosFin 65) f11324 := by
  apply lratCheckerSound f11324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11324
  · intro a ha; simp [p11324] at ha; subst a; trivial
  · exact checked11324
theorem derived11324 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11324 := by
  apply localUnsat_implies_entails f11324 [c11256, c11320, c11287, c11321, c11323, c11322, c4988, c10691] c11324 unsat11324 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11320 := derived11320 a h
  have h2 : Entails.eval a c11287 := derived11287 a h
  have h3 : Entails.eval a c11321 := derived11321 a h
  have h4 : Entails.eval a c11323 := derived11323 a h
  have h5 : Entails.eval a c11322 := derived11322 a h
  have h6 : Entails.eval a c4988 := h 4987 (by decide)
  have h7 : Entails.eval a c10691 := derived10691 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11325 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11325 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11324, some c11320, some c11310, some c11301, some c4017, some c4002, some c11303, some c11264, some c3994, some c4003, some c3986, some c3990, some c11304, some c11258, some c3999, some c4043, some c4018, some c8380, some c4042, some c3987, some c4007, some c10172, some c4040, some c4022, some c4023, some c11210, some c369, some c370, some c3989, some c5369, some c359, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11325 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked11325 : lratChecker f11325 p11325 = .success := by decide +kernel
theorem unsat11325 : Unsatisfiable (PosFin 65) f11325 := by
  apply lratCheckerSound f11325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11325
  · intro a ha; simp [p11325] at ha; subst a; trivial
  · exact checked11325
theorem derived11325 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11325 := by
  apply localUnsat_implies_entails f11325 [c11170, c11256, c11324, c11320, c11310, c11301, c4017, c4002, c11303, c11264, c3994, c4003, c3986, c3990, c11304, c11258, c3999, c4043, c4018, c8380, c4042, c3987, c4007, c10172, c4040, c4022, c4023, c11210, c369, c370, c3989, c5369, c359] c11325 unsat11325 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11324 := derived11324 a h
  have h3 : Entails.eval a c11320 := derived11320 a h
  have h4 : Entails.eval a c11310 := derived11310 a h
  have h5 : Entails.eval a c11301 := derived11301 a h
  have h6 : Entails.eval a c4017 := h 4016 (by decide)
  have h7 : Entails.eval a c4002 := h 4001 (by decide)
  have h8 : Entails.eval a c11303 := derived11303 a h
  have h9 : Entails.eval a c11264 := derived11264 a h
  have h10 : Entails.eval a c3994 := h 3993 (by decide)
  have h11 : Entails.eval a c4003 := h 4002 (by decide)
  have h12 : Entails.eval a c3986 := h 3985 (by decide)
  have h13 : Entails.eval a c3990 := h 3989 (by decide)
  have h14 : Entails.eval a c11304 := derived11304 a h
  have h15 : Entails.eval a c11258 := derived11258 a h
  have h16 : Entails.eval a c3999 := h 3998 (by decide)
  have h17 : Entails.eval a c4043 := h 4042 (by decide)
  have h18 : Entails.eval a c4018 := h 4017 (by decide)
  have h19 : Entails.eval a c8380 := derived8380 a h
  have h20 : Entails.eval a c4042 := h 4041 (by decide)
  have h21 : Entails.eval a c3987 := h 3986 (by decide)
  have h22 : Entails.eval a c4007 := h 4006 (by decide)
  have h23 : Entails.eval a c10172 := derived10172 a h
  have h24 : Entails.eval a c4040 := h 4039 (by decide)
  have h25 : Entails.eval a c4022 := h 4021 (by decide)
  have h26 : Entails.eval a c4023 := h 4022 (by decide)
  have h27 : Entails.eval a c11210 := derived11210 a h
  have h28 : Entails.eval a c369 := h 368 (by decide)
  have h29 : Entails.eval a c370 := h 369 (by decide)
  have h30 : Entails.eval a c3989 := h 3988 (by decide)
  have h31 : Entails.eval a c5369 := h 5368 (by decide)
  have h32 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11326 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11326 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11310, some c11324, some c11320, some c11325, some c10734, some c10743, some c11296, some c11287, some c10819, some c10115, some c4532, some c10719, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11326 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11326 : lratChecker f11326 p11326 = .success := by decide +kernel
theorem unsat11326 : Unsatisfiable (PosFin 65) f11326 := by
  apply lratCheckerSound f11326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11326
  · intro a ha; simp [p11326] at ha; subst a; trivial
  · exact checked11326
theorem derived11326 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11326 := by
  apply localUnsat_implies_entails f11326 [c11310, c11324, c11320, c11325, c10734, c10743, c11296, c11287, c10819, c10115, c4532, c10719] c11326 unsat11326 (by rfl) a
  have h0 : Entails.eval a c11310 := derived11310 a h
  have h1 : Entails.eval a c11324 := derived11324 a h
  have h2 : Entails.eval a c11320 := derived11320 a h
  have h3 : Entails.eval a c11325 := derived11325 a h
  have h4 : Entails.eval a c10734 := derived10734 a h
  have h5 : Entails.eval a c10743 := derived10743 a h
  have h6 : Entails.eval a c11296 := derived11296 a h
  have h7 : Entails.eval a c11287 := derived11287 a h
  have h8 : Entails.eval a c10819 := derived10819 a h
  have h9 : Entails.eval a c10115 := derived10115 a h
  have h10 : Entails.eval a c4532 := h 4531 (by decide)
  have h11 : Entails.eval a c10719 := derived10719 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11327 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨19, by decide⟩, true), (⟨14, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11327 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11018, some c11325, some c11310, some c11324, some c11320, some c10734, some c10743, some c10820, some c11296, some c4236, some c4147, some c3064, some c4758, some c4361, some c4364, some c4370, some c2986, some c4566, some c11326, some c8269, some c9855, some c10881, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11327 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked11327 : lratChecker f11327 p11327 = .success := by decide +kernel
theorem unsat11327 : Unsatisfiable (PosFin 65) f11327 := by
  apply lratCheckerSound f11327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11327
  · intro a ha; simp [p11327] at ha; subst a; trivial
  · exact checked11327
theorem derived11327 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11327 := by
  apply localUnsat_implies_entails f11327 [c11170, c11256, c11018, c11325, c11310, c11324, c11320, c10734, c10743, c10820, c11296, c4236, c4147, c3064, c4758, c4361, c4364, c4370, c2986, c4566, c11326, c8269, c9855, c10881] c11327 unsat11327 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11018 := derived11018 a h
  have h3 : Entails.eval a c11325 := derived11325 a h
  have h4 : Entails.eval a c11310 := derived11310 a h
  have h5 : Entails.eval a c11324 := derived11324 a h
  have h6 : Entails.eval a c11320 := derived11320 a h
  have h7 : Entails.eval a c10734 := derived10734 a h
  have h8 : Entails.eval a c10743 := derived10743 a h
  have h9 : Entails.eval a c10820 := derived10820 a h
  have h10 : Entails.eval a c11296 := derived11296 a h
  have h11 : Entails.eval a c4236 := h 4235 (by decide)
  have h12 : Entails.eval a c4147 := h 4146 (by decide)
  have h13 : Entails.eval a c3064 := h 3063 (by decide)
  have h14 : Entails.eval a c4758 := h 4757 (by decide)
  have h15 : Entails.eval a c4361 := h 4360 (by decide)
  have h16 : Entails.eval a c4364 := h 4363 (by decide)
  have h17 : Entails.eval a c4370 := h 4369 (by decide)
  have h18 : Entails.eval a c2986 := h 2985 (by decide)
  have h19 : Entails.eval a c4566 := h 4565 (by decide)
  have h20 : Entails.eval a c11326 := derived11326 a h
  have h21 : Entails.eval a c8269 := derived8269 a h
  have h22 : Entails.eval a c9855 := derived9855 a h
  have h23 : Entails.eval a c10881 := derived10881 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11328 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨14, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11328 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11170, some c11018, some c11325, some c11310, some c11324, some c11320, some c10734, some c10743, some c10820, some c11296, some c11327, some c5068, some c3075, some c2992, some c3218, some c3102, some c3602, some c4234, some c4543, some c4566, some c11326, some c8269, some c9855, some c10881, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11328 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked11328 : lratChecker f11328 p11328 = .success := by decide +kernel
theorem unsat11328 : Unsatisfiable (PosFin 65) f11328 := by
  apply lratCheckerSound f11328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11328
  · intro a ha; simp [p11328] at ha; subst a; trivial
  · exact checked11328
theorem derived11328 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11328 := by
  apply localUnsat_implies_entails f11328 [c11256, c11170, c11018, c11325, c11310, c11324, c11320, c10734, c10743, c10820, c11296, c11327, c5068, c3075, c2992, c3218, c3102, c3602, c4234, c4543, c4566, c11326, c8269, c9855, c10881] c11328 unsat11328 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c11018 := derived11018 a h
  have h3 : Entails.eval a c11325 := derived11325 a h
  have h4 : Entails.eval a c11310 := derived11310 a h
  have h5 : Entails.eval a c11324 := derived11324 a h
  have h6 : Entails.eval a c11320 := derived11320 a h
  have h7 : Entails.eval a c10734 := derived10734 a h
  have h8 : Entails.eval a c10743 := derived10743 a h
  have h9 : Entails.eval a c10820 := derived10820 a h
  have h10 : Entails.eval a c11296 := derived11296 a h
  have h11 : Entails.eval a c11327 := derived11327 a h
  have h12 : Entails.eval a c5068 := h 5067 (by decide)
  have h13 : Entails.eval a c3075 := h 3074 (by decide)
  have h14 : Entails.eval a c2992 := h 2991 (by decide)
  have h15 : Entails.eval a c3218 := h 3217 (by decide)
  have h16 : Entails.eval a c3102 := h 3101 (by decide)
  have h17 : Entails.eval a c3602 := h 3601 (by decide)
  have h18 : Entails.eval a c4234 := h 4233 (by decide)
  have h19 : Entails.eval a c4543 := h 4542 (by decide)
  have h20 : Entails.eval a c4566 := h 4565 (by decide)
  have h21 : Entails.eval a c11326 := derived11326 a h
  have h22 : Entails.eval a c8269 := derived8269 a h
  have h23 : Entails.eval a c9855 := derived9855 a h
  have h24 : Entails.eval a c10881 := derived10881 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11329 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨53, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11329 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10351, some c10354, some c10355, some c8380, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11329 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11329 : lratChecker f11329 p11329 = .success := by decide +kernel
theorem unsat11329 : Unsatisfiable (PosFin 65) f11329 := by
  apply lratCheckerSound f11329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11329
  · intro a ha; simp [p11329] at ha; subst a; trivial
  · exact checked11329
theorem derived11329 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11329 := by
  apply localUnsat_implies_entails f11329 [c10351, c10354, c10355, c8380] c11329 unsat11329 (by rfl) a
  have h0 : Entails.eval a c10351 := derived10351 a h
  have h1 : Entails.eval a c10354 := derived10354 a h
  have h2 : Entails.eval a c10355 := derived10355 a h
  have h3 : Entails.eval a c8380 := derived8380 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11330 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11330 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11310, some c11324, some c11320, some c11325, some c10734, some c11296, some c11287, some c10639, some c10792, some c11329, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11330 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11330 : lratChecker f11330 p11330 = .success := by decide +kernel
theorem unsat11330 : Unsatisfiable (PosFin 65) f11330 := by
  apply lratCheckerSound f11330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11330
  · intro a ha; simp [p11330] at ha; subst a; trivial
  · exact checked11330
theorem derived11330 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11330 := by
  apply localUnsat_implies_entails f11330 [c11310, c11324, c11320, c11325, c10734, c11296, c11287, c10639, c10792, c11329] c11330 unsat11330 (by rfl) a
  have h0 : Entails.eval a c11310 := derived11310 a h
  have h1 : Entails.eval a c11324 := derived11324 a h
  have h2 : Entails.eval a c11320 := derived11320 a h
  have h3 : Entails.eval a c11325 := derived11325 a h
  have h4 : Entails.eval a c10734 := derived10734 a h
  have h5 : Entails.eval a c11296 := derived11296 a h
  have h6 : Entails.eval a c11287 := derived11287 a h
  have h7 : Entails.eval a c10639 := derived10639 a h
  have h8 : Entails.eval a c10792 := derived10792 a h
  have h9 : Entails.eval a c11329 := derived11329 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11331 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11331 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11310, some c11320, some c11324, some c11325, some c10743, some c10734, some c11330, some c11328, some c10768, some c10821, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p11331 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked11331 : lratChecker f11331 p11331 = .success := by decide +kernel
theorem unsat11331 : Unsatisfiable (PosFin 65) f11331 := by
  apply lratCheckerSound f11331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11331
  · intro a ha; simp [p11331] at ha; subst a; trivial
  · exact checked11331
theorem derived11331 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11331 := by
  apply localUnsat_implies_entails f11331 [c11310, c11320, c11324, c11325, c10743, c10734, c11330, c11328, c10768, c10821] c11331 unsat11331 (by rfl) a
  have h0 : Entails.eval a c11310 := derived11310 a h
  have h1 : Entails.eval a c11320 := derived11320 a h
  have h2 : Entails.eval a c11324 := derived11324 a h
  have h3 : Entails.eval a c11325 := derived11325 a h
  have h4 : Entails.eval a c10743 := derived10743 a h
  have h5 : Entails.eval a c10734 := derived10734 a h
  have h6 : Entails.eval a c11330 := derived11330 a h
  have h7 : Entails.eval a c11328 := derived11328 a h
  have h8 : Entails.eval a c10768 := derived10768 a h
  have h9 : Entails.eval a c10821 := derived10821 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11332 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11332 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10426, some c10514, some c10510, some c10472, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11332 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11332 : lratChecker f11332 p11332 = .success := by decide +kernel
theorem unsat11332 : Unsatisfiable (PosFin 65) f11332 := by
  apply lratCheckerSound f11332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11332
  · intro a ha; simp [p11332] at ha; subst a; trivial
  · exact checked11332
theorem derived11332 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11332 := by
  apply localUnsat_implies_entails f11332 [c11331, c10426, c10514, c10510, c10472] c11332 unsat11332 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10426 := derived10426 a h
  have h2 : Entails.eval a c10514 := derived10514 a h
  have h3 : Entails.eval a c10510 := derived10510 a h
  have h4 : Entails.eval a c10472 := derived10472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11333 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨28, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11333 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10735, some c10403, some c11295, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11333 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11333 : lratChecker f11333 p11333 = .success := by decide +kernel
theorem unsat11333 : Unsatisfiable (PosFin 65) f11333 := by
  apply lratCheckerSound f11333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11333
  · intro a ha; simp [p11333] at ha; subst a; trivial
  · exact checked11333
theorem derived11333 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11333 := by
  apply localUnsat_implies_entails f11333 [c10735, c10403, c11295] c11333 unsat11333 (by rfl) a
  have h0 : Entails.eval a c10735 := derived10735 a h
  have h1 : Entails.eval a c10403 := derived10403 a h
  have h2 : Entails.eval a c11295 := derived11295 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c11334 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨60, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11334 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10792, some c11333, some c10692, some c11297, some c10734, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p11334 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11334 : lratChecker f11334 p11334 = .success := by decide +kernel
theorem unsat11334 : Unsatisfiable (PosFin 65) f11334 := by
  apply lratCheckerSound f11334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11334
  · intro a ha; simp [p11334] at ha; subst a; trivial
  · exact checked11334
theorem derived11334 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11334 := by
  apply localUnsat_implies_entails f11334 [c10792, c11333, c10692, c11297, c10734] c11334 unsat11334 (by rfl) a
  have h0 : Entails.eval a c10792 := derived10792 a h
  have h1 : Entails.eval a c11333 := derived11333 a h
  have h2 : Entails.eval a c10692 := derived10692 a h
  have h3 : Entails.eval a c11297 := derived11297 a h
  have h4 : Entails.eval a c10734 := derived10734 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11335 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨28, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11335 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11333, some c10734, some c10493, some c10702, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11335 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11335 : lratChecker f11335 p11335 = .success := by decide +kernel
theorem unsat11335 : Unsatisfiable (PosFin 65) f11335 := by
  apply lratCheckerSound f11335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11335
  · intro a ha; simp [p11335] at ha; subst a; trivial
  · exact checked11335
theorem derived11335 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11335 := by
  apply localUnsat_implies_entails f11335 [c11333, c10734, c10493, c10702] c11335 unsat11335 (by rfl) a
  have h0 : Entails.eval a c11333 := derived11333 a h
  have h1 : Entails.eval a c10734 := derived10734 a h
  have h2 : Entails.eval a c10493 := derived10493 a h
  have h3 : Entails.eval a c10702 := derived10702 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11336 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨53, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11336 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11296, some c11329, some c11334, some c10362, some c10361, some c10727, some c10356, some c10352, some c10649, some c10367, some c10370, some c11295, some c10829, some c10801, some c8457, some c10480, some c10469, some c5723, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11336 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked11336 : lratChecker f11336 p11336 = .success := by decide +kernel
theorem unsat11336 : Unsatisfiable (PosFin 65) f11336 := by
  apply lratCheckerSound f11336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11336
  · intro a ha; simp [p11336] at ha; subst a; trivial
  · exact checked11336
theorem derived11336 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11336 := by
  apply localUnsat_implies_entails f11336 [c11018, c11296, c11329, c11334, c10362, c10361, c10727, c10356, c10352, c10649, c10367, c10370, c11295, c10829, c10801, c8457, c10480, c10469, c5723] c11336 unsat11336 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11296 := derived11296 a h
  have h2 : Entails.eval a c11329 := derived11329 a h
  have h3 : Entails.eval a c11334 := derived11334 a h
  have h4 : Entails.eval a c10362 := derived10362 a h
  have h5 : Entails.eval a c10361 := derived10361 a h
  have h6 : Entails.eval a c10727 := derived10727 a h
  have h7 : Entails.eval a c10356 := derived10356 a h
  have h8 : Entails.eval a c10352 := derived10352 a h
  have h9 : Entails.eval a c10649 := derived10649 a h
  have h10 : Entails.eval a c10367 := derived10367 a h
  have h11 : Entails.eval a c10370 := derived10370 a h
  have h12 : Entails.eval a c11295 := derived11295 a h
  have h13 : Entails.eval a c10829 := derived10829 a h
  have h14 : Entails.eval a c10801 := derived10801 a h
  have h15 : Entails.eval a c8457 := derived8457 a h
  have h16 : Entails.eval a c10480 := derived10480 a h
  have h17 : Entails.eval a c10469 := derived10469 a h
  have h18 : Entails.eval a c5723 := h 5722 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11337 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11337 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11018, some c11296, some c11329, some c10727, some c10362, some c10352, some c10361, some c11334, some c11336, some c11335, some c10466, some c10819, some c10425, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11337 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked11337 : lratChecker f11337 p11337 = .success := by decide +kernel
theorem unsat11337 : Unsatisfiable (PosFin 65) f11337 := by
  apply lratCheckerSound f11337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11337
  · intro a ha; simp [p11337] at ha; subst a; trivial
  · exact checked11337
theorem derived11337 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11337 := by
  apply localUnsat_implies_entails f11337 [c11018, c11296, c11329, c10727, c10362, c10352, c10361, c11334, c11336, c11335, c10466, c10819, c10425] c11337 unsat11337 (by rfl) a
  have h0 : Entails.eval a c11018 := derived11018 a h
  have h1 : Entails.eval a c11296 := derived11296 a h
  have h2 : Entails.eval a c11329 := derived11329 a h
  have h3 : Entails.eval a c10727 := derived10727 a h
  have h4 : Entails.eval a c10362 := derived10362 a h
  have h5 : Entails.eval a c10352 := derived10352 a h
  have h6 : Entails.eval a c10361 := derived10361 a h
  have h7 : Entails.eval a c11334 := derived11334 a h
  have h8 : Entails.eval a c11336 := derived11336 a h
  have h9 : Entails.eval a c11335 := derived11335 a h
  have h10 : Entails.eval a c10466 := derived10466 a h
  have h11 : Entails.eval a c10819 := derived10819 a h
  have h12 : Entails.eval a c10425 := derived10425 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11338 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11338 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c10426, some c10510, some c10425, some c11332, some c10743, some c5059, some c4765, some c4541, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11338 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11338 : lratChecker f11338 p11338 = .success := by decide +kernel
theorem unsat11338 : Unsatisfiable (PosFin 65) f11338 := by
  apply lratCheckerSound f11338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11338
  · intro a ha; simp [p11338] at ha; subst a; trivial
  · exact checked11338
theorem derived11338 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11338 := by
  apply localUnsat_implies_entails f11338 [c11256, c10426, c10510, c10425, c11332, c10743, c5059, c4765, c4541] c11338 unsat11338 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c10426 := derived10426 a h
  have h2 : Entails.eval a c10510 := derived10510 a h
  have h3 : Entails.eval a c10425 := derived10425 a h
  have h4 : Entails.eval a c11332 := derived11332 a h
  have h5 : Entails.eval a c10743 := derived10743 a h
  have h6 : Entails.eval a c5059 := h 5058 (by decide)
  have h7 : Entails.eval a c4765 := h 4764 (by decide)
  have h8 : Entails.eval a c4541 := h 4540 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11339 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11339 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11296, some c11337, some c10360, some c11051, some c10322, some c10726, some c10063, some c393, some c389, some c392, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11339 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked11339 : lratChecker f11339 p11339 = .success := by decide +kernel
theorem unsat11339 : Unsatisfiable (PosFin 65) f11339 := by
  apply lratCheckerSound f11339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11339
  · intro a ha; simp [p11339] at ha; subst a; trivial
  · exact checked11339
theorem derived11339 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11339 := by
  apply localUnsat_implies_entails f11339 [c11170, c11296, c11337, c10360, c11051, c10322, c10726, c10063, c393, c389, c392] c11339 unsat11339 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11296 := derived11296 a h
  have h2 : Entails.eval a c11337 := derived11337 a h
  have h3 : Entails.eval a c10360 := derived10360 a h
  have h4 : Entails.eval a c11051 := derived11051 a h
  have h5 : Entails.eval a c10322 := derived10322 a h
  have h6 : Entails.eval a c10726 := derived10726 a h
  have h7 : Entails.eval a c10063 := derived10063 a h
  have h8 : Entails.eval a c393 := h 392 (by decide)
  have h9 : Entails.eval a c389 := h 388 (by decide)
  have h10 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11340 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11340 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c10743, some c10412, some c11338, some c10692, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11340 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11340 : lratChecker f11340 p11340 = .success := by decide +kernel
theorem unsat11340 : Unsatisfiable (PosFin 65) f11340 := by
  apply lratCheckerSound f11340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11340
  · intro a ha; simp [p11340] at ha; subst a; trivial
  · exact checked11340
theorem derived11340 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11340 := by
  apply localUnsat_implies_entails f11340 [c10743, c10412, c11338, c10692] c11340 unsat11340 (by rfl) a
  have h0 : Entails.eval a c10743 := derived10743 a h
  have h1 : Entails.eval a c10412 := derived10412 a h
  have h2 : Entails.eval a c11338 := derived11338 a h
  have h3 : Entails.eval a c10692 := derived10692 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11341 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨28, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11341 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11339, some c11340, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p11341 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked11341 : lratChecker f11341 p11341 = .success := by decide +kernel
theorem unsat11341 : Unsatisfiable (PosFin 65) f11341 := by
  apply lratCheckerSound f11341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11341
  · intro a ha; simp [p11341] at ha; subst a; trivial
  · exact checked11341
theorem derived11341 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11341 := by
  apply localUnsat_implies_entails f11341 [c11339, c11340] c11341 unsat11341 (by rfl) a
  have h0 : Entails.eval a c11339 := derived11339 a h
  have h1 : Entails.eval a c11340 := derived11340 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11342 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11342 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11337, some c11051, some c11296, some c10643, some c11334, some c10368, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11342 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11342 : lratChecker f11342 p11342 = .success := by decide +kernel
theorem unsat11342 : Unsatisfiable (PosFin 65) f11342 := by
  apply lratCheckerSound f11342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11342
  · intro a ha; simp [p11342] at ha; subst a; trivial
  · exact checked11342
theorem derived11342 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11342 := by
  apply localUnsat_implies_entails f11342 [c11337, c11051, c11296, c10643, c11334, c10368] c11342 unsat11342 (by rfl) a
  have h0 : Entails.eval a c11337 := derived11337 a h
  have h1 : Entails.eval a c11051 := derived11051 a h
  have h2 : Entails.eval a c11296 := derived11296 a h
  have h3 : Entails.eval a c10643 := derived10643 a h
  have h4 : Entails.eval a c11334 := derived11334 a h
  have h5 : Entails.eval a c10368 := derived10368 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11343 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11343 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11342, some c10426, some c10425, some c10480, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11343 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked11343 : lratChecker f11343 p11343 = .success := by decide +kernel
theorem unsat11343 : Unsatisfiable (PosFin 65) f11343 := by
  apply lratCheckerSound f11343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11343
  · intro a ha; simp [p11343] at ha; subst a; trivial
  · exact checked11343
theorem derived11343 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11343 := by
  apply localUnsat_implies_entails f11343 [c11342, c10426, c10425, c10480] c11343 unsat11343 (by rfl) a
  have h0 : Entails.eval a c11342 := derived11342 a h
  have h1 : Entails.eval a c10426 := derived10426 a h
  have h2 : Entails.eval a c10425 := derived10425 a h
  have h3 : Entails.eval a c10480 := derived10480 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c11344 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11344 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11341, some c11295, some c11342, some c10829, some c10801, some c10467, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11344 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11344 : lratChecker f11344 p11344 = .success := by decide +kernel
theorem unsat11344 : Unsatisfiable (PosFin 65) f11344 := by
  apply lratCheckerSound f11344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11344
  · intro a ha; simp [p11344] at ha; subst a; trivial
  · exact checked11344
theorem derived11344 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11344 := by
  apply localUnsat_implies_entails f11344 [c11341, c11295, c11342, c10829, c10801, c10467] c11344 unsat11344 (by rfl) a
  have h0 : Entails.eval a c11341 := derived11341 a h
  have h1 : Entails.eval a c11295 := derived11295 a h
  have h2 : Entails.eval a c11342 := derived11342 a h
  have h3 : Entails.eval a c10829 := derived10829 a h
  have h4 : Entails.eval a c10801 := derived10801 a h
  have h5 : Entails.eval a c10467 := derived10467 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11345 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11345 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11296, some c11337, some c11051, some c10360, some c10322, some c11344, some c11333, some c11335, some c10728, some c11343, some c10063, some c10726, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11345 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked11345 : lratChecker f11345 p11345 = .success := by decide +kernel
theorem unsat11345 : Unsatisfiable (PosFin 65) f11345 := by
  apply lratCheckerSound f11345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11345
  · intro a ha; simp [p11345] at ha; subst a; trivial
  · exact checked11345
theorem derived11345 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11345 := by
  apply localUnsat_implies_entails f11345 [c11296, c11337, c11051, c10360, c10322, c11344, c11333, c11335, c10728, c11343, c10063, c10726] c11345 unsat11345 (by rfl) a
  have h0 : Entails.eval a c11296 := derived11296 a h
  have h1 : Entails.eval a c11337 := derived11337 a h
  have h2 : Entails.eval a c11051 := derived11051 a h
  have h3 : Entails.eval a c10360 := derived10360 a h
  have h4 : Entails.eval a c10322 := derived10322 a h
  have h5 : Entails.eval a c11344 := derived11344 a h
  have h6 : Entails.eval a c11333 := derived11333 a h
  have h7 : Entails.eval a c11335 := derived11335 a h
  have h8 : Entails.eval a c10728 := derived10728 a h
  have h9 : Entails.eval a c11343 := derived11343 a h
  have h10 : Entails.eval a c10063 := derived10063 a h
  have h11 : Entails.eval a c10726 := derived10726 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11346 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11346 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11331, some c10767, some c10319, some c4742, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11346 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked11346 : lratChecker f11346 p11346 = .success := by decide +kernel
theorem unsat11346 : Unsatisfiable (PosFin 65) f11346 := by
  apply lratCheckerSound f11346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11346
  · intro a ha; simp [p11346] at ha; subst a; trivial
  · exact checked11346
theorem derived11346 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11346 := by
  apply localUnsat_implies_entails f11346 [c11256, c11331, c10767, c10319, c4742] c11346 unsat11346 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11331 := derived11331 a h
  have h2 : Entails.eval a c10767 := derived10767 a h
  have h3 : Entails.eval a c10319 := derived10319 a h
  have h4 : Entails.eval a c4742 := h 4741 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11347 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f11347 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11170, some c11256, some c11302, some c4975, some c4054, some c4994, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p11347 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11347 : lratChecker f11347 p11347 = .success := by decide +kernel
theorem unsat11347 : Unsatisfiable (PosFin 65) f11347 := by
  apply lratCheckerSound f11347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11347
  · intro a ha; simp [p11347] at ha; subst a; trivial
  · exact checked11347
theorem derived11347 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11347 := by
  apply localUnsat_implies_entails f11347 [c11170, c11256, c11302, c4975, c4054, c4994] c11347 unsat11347 (by rfl) a
  have h0 : Entails.eval a c11170 := derived11170 a h
  have h1 : Entails.eval a c11256 := derived11256 a h
  have h2 : Entails.eval a c11302 := derived11302 a h
  have h3 : Entails.eval a c4975 := h 4974 (by decide)
  have h4 : Entails.eval a c4054 := h 4053 (by decide)
  have h5 : Entails.eval a c4994 := h 4993 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11348 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨21, by decide⟩, false), (⟨51, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11348 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c11346, some c11345, some c11347, some c10711, some c11210, some c10772, some c10804, some c10486, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11348 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked11348 : lratChecker f11348 p11348 = .success := by decide +kernel
theorem unsat11348 : Unsatisfiable (PosFin 65) f11348 := by
  apply lratCheckerSound f11348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11348
  · intro a ha; simp [p11348] at ha; subst a; trivial
  · exact checked11348
theorem derived11348 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11348 := by
  apply localUnsat_implies_entails f11348 [c11331, c11346, c11345, c11347, c10711, c11210, c10772, c10804, c10486] c11348 unsat11348 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c11346 := derived11346 a h
  have h2 : Entails.eval a c11345 := derived11345 a h
  have h3 : Entails.eval a c11347 := derived11347 a h
  have h4 : Entails.eval a c10711 := derived10711 a h
  have h5 : Entails.eval a c11210 := derived11210 a h
  have h6 : Entails.eval a c10772 := derived10772 a h
  have h7 : Entails.eval a c10804 := derived10804 a h
  have h8 : Entails.eval a c10486 := derived10486 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11349 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨59, by decide⟩, true), (⟨18, by decide⟩, false), (⟨28, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11349 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11331, some c10921, some c11210, some c10764, some c10331, some c10748, some c10654, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p11349 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked11349 : lratChecker f11349 p11349 = .success := by decide +kernel
theorem unsat11349 : Unsatisfiable (PosFin 65) f11349 := by
  apply lratCheckerSound f11349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11349
  · intro a ha; simp [p11349] at ha; subst a; trivial
  · exact checked11349
theorem derived11349 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11349 := by
  apply localUnsat_implies_entails f11349 [c11331, c10921, c11210, c10764, c10331, c10748, c10654] c11349 unsat11349 (by rfl) a
  have h0 : Entails.eval a c11331 := derived11331 a h
  have h1 : Entails.eval a c10921 := derived10921 a h
  have h2 : Entails.eval a c11210 := derived11210 a h
  have h3 : Entails.eval a c10764 := derived10764 a h
  have h4 : Entails.eval a c10331 := derived10331 a h
  have h5 : Entails.eval a c10748 := derived10748 a h
  have h6 : Entails.eval a c10654 := derived10654 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c11350 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11350 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c11256, some c11170, some c4994, some c4995, some c4070, some c4996, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p11350 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked11350 : lratChecker f11350 p11350 = .success := by decide +kernel
theorem unsat11350 : Unsatisfiable (PosFin 65) f11350 := by
  apply lratCheckerSound f11350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11350
  · intro a ha; simp [p11350] at ha; subst a; trivial
  · exact checked11350
theorem derived11350 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c11350 := by
  apply localUnsat_implies_entails f11350 [c11256, c11170, c4994, c4995, c4070, c4996] c11350 unsat11350 (by rfl) a
  have h0 : Entails.eval a c11256 := derived11256 a h
  have h1 : Entails.eval a c11170 := derived11170 a h
  have h2 : Entails.eval a c4994 := h 4993 (by decide)
  have h3 : Entails.eval a c4995 := h 4994 (by decide)
  have h4 : Entails.eval a c4070 := h 4069 (by decide)
  have h5 : Entails.eval a c4996 := h 4995 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived11350

end CochromaticTwenty.Certificates.FixedCore0
