import MerLeanExperiment.GraphCode

namespace CochromaticTwenty

/-- Every finite ordinary simple graph has a bounded numeric adjacency code,
up to a proved vertex isomorphism. -/
theorem exists_bounded_code_iso (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ code : ℕ, code < 2 ^ triangle n ∧ Nonempty (G ≃g codeGraph n code) := by
  induction n with
  | zero =>
    refine ⟨0, by decide, ⟨{ toEquiv := Equiv.refl _, map_rel_iff' := ?_ }⟩⟩
    intro u
    exact Fin.elim0 u
  | succ n ih =>
    obtain ⟨code, hc, ⟨e⟩⟩ := ih (G.comap Fin.castSucc)
    obtain ⟨mask, hm, he⟩ := exists_extension_iso hc G e
    refine ⟨extendCode n code mask, ?_, he⟩
    have hm' : mask + 1 ≤ 2 ^ n := by omega
    have hmul := Nat.mul_le_mul_left (2 ^ triangle n) hm'
    simp only [triangle, pow_add, extendCode]
    nlinarith

end CochromaticTwenty

#print axioms CochromaticTwenty.exists_bounded_code_iso
