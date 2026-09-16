import MerLeanExperiment.Vendor.Dirichlet

namespace Erdos492Real

noncomputable section

/-- A finite family admits simultaneous integer approximations with arbitrarily large
denominator and any prescribed positive absolute error. -/
theorem exists_large_simultaneous_approximation
    {E : Type*} [Fintype E] (alpha : E → ℝ) (B : ℕ) (_hB : 1 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : ℕ, B ≤ q ∧ ∀ e, ∃ z : ℤ, |(q : ℝ) * alpha e - z| < δ := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (1 / δ)
  have hQpos : 0 < Q := by
    by_contra h
    have hQzero : Q = 0 := Nat.eq_zero_of_not_pos h
    subst Q
    norm_num at hQ
    exact (not_lt_of_ge (le_of_lt hδ) hQ)
  obtain ⟨d, hdpos, hdQ, hz⟩ :=
    Erdos485.simultaneous_dirichlet_mul (fun e => (B : ℝ) * alpha e) Q hQpos
  refine ⟨B * d, ?_, ?_⟩
  · calc
      B = B * 1 := by simp
      _ ≤ B * d := Nat.mul_le_mul_left B hdpos
  · intro e
    obtain ⟨z, hz⟩ := hz e
    refine ⟨z, ?_⟩
    have hinv : (1 : ℝ) / Q < δ := by
      rw [div_lt_iff₀ (by exact_mod_cast hQpos)]
      have hone : (1 : ℝ) < Q * δ := (div_lt_iff₀ hδ).mp hQ
      nlinarith
    have heq : ((B * d : ℕ) : ℝ) * alpha e =
        (d : ℝ) * ((B : ℝ) * alpha e) := by
      push_cast
      ring
    rw [heq]
    exact hz.trans hinv

end

end Erdos492Real
