import MerLeanExperiment.GaussianResidue

namespace ReciprocalSquares

/-- Fractions strictly inside the central unit interval have nearest integer zero. -/
theorem round_div_eq_zero (h d : ℝ) (hd : 2 * |h| < d) :
    round (h / d) = 0 := by
  have hdpos : 0 < d := by have := abs_nonneg h; linarith
  apply round_eq_zero_iff.mpr
  have habs : |h / d| < (1 / 2 : ℝ) := by
    rw [abs_div, abs_of_pos hdpos]
    apply (div_lt_iff₀ hdpos).mpr
    linarith
  exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2⟩

/-- A finite set of denominators between twice the frequency and a common
upper bound gives an explicit lower bound for the total residue energy. -/
theorem residueEnergy_ge_card_mul_ratio_sq
    (D E : Finset ℕ) (h U : ℝ) (hE : E ⊆ D) (hU : 0 < U)
    (hbounds : ∀ d ∈ E, 2 * |h| < (d : ℝ) ∧ (d : ℝ) ≤ U) :
    (E.card : ℝ) * (|h| / U) ^ 2 ≤
      residueEnergy D (fun d => h / (d : ℝ)) := by
  have hterms : ∀ d ∈ E,
      (|h| / U) ^ 2 ≤ (h / (d : ℝ) - (round (h / (d : ℝ)) : ℝ)) ^ 2 := by
    intro d hd
    obtain ⟨hlo, hhi⟩ := hbounds d hd
    have hdpos : (0 : ℝ) < d := by have := abs_nonneg h; linarith
    rw [round_div_eq_zero h (d : ℝ) hlo, Int.cast_zero, sub_zero]
    have hratio : |h| / U ≤ |h| / (d : ℝ) :=
      div_le_div_of_nonneg_left (abs_nonneg h) hdpos hhi
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |h| / U) hratio 2
    simpa only [div_pow, sq_abs] using hpow
  calc
    (E.card : ℝ) * (|h| / U) ^ 2 = ∑ _d ∈ E, (|h| / U) ^ 2 := by simp
    _ ≤ ∑ d ∈ E, (h / (d : ℝ) - (round (h / (d : ℝ)) : ℝ)) ^ 2 :=
      Finset.sum_le_sum hterms
    _ ≤ residueEnergy D (fun d => h / (d : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (by intros; positivity)

end ReciprocalSquares
