import MerLeanExperiment.GaussianResidue
import MerLeanExperiment.IntegerSeparation

namespace ReciprocalSquares

/-- Separation from every integral multiple bounds the normalized nearest-integer residue. -/
theorem residue_sq_lower_of_separation (h d L : ℝ) (hd : 0 < d) (hL : 0 ≤ L)
    (hsep : ∀ z : ℤ, L * d ≤ |h - d * (z : ℝ)|) :
    L ^ 2 ≤ (h / d - (round (h / d) : ℝ)) ^ 2 := by
  have hquot : h / d - (round (h / d) : ℝ) =
      (h - d * (round (h / d) : ℝ)) / d := by field_simp
  have hratio : L ≤ |h / d - (round (h / d) : ℝ)| := by
    rw [hquot, abs_div, abs_of_pos hd]
    exact (le_div_iff₀ hd).mpr (hsep _)
  have hpow := pow_le_pow_left₀ hL hratio 2
  simpa only [sq_abs] using hpow

/-- A finite family uniformly far from multiples supplies residue energy. -/
theorem residueEnergy_ge_card_mul_far_ratio_sq
    (D E : Finset ℕ) (h T U : ℝ) (hE : E ⊆ D) (hT : 0 ≤ T) (hU : 0 < U)
    (hbounds : ∀ d ∈ E, 0 < d ∧ (d : ℝ) ≤ U)
    (hfar : ∀ d ∈ E, ∀ z : ℤ, T ≤ |h - (d : ℝ) * (z : ℝ)|) :
    (E.card : ℝ) * (T / U) ^ 2 ≤ residueEnergy D (fun d => h / (d : ℝ)) := by
  have hterms : ∀ d ∈ E,
      (T / U) ^ 2 ≤ (h / (d : ℝ) - (round (h / (d : ℝ)) : ℝ)) ^ 2 := by
    intro d hd
    obtain ⟨hdpos, hdU⟩ := hbounds d hd
    apply residue_sq_lower_of_separation h (d : ℝ) (T / U)
      (by exact_mod_cast hdpos) (div_nonneg hT hU.le)
    intro z
    have hscale : T / U * (d : ℝ) ≤ T := by
      calc
        T / U * (d : ℝ) ≤ T / U * U :=
          mul_le_mul_of_nonneg_left hdU (div_nonneg hT hU.le)
        _ = T := div_mul_cancel₀ T hU.ne'
    exact hscale.trans (hfar d hd z)
  calc
    (E.card : ℝ) * (T / U) ^ 2 = ∑ _d ∈ E, (T / U) ^ 2 := by simp
    _ ≤ ∑ d ∈ E, (h / (d : ℝ) - (round (h / (d : ℝ)) : ℝ)) ^ 2 :=
      Finset.sum_le_sum hterms
    _ ≤ residueEnergy D (fun d => h / (d : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (by intros; positivity)

/-- A missing factor converts integer separation into a uniform squared residue. -/
theorem missing_factor_residue_sq_lower (h M H : ℤ) (b P : ℕ)
    (hbpos : 0 < b) (hPpos : 0 < P) (hPM : (P : ℤ) ∣ M)
    (hbM : ¬ (b : ℤ) ∣ M) (hnear : |h - M| ≤ H) (hscale : 2 * H ≤ (P : ℤ)) :
    (1 : ℝ) / (4 * (b : ℝ) ^ 2) ≤
      ((h : ℝ) / ((b * P : ℕ) : ℝ) -
        (round ((h : ℝ) / ((b * P : ℕ) : ℝ)) : ℝ)) ^ 2 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hPR : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hbound := residue_sq_lower_of_separation (h : ℝ) ((b * P : ℕ) : ℝ)
    (1 / (2 * (b : ℝ))) (by positivity) (by positivity) (by
      intro z
      have hsep := missing_factor_separation h M (b : ℤ) (P : ℤ) H
        hPM hbM hnear hscale z
      have hsepR : (P : ℝ) ≤ 2 * |(h : ℝ) - (b : ℝ) * (P : ℝ) * (z : ℝ)| := by
        exact_mod_cast hsep
      have hid : (1 / (2 * (b : ℝ))) * ((b * P : ℕ) : ℝ) = (P : ℝ) / 2 := by
        push_cast
        field_simp
      rw [hid]
      push_cast
      nlinarith [hsepR])
  convert hbound using 1
  ring

end ReciprocalSquares
