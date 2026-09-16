import MerLeanExperiment.MiddleDenominators
import MerLeanExperiment.ResidueLowerBounds
import MerLeanExperiment.FrequencySummation

namespace ReciprocalSquares

/-- The concrete middle-frequency denominator interval supplies a uniform
lower bound for the residue energy. -/
theorem middle_frequency_residueEnergy_lower (M : ℕ) (hM : 262144 ≤ M)
    (h : ℤ) (hlo : (M : ℝ) ^ 20 ≤ 2 * |(h : ℝ)|)
    (hhi : |(h : ℝ)| ≤ (M : ℝ) ^ 360) :
    (M : ℝ) ^ 9 / 1024 ≤
      residueEnergy (squareD (M ^ 10)) (fun d => (h : ℝ) / (d : ℝ)) := by
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hloNat : (M ^ 10) ^ 2 ≤ 2 * h.natAbs := by
    exact_mod_cast (show ((M : ℝ) ^ 10) ^ 2 ≤ 2 * (h.natAbs : ℝ) by
      simpa only [habs, ← pow_mul] using hlo)
  have hhiNat : h.natAbs ≤ (M ^ 10) ^ 36 := by
    exact_mod_cast (show (h.natAbs : ℝ) ≤ ((M : ℝ) ^ 10) ^ 36 by
      simpa only [habs, ← pow_mul] using hhi)
  obtain ⟨E, hE, hcard, hbounds⟩ := exists_middle_denominators M h.natAbs hM hloNat hhiNat
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hhpos : 0 < |(h : ℝ)| := by
    have : (0 : ℝ) < (M : ℝ) ^ 20 := pow_pos hMpos 20
    linarith
  have henergy := residueEnergy_ge_card_mul_ratio_sq (squareD (M ^ 10)) E
    (h : ℝ) (32 * |(h : ℝ)|) hE (by positivity) (by
      intro d hd
      obtain ⟨hdlo, hdhi⟩ := hbounds d hd
      constructor
      · rw [← habs]
        exact_mod_cast hdlo
      · rw [← habs]
        exact_mod_cast hdhi)
  have hratio : |(h : ℝ)| / (32 * |(h : ℝ)|) = (1 / 32 : ℝ) := by
    field_simp [ne_of_gt hhpos]
  have hcardReal : (M : ℝ) ^ 9 ≤ (E.card : ℝ) := by exact_mod_cast hcard
  rw [hratio] at henergy
  nlinarith

/-- Middle frequencies have exponentially small centered Bernoulli product. -/
theorem middle_frequency_norm_centeredProduct_le (M : ℕ) (hM : 262144 ≤ M)
    (p κ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ p * (1 - p))
    (h : ℤ) (hlo : (M : ℝ) ^ 20 ≤ 2 * |(h : ℝ)|)
    (hhi : |(h : ℝ)| ≤ (M : ℝ) ^ 360) :
    ‖centeredProduct (squareD (M ^ 10)) p h‖ ≤
      Real.exp (-κ * (M : ℝ) ^ 9 / 128) := by
  have hbound := norm_centeredProduct_le_of_energy_lower (squareD (M ^ 10))
    p κ ((M : ℝ) ^ 9 / 1024) h hp0 hp1 hκ0 hκ
    (middle_frequency_residueEnergy_lower M hM h hlo hhi)
  convert hbound using 1
  congr 1
  ring

end ReciprocalSquares
