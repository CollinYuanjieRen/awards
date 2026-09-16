import Jsp285.DivisorExtraction

/-! Quantitative and value bounds for occurrence-preserving divisor extraction. -/

namespace Jsp285

/-- The factor list gives a logarithmic fixed charge and a linear divisor charge. -/
theorem exists_divisorExtraction {ι : Type*} [DecidableEq ι]
    (B L K : ℕ) (hB : 0 < B) (Y : Finset ι) (v : ι → ℕ) :
    ∃ d : ℕ, ∃ Z : Finset ι, ∃ w : ι → ℕ,
      0 < d ∧ d ≤ B ∧ Z ⊆ Y ∧
      (∀ i ∈ Z, d * w i = v i) ∧
      Y.card - Z.card ≤ L * Nat.log 2 B + K * B ∧
      ∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e ≤ (Z.filter fun i ↦ ¬e ∣ w i).card := by
  obtain ⟨d, Z, w, factors, hd, hdprod, hfactors, hdB, hZY,
    hscale, hloss, hdiverse⟩ := exists_divisorExtractionAux B L K 1 (by omega) hB Y v
  refine ⟨d, Z, w, hd, by simpa using hdB, hZY, hscale, ?_, ?_⟩
  · calc
      Y.card - Z.card ≤ L * factors.length + K * factors.sum := hloss
      _ ≤ L * Nat.log 2 B + K * B := by
        apply Nat.add_le_add
        · apply Nat.mul_le_mul_left
          exact (Erdos344.length_le_log_prod_of_one_lt factors hfactors).trans
            (Nat.log_mono_right (by simpa [hdprod] using hdB))
        · apply Nat.mul_le_mul_left
          exact (Erdos344.sum_le_prod_of_one_lt factors hfactors).trans
            (by simpa [hdprod] using hdB)
  · intro e he hde
    exact hdiverse e he (by simpa using hde)

/-- Exact scaling transfers the original positive box to the normalized weights. -/
lemma normalized_weight_bounds {ι : Type*} {v w : ι → ℕ} {Y Z : Finset ι}
    {d n : ℕ} (hd : 0 < d) (hZY : Z ⊆ Y)
    (hbox : ∀ i ∈ Y, 0 < v i ∧ v i ≤ n)
    (hscale : ∀ i ∈ Z, d * w i = v i) :
    ∀ i ∈ Z, 0 < w i ∧ w i ≤ n / d := by
  intro i hi
  obtain ⟨hpos, hle⟩ := hbox i (hZY hi)
  have heq := hscale i hi
  constructor
  · by_contra h
    have : w i = 0 := by omega
    simp [this] at heq
    omega
  · apply (Nat.le_div_iff_mul_le hd).mpr
    nlinarith

end Jsp285
