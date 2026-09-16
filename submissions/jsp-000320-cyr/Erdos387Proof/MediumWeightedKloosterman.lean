import Erdos387Proof.PeriodicCompletion
import Erdos387Proof.FourierVariation

/-! The actual tent Fourier weight is summed against the inverse character.
The interval may exceed a full period; all blocks and the endpoint variation
remain visible. No cancellation estimate is an input. -/

namespace Erdos387Proof.MediumWeightedKloosterman

open FourierVariation FiniteAbel
open scoped BigOperators

/-- Partial summation on a fixed factor interval, with the full-modulus
coprimality mask retained in the zero-extended Kloosterman coefficient. -/
theorem norm_sum_tentWeight_inverse_le
    (X M q u A L : ℕ) [NeZero M] [NeZero q]
    (hX : 0 < X) (hu : 0 < u)
    (hcop : Nat.Coprime M q) (hsq : Squarefree q)
    (hlarge : ∀ p ∈ q.primeFactors, 2 < p)
    (b : ZMod (M * q)) (h i : ℤ) (R H : ℝ)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hh : |(h : ℝ)| ≤ H)
    (hi : |i| ≤ (X : ℤ))
    (hbound : (X : ℝ) / (M * q * u * (A + 1) : ℕ) ≤ R) :
    ‖∑ t ∈ Finset.range L,
      tentWeight X h i (M * q * u * (A + t + 1) : ℕ)⁻¹ *
        Erdos387.Kloosterman.coefficient (M * q) b ((A + t + 1 : ℕ) : ZMod (M * q))‖ ≤
      (8 * R + 128 * H * R^2) *
        (((L / (M * q) + 1 : ℕ) : ℝ) *
          PeriodicCompletion.Kloosterman.fixedMulSquarefreeIntervalBound M q hcop b) := by
  let w : ℕ → ℂ := fun t =>
    tentWeight X h i (M * q * u * (A + t + 1) : ℕ)⁻¹
  let f : ℕ → ℂ := fun t =>
    Erdos387.Kloosterman.coefficient (M * q) b ((A + t + 1 : ℕ) : ZMod (M * q))
  let E := PeriodicCompletion.Kloosterman.fixedMulSquarefreeIntervalBound M q hcop b
  have hE : 0 ≤ E := by
    have hzero := PeriodicCompletion.Kloosterman.norm_incompleteInterval_fixed_mul_squarefree_arbitrary
      M q hcop hsq hlarge b 0 0
    simpa only [Nat.zero_div, zero_add, Nat.cast_one, one_mul] using
      (norm_nonneg _).trans hzero
  have hpartial : ∀ m ≤ L, ‖∑ t ∈ Finset.range m, f t‖ ≤
      ((L / (M * q) + 1 : ℕ) : ℝ) * E := by
    intro m hm
    have heq : (∑ t ∈ Finset.range m, f t) =
        Erdos387.Kloosterman.incompleteInterval (M * q) b (A : ℤ) m := by
      rw [← PeriodicCompletion.Kloosterman.intervalSum_coefficient_eq_incompleteInterval]
      unfold PeriodicStripping.intervalSum f
      apply Finset.sum_congr rfl
      intro t ht
      congr 1
      push_cast
      ring
    rw [heq]
    apply (PeriodicCompletion.Kloosterman.norm_incompleteInterval_fixed_mul_squarefree_arbitrary
      M q hcop hsq hlarge b (A : ℤ) m).trans
    apply mul_le_mul_of_nonneg_right _ hE
    exact_mod_cast Nat.add_le_add_right (Nat.div_le_div_right hm) 1
  have hvar : variationMass w L ≤ 8 * R + 128 * H * R^2 := by
    apply variationMass_tentWeight_reciprocal_le X h i
      (fun t => M * q * u * (A + t + 1)) L hX hR hH hh hi
    · intro t
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (NeZero.pos M) (NeZero.pos q)) hu)
        (by omega)
    · intro a b hab
      exact Nat.mul_le_mul_left _ (by omega)
    · simpa only [Nat.add_zero] using hbound
  exact (norm_sum_mul_le_variation w f L hpartial).trans
    (mul_le_mul_of_nonneg_right hvar (mul_nonneg (by positivity) hE))

end Erdos387Proof.MediumWeightedKloosterman
