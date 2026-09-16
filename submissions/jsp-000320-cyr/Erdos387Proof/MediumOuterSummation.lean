import Erdos387Proof.MediumCompletionShape
import Erdos387Proof.MediumFrequencyBudget
import Erdos387Proof.MediumTotalEnvelope

/-! Sum the actual finite sieve/frequency multiplicities against the two
complementary completion shapes. No exponential-sum bound is assumed. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumOuterSummation

open Erdos387 Erdos387.CoverBPZ MediumComplementGrouping MediumFrequencyBudget
open MediumCompletionShape MediumTotalEnvelope
open scoped BigOperators

noncomputable def coefficient (B M X z L W H : ℕ) : ℝ :=
  (48 * B + 4608 * (H : ℝ) * (B : ℝ)^2) *
    (Real.log (M * X * z^L : ℕ) + 1) * (4 : ℝ)^(W+L) * z^L * H * M

theorem coefficient_nonneg (B M X z L W H : ℕ) :
    0 ≤ coefficient B M X z L W H := by
  unfold coefficient
  positivity

theorem sum_multiplicities_le {k z L H : ℕ} (hk : 1 ≤ k) (hz : 1 ≤ z) :
    ((∑ T ∈ (MediumSieveEuler.windowPrimes k z).powerset,
      if T.card ≤ L then splitFrequencyCount (∏ p ∈ T, p) k H else 0 : ℕ) : ℝ) ≤
      ((L : ℝ)+1) * (z : ℝ)^L * 2^L * (k : ℝ)^L * (2*H) := by
  have h := sum_splitFrequencyCount_le (P := MediumSieveEuler.windowPrimes k z)
    (k := k) (z := z) (L := L) (H := H)
    (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
    (fun p hp => Finset.mem_range.mpr (MediumSieveEuler.mem_windowPrimes.mp hp).2.2)
    hz hk (fun p hp => by have := (MediumSieveEuler.mem_windowPrimes.mp hp).2.1; omega)
  exact_mod_cast (show (∑ T ∈ (MediumSieveEuler.windowPrimes k z).powerset,
      if T.card ≤ L then splitFrequencyCount (∏ p ∈ T, p) k H else 0) ≤
      (L+1)*z^L*2^L*k^L*(2*H) by simpa only [Nat.mul_assoc] using h)

theorem sum_completion_multiplicities_le {B K X z medium large L W H : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) (hz : 1 ≤ z) :
    (∑ i : Fin S.k, ∑ c ∈ (vectors S X z medium large i).attach,
      ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        if T.card ≤ L then (splitFrequencyCount (∏ p ∈ T, p) S.k H : ℝ) *
          coefficient B (refinementModulus S) X z L W H *
            shape X ((representative c).val.otherValue i) else 0) ≤
      totalEnvelope S X z medium large L W H := by
  classical
  let A : ℝ := ((L : ℝ)+1) * (z : ℝ)^L * 2^L * (S.k : ℝ)^L * (2*H)
  let C : ℝ := coefficient B (refinementModulus S) X z L W H
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := coefficient_nonneg _ _ _ _ _ _ _
  have hcount := sum_multiplicities_le (H := H) (L := L)
    (show 1 ≤ S.k by have := S.hk3; omega) hz
  have hpoint (i : Fin S.k) (c : {a // a ∈ vectors S X z medium large i}) :
      (∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        if T.card ≤ L then (splitFrequencyCount (∏ p ∈ T, p) S.k H : ℝ) * C *
          shape X ((representative c).val.otherValue i) else 0) ≤
        A * C * shape X ((representative c).val.otherValue i) := by
    have heq : (∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        if T.card ≤ L then (splitFrequencyCount (∏ p ∈ T, p) S.k H : ℝ) * C *
          shape X ((representative c).val.otherValue i) else 0) =
        ((∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
          if T.card ≤ L then splitFrequencyCount (∏ p ∈ T, p) S.k H else 0 : ℕ) : ℝ) *
            C * shape X ((representative c).val.otherValue i) := by
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T hT
      split_ifs <;> simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hC)
      (by unfold shape; positivity)
  calc
    _ ≤ ∑ i : Fin S.k, ∑ c ∈ (vectors S X z medium large i).attach,
        A * C * shape X ((representative c).val.otherValue i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (fun c hc => hpoint i c)
    _ ≤ ∑ _i : Fin S.k, A * C * MediumOscillatoryMass.envelope S X z medium large := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (MediumOscillatoryMass.sum_completion_shape_le i hB)
        (mul_nonneg hA hC)
    _ = totalEnvelope S X z medium large L W H := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [totalEnvelope, budget, A, C, coefficient]
      push_cast
      ring

end Erdos387Proof.MediumOuterSummation
