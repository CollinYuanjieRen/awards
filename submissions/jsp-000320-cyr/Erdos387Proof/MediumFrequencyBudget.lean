import Erdos387Proof.MediumFourierTail

/-! Explicit finite multiplicities for the truncated sieve, gcd splitting,
compatible roots and common nonzero integer frequencies. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumFrequencyBudget

open Erdos387 IntegerSieveResidues MediumEndpointError
open scoped BigOperators

theorem card_nonzero_window (H : ℕ) :
    ((IntegerFourierWindow.window H).erase 0).card = 2 * H := by
  have hzero : (0 : ℤ) ∈ IntegerFourierWindow.window H := by
    simp [IntegerFourierWindow.window]
  rw [Finset.card_erase_of_mem hzero]
  simp [IntegerFourierWindow.window, Int.card_Icc]
  omega

noncomputable def splitFrequencyCount (g k H : ℕ) : ℕ :=
  ∑ u ∈ g.divisors,
    (localAssignmentResidues (g / u) k).card * ((IntegerFourierWindow.window H).erase 0).card

/-- Squarefreeness controls the number of divisor splittings; the local
root count uses exactly the residual quotient at each splitting. -/
theorem splitFrequencyCount_le {g k H L : ℕ} (hg : Squarefree g)
    (hk : 1 ≤ k) (hL : g.primeFactors.card ≤ L)
    (hlarge : ∀ p ∈ g.primeFactors, k < p) :
    splitFrequencyCount g k H ≤ 2^L * k^L * (2 * H) := by
  classical
  have hcard : g.divisors.card ≤ 2^L := by
    rw [card_divisors_squarefree hg]
    exact Nat.pow_le_pow_right (by norm_num) hL
  unfold splitFrequencyCount
  calc
    _ ≤ ∑ _u ∈ g.divisors, k^L * (2 * H) := by
      apply Finset.sum_le_sum
      intro u hu
      have hvdvd : g / u ∣ g := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hu)
      have hvlarge : ∀ p ∈ (g / u).primeFactors, k < p :=
        fun p hp => hlarge p (Nat.primeFactors_mono hvdvd hg.ne_zero hp)
      have hvcard : (g / u).primeFactors.card ≤ L :=
        (Finset.card_le_card (Nat.primeFactors_mono hvdvd hg.ne_zero)).trans hL
      rw [card_localAssignmentResidues hvlarge, card_nonzero_window]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hk hvcard)
    _ = g.divisors.card * (k^L * (2 * H)) := by simp
    _ ≤ _ := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (k^L * (2*H)) hcard

/-- All prime-subset, gcd, local-root, and nonzero-frequency multiplicities
are present in this actual finite sum. -/
theorem sum_splitFrequencyCount_le {P : Finset ℕ} {z k H L : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hPz : P ⊆ Finset.range z)
    (hz : 1 ≤ z) (hk : 1 ≤ k) (hlarge : ∀ p ∈ P, k < p) :
    (∑ T ∈ P.powerset, if T.card ≤ L then
      splitFrequencyCount (∏ p ∈ T, p) k H else 0) ≤
      (L + 1) * z^L * (2^L * k^L * (2 * H)) := by
  classical
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _T ∈ P.powerset.filter (fun T => T.card ≤ L), 2^L * k^L * (2*H) := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hTP,hTL⟩ := Finset.mem_filter.mp hT
      have hsub := Finset.mem_powerset.mp hTP
      have hprime : ∀ p ∈ T, p.Prime := fun p hp => hP p (hsub hp)
      apply splitFrequencyCount_le (MediumSignedMainTerm.primeSubsetProduct_squarefree hP hsub) hk
      · simpa only [Nat.primeFactors_prod hprime] using hTL
      · simpa only [Nat.primeFactors_prod hprime] using (fun p hp => hlarge p (hsub hp))
    _ = (P.powerset.filter (fun T => T.card ≤ L)).card * (2^L * k^L * (2*H)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_truncated_powerset_le hPz hz)

end Erdos387Proof.MediumFrequencyBudget
