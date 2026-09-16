import Erdos387Proof.MediumZeroMode
import Erdos387Proof.BrunTruncation

/-! Reassemble the signed local main terms before estimating errors.
In particular the result contains the truncated Brun sum, not its absolute
coefficient sum. -/

namespace Erdos387Proof.MediumSignedMainTerm

open Erdos387 MediumZeroMode
open scoped BigOperators

noncomputable def coefficient (L : ℕ) (T : Finset ℕ) : ℝ :=
  if T.card ≤ L then (-1 : ℝ) ^ T.card else 0

noncomputable def prefactor (Q A B : ℕ) (mass : ℝ) : ℝ :=
  (mass / Q) * ((Nat.totient Q : ℝ) / Q) * Real.log ((B : ℝ) / A)

theorem sum_mainTerm_eq_brun (P : Finset ℕ) (k L Q A B : ℕ) (mass : ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ T ∈ P.powerset, coefficient L T * mainTerm (∏ p ∈ T, p) Q k A B mass) =
      prefactor Q A B mass * brunSubsetSum P (MediumSieveEuler.alpha k) L := by
  classical
  unfold brunSubsetSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hprime : ∀ p ∈ T, p.Prime := fun p hp => hP p (Finset.mem_powerset.mp hT hp)
  have hpf := Nat.primeFactors_prod hprime
  unfold mainTerm coefficient prefactor subsetMonomial
  rw [hpf]
  split_ifs <;> ring

theorem primeSubsetProduct_squarefree {P T : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hT : T ⊆ P) : Squarefree (∏ p ∈ T, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hne
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hP p (hT hp)) (hP q (hT hq))).mpr hne
  · intro p hp
    exact (hP p (hT hp)).squarefree

/-- Only harmonic endpoint errors are bounded termwise. Every local main
term keeps its original sign through the exact Brun recombination. -/
theorem abs_sum_zeroMode_sub_brun_le (P : Finset ℕ) (k L Q A B : ℕ)
    (mass : ℝ) (hmass : 0 ≤ mass) (hQ : 0 < Q) (hA : 0 < A) (hAB : A ≤ B)
    (hP : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, Nat.Coprime Q p) :
    |(∑ T ∈ P.powerset, coefficient L T * zeroMode (∏ p ∈ T, p) Q k A B mass) -
        prefactor Q A B mass * brunSubsetSum P (MediumSieveEuler.alpha k) L| ≤
      ∑ T ∈ P.powerset, if T.card ≤ L then
        endpointError (∏ p ∈ T, p) Q k A mass else 0 := by
  classical
  rw [← sum_mainTerm_eq_brun P k L Q A B mass hP, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  have hsub := Finset.mem_powerset.mp hT
  have hcopT : Nat.Coprime Q (∏ p ∈ T, p) := by
    apply Nat.Coprime.prod_right
    intro p hp
    exact hcop p (hsub hp)
  have he := abs_zeroMode_sub_mainTerm_le (k := k)
    (primeSubsetProduct_squarefree hP hsub) hQ hcopT hA hAB mass hmass
  rw [← mul_sub, abs_mul]
  by_cases hTL : T.card ≤ L
  · simpa [coefficient, hTL, abs_pow] using he
  · simp [coefficient, hTL]

end Erdos387Proof.MediumSignedMainTerm
