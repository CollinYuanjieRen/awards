import Erdos387Proof.MediumReciprocalPhase
import Erdos387Proof.MediumComplementGrouping
import Erdos387Proof.MediumSieveEuler
import Erdos387Proof.SquarefreeTupleMultiplicity

/-! Finite geometric and sieve-support properties of the actual enlarged
medium certificates, including the subpower prime-factor budget. -/

namespace Erdos387Proof.MediumComplementBounds

open Erdos387 MediumCertificateCover MediumComplementGrouping MediumReciprocalPhase
open scoped BigOperators

theorem otherValue_le_X {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hC : C ∈ certificates S X z medium large i) : C.val.otherValue i ≤ X := by
  classical
  have hdvd : C.val.otherValue i ∣ C.val.value := by
    rw [← C.val.factor_mul_otherValue i]
    exact dvd_mul_left _ _
  exact (Nat.le_of_dvd C.val.value_pos hdvd).trans (Finset.mem_filter.mp hC).2.1

theorem lower_complement_lt {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hB : 0 < B) (hC : C ∈ certificates S X z medium large i) :
    (X / 2) / (B * large) < C.val.otherValue i := by
  classical
  obtain ⟨_, _, hnear, _, hlarge, _⟩ := Finset.mem_filter.mp hC
  have hl : 0 < large := (C.val.positive i).trans_le hlarge
  apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hB hl)).mpr
  rw [← C.val.factor_mul_otherValue i] at hnear
  calc
    X / 2 < B * (C.val.factor i * C.val.otherValue i) := hnear
    _ ≤ B * (large * C.val.otherValue i) := by gcongr
    _ = _ := by ring

theorem window_product_coprime_complement {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hC : C ∈ certificates S X z medium large i)
    {T : Finset ℕ} (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset) :
    Nat.Coprime (∏ p ∈ T, p) (CoverBPZ.refinementModulus S * C.val.otherValue i) := by
  have hsub := Finset.mem_powerset.mp hT
  have hp : ∀ p ∈ T, p.Prime := fun p h => (MediumSieveEuler.mem_windowPrimes.mp (hsub h)).1
  have hsq : Squarefree (∏ p ∈ T, p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hpT q hqT hne
      change IsRelPrime p q
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hp p hpT) (hp q hqT)).mpr hne
    · intro p hpT
      exact (hp p hpT).squarefree
  have hsupp : ∀ p ∈ (∏ v ∈ T, v).primeFactors,
      max (2 * S.k) 3 ≤ p ∧ p < z := by
    rw [Nat.primeFactors_prod hp]
    intro p hpT
    obtain ⟨_, hlow, hhigh⟩ := MediumSieveEuler.mem_windowPrimes.mp (hsub hpT)
    have hk := S.hk3
    exact ⟨by omega, hhigh⟩
  exact (certificate_sieve_complement_applicability hC hsq hsupp).2.2.2.2.1

theorem subpower_primeFactors_card_le {B K N : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (hN : 0 < N)
    {i : Fin S.k} {C : RefinedTupleCertificate S (SubpowerScale.X N S.k)}
    (hC : C ∈ certificates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) i) :
    (C.val.otherValue i).primeFactors.card ≤ N ^ 2 := by
  exact SquarefreeTupleMultiplicity.primeFactors_card_le_square_of_rough_le_X
    hN (by have := S.hk3; omega) (certificate_otherValue_squarefree hC)
    (certificate_otherValue_rough hC) (otherValue_le_X hC)

end Erdos387Proof.MediumComplementBounds
