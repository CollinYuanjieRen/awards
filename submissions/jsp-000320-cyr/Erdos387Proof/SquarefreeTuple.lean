import ErdosProblems.Erdos387.SquarefreeCandidates
import ErdosProblems.Erdos387.DivisorSwitching

/-!
# Squarefree divisor tuples

The squarefree residual condition on a refined candidate passes to every
coordinate of any cover divisor tuple.  Pairwise coprimality of the residual
quotients then passes squarefreeness to the tuple product and to every
complementary product.
-/

namespace Erdos387

open scoped BigOperators

namespace CoverBPZ

theorem coverDivisorTuple_squarefree_data
    {B K X z n : ℕ} (S : BPZSection6Input B K)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (hn : S.k < n)
    (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    (E : CoverDivisorTuple (S.toCoverFactorization hn hprog)) :
    (∀ j : Fin S.k, Squarefree (E.factor j)) ∧
      Squarefree E.value ∧
      ∀ i : Fin S.k, Squarefree (E.otherValue i) := by
  classical
  rw [RefinedSquarefreeCandidates, Finset.mem_filter] at hnSq
  have hquotientSq : ∀ j : Fin S.k,
      Squarefree
        ((n - j.val) /
          (S.toCoverFactorization hn hprog).g j.val) := by
    intro j
    simpa only [BPZSection6Input.toCoverFactorization,
      S.gNat_eq j.isLt] using hnSq.2 j
  have hfactorSq : ∀ j : Fin S.k, Squarefree (E.factor j) := by
    intro j
    exact Squarefree.squarefree_of_dvd (E.divides j) (hquotientSq j)
  have hfactorPairwise : ∀ a b : Fin S.k, a ≠ b →
      Nat.Coprime (E.factor a) (E.factor b) := by
    intro a b hab
    exact Nat.Coprime.of_dvd_right (E.divides b)
      (Nat.Coprime.of_dvd_left (E.divides a)
        (S.coverQuotients_pairwise_coprime hn hprog
          a a.isLt b b.isLt (fun h => hab (Fin.ext h))))
  have hvalueSq : Squarefree E.value := by
    unfold CoverDivisorTuple.value
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro a _ha b _hb hab
      change IsRelPrime (E.factor a) (E.factor b)
      rw [← Nat.coprime_iff_isRelPrime]
      exact hfactorPairwise a b hab
    · intro j _hj
      exact hfactorSq j
  have hotherSq : ∀ i : Fin S.k, Squarefree (E.otherValue i) := by
    intro i
    unfold CoverDivisorTuple.otherValue
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro a _ha b _hb hab
      change IsRelPrime (E.factor a) (E.factor b)
      rw [← Nat.coprime_iff_isRelPrime]
      exact hfactorPairwise a b hab
    · intro j _hj
      exact hfactorSq j
  exact ⟨hfactorSq, hvalueSq, hotherSq⟩

theorem coverDivisorTuple_rough_data
    {B K X z n : ℕ} (S : BPZSection6Input B K)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (hn : S.k < n)
    (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
    (hz : 2 * S.k ≤ z) :
    Nat.Coprime (refinementModulus S) E.value ∧
      ∀ p ∈ E.value.primeFactors, z ≤ p := by
  classical
  have hnData := hnSq
  rw [RefinedSquarefreeCandidates, Finset.mem_filter,
    RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  have hrough : IsZRough z (n.choose S.k) := hnData.1.2
  have hvalueDvd : E.value ∣ n.choose S.k := by
    rw [CoverDivisorTuple.value,
      choose_eq_prod_coverQuotients (S.toCoverFactorization hn hprog),
      ← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_dvd_prod_of_dvd E.factor
      (fun j : Fin S.k =>
        (n - j.val) / (S.toCoverFactorization hn hprog).g j.val)
      (by intro j _hj; exact E.divides j)
  constructor
  · exact coprime_refinementModulus_of_dvd_choose_of_rough
      S hz hrough hvalueDvd
  · intro p hpMem
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hpDvd : p ∣ n.choose S.k :=
      (Nat.dvd_of_mem_primeFactors hpMem).trans hvalueDvd
    by_contra hpz
    exact hrough p hpPrime (by omega) hpDvd

theorem sieve_mul_otherValue_applicability
    {B K X z n g : ℕ} (S : BPZSection6Input B K)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (hn : S.k < n)
    (hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    (E : CoverDivisorTuple (S.toCoverFactorization hn hprog))
    (i : Fin S.k) (hz : 2 * S.k ≤ z)
    (hgSq : Squarefree g)
    (hgSupport : ∀ p ∈ g.primeFactors,
      max (2 * S.k) 3 ≤ p ∧ p < z) :
    Nat.Coprime g (E.otherValue i) ∧
      Squarefree (g * E.otherValue i) ∧
      Nat.Coprime (refinementModulus S) (g * E.otherValue i) ∧
      ∀ p ∈ (g * E.otherValue i).primeFactors, 2 < p := by
  classical
  obtain ⟨hfactorSq, hvalueSq, hotherSq⟩ :=
    coverDivisorTuple_squarefree_data S hnSq hn hprog E
  obtain ⟨hMvalue, hvalueRough⟩ :=
    coverDivisorTuple_rough_data S hnSq hn hprog E hz
  have hDdvd : E.otherValue i ∣ E.value := by
    rw [← E.factor_mul_otherValue i]
    exact dvd_mul_left _ _
  have hDrough : ∀ p ∈ (E.otherValue i).primeFactors, z ≤ p := by
    intro p hpMem
    apply hvalueRough p
    apply Nat.mem_primeFactors.mpr
    exact ⟨Nat.prime_of_mem_primeFactors hpMem,
      (Nat.dvd_of_mem_primeFactors hpMem).trans hDdvd,
      hvalueSq.ne_zero⟩
  have hgD : Nat.Coprime g (E.otherValue i) := by
    by_contra hcop
    obtain ⟨p, hpPrime, hpg, hpD⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpgMem : p ∈ g.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpg, hgSq.ne_zero⟩
    have hpDMem : p ∈ (E.otherValue i).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpD, (hotherSq i).ne_zero⟩
    have hpUpper := (hgSupport p hpgMem).2
    have hpLower := hDrough p hpDMem
    omega
  have hMg : Nat.Coprime (refinementModulus S) g := by
    by_contra hcop
    obtain ⟨p, hpPrime, hpM, hpg⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpSmall :=
      prime_lt_two_mul_k_of_dvd_refinementModulus S hpPrime hpM
    have hpgMem : p ∈ g.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpg, hgSq.ne_zero⟩
    have hpLarge := (hgSupport p hpgMem).1
    omega
  have hMD : Nat.Coprime (refinementModulus S) (E.otherValue i) :=
    Nat.Coprime.of_dvd_right hDdvd hMvalue
  refine ⟨hgD, (Nat.squarefree_mul hgD).2 ⟨hgSq, hotherSq i⟩,
    hMg.mul_right hMD, ?_⟩
  intro p hpMem
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hpDvd : p ∣ g * E.otherValue i :=
    Nat.dvd_of_mem_primeFactors hpMem
  rcases hpPrime.dvd_mul.mp hpDvd with hpg | hpD
  · have hpgMem : p ∈ g.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpg, hgSq.ne_zero⟩
    have hpLower := (hgSupport p hpgMem).1
    omega
  · have hpDMem : p ∈ (E.otherValue i).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpD, (hotherSq i).ne_zero⟩
    have hpLower := hDrough p hpDMem
    have hk3 := S.hk3
    omega

end CoverBPZ

end Erdos387
