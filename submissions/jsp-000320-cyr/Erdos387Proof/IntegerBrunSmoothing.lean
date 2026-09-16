import Erdos387Proof.TentFourier
import ErdosProblems.Erdos387.BrunSieve
import ErdosProblems.Erdos387.LocalDensity
import ErdosProblems.Erdos387.Section6Counting
import Erdos387Proof.ConstrainedSieveResidues

/-! A nonnegative even Brun weight on all integers and its finite tent
majorization. Negative integers in the tent support are included explicitly. -/

namespace Erdos387Proof.IntegerBrunSmoothing

open Erdos387 Erdos387Proof.TentFourier
open scoped BigOperators

noncomputable def badPrimes (P : Finset ℕ) (k : ℕ) (n : ℤ) : Finset ℕ :=
  P.filter (fun p => (n % (p : ℤ)).toNat < k)

noncomputable def weight (P : Finset ℕ) (k L : ℕ) (n : ℤ) : ℝ :=
  brunTruncation L (badPrimes P k n).card

theorem weight_nonneg (P : Finset ℕ) (k : ℕ) {L : ℕ} (hL : Even L) (n : ℤ) :
    0 ≤ weight P k L n := by
  unfold weight
  exact_mod_cast brunTruncation_nonneg_of_even (m := (badPrimes P k n).card) hL

theorem weight_eq_one_of_no_bad (P : Finset ℕ) (k L : ℕ) (n : ℤ)
    (hgood : ∀ p ∈ P, k ≤ (n % (p : ℤ)).toNat) : weight P k L n = 1 := by
  have hb : badPrimes P k n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp, hbad⟩ := Finset.mem_filter.mp hp
    exact (not_lt_of_ge (hgood p hp)) hbad
  simp [weight, hb]

/-- Exact signed subset expansion of the everywhere nonnegative weight. -/
theorem weight_eq_sum_subsets (P : Finset ℕ) (k L : ℕ) (n : ℤ) :
    weight P k L n = ∑ T ∈ P.powerset,
      if T ⊆ badPrimes P k n then
        (if T.card ≤ L then (-1 : ℝ)^T.card else 0) else 0 := by
  classical
  have hb : badPrimes P k n ⊆ P := Finset.filter_subset _ _
  have hsum : (∑ T ∈ (badPrimes P k n).powerset,
      if T.card ≤ L then (-1 : ℤ)^T.card else 0) =
      brunTruncation L (badPrimes P k n).card := by
    rw [Finset.sum_powerset_apply_card (x := badPrimes P k n)
      (f := fun j => if j ≤ L then (-1 : ℤ)^j else 0)]
    simp only [nsmul_eq_mul']
    simpa [mul_comm] using
      sum_range_choose_ite_eq_brunTruncation L (badPrimes P k n).card
  have hfilter : (P.powerset.filter fun T => T ⊆ badPrimes P k n) =
      (badPrimes P k n).powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hb, h⟩⟩
  rw [← Finset.sum_filter, hfilter]
  unfold weight
  exact_mod_cast hsum.symm

/-- Original binomial roughness excludes every selected local bad class. -/
theorem no_bad_of_rough {P : Finset ℕ} {k z n : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ k < p ∧ p < z)
    (hkn : k ≤ n) (hrough : IsZRough z (n.choose k)) :
    ∀ p ∈ P, k ≤ ((n : ℤ) % (p : ℤ)).toNat := by
  intro p hp
  obtain ⟨hpp, hkp, hpz⟩ := hP p hp
  simp only [← Int.natCast_mod, Int.toNat_natCast]
  by_contra hbad
  have hlt : n % p < k := by omega
  exact hrough p hpp hpz
    ((prime_dvd_choose_iff_exists_mod_eq hpp hkp hkn).mpr ⟨n % p, hlt, rfl⟩)

noncomputable def weightedMass (P : Finset ℕ) (k L X : ℕ) (R : ℤ → Prop) : ℝ := by
  classical
  exact ∑ n ∈ supportInterval X, tent X n * (if R n then weight P k L n else 0)

noncomputable def subsetMass (P : Finset ℕ) (k X : ℕ) (R : ℤ → Prop)
    (T : Finset ℕ) : ℝ := by
  classical
  exact ∑ n ∈ supportInterval X,
    tent X n * (if R n ∧ T ⊆ badPrimes P k n then (1 : ℝ) else 0)

/-- Every signed sieve coefficient remains outside its exact congruence
mass. This identity makes no inequality or absolute-value replacement. -/
theorem weightedMass_eq_sum_subsets (P : Finset ℕ) (k L X : ℕ) (R : ℤ → Prop) :
    weightedMass P k L X R =
      ∑ T ∈ P.powerset, (if T.card ≤ L then (-1 : ℝ)^T.card else 0) *
        subsetMass P k X R T := by
  classical
  have hterm (n : ℤ) : tent X n * (if R n then weight P k L n else 0) =
      ∑ T ∈ P.powerset, (if T.card ≤ L then (-1 : ℝ)^T.card else 0) *
        (tent X n * (if R n ∧ T ⊆ badPrimes P k n then (1 : ℝ) else 0)) := by
    by_cases hn : R n
    · rw [if_pos hn, weight_eq_sum_subsets, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hbad : T ⊆ badPrimes P k n
      · simp only [hbad, hn, and_self, if_true, mul_one]
        ring
      · simp [hbad]
    · simp [hn]
  unfold weightedMass
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  exact (Finset.mul_sum _ _ _).symm

/-- Smoothing enlarges a finite sifted set using a pointwise nonnegative
weight, before its signed subset expansion is used. -/
theorem card_le_weightedMass (P : Finset ℕ) (k L X : ℕ) (A : Finset ℕ)
    (R : ℤ → Prop) (hX : 0 < X) (hL : Even L)
    (hAX : ∀ n ∈ A, n ≤ X)
    (hR : ∀ n ∈ A, R (n : ℤ))
    (hgood : ∀ n ∈ A, ∀ p ∈ P, k ≤ ((n : ℤ) % (p : ℤ)).toNat) :
    (A.card : ℝ) ≤ weightedMass P k L X R := by
  classical
  let A' : Finset ℤ := A.image (fun n : ℕ => (n : ℤ))
  have hsub : A' ⊆ supportInterval X := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    simp only [supportInterval, Finset.mem_Icc]
    have hmX := hAX m hm
    constructor <;> omega
  have heach : ∀ n ∈ A', tent X n * (if R n then weight P k L n else 0) = 1 := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    rw [if_pos (hR m hm), weight_eq_one_of_no_bad P k L _ (hgood m hm),
      mul_one, tent_eq_one hX (by omega) (by exact_mod_cast hAX m hm)]
  calc
    (A.card : ℝ) = ∑ n ∈ A', tent X n * (if R n then weight P k L n else 0) := by
      rw [Finset.sum_congr rfl heach]
      simp [A', Finset.card_image_of_injective, Nat.cast_injective]
    _ ≤ weightedMass P k L X R := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n hn hnA
      apply mul_nonneg (tent_nonneg X n)
      split
      · exact weight_nonneg P k hL n
      · exact le_rfl

/-- Projecting an integer residue to a divisor works also for negative
integers; all local classes retain canonical natural representatives. -/
theorem residue_mod_divisor (n : ℤ) {g p : ℕ} (hg : 0 < g) (hp : p ∣ g) :
    (n % (g : ℤ)).toNat % p = (n % (p : ℤ)).toNat := by
  have hnonneg : 0 ≤ n % (g : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hg.ne')
  have hcast : (((n % (g : ℤ)).toNat % p : ℕ) : ℤ) = n % (p : ℤ) := by
    rw [Int.natCast_mod, Int.toNat_of_nonneg hnonneg]
    exact Int.emod_emod_of_dvd n (by exact_mod_cast hp)
  exact_mod_cast congrArg Int.toNat hcast

theorem residue_mem_localAssignmentResidues_iff (n : ℤ) {g k : ℕ}
    (hg : Squarefree g) :
    (n % (g : ℤ)).toNat ∈ localAssignmentResidues g k ↔
      ∀ p ∈ g.primeFactors, (n % (p : ℤ)).toNat < k := by
  rw [ConstrainedSieveResidues.mem_localAssignmentResidues_iff hg]
  have hg0 := Nat.pos_of_ne_zero hg.ne_zero
  have hlt : (n % (g : ℤ)).toNat < g := Int.natMod_lt hg.ne_zero
  simp only [hlt, true_and]
  constructor <;> intro h p hp
  · have he := h p hp
    rwa [residue_mod_divisor n hg0 (Nat.dvd_of_mem_primeFactors hp)] at he
  · rw [residue_mod_divisor n hg0 (Nat.dvd_of_mem_primeFactors hp)]
    exact h p hp

end Erdos387Proof.IntegerBrunSmoothing
