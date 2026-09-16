/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Erdos387Proof.SquarefreeTuple
import ErdosProblems.Erdos387.RoughDivisorFamily
import ErdosProblems.Erdos387.SubpowerScale

/-!
# Multiplicity of squarefree tuples with a fixed product

A positive pairwise-coprime tuple with squarefree product `D` is determined
by assigning every prime factor of `D` to its unique coordinate.  This gives
an exact finite multiplicity bound and, on the subpower scale, the uniform
`k^(N^2)` envelope needed when several complementary tuples have the same
product.
-/

namespace Erdos387Proof

open Erdos387
open scoped BigOperators ArithmeticFunction.Omega

namespace SquarefreeTupleMultiplicity

/-- A finite family of positive pairwise-coprime tuples with fixed squarefree
product has at most one member for each assignment of the prime factors of
the product to coordinates. -/
theorem card_le_card_pow_primeFactors_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → ℕ)) (D : ℕ)
    (hDsq : Squarefree D)
    (hpos : ∀ f ∈ A, ∀ i, 0 < f i)
    (hpair : ∀ f ∈ A, ∀ i j, i ≠ j → Nat.Coprime (f i) (f j))
    (hprod : ∀ f ∈ A, ∏ i, f i = D) :
    A.card ≤ Fintype.card ι ^ D.primeFactors.card := by
  classical
  have hownerExists : ∀ f : A, ∀ p : D.primeFactors,
      ∃ i : ι, p.1 ∣ f.1 i := by
    intro f p
    have hpPrime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
    have hpD : p.1 ∣ D := Nat.dvd_of_mem_primeFactors p.2
    have hpProd : p.1 ∣ ∏ i, f.1 i := by
      simpa only [hprod f.1 f.2] using hpD
    obtain ⟨i, _hi, hpi⟩ :=
      (hpPrime.prime.dvd_finsetProd_iff (fun i : ι => f.1 i)).mp hpProd
    exact ⟨i, hpi⟩
  let owner : A → D.primeFactors → ι := fun f p =>
    Classical.choose (hownerExists f p)
  have hownerDvd : ∀ f : A, ∀ p : D.primeFactors,
      p.1 ∣ f.1 (owner f p) := by
    intro f p
    exact Classical.choose_spec (hownerExists f p)
  have hownerUnique : ∀ f : A, ∀ p : D.primeFactors, ∀ i : ι,
      p.1 ∣ f.1 i → owner f p = i := by
    intro f p i hpi
    by_contra hne
    have hcop := hpair f.1 f.2 (owner f p) i hne
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p.1, Nat.prime_of_mem_primeFactors p.2,
        hownerDvd f p, hpi⟩) hcop
  have hownerInjective : Function.Injective owner := by
    intro f g hfg
    apply Subtype.ext
    funext i
    have hfDvd : f.1 i ∣ D := by
      rw [← hprod f.1 f.2]
      exact Finset.dvd_prod_of_mem f.1 (Finset.mem_univ i)
    have hgDvd : g.1 i ∣ D := by
      rw [← hprod g.1 g.2]
      exact Finset.dvd_prod_of_mem g.1 (Finset.mem_univ i)
    have hfSq : Squarefree (f.1 i) := hDsq.squarefree_of_dvd hfDvd
    have hgSq : Squarefree (g.1 i) := hDsq.squarefree_of_dvd hgDvd
    rw [← Nat.prod_primeFactors_of_squarefree hfSq,
      ← Nat.prod_primeFactors_of_squarefree hgSq]
    congr 1
    ext p
    constructor
    · intro hpF
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpF
      have hpFi : p ∣ f.1 i := Nat.dvd_of_mem_primeFactors hpF
      have hpD : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr
        ⟨hpPrime, hpFi.trans hfDvd, hDsq.ne_zero⟩
      let pp : D.primeFactors := ⟨p, hpD⟩
      have hfOwner : owner f pp = i := hownerUnique f pp i hpFi
      have hgOwner : owner g pp = i := by
        calc
          owner g pp = owner f pp := (congrFun hfg pp).symm
          _ = i := hfOwner
      have hpGi : p ∣ g.1 i := by
        rw [← hgOwner]
        exact hownerDvd g pp
      exact Nat.mem_primeFactors.mpr
        ⟨hpPrime, hpGi, (hpos g.1 g.2 i).ne'⟩
    · intro hpG
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpG
      have hpGi : p ∣ g.1 i := Nat.dvd_of_mem_primeFactors hpG
      have hpD : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr
        ⟨hpPrime, hpGi.trans hgDvd, hDsq.ne_zero⟩
      let pp : D.primeFactors := ⟨p, hpD⟩
      have hgOwner : owner g pp = i := hownerUnique g pp i hpGi
      have hfOwner : owner f pp = i := by
        calc
          owner f pp = owner g pp := congrFun hfg pp
          _ = i := hgOwner
      have hpFi : p ∣ f.1 i := by
        rw [← hfOwner]
        exact hownerDvd f pp
      exact Nat.mem_primeFactors.mpr
        ⟨hpPrime, hpFi, (hpos f.1 f.2 i).ne'⟩
  have hcard := Fintype.card_le_of_injective owner hownerInjective
  simpa only [Fintype.card_coe, Fintype.card_fun] using hcard

/-- Specialization to the `k-1` coordinates complementary to `i`. -/
theorem card_complement_tuples_le_pow_primeFactors_card
    {k D : ℕ} (i : Fin k)
    (A : Finset ({j : Fin k // j ≠ i} → ℕ))
    (hDsq : Squarefree D)
    (hpos : ∀ f ∈ A, ∀ j, 0 < f j)
    (hpair : ∀ f ∈ A, ∀ a b, a ≠ b → Nat.Coprime (f a) (f b))
    (hprod : ∀ f ∈ A, ∏ j, f j = D) :
    A.card ≤ (k - 1) ^ D.primeFactors.card := by
  simpa only [Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Fintype.card_fin] using
      card_le_card_pow_primeFactors_card A D hDsq hpos hpair hprod

/-- The full subpower endpoint is strictly below the next `z`-power. -/
theorem X_lt_z_pow_square_succ
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    SubpowerScale.X N k <
      SubpowerScale.z N k ^ (N ^ 2 + 1) := by
  have hrough : 0 < SubpowerScale.roughPower N k :=
    SubpowerScale.roughPower_pos hN hk
  have hExp : BPZScale.xExp k * N ^ (2 * k + 5) =
      SubpowerScale.roughPower N k * N ^ 2 := by
    unfold SubpowerScale.roughPower
    rw [show N ^ (2 * k + 5) = N ^ (2 * k + 3) * N ^ 2 by
      simpa using pow_add N (2 * k + 3) 2]
    ring
  rw [SubpowerScale.X_eq_pow_two, SubpowerScale.z, ← pow_mul, hExp]
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr (by
    nlinarith)

/-- A rough number below the subpower endpoint has at most `N^2` distinct
prime factors. -/
theorem primeFactors_card_le_square_of_rough_le_X
    {N k D : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hDsq : Squarefree D)
    (hDrough : IsZRough (SubpowerScale.z N k) D)
    (hDX : D ≤ SubpowerScale.X N k) :
    D.primeFactors.card ≤ N ^ 2 := by
  have hz : 1 < SubpowerScale.z N k :=
    SubpowerScale.two_le_z hN hk
  have hDPow : D < SubpowerScale.z N k ^ (N ^ 2 + 1) :=
    hDX.trans_lt (X_lt_z_pow_square_succ hN hk)
  exact (primeFactors_card_le_cardFactors D).trans
    (cardFactors_le_of_rough_lt_pow hz hDsq.ne_zero hDrough hDPow)

/-- For a complementary tuple with fixed squarefree rough product below
`X`, all multiplicity is absorbed by `k^(N^2)`. -/
theorem card_complement_tuples_le_k_pow_square
    {N k D : ℕ} (hN : 0 < N) (hk : 0 < k) (i : Fin k)
    (A : Finset ({j : Fin k // j ≠ i} → ℕ))
    (hDsq : Squarefree D)
    (hDrough : IsZRough (SubpowerScale.z N k) D)
    (hDX : D ≤ SubpowerScale.X N k)
    (hpos : ∀ f ∈ A, ∀ j, 0 < f j)
    (hpair : ∀ f ∈ A, ∀ a b, a ≠ b → Nat.Coprime (f a) (f b))
    (hprod : ∀ f ∈ A, ∏ j, f j = D) :
    A.card ≤ k ^ (N ^ 2) := by
  have homega : D.primeFactors.card ≤ N ^ 2 :=
    primeFactors_card_le_square_of_rough_le_X hN hk hDsq hDrough hDX
  calc
    A.card ≤ (k - 1) ^ D.primeFactors.card :=
      card_complement_tuples_le_pow_primeFactors_card i A hDsq hpos hpair hprod
    _ ≤ k ^ D.primeFactors.card :=
      Nat.pow_le_pow_left (Nat.sub_le k 1) _
    _ ≤ k ^ (N ^ 2) := Nat.pow_le_pow_right (by omega) homega

end SquarefreeTupleMultiplicity

end Erdos387Proof
