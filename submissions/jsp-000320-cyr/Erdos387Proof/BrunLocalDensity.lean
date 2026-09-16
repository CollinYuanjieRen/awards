import Mathlib

/-!
# Local density after splitting the sieve modulus

These finite identities preserve the signed Brun main term when a varying
coordinate shares prime factors with its sieve modulus. They do not assume
an error-count estimate.
-/

namespace Erdos387Proof

open scoped BigOperators

/-- Removing the common factor identifies the remaining coprimality condition. -/
theorem gcd_mul_split_iff {u v t : ℕ} (hu : 0 < u) :
    Nat.gcd (u * v) (u * t) = u ↔ Nat.Coprime v t := by
  rw [Nat.gcd_mul_left, Nat.Coprime]
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left hu (by simpa using h)
  · intro h
    simp [h]

/-- A squarefree sieve modulus has disjoint factors on either side of the split. -/
theorem squarefree_gcd_split {g u v t : ℕ} (hg : Squarefree g)
    (hguv : g = u * v) :
    Nat.Coprime u v ∧ (Nat.gcd g (u * t) = u ↔ Nat.Coprime v t) := by
  have hs : Squarefree (u * v) := hguv ▸ hg
  have hu : 0 < u := Nat.pos_of_ne_zero (by
    intro h
    simp [h] at hs)
  exact ⟨(Nat.squarefree_mul_iff.mp hs).1, hguv ▸ gcd_mul_split_iff hu⟩

/-- Multiplying local factors and summing over squarefree divisors is a finite
Euler product. -/
theorem sum_divisors_prod_primeFactors {g : ℕ} (hg : Squarefree g)
    (w : ℕ → ℝ) :
    (∑ d ∈ g.divisors, ∏ p ∈ d.primeFactors, w p) =
      ∏ p ∈ g.primeFactors, (1 + w p) := by
  classical
  rw [← Nat.divisors_filter_squarefree_of_squarefree hg,
    Nat.sum_divisors_filter_squarefree hg.ne_zero, Nat.factors_eq]
  change (∑ s ∈ g.primeFactors.powerset,
    ∏ p ∈ s.val.prod.primeFactors, w p) = _
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro s hs
  have hprime : ∀ p ∈ s, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.mp hs) hp)
  rw [s.prod_val, Function.id_def, Nat.primeFactors_prod hprime]

/-- The normalized totient and the prime-factor cardinality have the expected
local product, with no squarefreeness needed. -/
theorem pow_primeFactors_card_mul_totient_div (k d : ℕ) (hd : d ≠ 0) :
    (k : ℝ) ^ d.primeFactors.card * (Nat.totient d : ℝ) / (d : ℝ) =
      ∏ p ∈ d.primeFactors, ((k : ℝ) * (1 - (p : ℝ)⁻¹)) := by
  have htot : (Nat.totient d : ℝ) =
      (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ))
      (Nat.totient_eq_mul_prod_factors d)
    push_cast at h
    exact h
  rw [htot, Finset.prod_mul_distrib, Finset.prod_const]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  field_simp

/-- Exact local density of the coupled coordinate and `k` forbidden residues.
The divisor substitution is retained in the consumer-facing form. -/
theorem squarefree_divisor_local_density (k g : ℕ) (hg : Squarefree g) :
    (∑ u ∈ g.divisors,
      (k : ℝ) ^ (g / u).primeFactors.card *
        (Nat.totient (g / u) : ℝ) / (g / u : ℕ) / (g : ℝ)) =
      ∏ p ∈ g.primeFactors,
        (((k : ℝ) + 1) / p - (k : ℝ) / (p : ℝ) ^ 2) := by
  classical
  rw [← Finset.sum_div]
  rw [Nat.sum_div_divisors g
    (fun d => (k : ℝ) ^ d.primeFactors.card *
      (Nat.totient d : ℝ) / (d : ℝ))]
  have hsum :
      (∑ d ∈ g.divisors,
        (k : ℝ) ^ d.primeFactors.card * (Nat.totient d : ℝ) / (d : ℝ)) =
        ∏ p ∈ g.primeFactors, (1 + (k : ℝ) * (1 - (p : ℝ)⁻¹)) := by
    calc
      _ = ∑ d ∈ g.divisors,
          ∏ p ∈ d.primeFactors, ((k : ℝ) * (1 - (p : ℝ)⁻¹)) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact pow_primeFactors_card_mul_totient_div k d
          (Nat.pos_of_mem_divisors hd).ne'
      _ = _ := sum_divisors_prod_primeFactors hg _
  have hgR : (g : ℝ) = ∏ p ∈ g.primeFactors, (p : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (Nat.prod_primeFactors_of_squarefree hg).symm
    push_cast at h
    exact h
  rw [hsum, hgR]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  field_simp
  ring

end Erdos387Proof
