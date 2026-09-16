import MerLeanExperiment.SquareModulus
import Mathlib.Data.Nat.GCD.BigOperators

namespace ReciprocalSquares

theorem prime_square_product_dvd (S : Finset ℕ) (n : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ^ 2 ∣ n) :
    (S.prod id) ^ 2 ∣ n := by
  classical
  revert hprime hdiv
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    intro hprime hdiv
    have hp := hprime p (Finset.mem_insert_self _ _)
    have hcop : Nat.Coprime p (S.prod id) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hqprime := hprime q (Finset.mem_insert_of_mem hq)
      apply hp.coprime_iff_not_dvd.mpr
      intro hpq
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
      exact hpS (heq.symm ▸ hq)
    have hcop2 : Nat.Coprime (p ^ 2) ((S.prod id) ^ 2) := by
      rw [Nat.coprime_pow_left_iff (by decide), Nat.coprime_pow_right_iff (by decide)]
      exact hcop
    rw [Finset.prod_insert hpS, id_eq, mul_pow]
    exact hcop2.mul_dvd_of_dvd_of_dvd (hdiv p (Finset.mem_insert_self _ _))
      (ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
        (fun q hq => hdiv q (Finset.mem_insert_of_mem hq)))

/-- A smooth base is coprime to every large-prime subset product. -/
theorem smoothRoot_coprime_large_product {N a : ℕ} (ha : a ∈ smoothRoots N)
    (S : Finset ℕ) (hS : S ⊆ largePrimes N) : Nat.Coprime a (S.prod id) := by
  apply Nat.Coprime.prod_right
  intro p hp
  have hpprime := largePrimes_prime (hS hp)
  apply Nat.Coprime.symm
  apply hpprime.coprime_iff_not_dvd.mpr
  intro hpa
  have hsmall := Nat.mem_smoothNumbers'.mp (Finset.mem_filter.mp ha).2 p hpprime hpa
  have hlarge := (Finset.mem_filter.mp (hS hp)).2
  omega

/-- Divisibility by all individual base and prime-square factors suffices for
divisibility by the actual common modulus. Coprimality is proved from the construction. -/
theorem squareModulus_dvd_of_factors (N n : ℕ)
    (hB : ∀ b ∈ squareB N, b ∣ n) (hQ : ∀ q ∈ squareQ N, q ∣ n) :
    squareModulus N ∣ n := by
  apply Finset.lcm_dvd
  intro d hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hd).1
  obtain ⟨⟨b, S⟩, hpair, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hb, hS⟩ := Finset.mem_product.mp hpair
  have hsub := Finset.mem_powerset.mp hS
  have hbdiv := hB (b ^ 2) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  have hproddiv : (S.prod id) ^ 2 ∣ n := prime_square_product_dvd S n
    (fun p hp => largePrimes_prime (hsub hp))
    (fun p hp => hQ (p ^ 2) (Finset.mem_image.mpr ⟨p, hsub hp, rfl⟩))
  have hcop : Nat.Coprime (b ^ 2) ((S.prod id) ^ 2) := by
    rw [Nat.coprime_pow_left_iff (by decide), Nat.coprime_pow_right_iff (by decide)]
    exact smoothRoot_coprime_large_product hb S hsub
  simpa only [rootProduct, mul_pow, id_eq] using
    hcop.mul_dvd_of_dvd_of_dvd hbdiv hproddiv

theorem squareModulus_int_dvd_of_factors (N : ℕ) (M : ℤ)
    (hB : ∀ b ∈ squareB N, (b : ℤ) ∣ M)
    (hQ : ∀ q ∈ squareQ N, (q : ℤ) ∣ M) :
    (squareModulus N : ℤ) ∣ M := by
  apply Int.natCast_dvd.mpr
  exact squareModulus_dvd_of_factors N M.natAbs
    (fun b hb => Int.natCast_dvd.mp (hB b hb))
    (fun q hq => Int.natCast_dvd.mp (hQ q hq))

/-- A nearby integer at a nonzero centered frequency must miss a construction factor. -/
theorem exists_missing_factor_of_near (N : ℕ) (h M H : ℤ)
    (hlarge : H < |h|) (hcenter : 2 * |h| ≤ (squareModulus N : ℤ))
    (hnear : |h - M| ≤ H) :
    ∃ b ∈ squareB N ∪ squareQ N, ¬ (b : ℤ) ∣ M := by
  classical
  by_contra hnone
  push Not at hnone
  have hdiv : (squareModulus N : ℤ) ∣ M := squareModulus_int_dvd_of_factors N M
    (fun b hb => hnone b (Finset.mem_union_left _ hb))
    (fun q hq => hnone q (Finset.mem_union_right _ hq))
  have hMne : M ≠ 0 := by
    intro heq
    subst M
    simp only [sub_zero] at hnear
    omega
  have hlower := Int.le_abs_of_dvd hMne hdiv
  have hupper : |M| ≤ |h| + |h - M| := by
    calc
      |M| = |h - (h - M)| := by congr 1; ring
      _ ≤ |h| + |h - M| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le h (-(h - M))
  omega

end ReciprocalSquares
