import Mathlib

/-!
# Erdős Problem #1074: the Pillai primes are infinite (Erdős–Hardy–Subbarao)

A prime `p` is a *Pillai prime* if there is an `m ≥ 1` with `p ∤ 1 (mod m)`, i.e. `p ≢ 1 (mod m)`,
and `p ∣ m! + 1`; the `m ≥ 1` with such a prime are the *EHS numbers*.  Erdős asked whether the
Pillai primes have a relative density among the primes and whether the EHS numbers have a density
(OPEN; not addressed here).  The problem page records that Erdős, Hardy and Subbarao proved that
both sets are infinite.  This file proves that the set of Pillai primes is infinite, in the exact
shape of the formal-conjectures statement `Erdos1074.erdos_1074.variants.PillaiPrimes_infinite`
(tagged "research solved" with `sorry`), with the definitions `EHSNumbers` and `PillaiPrimes`
copied verbatim.  The infinitude of the EHS numbers (which formal-conjectures links to an
AlphaProof proof) and the density questions are not claimed.

Proof (Hardy–Subbarao, Amer. Math. Monthly 109 (2002), Theorem 2.1, simplified).  For every
`K` let `n = 10K + 7` and pick a prime `p ∣ n! + 1`; then `p > n`.  If `p ≢ 1 (mod n)`, then `p`
is a Pillai prime with witness `n`.  Otherwise `p = 1 + A·n` with `A ≥ 2`; put
`m = p − 1 − n = (A − 1)·n ≥ n`.  By Wilson's theorem and `(p − 1)! = m! · ∏_{i=1}^{n} (m + i)`
with `m + i ≡ −(n + 1 − i) (mod p)`, we get `−1 ≡ (p − 1)! ≡ m! · (−1)^n · n! ≡ m!` (as `n` is odd
and `n! ≡ −1`), so `p ∣ m! + 1`; and `p ≡ 1 (mod m)` would force `(A − 1)·n ∣ A·n`, i.e. `A = 2`
and `p = 2n + 1 = 5·(4K + 3)`, not prime.  Hence `p` is a Pillai prime with witness `m`.  In both
cases there is a Pillai prime larger than `10K + 7`, so the set is unbounded, hence infinite.
-/

namespace Erdos1074

open scoped Nat
open Nat

/-- The EHS numbers (after Erdős, Hardy, and Subbarao) are those $m\geq 1$ such that there
exists a prime $p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$. -/
abbrev EHSNumbers : Set ℕ := {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-- The Pillai primes are those primes $p$ such that there exists an $m \ge 1$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$-/
abbrev PillaiPrimes : Set ℕ := {p | p.Prime ∧ ∃ m ≥ 1, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

end Erdos1074

open Erdos1074

open scoped Nat
open Nat

private lemma prod_range_sub_eq_factorial (n : ℕ) :
    ∏ i ∈ Finset.range n, (n - i) = n ! := by
  rw [← Finset.prod_range_add_one_eq_factorial n, ← Finset.prod_range_reflect (fun j => j + 1) n]
  refine Finset.prod_congr rfl ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  omega

private lemma exists_pillaiPrime_gt (K : ℕ) : ∃ p ∈ PillaiPrimes, K < p := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 10 * K + 7 := ⟨_, rfl⟩
  have hn7 : 7 ≤ n := by omega
  have hnodd : Odd n := ⟨5 * K + 3, by omega⟩
  have hne1 : n ! + 1 ≠ 1 := by have := Nat.factorial_pos n; omega
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = Nat.minFac (n ! + 1) := ⟨_, rfl⟩
  have hp : p.Prime := by rw [hpdef]; exact Nat.minFac_prime hne1
  have hpdvd : p ∣ n ! + 1 := by rw [hpdef]; exact Nat.minFac_dvd _
  have hp1 : 1 < p := hp.one_lt
  have hnp : n < p := by
    by_contra hcon
    have hle : p ≤ n := by omega
    have h1 : p ∣ n ! := (Nat.Prime.dvd_factorial hp).mpr hle
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hpdvd
    have := Nat.le_of_dvd one_pos h2
    omega
  by_cases hcase : p ≡ 1 [MOD n]
  · -- `p ≡ 1 (mod n)`: pass to the smaller witness `m = p - 1 - n`
    obtain ⟨A, hA⟩ : n ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hcase.symm
    have hA2 : 2 ≤ A := by
      by_contra hcon
      have hAv : A = 0 ∨ A = 1 := by omega
      rcases hAv with rfl | rfl
      · omega
      · have h2d : (2 : ℕ) ∣ p := ⟨5 * K + 4, by omega⟩
        rcases hp.eq_one_or_self_of_dvd 2 h2d with h' | h' <;> omega
    obtain ⟨B, rfl⟩ : ∃ B, A = B + 2 := ⟨A - 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = n * (B + 1) := ⟨_, rfl⟩
    have hmn : m + n = p - 1 := by rw [hm, hA]; ring
    have hnm : n ≤ m := by rw [hm]; exact Nat.le_mul_of_pos_right n (by omega)
    have hm1 : 1 ≤ m := by omega
    have inst : Fact p.Prime := ⟨hp⟩
    have hnf : ((n ! : ℕ) : ZMod p) = -1 := by
      have h0 : ((n ! + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpdvd
      rw [Nat.cast_add, Nat.cast_one] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hasc : (((m + 1).ascFactorial n : ℕ) : ZMod p) = -(((n ! : ℕ) : ZMod p)) := by
      rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
      have hstep : ∀ i ∈ Finset.range n,
          (((m + 1 + i : ℕ) : ZMod p)) = -(((n - i : ℕ) : ZMod p)) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have h1 : (m + 1 + i) + (n - i) = p := by omega
        have h2 : (((m + 1 + i) + (n - i) : ℕ) : ZMod p) = 0 := by
          rw [h1]; exact ZMod.natCast_self p
        rw [Nat.cast_add] at h2
        exact eq_neg_of_add_eq_zero_left h2
      have hneg : ∀ i ∈ Finset.range n,
          (-(((n - i : ℕ) : ZMod p))) = (-1 : ZMod p) * (((n - i : ℕ) : ZMod p)) := by
        intro i _; ring
      rw [Finset.prod_congr rfl hstep, Finset.prod_congr rfl hneg, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_range, ← Nat.cast_prod, prod_range_sub_eq_factorial,
        hnodd.neg_one_pow, neg_one_mul]
    have hmfact : ((m ! : ℕ) : ZMod p) = -1 := by
      have hfe : m ! * ((m + 1).ascFactorial n) = (p - 1)! := by
        rw [Nat.factorial_mul_ascFactorial, hmn]
      have hw : (((p - 1)! : ℕ) : ZMod p) = -1 := ZMod.wilsons_lemma p
      rw [← hfe, Nat.cast_mul, hasc, hnf] at hw
      simpa using hw
    have hdvdm : p ∣ m ! + 1 := by
      have h0 : ((m ! + 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_add, Nat.cast_one, hmfact]; ring
      exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    have hnotm : ¬ p ≡ 1 [MOD m] := by
      intro hcon
      have hdm : m ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hcon.symm
      rw [hm, hA] at hdm
      have hdm' : (B + 1) * n ∣ (B + 2) * n := by
        rw [mul_comm (B + 1) n, mul_comm (B + 2) n]; exact hdm
      have hBd : (B + 1) ∣ (B + 2) := Nat.dvd_of_mul_dvd_mul_right (by omega) hdm'
      have hB1 : (B + 1) ∣ 1 := by
        have h := Nat.dvd_sub hBd (dvd_refl (B + 1))
        simpa using h
      have hB0 : B = 0 := by
        have := Nat.le_of_dvd one_pos hB1
        omega
      subst hB0
      have h5 : (5 : ℕ) ∣ p := ⟨4 * K + 3, by omega⟩
      rcases hp.eq_one_or_self_of_dvd 5 h5 with h' | h' <;> omega
    exact ⟨p, ⟨hp, m, hm1, hnotm, hdvdm⟩, by omega⟩
  · exact ⟨p, ⟨hp, n, by omega, hcase, hpdvd⟩, by omega⟩

/-- **Erdős–Hardy–Subbarao**: the set of Pillai primes is infinite (the formal-conjectures shape
`erdos_1074.variants.PillaiPrimes_infinite`). -/
theorem pillaiPrimes_infinite : PillaiPrimes.Infinite := by
  exact Set.infinite_of_forall_exists_gt exists_pillaiPrime_gt

/-- The same statement as a negation (`Set.Infinite` is by definition `¬ Set.Finite`), used as the
graded root because its head symbol is a negation. -/
theorem pillaiPrimes_not_finite : ¬ PillaiPrimes.Finite :=
  pillaiPrimes_infinite
