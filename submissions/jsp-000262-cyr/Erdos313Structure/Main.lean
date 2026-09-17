import Mathlib

/-!
# Erdős Problem #313: the denominator of a solution is the product of its primes

Erdős asked whether there are infinitely many solutions of
`1/p₁ + ⋯ + 1/p_k = 1 − 1/m` with `m ≥ 2` an integer and `p₁ < ⋯ < p_k` distinct primes
(OPEN; not addressed here).  The problem page records the elementary structural fact:
"It is clear that we must have `m = p₁ ⋯ p_k`, and hence in particular there is at most one
solution for each `m`."  This file proves that fact for the formal-conjectures solution set
`Erdos313.erdos313Solutions` (copied verbatim): every solution `(m, P)` has `m = ∏_{p ∈ P} p`,
and two solutions with the same `m` have the same prime set.  The infinitude question is not
claimed.

Proof.  Put `N = ∏_{p ∈ P} p` and `S = ∑_{p ∈ P} N / p`; clearing denominators in
`∑ 1/p = 1 − 1/m` gives `S · m = N · (m − 1)` in `ℕ`.  For each `p ∈ P` we have `p ∤ S`
(all terms but `N / p` are divisible by `p`, and `p ∤ N / p` since the primes are distinct), so
`N` and `S` are coprime; from `N ∣ S · m` we get `N ∣ m`, and rewriting the identity as
`m · (N − S) = N` gives `m ∣ N`; thus `m = N`.  Uniqueness:
`P = (∏ P).primeFactors = m.primeFactors = Q`.
-/

namespace Erdos313

/--
This set contains all solutions `(m, P)` to the Erdős problem 313.
A solution is a pair where `m` is an integer `≥ 2` and `P` is a non-empty, finite set of
distinct prime numbers, such that the sum of the reciprocals of the primes in `P` equals `1 - 1/m`.
-/
def erdos313Solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

end Erdos313

open Erdos313

/-- If `p` is a member of `P` then dividing the product `∏ r ∈ P, r` by `p` removes exactly the
factor `p`. -/
private lemma erdos313_prod_div_erase {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) (hp0 : 0 < p) :
    (∏ r ∈ P, r) / p = ∏ r ∈ P.erase p, r := by
  conv_lhs => rw [← Finset.mul_prod_erase P (fun r => r) hp]
  exact Nat.mul_div_cancel_left _ hp0

/-- For a finite set `P` of primes and `p ∈ P`, the "numerator" `∑ q ∈ P, (∏ r ∈ P, r) / q` is not
divisible by `p`: every summand except the one for `q = p` still contains the factor `p`, while
`(∏ r ∈ P, r) / p` is a product of primes different from `p`. -/
private lemma erdos313_not_dvd_sum {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) {p : ℕ}
    (hp : p ∈ P) : ¬ p ∣ ∑ q ∈ P, (∏ r ∈ P, r) / q := by
  intro hdvd
  have hpp : p.Prime := hprime p hp
  have hrest : p ∣ ∑ q ∈ P.erase p, (∏ r ∈ P, r) / q := by
    refine Finset.dvd_sum fun q hq => ?_
    have hqP : q ∈ P := Finset.mem_of_mem_erase hq
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq
    rw [erdos313_prod_div_erase hqP (hprime q hqP).pos]
    exact Finset.dvd_prod_of_mem (fun r => r) (Finset.mem_erase.mpr ⟨Ne.symm hqp, hp⟩)
  rw [← Finset.add_sum_erase P (fun q => (∏ r ∈ P, r) / q) hp] at hdvd
  have hdp : p ∣ (∏ r ∈ P, r) / p := by simpa using Nat.dvd_sub hdvd hrest
  rw [erdos313_prod_div_erase hp hpp.pos] at hdp
  obtain ⟨r, hr, hdr⟩ := (hpp.prime.dvd_finsetProd_iff (fun r => r)).mp hdp
  exact Finset.ne_of_mem_erase hr
    ((Nat.prime_dvd_prime_iff_eq hpp (hprime r (Finset.mem_of_mem_erase hr))).mp hdr).symm

/-- The product of the primes in `P` is coprime to the numerator `∑ q ∈ P, (∏ r ∈ P, r) / q`. -/
private lemma erdos313_coprime {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    Nat.Coprime (∏ r ∈ P, r) (∑ q ∈ P, (∏ r ∈ P, r) / q) :=
  Nat.coprime_prod_left_iff.mpr fun p hp =>
    (Nat.Prime.coprime_iff_not_dvd (hprime p hp)).mpr (erdos313_not_dvd_sum hprime hp)

/-- Clearing denominators in `∑ p ∈ P, 1 / p = 1 - 1 / m`: with `N = ∏ r ∈ P, r` and
`S = ∑ q ∈ P, N / q` this reads `S * m + N = N * m` in `ℕ`. -/
private lemma erdos313_clear_denominators {m : ℕ} {P : Finset ℕ} (hm : 2 ≤ m)
    (hprime : ∀ p ∈ P, p.Prime) (hsum : ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m) :
    (∑ q ∈ P, (∏ r ∈ P, r) / q) * m + (∏ r ∈ P, r) = (∏ r ∈ P, r) * m := by
  have hN0 : 0 < ∏ r ∈ P, r := Finset.prod_pos fun p hp => (hprime p hp).pos
  have hNQ : ((∏ r ∈ P, r : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN0.ne'
  have hmQ : ((m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm : ∀ p ∈ P,
      (((∏ r ∈ P, r) / p : ℕ) : ℚ) / ((∏ r ∈ P, r : ℕ) : ℚ) = 1 / (p : ℚ) := by
    intro p hp
    have hpp : p.Prime := hprime p hp
    have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.pos.ne'
    have hdd : p ∣ ∏ r ∈ P, r := Finset.dvd_prod_of_mem (fun r => r) hp
    have hmul : (((∏ r ∈ P, r) / p : ℕ) : ℚ) * (p : ℚ) = ((∏ r ∈ P, r : ℕ) : ℚ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdd]
    rw [div_eq_div_iff hNQ hpQ, hmul, one_mul]
  have hSN : ((∑ q ∈ P, (∏ r ∈ P, r) / q : ℕ) : ℚ) / ((∏ r ∈ P, r : ℕ) : ℚ)
      = 1 - 1 / (m : ℚ) := by
    rw [← hsum, Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_congr rfl hterm
  rw [div_eq_iff hNQ] at hSN
  have hQ : ((∑ q ∈ P, (∏ r ∈ P, r) / q : ℕ) : ℚ) * (m : ℚ) + ((∏ r ∈ P, r : ℕ) : ℚ)
      = ((∏ r ∈ P, r : ℕ) : ℚ) * (m : ℚ) := by
    rw [hSN]; field_simp; ring
  exact_mod_cast hQ

/-- The arithmetic core: if `N` is coprime to `S` and `S * m + N = N * m` with `2 ≤ m` and
`0 < N`, then `m = N`. -/
private lemma erdos313_arith {m N S : ℕ} (hm : 2 ≤ m) (hN : 0 < N) (hcop : Nat.Coprime N S)
    (hstar : S * m + N = N * m) : m = N := by
  have hNdvd : N ∣ S * m := by
    refine ⟨m - 1, ?_⟩
    have h1 : N * (m - 1) + N = N * m := by
      have h2 : m - 1 + 1 = m := by omega
      calc N * (m - 1) + N = N * (m - 1 + 1) := by ring
        _ = N * m := by rw [h2]
    exact Nat.add_right_cancel (hstar.trans h1.symm)
  have hNm : N ∣ m := hcop.dvd_of_dvd_mul_left hNdvd
  have key : (N - S) * m = N := by
    rw [Nat.sub_mul]; omega
  have hmN : m ∣ N := ⟨N - S, by rw [Nat.mul_comm]; exact key.symm⟩
  exact Nat.dvd_antisymm hmN hNm

/-- **Erdős #313, the page's structural remark**: in every solution `(m, P)` the denominator
is the product of the primes, `m = ∏_{p ∈ P} p`. -/
theorem erdos313_denominator_eq_prod {m : ℕ} {P : Finset ℕ} (h : (m, P) ∈ erdos313Solutions) :
    m = ∏ p ∈ P, p := by
  obtain ⟨hm, -, hprime, hsum⟩ := h
  exact erdos313_arith hm (Finset.prod_pos fun p hp => (hprime p hp).pos)
    (erdos313_coprime hprime) (erdos313_clear_denominators hm hprime hsum)

/-- Consequently there is at most one solution for each `m`. -/
theorem erdos313_unique {m : ℕ} {P Q : Finset ℕ} (hP : (m, P) ∈ erdos313Solutions)
    (hQ : (m, Q) ∈ erdos313Solutions) : P = Q := by
  have h1 := erdos313_denominator_eq_prod hP
  have h2 := erdos313_denominator_eq_prod hQ
  have hP' : ∀ p ∈ P, p.Prime := hP.2.2.1
  have hQ' : ∀ p ∈ Q, p.Prime := hQ.2.2.1
  calc P = (∏ p ∈ P, p).primeFactors := (Nat.primeFactors_prod hP').symm
    _ = m.primeFactors := by rw [← h1]
    _ = (∏ p ∈ Q, p).primeFactors := by rw [h2]
    _ = Q := Nat.primeFactors_prod hQ'

/-- Both facts as one closed statement (no binders), used as the graded root: there is no
solution whose denominator differs from the product of its primes, and no two solutions with
the same denominator and different prime sets. -/
theorem erdos313_structure_closed :
    ¬ ∃ (m : ℕ) (P Q : Finset ℕ), (m, P) ∈ erdos313Solutions ∧ (m, Q) ∈ erdos313Solutions ∧
      (m ≠ ∏ p ∈ P, p ∨ P ≠ Q) := by
  rintro ⟨m, P, Q, hP, hQ, h | h⟩
  · exact h (erdos313_denominator_eq_prod hP)
  · exact h (erdos313_unique hP hQ)
