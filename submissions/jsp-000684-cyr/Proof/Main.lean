import Mathlib

/-!
# Erdős problem #828 — the scoped exercise `φ(n) ∣ n`

Erdős problem #828 asks (a conjecture of Graham): is it true that for every `a ∈ ℤ` there are
infinitely many `n` with `φ(n) ∣ n + a`?  The problem page also records, as an aside, the
"easy exercise" that `φ(n) ∣ n` if and only if `n = 2 ^ a * 3 ^ b`.  This file formalises **only
that exercise**, in its corrected form.

The page's literal statement (`n = 2 ^ a * 3 ^ b` for some `a, b ≥ 0`) is false: for `n = 3 ^ b`
with `b ≥ 1` we have `a = 0`, yet `φ(3 ^ b) = 2 * 3 ^ (b - 1)` is even while `3 ^ b` is odd, so
`φ(n) ∤ n`.  (For `b = 1`: `φ(3) = 2` does not divide `3`.)  This package therefore proves the
corrected form, which additionally requires `a ≥ 1` and allows the degenerate solutions `n = 0`
and `n = 1` (`φ 0 = 0 ∣ 0` and `φ 1 = 1 ∣ 1`); theorem `not_totient_dvd_three_pow` (T4) records
the failure of the page's literal statement.

## Main results

* `Erdos828.totient_dvd_two_pow_mul_three_pow` (T2): `φ (2 ^ a * 3 ^ b) ∣ 2 ^ a * 3 ^ b` for `a ≥ 1`.
* `Erdos828.not_totient_dvd_three_pow` (T4): `φ (3 ^ b) ∤ 3 ^ b` for `b ≥ 1`.
* `Erdos828.exists_eq_two_pow_mul_three_pow_of_totient_dvd` (T3): if `n ≥ 2` and `φ n ∣ n` then
  `n = 2 ^ a * 3 ^ b` with `a ≥ 1`.
* `Erdos828.totient_dvd_iff` (T1): `φ n ∣ n ↔ n ≤ 1 ∨ ∃ a b, 0 < a ∧ n = 2 ^ a * 3 ^ b`.

## Proof sketch

For (⇐) one computes `φ (2 ^ a * 3 ^ b)` by multiplicativity.  For (⇒) one uses Euler's product
formula `Nat.totient_mul_prod_primeFactors`, i.e. `φ n * ∏ p ∈ n.primeFactors, p =
n * ∏ p ∈ n.primeFactors, (p - 1)`.  Cancelling `φ n` in `φ n ∣ n` turns this into
`(∏ p ∈ n.primeFactors, (p - 1)) ∣ ∏ p ∈ n.primeFactors, p`.  Every odd prime `p` contributes an
even factor `p - 1`, which forces `2 ∈ n.primeFactors`, then forces at most one odd prime in
`n.primeFactors`, and finally that odd prime `q` satisfies `q - 1 ∣ 2`, so `q = 3`.

## Scope

Not claimed here: Graham's question of Erdős problem #828 (whether `φ(n) ∣ n + a` has infinitely
many solutions for every `a`), Lehmer's conjecture, and anything from Guy's problem B37 beyond
this exercise.
-/

namespace Erdos828

/-- **T2.** For `a ≥ 1` and any `b`, the totient of `2 ^ a * 3 ^ b` divides `2 ^ a * 3 ^ b`. -/
theorem totient_dvd_two_pow_mul_three_pow (a b : ℕ) (ha : 0 < a) :
    Nat.totient (2 ^ a * 3 ^ b) ∣ 2 ^ a * 3 ^ b := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ (a' + 1)) (3 ^ b) :=
    Nat.Coprime.pow _ _ (by decide)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos a')]
  cases b with
  | zero =>
      simp only [pow_zero, mul_one, Nat.totient_one]
      norm_num
      exact pow_dvd_pow 2 (by omega)
  | succ b' =>
      rw [Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos b')]
      simp only [Nat.succ_sub_one]
      exact ⟨3, by ring⟩

/-- **T4.** For `b ≥ 1` the totient of `3 ^ b` does not divide `3 ^ b`: this is the counterexample
to the literal form of the statement on the problem page. -/
theorem not_totient_dvd_three_pow (b : ℕ) (hb : 0 < b) : ¬ Nat.totient (3 ^ b) ∣ 3 ^ b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos b')]
  intro h
  have h2 : (2 : ℕ) ∣ 3 ^ (b' + 1) := by
    refine dvd_trans ?_ h
    simp only [Nat.succ_sub_one]
    exact dvd_mul_of_dvd_right (by norm_num) _
  have h3 : (2 : ℕ) ∣ 3 := Nat.prime_two.dvd_of_dvd_pow h2
  norm_num at h3

/-- **T3.** If `n ≥ 2` and `φ n ∣ n`, then `n = 2 ^ a * 3 ^ b` with `a ≥ 1`. -/
theorem exists_eq_two_pow_mul_three_pow_of_totient_dvd (n : ℕ) (hn : 2 ≤ n)
    (h : Nat.totient n ∣ n) : ∃ a b : ℕ, 0 < a ∧ n = 2 ^ a * 3 ^ b := by
  have hn0 : n ≠ 0 := by omega
  have hφpos : 0 < Nat.totient n := Nat.totient_pos.2 (by omega)
  -- Euler's product formula, with `φ n` cancelled using `φ n ∣ n`.
  have key : (∏ p ∈ n.primeFactors, (p - 1)) ∣ ∏ p ∈ n.primeFactors, p := by
    obtain ⟨m, hm⟩ := h
    have e := Nat.totient_mul_prod_primeFactors n
    have e' : Nat.totient n * (∏ p ∈ n.primeFactors, p)
        = Nat.totient n * (m * ∏ p ∈ n.primeFactors, (p - 1)) := by
      rw [e, ← mul_assoc, ← hm]
    exact ⟨m, by rw [Nat.eq_of_mul_eq_mul_left hφpos e']; ring⟩
  -- Step A: `2` is a prime factor of `n`.
  have h2mem : 2 ∈ n.primeFactors := by
    by_contra h2
    obtain ⟨p, hp⟩ : (n.primeFactors).Nonempty := Nat.nonempty_primeFactors.2 (by omega)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpne : p ≠ 2 := by rintro rfl; exact h2 hp
    have hev : (2 : ℕ) ∣ p - 1 := by
      have h2le := hpp.two_le
      rcases hpp.eq_two_or_odd with hh | hh
      · exact absurd hh hpne
      · omega
    have hd2 : (2 : ℕ) ∣ ∏ q ∈ n.primeFactors, q :=
      (hev.trans (Finset.dvd_prod_of_mem (fun q => q - 1) hp)).trans key
    obtain ⟨q, hq, hq2⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).1 hd2
    have : (2 : ℕ) = q :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_of_mem_primeFactors hq)).1 hq2
    exact h2 (this ▸ hq)
  -- Split off the factor `2`.
  have hprodP : ∏ p ∈ n.primeFactors, p = 2 * ∏ p ∈ n.primeFactors.erase 2, p :=
    (Finset.mul_prod_erase _ _ h2mem).symm
  have hprodP1 : ∏ p ∈ n.primeFactors, (p - 1) = ∏ p ∈ n.primeFactors.erase 2, (p - 1) := by
    rw [← Finset.mul_prod_erase n.primeFactors (fun p => p - 1) h2mem]
    norm_num
  have key' : (∏ p ∈ n.primeFactors.erase 2, (p - 1)) ∣ ∏ p ∈ n.primeFactors, p := by
    rw [← hprodP1]; exact key
  -- The product of the odd prime factors is odd.
  have hoddQ : ¬ (2 : ℕ) ∣ ∏ p ∈ n.primeFactors.erase 2, p := by
    intro hd
    obtain ⟨q, hq, hq2⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).1 hd
    have hq' : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq
    have : (2 : ℕ) = q :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_of_mem_primeFactors hq')).1 hq2
    exact (Finset.ne_of_mem_erase hq) this.symm
  -- Step B: each odd prime factor contributes a factor `2` to `∏ (p - 1)`.
  have hpow : (2 : ℕ) ^ (n.primeFactors.erase 2).card
      ∣ ∏ p ∈ n.primeFactors.erase 2, (p - 1) := by
    have hd := Finset.prod_dvd_prod_of_dvd (s := n.primeFactors.erase 2)
      (fun _ => (2 : ℕ)) (fun p => p - 1) ?_
    · simpa using hd
    · intro p hp
      have hp' : p ∈ n.primeFactors := Finset.mem_of_mem_erase hp
      have hpp := Nat.prime_of_mem_primeFactors hp'
      have hne : p ≠ 2 := Finset.ne_of_mem_erase hp
      have h2le := hpp.two_le
      rcases hpp.eq_two_or_odd with hh | hh
      · exact absurd hh hne
      · omega
  have chain : (2 : ℕ) ^ (n.primeFactors.erase 2).card
      ∣ 2 * ∏ p ∈ n.primeFactors.erase 2, p := by
    rw [← hprodP]; exact hpow.trans key'
  -- Hence at most one odd prime factor.
  have hcard : (n.primeFactors.erase 2).card ≤ 1 := by
    by_contra hc
    have hc2 : 2 ≤ (n.primeFactors.erase 2).card := Nat.lt_of_not_le hc
    have hdvd4 : (2 : ℕ) * 2 ∣ 2 * ∏ p ∈ n.primeFactors.erase 2, p := by
      refine dvd_trans ?_ chain
      calc (2 : ℕ) * 2 = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ (n.primeFactors.erase 2).card := pow_dvd_pow 2 hc2
    exact hoddQ ((Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 hdvd4)
  -- Step C: if there is an odd prime factor `q`, then `q - 1 ∣ 2`, so `q = 3`.
  have hQ : n.primeFactors.erase 2 = ∅ ∨ n.primeFactors.erase 2 = {3} := by
    rcases Nat.eq_zero_or_pos (n.primeFactors.erase 2).card with h0 | hpos
    · exact Or.inl (Finset.card_eq_zero.1 h0)
    · refine Or.inr ?_
      obtain ⟨q, hq⟩ :=
        Finset.card_eq_one.1 (by omega : (n.primeFactors.erase 2).card = 1)
      have hqmem : q ∈ n.primeFactors.erase 2 := by rw [hq]; exact Finset.mem_singleton_self q
      have hq' : q ∈ n.primeFactors := Finset.mem_of_mem_erase hqmem
      have hqp := Nat.prime_of_mem_primeFactors hq'
      have hqne : q ≠ 2 := Finset.ne_of_mem_erase hqmem
      have e1 : ∏ p ∈ n.primeFactors, (p - 1) = q - 1 := by
        rw [hprodP1, hq, Finset.prod_singleton]
      have e2 : ∏ p ∈ n.primeFactors, p = 2 * q := by rw [hprodP, hq, Finset.prod_singleton]
      rw [e1, e2] at key
      have hqle := hqp.two_le
      have hq2 : q - 1 ∣ 2 := by
        have hA : q - 1 ∣ 2 * (q - 1) := dvd_mul_left _ _
        have hsub := Nat.dvd_sub key hA
        have heq : 2 * q - 2 * (q - 1) = 2 := by omega
        rwa [heq] at hsub
      have hle : q - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
      have hq3 : q = 3 := by omega
      rw [hq, hq3]
  -- Conclude.
  have hfact : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    Nat.prod_primeFactors_pow_factorization hn0
  have h2pos : 0 < n.factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 (Nat.dvd_of_mem_primeFactors h2mem)
  have hPins : n.primeFactors = insert 2 (n.primeFactors.erase 2) :=
    (Finset.insert_erase h2mem).symm
  rcases hQ with hQ | hQ
  · refine ⟨n.factorization 2, 0, h2pos, ?_⟩
    conv_lhs => rw [hfact]
    rw [hPins, hQ]
    simp
  · refine ⟨n.factorization 2, n.factorization 3, h2pos, ?_⟩
    conv_lhs => rw [hfact]
    rw [hPins, hQ, Finset.prod_insert (by decide), Finset.prod_singleton]

/-- **T1.** The corrected form of the exercise on the Erdős problem page: `φ n ∣ n` exactly for
`n ≤ 1` and for `n = 2 ^ a * 3 ^ b` with `a ≥ 1`. -/
theorem totient_dvd_iff (n : ℕ) :
    Nat.totient n ∣ n ↔ n ≤ 1 ∨ ∃ a b : ℕ, 0 < a ∧ n = 2 ^ a * 3 ^ b := by
  constructor
  · intro h
    by_cases hn : n ≤ 1
    · exact Or.inl hn
    · exact Or.inr (exists_eq_two_pow_mul_three_pow_of_totient_dvd n (by omega) h)
  · rintro (h | ⟨a, b, ha, rfl⟩)
    · interval_cases n
      · decide
      · decide
    · exact totient_dvd_two_pow_mul_three_pow a b ha

end Erdos828
