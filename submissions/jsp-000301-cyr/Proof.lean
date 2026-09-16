import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic

/-!
# Consecutive powerful nonsquares

Formalizes JSP-000301, the scoped yes/no question, not the counting part of Erdős #365.
Classical counterexample attributed to S. W. Golomb: 12167 and 12168.
-/

/-- Golomb's pair consists of two positive consecutive powerful nonsquares. -/
theorem powerful_pair_witness :
    0 < 12167 ∧
      (∀ p : ℕ, p.Prime → p ∣ 12167 → p ^ 2 ∣ 12167) ∧
      (∀ p : ℕ, p.Prime → p ∣ 12168 → p ^ 2 ∣ 12168) ∧
      ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 := by
  constructor
  · norm_num
  constructor
  · intro p hp hpdvd
    have hpow : p ∣ 23 ^ 3 := by
      norm_num at hpdvd ⊢
      exact hpdvd
    have hp23 : p ∣ 23 := hp.dvd_of_dvd_pow hpow
    have hpeq : p = 23 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp23
    subst p
    norm_num
  constructor
  · intro p hp hpdvd
    have hfac : p ∣ 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by
      norm_num at hpdvd ⊢
      exact hpdvd
    rcases hp.dvd_mul.mp hfac with hp23 | hp13
    · rcases hp.dvd_mul.mp hp23 with hp2 | hp3
      · have hpdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow hp2
        have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdvd2
        subst p
        norm_num
      · have hpdvd3 : p ∣ 3 := hp.dvd_of_dvd_pow hp3
        have hpeq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdvd3
        subst p
        norm_num
    · have hpdvd13 : p ∣ 13 := hp.dvd_of_dvd_pow hp13
      have hpeq : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdvd13
      subst p
      norm_num
  constructor <;> norm_num

/-- Two consecutive positive powerful integers need not include a perfect square. -/
theorem consecutive_powerful_not_always_square :
    ¬ (∀ n : ℕ, 0 < n →
      (∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n) →
      (∀ p : ℕ, p.Prime → p ∣ n + 1 → p ^ 2 ∣ n + 1) →
      IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  rcases powerful_pair_witness with ⟨hpos, hpowerful, hnextPowerful, hnonsquare, hnextNonsquare⟩
  rcases h 12167 hpos hpowerful hnextPowerful with hsquare | hnextSquare
  · exact hnonsquare hsquare
  · exact hnextNonsquare hnextSquare
