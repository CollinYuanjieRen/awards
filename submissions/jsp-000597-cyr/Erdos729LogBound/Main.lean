import Mathlib

/-!
# Erdős Problem #729: Erdős's bound `a + b ≤ n + O(log n)` for `a! b! ∣ n!`

Erdős asked whether `a + b ≤ n + O(log n)` still follows from `a! b! ∣ n!` "ignoring small primes"
(PROVED by Barreto and Leeham; NOT formalized here).  The problem page records the classical
fact: "Erdős proved that if `a! b! ∣ n!` then `a + b ≤ n + O(log n)`.  The proof is easy, and can
be done with powers of `2` alone: Legendre's formula implies that if `2^k` is the highest power of
`2` dividing `n!` then `k = n + O(log n)`, and hence if `a! b! ∣ n!` then `a + b ≤ n + O(log n)`."
This file proves both statements with explicit constants: `n − (log₂ n + 1) ≤ k ≤ n` where
`k = padicValNat 2 n!` (Legendre: `k = n − s₂(n)` with `s₂` the binary digit sum), and
`a! b! ∣ n! → a + b ≤ n + 2 log₂ n + 2` (`Nat.log 2`), whence the `O(log n)` form.

There is a formal-conjectures rendering of the main question (`erdos_729`, with plby's proof of
Barreto's theorem), but not of this remark; the statements here are ours.
-/

namespace Erdos729

open Nat

/-- Every binary digit is at most `1`, so the binary digit sum of `m` is at most the number of
binary digits of `m`, which is at most `log₂ m + 1`. -/
theorem digits_two_sum_le_log (m : ℕ) : (Nat.digits 2 m).sum ≤ Nat.log 2 m + 1 := by
  have h1 : (Nat.digits 2 m).sum ≤ (Nat.digits 2 m).length • 1 :=
    List.sum_le_card_nsmul _ 1 (fun x hx => by
      have := Nat.digits_lt_base (by norm_num) hx
      omega)
  have h2 : (Nat.digits 2 m).length ≤ Nat.log 2 m + 1 :=
    (Nat.digits_length_le_iff (by norm_num) m).mpr (Nat.lt_pow_succ_log_self (by norm_num) m)
  simp only [smul_eq_mul, mul_one] at h1
  omega

/-- Legendre's formula at `p = 2`: the exponent of `2` in `m !` is `m` minus the binary digit
sum of `m`. -/
theorem padicValNat_two_factorial_eq (m : ℕ) :
    padicValNat 2 m ! = m - (Nat.digits 2 m).sum := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa using sub_one_mul_padicValNat_factorial (p := 2) m

/-- If `a ! ∣ n !` and `n` is positive then `a ≤ n`. -/
theorem factorial_dvd_le (a n : ℕ) (h : a ! ∣ n !) (hn : 0 < n) : a ≤ n := by
  by_contra hc
  have : n ! < a ! := (Nat.factorial_lt hn).mpr (by omega)
  have := Nat.le_of_dvd (Nat.factorial_pos n) h
  omega

/-- Legendre for `p = 2`, in the page's form: the exponent `k` of `2` in `n!` satisfies
`n − (log₂ n + 1) ≤ k ≤ n`. -/
theorem padicValNat_two_factorial_bounds (n : ℕ) :
    padicValNat 2 n ! ≤ n ∧ n ≤ padicValNat 2 n ! + (Nat.log 2 n + 1) := by
  have hv := padicValNat_two_factorial_eq n
  have hs := Nat.digit_sum_le 2 n
  have hl := digits_two_sum_le_log n
  omega

/-- **Erdős's bound with explicit constants**: `a! b! ∣ n!` implies `a + b ≤ n + 2 log₂ n + 2`. -/
theorem add_le_of_factorial_mul_factorial_dvd (a b n : ℕ) (h : a ! * b ! ∣ n !) :
    a + b ≤ n + 2 * Nat.log 2 n + 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hda : a ! ∣ n ! := dvd_trans (dvd_mul_right _ _) h
  have hdb : b ! ∣ n ! := dvd_trans (dvd_mul_left _ _) h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.factorial_zero, Nat.dvd_one] at hda hdb
    have ha := Nat.factorial_eq_one.mp hda
    have hb := Nat.factorial_eq_one.mp hdb
    have hz : Nat.log 2 0 = 0 := Nat.log_zero_right 2
    omega
  · have hab : a ≤ n := factorial_dvd_le a n hda hn
    have hbb : b ≤ n := factorial_dvd_le b n hdb hn
    have hpow : 2 ^ (padicValNat 2 a ! + padicValNat 2 b !) ∣ n ! := by
      rw [pow_add]
      exact dvd_trans (mul_dvd_mul pow_padicValNat_dvd pow_padicValNat_dvd) h
    have hle : padicValNat 2 a ! + padicValNat 2 b ! ≤ padicValNat 2 n ! :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp hpow
    rw [padicValNat_two_factorial_eq, padicValNat_two_factorial_eq,
      padicValNat_two_factorial_eq] at hle
    have hsa : (Nat.digits 2 a).sum ≤ Nat.log 2 a + 1 := digits_two_sum_le_log a
    have hsb : (Nat.digits 2 b).sum ≤ Nat.log 2 b + 1 := digits_two_sum_le_log b
    have hla : Nat.log 2 a ≤ Nat.log 2 n := Nat.log_mono_right hab
    have hlb : Nat.log 2 b ≤ Nat.log 2 n := Nat.log_mono_right hbb
    have hsa2 : (Nat.digits 2 a).sum ≤ a := Nat.digit_sum_le 2 a
    have hsb2 : (Nat.digits 2 b).sum ≤ b := Nat.digit_sum_le 2 b
    have hsn : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
    omega

/-- The `O(log n)` form: some constant `C` has `a! b! ∣ n! → a + b ≤ n + C (log₂ n + 1)`. -/
theorem erdos_729_erdos_bound :
    ∃ C : ℕ, ∀ a b n : ℕ, a ! * b ! ∣ n ! → a + b ≤ n + C * (Nat.log 2 n + 1) := by
  refine ⟨2, fun a b n h => ?_⟩
  have := add_le_of_factorial_mul_factorial_dvd a b n h
  omega

end Erdos729

open Nat in
/-- **Erdős #729, the classical bound, closed form**: there are no `a, b, n` with `a! b! ∣ n!`
and `a + b > n + 2 log₂ n + 2`. -/
theorem erdos_729_erdos_bound_closed :
    ¬ ∃ a b n : ℕ, a ! * b ! ∣ n ! ∧ n + 2 * Nat.log 2 n + 2 < a + b := by
  rintro ⟨a, b, n, h, hlt⟩
  exact absurd (Erdos729.add_le_of_factorial_mul_factorial_dvd a b n h) (not_le.mpr hlt)
