import Mathlib

/-!
# Erdős problem #364 — Mahler's observation on consecutive powerful numbers

Erdős problem #364 asks whether there are any triples of consecutive positive integers all of
which are *powerful* (`n` is powerful when `p ∣ n → p ^ 2 ∣ n` for every prime `p`).  That
question is open.  This file formalises two of the remarks recorded on the problem page.

The first is **Mahler's observation**: Erdős originally asked Mahler whether there are infinitely
many pairs of consecutive powerful numbers, and Mahler immediately observed that the answer is
yes, because the Pell equation `x ^ 2 = 8 * y ^ 2 + 1` has infinitely many solutions — for each
one, `8 * y ^ 2 = 2 ^ 3 * y ^ 2` and its successor `x ^ 2` are both powerful.  The Pell input
(`Erdos364.exists_pell_gt`) is Mathlib's: it is read off from `Pell.pell_eq` and `Pell.yn_ge_n`
for `a = 3`, so that `d = a * a - 1 = 8`.

The second is the page's **trivial remark** that there are no quadruples of consecutive powerful
numbers, since one of any four consecutive integers is `2 (mod 4)`, hence divisible by `2` but
not by `2 ^ 2`.  (That remark is also proved in the `formal-conjectures` repository; the proof
given here is our own.)

Not claimed here: the question of Erdős problem #364 whether three consecutive powerful numbers
exist (Erdős's conjecture that there are none), the strong variant, and the finiteness statements
conditional on the abc conjecture.

## Main results

* `Erdos364.exists_consecutive_powerful_gt`: beyond every bound there is a pair of consecutive
  powerful numbers.
* `Erdos364.infinite_consecutive_powerful`: the set of such `n` is infinite.
* `Erdos364.exists_pell_gt`: solutions of `x ^ 2 = 8 * y ^ 2 + 1` with `y` arbitrarily large.
* `Erdos364.powerful_eight_mul_sq`, `Erdos364.powerful_sq`: the two powerfulness facts behind the
  pair `(8 * y ^ 2, x ^ 2)`.
* `Erdos364.not_four_consecutive_powerful`: no four consecutive powerful numbers.
-/

namespace Erdos364

/-- `Powerful n` transcribes the condition stated on the problem page: "if `p ∣ n` then
`p ^ 2 ∣ n`", quantified over primes `p`.  For `n = 0` and `n = 1` it holds vacuously; the
theorems below always exhibit `n` beyond a prescribed bound, so these degenerate values play no
role. -/
def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Every square is powerful: a prime dividing `x ^ 2` divides `x`, hence its square divides
`x ^ 2`. -/
theorem powerful_sq (x : ℕ) : Powerful (x ^ 2) := by
  intro p hp hdvd
  have hpx : p ∣ x := hp.dvd_of_dvd_pow hdvd
  exact pow_dvd_pow_of_dvd hpx 2

/-- Every number of the form `8 * y ^ 2 = 2 ^ 3 * y ^ 2` is powerful: a prime dividing it is
either `2`, and `2 ^ 2 ∣ 8`, or divides `y`, and then its square divides `y ^ 2`. -/
theorem powerful_eight_mul_sq (y : ℕ) : Powerful (8 * y ^ 2) := by
  intro p hp hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h8 | hy
  · have h23 : p ∣ 2 ^ 3 := by simpa using h8
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h23)
    subst hp2
    exact Dvd.dvd.mul_right (by norm_num) _
  · have hpy : p ∣ y := hp.dvd_of_dvd_pow hy
    exact dvd_trans (pow_dvd_pow_of_dvd hpy 2) (dvd_mul_left _ _)

/-- The Pell equation `x ^ 2 = 8 * y ^ 2 + 1` has solutions with `y` arbitrarily large.  This is
Mathlib's Pell development with `a = 3`, so `d = a * a - 1 = 8`: `Pell.pell_eq` gives the
equation (with truncated subtraction) and `Pell.yn_ge_n` gives `n ≤ yn n`. -/
theorem exists_pell_gt (N : ℕ) : ∃ x y : ℕ, N < y ∧ x ^ 2 = 8 * y ^ 2 + 1 := by
  have a1 : (1 : ℕ) < 3 := by norm_num
  have aux : ∀ x y : ℕ, x * x - 8 * y * y = 1 → x ^ 2 = 8 * y ^ 2 + 1 := by
    intro x y h
    have hle : 8 * y * y ≤ x * x := by
      refine Nat.le_of_not_lt fun hc => ?_
      rw [Nat.sub_eq_zero_of_le (le_of_lt hc)] at h
      exact absurd h (by decide)
    have key : x * x = 1 + 8 * y * y := Nat.eq_add_of_sub_eq hle h
    rw [pow_two, pow_two, key]
    ring
  refine ⟨Pell.xn a1 (N + 1), Pell.yn a1 (N + 1), ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self N) (Pell.yn_ge_n a1 (N + 1))
  · exact aux _ _ (Pell.pell_eq a1 (N + 1))

/-- Mahler's observation, in the form "beyond every bound `N` there is an `n > N` with `n` and
`n + 1` both powerful": take a Pell solution `x ^ 2 = 8 * y ^ 2 + 1` with `y > N` and put
`n = 8 * y ^ 2`. -/
theorem exists_consecutive_powerful_gt (N : ℕ) : ∃ n : ℕ, N < n ∧ Powerful n ∧ Powerful (n + 1) := by
  obtain ⟨x, y, hy, hxy⟩ := exists_pell_gt N
  refine ⟨8 * y ^ 2, ?_, powerful_eight_mul_sq y, ?_⟩
  · have h1 : y ≤ y ^ 2 := Nat.le_self_pow (by norm_num) y
    have h2 : y ^ 2 ≤ 8 * y ^ 2 := Nat.le_mul_of_pos_left _ (by norm_num)
    exact lt_of_lt_of_le hy (le_trans h1 h2)
  · rw [← hxy]
    exact powerful_sq x

/-- Mahler's observation, in the form "there are infinitely many pairs of consecutive powerful
numbers". -/
theorem infinite_consecutive_powerful : {n : ℕ | Powerful n ∧ Powerful (n + 1)}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨n, hn, h1, h2⟩ := exists_consecutive_powerful_gt N
  exact ⟨n, ⟨h1, h2⟩, hn⟩

/-- The page's trivial remark: there are no quadruples of consecutive powerful numbers, since one
of any four consecutive integers is `2 (mod 4)`, hence divisible by `2` but not by `2 ^ 2`. -/
theorem not_four_consecutive_powerful (n : ℕ) : ¬ (Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) ∧ Powerful (n + 3)) := by
  rintro ⟨h0, h1, h2, h3⟩
  have key : ∀ m : ℕ, m % 4 = 2 → ¬ Powerful m := by
    intro m hm hpow
    have hdvd : (2 : ℕ) ∣ m := by omega
    have hsq : (2 : ℕ) ^ 2 ∣ m := hpow 2 Nat.prime_two hdvd
    have h4 : (4 : ℕ) ∣ m := by simpa using hsq
    omega
  have hcase : n % 4 = 2 ∨ (n + 1) % 4 = 2 ∨ (n + 2) % 4 = 2 ∨ (n + 3) % 4 = 2 := by omega
  rcases hcase with h | h | h | h
  · exact key n h h0
  · exact key (n + 1) h h1
  · exact key (n + 2) h h2
  · exact key (n + 3) h h3

end Erdos364
