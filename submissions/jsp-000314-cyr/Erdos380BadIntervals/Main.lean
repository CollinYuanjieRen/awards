import Mathlib

/-!
# Erdős Problem #380: Tao's observation on bad intervals

Erdős and Graham call an interval `[u, v]` of positive integers *bad* if the greatest prime
factor of `∏_{u ≤ m ≤ v} m` occurs with exponent greater than `1`, and ask for the asymptotics of
the count `B(x)` of `n ≤ x` lying in a bad interval (PROVED by Tao; NOT formalized here).  The
problem page records: "Tao notes in the comments that if `[u, v]` is bad then it cannot contain
any primes, and hence certainly `v < 2u`."  This file proves both parts of that observation.

Definitions: `intervalProd u v = ∏ m ∈ Finset.Icc u v, m`; `P n = n.primeFactors.sup id` (the
largest prime factor, `0` for `n ≤ 1`); `IsBad u v ↔ 1 ≤ u ∧ u ≤ v ∧ P (intervalProd u v) ^ 2 ∣
intervalProd u v` (the exponent of the largest prime factor is `≥ 2`).  Intervals are intervals of
positive integers, as on the page (`[0, v]` has product `0` and is excluded by `1 ≤ u`); the
degenerate `[1, 1]` has product `1`, `P 1 = 0`, and `0 ^ 2 ∣ 1` fails, so it is not bad.

Proof idea (Tao).  If a prime `q` lies in `[u, v]`, let `p = P (intervalProd u v) ≥ q`; `p` divides
some `m ∈ [u, v]`, and if `p ≤ v` then `p` is itself a prime of `[u, v]`; by Bertrand's postulate
there is a prime in `(p, 2p]`, which would lie in `[u, v]` and exceed `p` if `2p ≤ v`; so `v < 2p`,
the only multiple of `p` in `[u, v]` is `p`, and `p` has exponent exactly `1` — contradiction.
Hence a bad interval contains no prime, and `v < 2u` again by Bertrand.  There is no
formal-conjectures rendering of this problem; the definitions are ours.
-/

namespace Erdos380

/-- The product `∏_{u ≤ m ≤ v} m`. -/
def intervalProd (u v : ℕ) : ℕ := ∏ m ∈ Finset.Icc u v, m

/-- The largest prime factor of `n` (`0` when `n ≤ 1`). -/
def P (n : ℕ) : ℕ := n.primeFactors.sup id

/-- `[u, v]` is *bad*: an interval of positive integers whose product is divisible by the square
of its largest prime factor. -/
def IsBad (u v : ℕ) : Prop := 1 ≤ u ∧ u ≤ v ∧ P (intervalProd u v) ^ 2 ∣ intervalProd u v

/-- The product over an interval of positive integers is nonzero. -/
theorem intervalProd_ne_zero {u v : ℕ} (hu : 1 ≤ u) : intervalProd u v ≠ 0 := by
  rw [intervalProd, Finset.prod_ne_zero_iff]
  intro a ha
  rw [Finset.mem_Icc] at ha
  omega

/-- Every member of the interval divides its product. -/
theorem dvd_intervalProd {u v m : ℕ} (h : m ∈ Finset.Icc u v) : m ∣ intervalProd u v :=
  Finset.dvd_prod_of_mem (fun m => m) h

/-- Every prime factor is at most the largest prime factor. -/
theorem le_P {n q : ℕ} (hq : q ∈ n.primeFactors) : q ≤ P n :=
  Finset.le_sup (f := id) hq

/-- For `1 < n`, the largest prime factor is itself a prime factor. -/
theorem P_mem {n : ℕ} (hn : 1 < n) : P n ∈ n.primeFactors := by
  obtain ⟨i, hi, hsup⟩ :=
    Finset.exists_mem_eq_sup n.primeFactors (Nat.nonempty_primeFactors.mpr hn) id
  rw [P, hsup]
  exact hi

/-- A bad interval contains no prime. -/
theorem not_prime_mem_of_isBad {u v : ℕ} (hb : IsBad u v) (p : ℕ) (hp : p.Prime) :
    ¬ (u ≤ p ∧ p ≤ v) := by
  obtain ⟨hu, _huv, hsq⟩ := hb
  rintro ⟨hup, hpv⟩
  set N := intervalProd u v with hN
  have hN0 : N ≠ 0 := intervalProd_ne_zero hu
  -- `p` is a prime factor of `N`
  have hpN : p ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, dvd_intervalProd (Finset.mem_Icc.mpr ⟨hup, hpv⟩), hN0⟩
  have hN1 : 1 < N := Nat.nonempty_primeFactors.mp ⟨p, hpN⟩
  -- let `P N` be the largest prime factor
  have hPmem : P N ∈ N.primeFactors := P_mem hN1
  obtain ⟨hPprime, hPdvd, -⟩ := Nat.mem_primeFactors.mp hPmem
  have hpP : p ≤ P N := le_P hpN
  -- `P N` divides some member of the interval, hence `P N ≤ v`
  obtain ⟨m, hm, hPm⟩ :=
    (Prime.dvd_finsetProd_iff hPprime.prime (fun m => m)).mp hPdvd
  rw [Finset.mem_Icc] at hm
  have hPv : P N ≤ v := le_trans (Nat.le_of_dvd (by omega) hPm) hm.2
  have hPIcc : P N ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨le_trans hup hpP, hPv⟩
  -- Bertrand: there is no room for `2 * P N` inside the interval
  have hlt : v < 2 * P N := by
    by_contra hcon
    obtain ⟨r, hr, hPr, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul (P N) hPprime.pos.ne'
    have hrIcc : r ∈ Finset.Icc u v :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have : r ≤ P N :=
      le_P (Nat.mem_primeFactors.mpr ⟨hr, dvd_intervalProd hrIcc, hN0⟩)
    omega
  -- split off the single factor `P N`
  set M := ∏ x ∈ (Finset.Icc u v).erase (P N), x with hM
  have hsplit : P N * M = N := Finset.mul_prod_erase _ (fun m => m) hPIcc
  -- `P N` divides no other member of the interval
  have hPM : ¬ P N ∣ M := by
    intro hdvd
    obtain ⟨m', hm', hPm'⟩ :=
      (Prime.dvd_finsetProd_iff hPprime.prime (fun m => m)).mp hdvd
    have hne : m' ≠ P N := Finset.ne_of_mem_erase hm'
    have hm'Icc := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm')
    exact hne (Nat.eq_of_dvd_of_lt_two_mul (by omega) hPm' (by omega))
  -- but badness forces it
  refine hPM ?_
  have : P N * P N ∣ P N * M := by
    rw [hsplit]
    calc P N * P N = P N ^ 2 := (sq (P N)).symm
    _ ∣ N := hsq
  exact (mul_dvd_mul_iff_left hPprime.pos.ne').mp this

/-- A bad interval `[u, v]` satisfies `v < 2u`. -/
theorem lt_two_mul_of_isBad {u v : ℕ} (hb : IsBad u v) : v < 2 * u := by
  by_contra hcon
  have hu : 1 ≤ u := hb.1
  obtain ⟨r, hr, hur, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul u (by omega : u ≠ 0)
  exact not_prime_mem_of_isBad hb r hr ⟨by omega, by omega⟩

end Erdos380

open Erdos380 in
/-- **Erdős #380, Tao's observation, closed form**: no bad interval contains a prime or has
`v ≥ 2u`. -/
theorem erdos_380_tao_closed :
    ¬ ∃ u v : ℕ, IsBad u v ∧ ((∃ p : ℕ, p.Prime ∧ u ≤ p ∧ p ≤ v) ∨ 2 * u ≤ v) := by
  rintro ⟨u, v, hb, h | h⟩
  · obtain ⟨p, hp, hup, hpv⟩ := h
    exact not_prime_mem_of_isBad hb p hp ⟨hup, hpv⟩
  · exact absurd (lt_two_mul_of_isBad hb) (not_lt.mpr h)
