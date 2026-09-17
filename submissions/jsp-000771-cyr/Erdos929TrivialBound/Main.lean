import Mathlib

/-!
# Erdős Problem #929: the trivial bound `S(k) ≤ k + 1`

Let `S(k)` be the minimal `x` such that there is a positive-density set of `n` for which
`n + 1, …, n + k` are all divisible by primes `≤ x`.  Erdős asked to estimate `S(k)`, in
particular whether `S(k) ≥ k^{1 − o(1)}` (OPEN; not addressed here, nor the sieve lower bound or
the Ford–Green–Konyagin–Maynard–Tao upper bound).  The problem page records: "It is trivial that
`S(k) ≤ k + 1` since, for example, one can take `n ≡ 1 (mod (k + 1)!)`."  This file proves that
bound for every `k ≥ 1`: the set `{n : n ≡ 1 (mod (k + 1)!)}` has positive density, and for
`n` in it each `n + i` (`1 ≤ i ≤ k`) is divisible by `i + 1`, hence by a prime `≤ i + 1 ≤ k + 1`.

There is no formal-conjectures statement for #929, so the definitions are ours.  "Positive
density" is taken as positive lower density in the elementary form `HasPosDensity T`: for some
`d ≥ 1` and all large `N`, `N ≤ d · |T ∩ [1, N]|` (i.e. lower density `≥ 1/d`).  `S k` is the
least `x` admitting a positive-density set `T` such that every `n ∈ T` has each `n + i`
(`1 ≤ i ≤ k`) divisible by a prime `≤ x` (`sInf`).
-/

open Finset

open Classical in
/-- `T` has positive (lower) density: for some `d ≥ 1` and all large `N`, `N ≤ d · |T ∩ [1, N]|`. -/
def HasPosDensity (T : Set ℕ) : Prop :=
  ∃ d : ℕ, 1 ≤ d ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, N ≤ d * ((Finset.Icc 1 N).filter (· ∈ T)).card

/-- `x` is admissible for `k`: there is a positive-density set of `n` such that `n + 1, …, n + k`
are all divisible by primes `≤ x`. -/
def Admissible (k x : ℕ) : Prop :=
  ∃ T : Set ℕ, HasPosDensity T ∧
    ∀ n ∈ T, ∀ i ∈ Finset.Icc 1 k, ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ p ∣ n + i

/-- `S(k)`: the least admissible `x`. -/
noncomputable def S (k : ℕ) : ℕ := sInf {x | Admissible k x}

/-- The residue class `{n | n ≡ 1 (mod m)}` has positive density for `m ≥ 1`. -/
theorem hasPosDensity_modEq_one (m : ℕ) (hm : 1 ≤ m) :
    HasPosDensity {n : ℕ | n % m = 1 % m} := by
  refine ⟨2 * m, by omega, 2 * m, ?_⟩
  intro N hN
  have hdm : m * (N / m) + N % m = N := Nat.div_add_mod N m
  have hmod : N % m < m := Nat.mod_lt _ (by omega)
  -- it suffices to bound the cardinality below by `N / m`
  have key : ∀ c : ℕ, N / m ≤ c → N ≤ 2 * m * c := by
    intro c hc
    calc N ≤ 2 * (m * (N / m)) := by omega
      _ = 2 * m * (N / m) := by ring
      _ ≤ 2 * m * c := Nat.mul_le_mul le_rfl hc
  apply key
  -- the `N / m` numbers `1 + m * j` (`j < N / m`) lie in `[1, N]` and in the class
  rw [← Finset.card_range (N / m)]
  apply Finset.card_le_card_of_injOn (fun j => 1 + m * j)
  · intro j hj
    simp only [Finset.coe_range, Set.mem_Iio] at hj
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have h1 : m * (j + 1) ≤ m * (N / m) := Nat.mul_le_mul_left m (by omega)
      have h2 : m * (j + 1) = m * j + m := by ring
      omega
    · show (1 + m * j) % m = 1 % m
      simp [Nat.add_mul_mod_self_left]
  · intro a _ b _ hab
    simp only at hab
    have h : m * a = m * b := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h

/-- For `n ≡ 1 (mod (k + 1)!)` and `1 ≤ i ≤ k`, `n + i` is divisible by a prime `≤ k + 1`. -/
theorem exists_prime_dvd_of_modEq (k n i : ℕ) (hn : n % (k + 1).factorial = 1 % (k + 1).factorial)
    (hi : i ∈ Finset.Icc 1 k) : ∃ p : ℕ, p.Prime ∧ p ≤ k + 1 ∧ p ∣ n + i := by
  rw [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  have hF : 2 ≤ (k + 1).factorial := le_trans (by omega) (Nat.self_le_factorial (k + 1))
  have hone : 1 % (k + 1).factorial = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hone] at hn
  -- `i + 1` divides `(k + 1)!` because `2 ≤ i + 1 ≤ k + 1`
  have hfac : (i + 1) ∣ (k + 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  have hdm : (k + 1).factorial * (n / (k + 1).factorial) + n % (k + 1).factorial = n :=
    Nat.div_add_mod n (k + 1).factorial
  have hni : n + i = (k + 1).factorial * (n / (k + 1).factorial) + (i + 1) := by omega
  have hdvd : (i + 1) ∣ n + i := by
    rw [hni]
    exact dvd_add (hfac.mul_right _) dvd_rfl
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show i + 1 ≠ 1 by omega)
  exact ⟨p, hp, le_trans (Nat.le_of_dvd (by omega) hpd) (by omega), hpd.trans hdvd⟩

/-- `x = k + 1` is admissible (witness `n ≡ 1 (mod (k + 1)!)`). -/
theorem admissible_succ (k : ℕ) : Admissible k (k + 1) := by
  refine ⟨{n : ℕ | n % (k + 1).factorial = 1 % (k + 1).factorial},
    hasPosDensity_modEq_one _ (Nat.factorial_pos (k + 1)), ?_⟩
  intro n hn i hi
  exact exists_prime_dvd_of_modEq k n i hn hi

/-- **Erdős #929, the page's trivial bound**: `S(k) ≤ k + 1`. -/
theorem erdos_929_S_le (k : ℕ) : S k ≤ k + 1 := by
  exact Nat.sInf_le (admissible_succ k)

/-- Closed form of `erdos_929_S_le`. -/
theorem erdos_929_S_le_closed : ¬ ∃ k : ℕ, k + 1 < S k := by
  rintro ⟨k, h⟩
  exact absurd (erdos_929_S_le k) (not_le.mpr h)
