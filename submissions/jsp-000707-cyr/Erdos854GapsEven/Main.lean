import Mathlib

/-!
# Erdős Problem #854: all gaps `a_{i+1} − a_i` between integers coprime to a primorial are even

Let `n_k` be the `k`-th primorial (the product of the first `k` primes) and let
`1 = a_1 < a_2 < ⋯ < a_{φ(n_k)} = n_k − 1` be the integers coprime to `n_k`.  Erdős asked to
estimate the smallest even integer not of the form `a_{i+1} − a_i`, and whether there are
`≫ max_i (a_{i+1} − a_i)` many even integers of that form (OPEN; not addressed here).  The
problem page records: "Clearly all differences `a_{i+1} − a_i` are even."  This file proves that
remark: for `k ≥ 1` the prime `2` divides `n_k`, so every integer coprime to `n_k` is odd and
consecutive ones differ by an even number.

There is no formal-conjectures statement for #854, so the definitions are ours.  The sequence of
integers coprime to `n_k` is taken as Mathlib's `Nat.nth` enumeration of the (infinite,
`n_k`-periodic) set of all naturals coprime to `n_k`, indexed from `0`: `coprimeSeq k i = a_{i+1}`;
its initial segment `i < φ(n_k)` is exactly the page's `a_1, …, a_{φ(n_k)}`, and the evenness of
the gaps holds for every index.
-/

open Finset

/-- The `k`-th primorial `n_k`: the product of the first `k` primes (`Nat.nth Nat.Prime`). -/
noncomputable def primorialK (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- The increasing enumeration `a_1 < a_2 < ⋯` of the naturals coprime to `n_k`, indexed from `0`
(`coprimeSeq k i = a_{i+1}`). -/
noncomputable def coprimeSeq (k : ℕ) : ℕ → ℕ := Nat.nth (fun a ↦ Nat.Coprime a (primorialK k))

/-- The second prime is `3`. -/
theorem nth_prime_one_eq_three : Nat.nth Nat.Prime 1 = 3 := by
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  rwa [hc] at h

/-- The third prime is `5`. -/
theorem nth_prime_two_eq_five : Nat.nth Nat.Prime 2 = 5 := by
  have hc : Nat.count Nat.Prime 5 = 2 := by decide
  have h := Nat.nth_count (p := Nat.Prime) (n := 5) (by norm_num)
  rwa [hc] at h

/-- Every primorial is positive. -/
theorem primorialK_pos (k : ℕ) : 0 < primorialK k :=
  Finset.prod_pos fun i _ ↦ (Nat.prime_nth_prime i).pos

/-- The primorials `n_1 = 2, n_2 = 6, n_3 = 30`. -/
theorem primorialK_one_two_three : primorialK 1 = 2 ∧ primorialK 2 = 6 ∧ primorialK 3 = 30 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [primorialK, Finset.prod_range_one, Nat.nth_prime_zero_eq_two]
  · rw [primorialK, Finset.prod_range_succ, Finset.prod_range_one,
      Nat.nth_prime_zero_eq_two, nth_prime_one_eq_three]
    rfl
  · rw [primorialK, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one,
      Nat.nth_prime_zero_eq_two, nth_prime_one_eq_three, nth_prime_two_eq_five]
    rfl

/-- For `k ≥ 1`, `2 ∣ n_k`. -/
theorem two_dvd_primorialK (k : ℕ) (hk : 1 ≤ k) : 2 ∣ primorialK k := by
  have h0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr hk
  have h := Finset.dvd_prod_of_mem (fun i ↦ Nat.nth Nat.Prime i) h0
  rwa [Nat.nth_prime_zero_eq_two] at h

/-- The set of naturals coprime to `n_k` is infinite (it contains every `1 + n_k · t`). -/
theorem coprime_primorialK_infinite (k : ℕ) :
    (Set.ofPred fun a ↦ Nat.Coprime a (primorialK k)).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ ↦ 1 + primorialK k * t) ?_ ?_
  · intro a b hab
    simp only [add_right_inj] at hab
    exact Nat.eq_of_mul_eq_mul_left (primorialK_pos k) hab
  · intro t
    show Nat.Coprime (1 + primorialK k * t) (primorialK k)
    exact (Nat.coprime_add_mul_left_left 1 (primorialK k) t).mpr (Nat.coprime_one_left _)

/-- For `k ≥ 1`, every term of the sequence is odd. -/
theorem coprimeSeq_odd (k i : ℕ) (hk : 1 ≤ k) : Odd (coprimeSeq k i) := by
  have h : Nat.Coprime (coprimeSeq k i) (primorialK k) :=
    Nat.nth_mem_of_infinite (coprime_primorialK_infinite k) i
  exact (Nat.Coprime.coprime_dvd_right (two_dvd_primorialK k hk) h).odd_of_right

/-- The sequence is strictly increasing and starts at `a_1 = 1`. -/
theorem coprimeSeq_strictMono_and_zero (k : ℕ) (hk : 1 ≤ k) :
    StrictMono (coprimeSeq k) ∧ coprimeSeq k 0 = 1 := by
  refine ⟨Nat.nth_strictMono (coprime_primorialK_infinite k), ?_⟩
  have hne : primorialK k ≠ 1 := by
    intro h
    have h2 := two_dvd_primorialK k hk
    rw [h] at h2
    omega
  have hcount : Nat.count (fun a ↦ Nat.Coprime a (primorialK k)) 1 = 0 := by
    simp [Nat.count_succ, Nat.coprime_zero_left, hne]
  have h := Nat.nth_count (p := fun a ↦ Nat.Coprime a (primorialK k)) (n := 1)
    (Nat.coprime_one_left _)
  rw [hcount] at h
  exact h

/-- **Erdős #854, the page's remark**: for `k ≥ 1`, every gap `a_{i+1} − a_i` between consecutive
integers coprime to `n_k` is even. -/
theorem erdos_854_gap_even (k i : ℕ) (hk : 1 ≤ k) :
    Even (coprimeSeq k (i + 1) - coprimeSeq k i) := by
  exact Nat.Odd.sub_odd (coprimeSeq_odd k (i + 1) hk) (coprimeSeq_odd k i hk)

/-- Closed form of `erdos_854_gap_even`. -/
theorem erdos_854_gap_even_closed :
    ¬ ∃ k i : ℕ, 1 ≤ k ∧ ¬ Even (coprimeSeq k (i + 1) - coprimeSeq k i) := by
  rintro ⟨k, i, hk, h⟩
  exact h (erdos_854_gap_even k i hk)
