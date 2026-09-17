import Mathlib

/-!
# Erdős Problem #124: `gcd(d₁, …, d_r) = 1` is necessary in the second question

For integers `3 ≤ d₁ < ⋯ < d_r` let `sumsOfDistinctPowers dᵢ k` be the integers that are sums of
distinct powers `dᵢ^j` with `j ≥ k` (numbers with only the digits `0, 1` in base `dᵢ`, divisible by
`dᵢ^k`).  The second question of #124 (Burr–Erdős–Graham–Li) asks whether, for `k ≠ 0` and
`gcd(d₁, …, d_r) = 1` with `∑ 1/(dᵢ − 1) ≥ 1`, every large integer is a sum of one element from
each `sumsOfDistinctPowers dᵢ k` (OPEN; not addressed here).  The problem page records: "It is
trivial that `gcd(d₁, …, d_r) = 1` is a necessary condition in the second question."  This file
proves that remark with the formal-conjectures definition `Erdos124.sumsOfDistinctPowers`
(copied verbatim) and the formal-conjectures shape of the hypothesis (`∀ᶠ n in atTop,
n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k`, a pointwise sum of sets): if `k ≠ 0` and every
sufficiently large integer is such a sum, then `D.gcd id = 1`.  The `∑ 1/(dᵢ − 1) ≥ 1` condition
and both questions of #124 are not claimed.

Proof.  For `k ≥ 1` every element of `sumsOfDistinctPowers d k` is divisible by `d`, hence by
`g = gcd D`; so every element of the pointwise sum is divisible by `g`.  If `g ≠ 1` (including
`D = ∅`, where the sum is `{0}`), the integers `≡ 1 (mod g)`, which are unbounded, are never
represented, contradicting the hypothesis.
-/

open Filter
open scoped Pointwise

namespace Erdos124

/-- The set of integers which are the sum of distinct powers `d ^ i` with `i ≥ k`. -/
def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

end Erdos124

open Erdos124

/-- For `k ≠ 0`, every element of `sumsOfDistinctPowers d k` is divisible by `d`: it is a sum of
powers `d ^ i` with `i ≥ k ≥ 1`, and each such power is divisible by `d`. -/
theorem dvd_of_mem_sumsOfDistinctPowers {d k x : ℕ} (hk : k ≠ 0)
    (hx : x ∈ sumsOfDistinctPowers d k) : d ∣ x := by
  obtain ⟨s, hs, rfl⟩ := hx
  refine Finset.dvd_sum fun i hi => dvd_pow_self d ?_
  have := hs i hi
  omega

/-- Every element of the pointwise sum `∑ d ∈ D, sumsOfDistinctPowers d k` (with `k ≠ 0`) is
divisible by `D.gcd id`. -/
private lemma gcd_dvd_of_mem_finsetSum {k : ℕ} (hk : k ≠ 0) {D : Finset ℕ} {n : ℕ}
    (hn : n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k) : D.gcd id ∣ n := by
  rw [Set.mem_finsetSum] at hn
  obtain ⟨g, hg, rfl⟩ := hn
  exact Finset.dvd_sum fun d hd =>
    (Finset.gcd_dvd hd).trans (dvd_of_mem_sumsOfDistinctPowers hk (hg hd))

/-- **Erdős #124, the page's remark**: `gcd(d₁, …, d_r) = 1` is necessary for the second question:
if `k ≠ 0` and every sufficiently large integer is a sum of one element from each
`sumsOfDistinctPowers dᵢ k`, then `D.gcd id = 1`. -/
theorem erdos_124_gcd_eq_one_of_eventually (k : ℕ) (hk : k ≠ 0) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 3 ≤ d) (h : ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k) :
    D.gcd id = 1 := by
  -- The hypothesis `3 ≤ d` is not needed: divisibility by `D.gcd id` alone gives the result.
  have _hD := hD
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  by_contra hne
  rcases Nat.eq_zero_or_pos (D.gcd id) with h0 | hpos
  · -- `D.gcd id = 0` would force `N + 1 = 0`.
    have hdvd := gcd_dvd_of_mem_finsetSum hk (hN (N + 1) (by omega))
    rw [h0, zero_dvd_iff] at hdvd
    omega
  · -- Otherwise `g := D.gcd id ≥ 2` divides `g * N + 1`, hence divides `1`.
    have hle : N ≤ D.gcd id * N := Nat.le_mul_of_pos_left N hpos
    have hdvd := gcd_dvd_of_mem_finsetSum hk (hN (D.gcd id * N + 1) (by omega))
    have hone : D.gcd id ∣ 1 := (Nat.dvd_add_right (Dvd.intro N rfl)).mp hdvd
    have := Nat.le_of_dvd Nat.one_pos hone
    omega

/-- The same as a closed statement (no binders), used as the graded root. -/
theorem erdos_124_gcd_closed :
    ¬ ∃ (k : ℕ) (D : Finset ℕ), k ≠ 0 ∧ (∀ d ∈ D, 3 ≤ d) ∧
      (∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k) ∧ D.gcd id ≠ 1 := by
  rintro ⟨k, D, hk, hD, h, hne⟩
  exact hne (erdos_124_gcd_eq_one_of_eventually k hk D hD h)
