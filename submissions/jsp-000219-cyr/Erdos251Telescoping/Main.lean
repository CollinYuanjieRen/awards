import Mathlib

/-!
# Erdős Problem #251: the example `g_n = p_n + 1` (a rational value of `∑ p_n / (g_1 ⋯ g_n)`)

Erdős asked whether `∑ p_n / 2^n` is irrational (OPEN; not addressed here).  The problem page
records his further conjecture that if `g_n ≥ 2` and `g_n = o(p_n)` then
`∑_{n ≥ 1} p_n / (g_1 ⋯ g_n)` is irrational, and: "The example `g_n = p_n + 1` shows that some
condition on the growth of the `g_n` is necessary here."  This file proves that example: with
`g_n = p_n + 1` (so `g_n ≥ 2` but `g_n = o(p_n)` fails) the series telescopes,
`p_n / (g_1 ⋯ g_n) = 1/(g_1 ⋯ g_{n−1}) − 1/(g_1 ⋯ g_n)`, so its sum is `1`, which is rational.

The primes are indexed from `0` as in the formal-conjectures statement `Erdos251.erdos_251`
(`Nat.nth Nat.Prime n`, so `p_0 = 2`), and the sum is taken in `ℝ`; the definitions are ours
(there is no formal-conjectures statement for the example).  The irrationality questions are not
claimed.
-/

open Finset

/-- The `n`-th term `p_n / (g_1 ⋯ g_n)` with `g_i = p_i + 1` (primes indexed from `0`). -/
noncomputable def primeTerm (n : ℕ) : ℝ :=
  (Nat.nth Nat.Prime n : ℝ) / ∏ i ∈ Finset.range (n + 1), ((Nat.nth Nat.Prime i : ℝ) + 1)

/-- Each factor `g_i = p_i + 1` is at least `2`, as a real number. -/
theorem two_le_nth_prime_add_one_real (i : ℕ) : (2 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) + 1 := by
  have h := (Nat.prime_nth_prime i).two_le
  have : (2 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) := by exact_mod_cast h
  linarith

/-- The partial products `g_1 ⋯ g_N` are positive. -/
theorem prod_nth_prime_add_one_pos (N : ℕ) :
    (0 : ℝ) < ∏ i ∈ Finset.range N, ((Nat.nth Nat.Prime i : ℝ) + 1) := by
  refine Finset.prod_pos ?_
  intro i _
  have := two_le_nth_prime_add_one_real i
  linarith

/-- The example satisfies the hypothesis `g_n ≥ 2`. -/
theorem two_le_nth_prime_add_one (n : ℕ) : 2 ≤ Nat.nth Nat.Prime n + 1 := by
  have := (Nat.prime_nth_prime n).two_le
  omega

/-- Telescoping partial sums: `∑_{n < N} p_n / (g_1 ⋯ g_n) = 1 − 1 / (g_1 ⋯ g_{N−1})`. -/
theorem sum_primeTerm_range (N : ℕ) :
    ∑ n ∈ Finset.range N, primeTerm n =
      1 - 1 / ∏ i ∈ Finset.range N, ((Nat.nth Nat.Prime i : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, primeTerm, Finset.prod_range_succ]
    have hP : (0 : ℝ) < ∏ i ∈ Finset.range N, ((Nat.nth Nat.Prime i : ℝ) + 1) :=
      prod_nth_prime_add_one_pos N
    have hp : (0 : ℝ) < (Nat.nth Nat.Prime N : ℝ) + 1 := by
      have := two_le_nth_prime_add_one_real N
      linarith
    field_simp
    ring

/-- The denominators grow at least like `2^N`. -/
theorem two_pow_le_prod (N : ℕ) :
    (2 : ℝ) ^ N ≤ ∏ i ∈ Finset.range N, ((Nat.nth Nat.Prime i : ℝ) + 1) := by
  calc (2 : ℝ) ^ N = ∏ _i ∈ Finset.range N, (2 : ℝ) := by simp
    _ ≤ ∏ i ∈ Finset.range N, ((Nat.nth Nat.Prime i : ℝ) + 1) :=
        Finset.prod_le_prod (fun i _ => by norm_num)
          (fun i _ => two_le_nth_prime_add_one_real i)

/-- **Erdős #251, the page's example**: with `g_n = p_n + 1` the series `∑ p_n / (g_1 ⋯ g_n)`
converges to `1`. -/
theorem erdos_251_example_hasSum : HasSum primeTerm 1 := by
  have hnn : ∀ n, 0 ≤ primeTerm n := fun n =>
    div_nonneg (by positivity) (prod_nth_prime_add_one_pos (n + 1)).le
  have hPtop : Filter.Tendsto
      (fun N => ∏ i ∈ Finset.range N, ((Nat.nth Nat.Prime i : ℝ) + 1))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono two_pow_le_prod
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp only [sum_primeTerm_range]
  have h0 : Filter.Tendsto
      (fun N => 1 / ∏ i ∈ Finset.range N, ((Nat.nth Nat.Prime i : ℝ) + 1))
      Filter.atTop (nhds 0) := Filter.Tendsto.div_atTop tendsto_const_nhds hPtop
  simpa using tendsto_const_nhds.sub h0

/-- Consequently the sum is rational, so some growth condition on the `g_n` is necessary. -/
theorem erdos_251_example_not_irrational : ¬ Irrational (∑' n : ℕ, primeTerm n) := by
  rw [erdos_251_example_hasSum.tsum_eq]
  exact fun h => h ⟨1, by norm_num⟩

/-- Closed form: the series with `g_n = p_n + 1` sums to `1` and its sum is not irrational. -/
theorem erdos_251_example_closed :
    HasSum (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) /
        ∏ i ∈ Finset.range (n + 1), ((Nat.nth Nat.Prime i : ℝ) + 1)) 1 ∧
      ¬ Irrational (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) /
        ∏ i ∈ Finset.range (n + 1), ((Nat.nth Nat.Prime i : ℝ) + 1)) :=
  ⟨erdos_251_example_hasSum, erdos_251_example_not_irrational⟩
