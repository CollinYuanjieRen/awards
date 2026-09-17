import Mathlib

/-!
# Erdős Problem #367: the trivial bound `∏_{n ≤ m < n+k} B₂(m) ≪ n²` for `k ≤ 2`

Let `B₂(n)` be the `2`-full (powerful) part of `n`.  Erdős asked whether, for every fixed
`k ≥ 1`, `∏_{n ≤ m < n+k} B₂(m) ≪ n^{2+o(1)}` (OPEN).  The problem page records van Doorn's
remark that for `k ≤ 2` one trivially has `∏_{n ≤ m < n+k} B₂(m) ≪ n²`, while this fails for
every `k ≥ 3`.  This file proves the `k ≤ 2` bound in the exact shape of the formal-conjectures
statement `Erdos367.erdos_367.variants.k_le_two` (tagged "research solved" with `sorry`), with
the definition `B` copied verbatim: `B₂(m) ≤ m` for `m ≥ 1`, so the product over at most two
consecutive integers is at most `n(n+1) ≤ 2n²`.  The open question, and the `k ≥ 3` failure
(`∏_{n ≤ m < n+3} B₂(m) ≫ n² log n` infinitely often), are not addressed.
-/

open Filter Finset
open scoped Asymptotics

/-- `B r n` is the `r`-full part of `n`: the product of prime powers `p^a ∥ n` with `a ≥ r`
(formal-conjectures definition). -/
def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i

/-- The `r`-full part divides `n`, hence `B r n ≤ n` for `n ≥ 1`. -/
theorem B_dvd (r n : ℕ) : B r n ∣ n := by
  by_cases hn : n = 0
  · simp [B, hn]
  · calc B r n ∣ ∏ i ∈ n.factorization.support, i ^ n.factorization i :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    _ = n := Nat.prod_factorization_pow_eq_self hn

/-- The product over two consecutive integers, expanded. -/
private lemma prod_B_Ico_two (n : ℕ) :
    (∏ m ∈ Finset.Ico n (n + 2), B 2 m) = B 2 n * B 2 (n + 1) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, Finset.prod_Ico_succ_top (by omega),
    Finset.prod_Ico_succ_top (by omega), Finset.Ico_self, Finset.prod_empty, one_mul]

/-- The trivial bound: for `k ≤ 2` and `n ≥ 1`, the product of the `2`-full parts over
`n ≤ m < n + k` is at most `2 n²`. -/
private lemma prod_B_le (k n : ℕ) (hk : k ≤ 2) (hn : 1 ≤ n) :
    (∏ m ∈ Finset.Ico n (n + k), B 2 m) ≤ 2 * n ^ 2 := by
  have hBn : B 2 n ≤ n := Nat.le_of_dvd hn (B_dvd 2 n)
  have hBn1 : B 2 (n + 1) ≤ n + 1 := Nat.le_of_dvd (by omega) (B_dvd 2 (n + 1))
  interval_cases k
  · simp only [Nat.add_zero, Finset.Ico_self, Finset.prod_empty]
    nlinarith
  · rw [Finset.prod_Ico_succ_top (by omega), Finset.Ico_self, Finset.prod_empty, one_mul]
    nlinarith
  · rw [prod_B_Ico_two]
    nlinarith

/-- The asymptotic form of `prod_B_le`. -/
private lemma isBigO_prod_B (k : ℕ) (hk : k ≤ 2) :
    (fun n ↦ ((∏ m ∈ Finset.Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (2 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hrpow : (n : ℝ) ^ (2 : ℝ) = ((n : ℝ)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (n : ℝ) 2]
    norm_num
  rw [hrpow, Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
  have := prod_B_le k n hk hn
  calc ((∏ m ∈ Finset.Ico n (n + k), B 2 m : ℕ) : ℝ) ≤ ((2 * n ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast this
    _ = 2 * (n : ℝ) ^ (2 : ℕ) := by push_cast; ring

/-- **The `k = 2` case.**  `B₂(n) B₂(n+1) ≪ n²`. -/
theorem erdos_367_two :
    (fun n ↦ ((∏ m ∈ .Ico n (n + 2), B 2 m : ℕ) : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  exact isBigO_prod_B 2 le_rfl

/-- **Erdős #367, the trivial `k ≤ 2` bound (van Doorn).**  Exactly the formal-conjectures
statement `erdos_367.variants.k_le_two`.  The open question and the `k ≥ 3` behaviour are not
claimed. -/
theorem erdos_367_k_le_two : ∀ k : ℕ, k ≤ 2 →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  intro k hk
  exact isBigO_prod_B k hk
