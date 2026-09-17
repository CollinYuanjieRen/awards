import Mathlib

/-!
# Erdős Problem #400: `g_k(n) ≪_k log n`

For `k ≥ 2` let `g_k(n)` be the maximum of `(a₁ + ⋯ + a_k) − n` over integers `a₁, …, a_k` with
`a₁! ⋯ a_k! ∣ n!`.  Erdős and Graham asked whether `∑_{n ≤ x} g_k(n) ∼ c_k x log x` and whether
`g_k(n) = c_k log x + o(log x)` for almost all `n < x` (both OPEN); the problem page records that
"it is easy to show that `g_k(n) ≪_k log n` always, but the best possible constant is unknown".
This file proves that bound, in the exact shape of the formal-conjectures statement
`Erdos400.erdos_400.variants.upper_bound` (tagged "research solved" with `sorry`), with the
definition `g` copied verbatim.

Proof.  Compare `2`-adic valuations: by Legendre, `v₂(a!) = a − s₂(a)` where `s₂` is the binary
digit sum.  From `∏ aᵢ! ∣ n!` we get `∑ (aᵢ − s₂(aᵢ)) ≤ n − s₂(n)`, so
`∑ aᵢ − n ≤ ∑ s₂(aᵢ) ≤ k (⌊log₂ n⌋ + 1)` (each `aᵢ ≤ n`).  The set defining `g_k(n)` is
nonempty and bounded, so `g_k(n) ≤ k (log₂ n + 1) ≪_k log n`.  The asymptotic questions and the
best constant are not addressed.
-/

open Nat Filter Finset
open scoped Asymptotics Topology

/-- For any `k ≥ 2` let `g_k(n)` denote the maximum value of `(a₁ + ⋯ + a_k) − n` where
`a₁, …, a_k` are integers such that `a₁! ⋯ a_k! ∣ n!` (formal-conjectures definition). -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup { ((∑ i, a i) - n) | (a : Fin k → ℕ) (_ : (∏ i, (a i) !) ∣ n !) }

/-- The binary digit sum of `m` is at most `⌊log₂ m⌋ + 1` (the number of binary digits). -/
private lemma digitSum_le_log_succ (m : ℕ) : (Nat.digits 2 m).sum ≤ Nat.log 2 m + 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · calc (Nat.digits 2 m).sum ≤ (Nat.digits 2 m).length • 1 :=
          List.sum_le_card_nsmul _ 1 fun x hx => by
            have := Nat.digits_lt_base (by norm_num) hx; omega
      _ = Nat.log 2 m + 1 := by simp [Nat.length_digits 2 m (by norm_num) hm]

/-- Legendre's formula in base `2`: `v₂(m!) = m - s₂(m)`. -/
private lemma padicValNat_two_factorial (m : ℕ) :
    padicValNat 2 (m !) = m - (Nat.digits 2 m).sum := by
  simpa using sub_one_mul_padicValNat_factorial (p := 2) m

/-- The explicit bound: `g_k(n) ≤ k · (log₂ n + 1)` for all `k` and `n`. -/
theorem g_le (k n : ℕ) : g k n ≤ k * (Nat.log 2 n + 1) := by
  refine csSup_le' ?_
  rintro _ ⟨a, hdvd, rfl⟩
  have hdvd' : ∀ i : Fin k, (a i)! ∣ n ! := fun i =>
    dvd_trans (Finset.dvd_prod_of_mem (fun i => (a i)!) (Finset.mem_univ i)) hdvd
  rcases eq_or_ne n 0 with rfl | hn
  · have h1 : ∀ i : Fin k, a i ≤ 1 := by
      intro i
      have h := hdvd' i
      rw [Nat.factorial_zero, Nat.dvd_one] at h
      exact Nat.factorial_eq_one.mp h
    have h2 : ∑ i, a i ≤ k := by
      simpa using Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin k)) a 1 fun i _ => h1 i
    simpa using h2
  · have hn' : n ! ≠ 0 := Nat.factorial_ne_zero n
    have hprod : (∏ i, (a i)!) ≠ 0 := by
      simp [Finset.prod_ne_zero_iff, Nat.factorial_ne_zero]
    have hfac : (∏ i, (a i)!).factorization 2 ≤ (n !).factorization 2 :=
      Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hprod hn').mpr hdvd) 2
    rw [Nat.factorization_prod fun i _ => Nat.factorial_ne_zero (a i), Finset.sum_apply'] at hfac
    simp only [Nat.factorization_def _ Nat.prime_two, padicValNat_two_factorial] at hfac
    rw [Finset.sum_tsub_distrib _ fun i _ => Nat.digit_sum_le 2 (a i)] at hfac
    have hain : ∀ i : Fin k, a i ≤ n := by
      intro i
      by_contra hcon
      exact absurd (Nat.le_of_dvd (Nat.factorial_pos n) (hdvd' i))
        (not_le.mpr ((Nat.factorial_lt (Nat.pos_of_ne_zero hn)).mpr (not_le.mp hcon)))
    have hT : ∑ i, (Nat.digits 2 (a i)).sum ≤ k * (Nat.log 2 n + 1) := by
      have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin k))
        (fun i : Fin k => (Nat.digits 2 (a i)).sum) (Nat.log 2 n + 1)
        fun i _ => (digitSum_le_log_succ (a i)).trans
          (Nat.add_le_add_right (Nat.log_mono_right (hain i)) 1)
      simpa using h
    have hsn : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
    obtain ⟨L, hL⟩ : ∃ L, k * (Nat.log 2 n + 1) = L := ⟨_, rfl⟩
    rw [hL] at hT ⊢
    omega

/-- `g_{k+2}(n) ≪ log n` (data-binder form, no hypothesis on `k`). -/
theorem g_isBigO_log (k : ℕ) :
    (fun n : ℕ ↦ (g (k + 2) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  refine Asymptotics.IsBigO.of_bound (2 * (k + 2) / Real.log 2) ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by omega
  have hlogn : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
  have hlogn0 : (0 : ℝ) ≤ Real.log (n : ℝ) := hlog2.le.trans hlogn
  -- `⌊log₂ n⌋ ≤ log n / log 2`
  have hnatlog : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    have h1 : ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hn0
    have h2 : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at h2
  have hone : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := (one_le_div₀ hlog2).mpr hlogn
  have hg : (g (k + 2) n : ℝ) ≤ ((k : ℝ) + 2) * ((Nat.log 2 n : ℝ) + 1) := by
    have := g_le (k + 2) n
    have : ((g (k + 2) n : ℕ) : ℝ) ≤ (((k + 2) * (Nat.log 2 n + 1) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this
    linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hlogn0]
  have hstep : ((k : ℝ) + 2) * ((Nat.log 2 n : ℝ) + 1)
      ≤ ((k : ℝ) + 2) * (2 * (Real.log (n : ℝ) / Real.log 2)) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) + 2 := by positivity
    nlinarith [hnatlog, hone]
  have : ((k : ℝ) + 2) * (2 * (Real.log (n : ℝ) / Real.log 2))
      = 2 * ((k : ℝ) + 2) / Real.log 2 * Real.log (n : ℝ) := by
    field_simp
  linarith [hg.trans hstep, this.symm.le, this.le]

/-- **Erdős #400, the easy upper bound (Erdős–Graham).**  `g_k(n) ≪_k log n` for every `k ≥ 2`, in
the exact shape of the formal-conjectures statement `erdos_400.variants.upper_bound` (`≪` is
`IsBigO atTop`).  The asymptotic questions and the best constant are not claimed. -/
theorem erdos_400_upper_bound (k : ℕ) (hk : k ≥ 2) :
    (fun n : ℕ ↦ (g k n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  exact g_isBigO_log k'
