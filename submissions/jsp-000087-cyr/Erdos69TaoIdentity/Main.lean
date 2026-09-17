import Mathlib

/-!
# Erdős Problem #69: Tao's identity `∑_{n ≥ 2} ω(n)/2^n = ∑_p 1/(2^p − 1)`

Erdős asked whether `∑_{n ≥ 2} ω(n)/2^n` is irrational, where `ω(n)` is the number of distinct
prime divisors of `n`.  The problem page records Tao's observation that this is a special case of
Erdős Problem #257, because
`∑_{n ≥ 2} ω(n)/2^n = ∑_p 1/(2^p − 1)`, and that the irrationality was proved unconditionally by
Tao and Teräväinen (2025).  This file proves the identity, in the exact shape of the
formal-conjectures statement `Erdos69.erdos_69.variants.specialisation_of_erdos_257` (tagged
"research solved" with `sorry`).  The irrationality itself (`erdos_69`, Tao–Teräväinen) is not
claimed.

Proof.  `ω(n) = ∑_{p ∣ n, p prime} 1`, so, all terms being nonnegative, the double series can be
reindexed by the pairs `(p, m)` with `n = p·(m + 1)`:
`∑_{n ≥ 2} ω(n)/2^n = ∑_p ∑_{m ≥ 0} 2^{-p(m+1)} = ∑_p 2^{-p}/(1 − 2^{-p}) = ∑_p 1/(2^p − 1)`.
-/

open scoped ArithmeticFunction.omega

private noncomputable def erdos69G (x : ℕ × ℕ) : ℝ :=
  if x.2 ∈ x.1.primeFactors then ((2 : ℝ) ^ x.1)⁻¹ else 0

lemma erdos69_omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

private lemma erdos69G_nonneg (x : ℕ × ℕ) : 0 ≤ erdos69G x := by
  unfold erdos69G; split
  · positivity
  · exact le_refl 0

private lemma erdos69G_le (x : ℕ × ℕ) :
    erdos69G x ≤ (3 / 4 : ℝ) ^ x.1 * (3 / 4 : ℝ) ^ x.2 := by
  unfold erdos69G
  split
  · rename_i h
    obtain ⟨hp, hdvd, hn0⟩ := Nat.mem_primeFactors.mp h
    have hpn : x.2 ≤ x.1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    have hstep : (3 / 4 : ℝ) ^ x.1 ≤ (3 / 4 : ℝ) ^ x.2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hpn
    calc ((2 : ℝ) ^ x.1)⁻¹ = (1 / 2 : ℝ) ^ x.1 := by rw [one_div, inv_pow]
      _ ≤ (9 / 16 : ℝ) ^ x.1 := by
          exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (3 / 4 : ℝ) ^ x.1 * (3 / 4 : ℝ) ^ x.1 := by rw [← mul_pow]; norm_num
      _ ≤ (3 / 4 : ℝ) ^ x.1 * (3 / 4 : ℝ) ^ x.2 := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
  · positivity

private lemma erdos69G_summable : Summable erdos69G := by
  refine Summable.of_nonneg_of_le erdos69G_nonneg erdos69G_le ?_
  exact Summable.mul_of_nonneg
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (by intro i; positivity) (by intro i; positivity)

private lemma erdos69G_row (n : ℕ) :
    ∑' p : ℕ, erdos69G (n, p) = (ω n : ℝ) / 2 ^ n := by
  rw [tsum_eq_sum (s := n.primeFactors) (fun b hb => by simp [erdos69G, hb])]
  rw [Finset.sum_congr rfl (fun b hb => (by simp [erdos69G, hb] :
    erdos69G (n, b) = ((2 : ℝ) ^ n)⁻¹))]
  rw [Finset.sum_const, nsmul_eq_mul, erdos69_omega_eq_card, div_eq_mul_inv]

private lemma erdos69G_col_prime {p : ℕ} (hp : p.Prime) :
    ∑' n : ℕ, erdos69G (n, p) = 1 / ((2 : ℝ) ^ p - 1) := by
  have hp0 : 0 < p := hp.pos
  have hinj : Function.Injective (fun m : ℕ => p * (m + 1)) := by
    intro a b hab
    simpa [Nat.mul_right_inj hp0.ne', Nat.succ_inj] using hab
  have hsupp : Function.support (fun n : ℕ => erdos69G (n, p)) ⊆
      Set.range (fun m : ℕ => p * (m + 1)) := by
    intro n hn
    simp only [Function.mem_support, ne_eq, erdos69G] at hn
    by_cases hmem : p ∈ Nat.primeFactors n
    · obtain ⟨_, hdvd, hn0⟩ := Nat.mem_primeFactors.mp hmem
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hn0 hk
      refine ⟨k - 1, ?_⟩
      show p * (k - 1 + 1) = n
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
      exact hk.symm
    · exact absurd (by simp [hmem]) hn
  rw [← hinj.tsum_eq hsupp]
  have hterm : ∀ m : ℕ, erdos69G (p * (m + 1), p) = ((2 : ℝ) ^ p)⁻¹ * (((2 : ℝ) ^ p)⁻¹) ^ m := by
    intro m
    have hmem : p ∈ Nat.primeFactors (p * (m + 1)) := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, ⟨m + 1, rfl⟩, by positivity⟩
    simp only [erdos69G, hmem, ite_true]
    rw [pow_mul, ← inv_pow, pow_succ, mul_comm]
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) ?_]
  · have h1 : (1 : ℝ) < 2 ^ p := one_lt_pow₀ (by norm_num) hp0.ne'
    have h2 : (2 : ℝ) ^ p ≠ 0 := by positivity
    field_simp
  · have h1 : (1 : ℝ) < 2 ^ p := one_lt_pow₀ (by norm_num) hp0.ne'
    rw [inv_lt_one_iff₀]
    right; exact h1

private lemma erdos69G_col_not_prime {p : ℕ} (hp : ¬ p.Prime) :
    ∑' n : ℕ, erdos69G (n, p) = 0 := by
  have : ∀ n : ℕ, erdos69G (n, p) = 0 := by
    intro n
    simp only [erdos69G]
    rw [ite_eq_right_iff]
    intro hmem
    exact absurd (Nat.prime_of_mem_primeFactors hmem) hp
  simp [this]

/-- **Tao's identity** (Erdős #69 as a special case of #257), stated without the `let`. -/
theorem erdos_69_tao_identity :
    ∑' n, ω (n + 2) / (2 ^ (n + 2) : ℝ) = ∑' p : { n : ℕ | n.Prime }, 1 / (2 ^ p.1 - 1) := by
  have hsum := erdos69G_summable
  have hrow : ∀ b : ℕ, Summable fun c : ℕ => erdos69G (b, c) := fun b => hsum.prod_factor b
  have hcol : ∀ c : ℕ, Summable fun b : ℕ => erdos69G (b, c) :=
    fun c => hsum.prod_symm.prod_factor c
  have hS : Summable (fun n : ℕ => (ω n : ℝ) / 2 ^ n) := by
    have h := hsum.prod
    simpa only [erdos69G_row] using h
  have hcomm : ∑' (p : ℕ) (n : ℕ), erdos69G (n, p) = ∑' (n : ℕ) (p : ℕ), erdos69G (n, p) :=
    Summable.tsum_comm' hsum hrow hcol
  have hL : ∑' (n : ℕ) (p : ℕ), erdos69G (n, p) = ∑' n : ℕ, (ω n : ℝ) / 2 ^ n :=
    tsum_congr erdos69G_row
  have hR : ∑' (p : ℕ) (n : ℕ), erdos69G (n, p)
      = ∑' p : ℕ, Set.indicator {n : ℕ | n.Prime} (fun q : ℕ => 1 / ((2 : ℝ) ^ q - 1)) p := by
    refine tsum_congr fun p => ?_
    by_cases hp : p.Prime
    · rw [erdos69G_col_prime hp, Set.indicator_of_mem (show p ∈ {n : ℕ | n.Prime} from hp)]
    · rw [erdos69G_col_not_prime hp, Set.indicator_of_notMem (show p ∉ {n : ℕ | n.Prime} from hp)]
  rw [← tsum_subtype {n : ℕ | n.Prime} (fun q : ℕ => 1 / ((2 : ℝ) ^ q - 1))] at hR
  have key : ∑' n : ℕ, (ω n : ℝ) / 2 ^ n
      = ∑' p : { n : ℕ | n.Prime }, 1 / ((2 : ℝ) ^ p.1 - 1) := by
    rw [← hL, ← hcomm, hR]
  rw [← key]
  have h2 := hS.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  rw [← h2]
  norm_num

namespace Erdos69

/--
Tao observed that `erdos_69` is a special case of `erdos_257`, since
$$
\sum_{n\geq 2}\frac{\omega(n)}{2^n} = \sum_p \frac{1}{2^p - 1}.
$$
-/
theorem erdos_69.variants.specialisation_of_erdos_257 :
    let A := { n : ℕ | n.Prime }
    ∑' n, ω (n + 2) / (2 ^ (n + 2) : ℝ) = ∑' p : A, 1 / (2 ^ p.1 - 1) := by
  intro A
  exact erdos_69_tao_identity

end Erdos69
