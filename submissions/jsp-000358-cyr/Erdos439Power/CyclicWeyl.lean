import Mathlib

open scoped BigOperators ComplexConjugate

namespace Erdos439Power

section FiniteGroup

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Multiplicative finite difference of a complex-valued phase. -/
noncomputable def cyclicDifference (f : G → ℂ) (h x : G) : ℂ :=
  f (x + h) * conj (f x)

/-- Average absolute terminal correlation after `d` cyclic differences. -/
noncomputable def cyclicWeylMean (f : G → ℂ) : ℕ → ℝ
  | 0 => ‖𝔼 x, f x‖
  | d + 1 => 𝔼 h, cyclicWeylMean (cyclicDifference f h) d

lemma cyclicWeylMean_nonneg (f : G → ℂ) (d : ℕ) :
    0 ≤ cyclicWeylMean f d := by
  induction d generalizing f with
  | zero => exact norm_nonneg _
  | succ d ih => exact Finset.expect_nonneg (fun h _ => ih _)

lemma expect_conj (f : G → ℂ) :
    (𝔼 x, conj (f x)) = conj (𝔼 x, f x) := by
  simp only [Fintype.expect_eq_sum_div_card, map_div₀, map_sum, map_natCast]

lemma expect_cyclicDifference (f : G → ℂ) :
    (𝔼 h, 𝔼 x, cyclicDifference f h x) = (𝔼 x, f x) * conj (𝔼 x, f x) := by
  rw [Finset.expect_comm]
  simp only [cyclicDifference, ← Finset.expect_mul]
  have ht (x : G) : (𝔼 h, f (x + h)) = 𝔼 y, f y := by
    exact Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
  simp_rw [ht]
  rw [← Finset.mul_expect, expect_conj]

lemma norm_expect_sq_le_cyclicWeylMean_one (f : G → ℂ) :
    ‖𝔼 x, f x‖ ^ 2 ≤ cyclicWeylMean f 1 := by
  have hid : ‖𝔼 h, 𝔼 x, cyclicDifference f h x‖ = ‖𝔼 x, f x‖ ^ 2 := by
    rw [expect_cyclicDifference, norm_mul, Complex.norm_conj, pow_two]
  rw [← hid]
  exact RCLike.norm_expect_le (K := ℂ)

lemma cyclicWeylMean_sq_le (f : G → ℂ) (d : ℕ) :
    cyclicWeylMean f d ^ 2 ≤ cyclicWeylMean f (d + 1) := by
  induction d generalizing f with
  | zero => exact norm_expect_sq_le_cyclicWeylMean_one f
  | succ d ih =>
      change (𝔼 h, cyclicWeylMean (cyclicDifference f h) d) ^ 2 ≤
        𝔼 h, cyclicWeylMean (cyclicDifference f h) (d + 1)
      have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
        (fun h => cyclicWeylMean (cyclicDifference f h) d) (fun _ : G => (1 : ℝ))
      simp only [mul_one, one_pow, Finset.expect_const, Finset.univ_nonempty,
        mul_one] at hcs
      exact hcs.trans (Finset.expect_le_expect (fun h _ => ih _))

/-- Finite cyclic Weyl differencing, with no analytic or polynomial premise. -/
theorem norm_expect_pow_le_cyclicWeylMean (f : G → ℂ) (d : ℕ) :
    ‖𝔼 x, f x‖ ^ (2 ^ d) ≤ cyclicWeylMean f d := by
  induction d with
  | zero => simp [cyclicWeylMean]
  | succ d ih =>
      rw [pow_succ, pow_mul]
      exact (pow_le_pow_left₀ (by positivity) ih 2).trans
        (cyclicWeylMean_sq_le f d)

lemma cyclicWeylMean_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (d : ℕ) :
    cyclicWeylMean f d ≤ 1 := by
  induction d generalizing f with
  | zero =>
      exact (RCLike.norm_expect_le (K := ℂ)).trans
        (Finset.expect_le Finset.univ_nonempty (fun x _ => hf x))
  | succ d ih =>
      apply Finset.expect_le Finset.univ_nonempty
      intro h _
      apply ih
      intro x
      simp only [cyclicDifference, norm_mul, Complex.norm_conj]
      exact (mul_le_mul (hf (x + h)) (hf x) (norm_nonneg _) (by positivity)).trans_eq
        (one_mul 1)

end FiniteGroup

end Erdos439Power
