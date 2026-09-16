import MerLeanExperiment.ThreeCenterUpper
import MerLeanExperiment.DyadicUpper

/-!
The two sharp upper-bound branches over the exact intervals in `SendovAnswer`.
-/

namespace PlanarMinimax

private theorem three_le_of_two_pow_lt {m n : ℕ} (hm : 2 ≤ m) (hmn : 2 ^ m < n) :
    3 ≤ n := by
  have hp : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
  norm_num at hp
  omega

/-- Both infinite-family upper bounds, with the exact interval conditions of `SendovAnswer`. -/
theorem sendov_upper_bounds :
    (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
      2 ^ m < n → n ≤ 2 ^ m + 2 ^ (m - 2) →
        minimaxAngle n ≤ Real.pi * (1 - 2 / (2 * (m : ℝ) + 1))) ∧
    (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
      2 ^ m + 2 ^ (m - 2) < n → n ≤ 2 ^ (m + 1) →
        minimaxAngle n ≤ Real.pi * (1 - 1 / ((m : ℝ) + 1))) := by
  constructor
  · intro m hm n hmn hn
    exact minimaxAngle_le_threeCenter hm (three_le_of_two_pow_lt hm hmn) hn
  · intro m hm n hmn hn
    have hpow : 2 ^ m < n := lt_of_lt_of_le (Nat.lt_add_of_pos_right (by positivity)) hmn.le
    have hN : 3 ≤ n := three_le_of_two_pow_lt hm hpow
    have hk : 2 ≤ m + 1 := by omega
    simpa [Nat.cast_add, Nat.cast_one] using
      (minimaxAngle_le_dyadic hk hN hn)

#print axioms sendov_upper_bounds

end PlanarMinimax
