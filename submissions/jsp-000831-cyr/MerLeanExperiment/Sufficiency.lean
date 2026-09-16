import MerLeanExperiment.CountBridge
import MerLeanExperiment.IntervalIdentity
import MerLeanExperiment.ShiftSum

/-! The Hecke–Ostrowski sufficiency direction by bounded shifted fractional-part sums. -/

namespace Kesten

/-- If the interval length belongs to `ℤ α + ℤ`, then its counting discrepancy is bounded. -/
theorem bounded_remainder_of_integer_relation (α u v : ℝ) (hu : 0 ≤ u) (huv : u < v)
    (hv : v ≤ 1) (hrel : ∃ k l : ℤ, v - u = (k : ℝ) * α + (l : ℝ)) :
    HasBoundedRemainder α u v := by
  obtain ⟨k, l, hrel⟩ := hrel
  let a : ℤ → ℝ := fun j ↦ Int.fract (α * ((j : ℝ) + 1) - u)
  have ha : ∀ j : ℤ, |a j| ≤ 1 := by
    intro j
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  rw [hasBoundedRemainder_iff_forall]
  refine ⟨2 * (k.natAbs : ℝ), by positivity, ?_⟩
  intro n
  rw [count_discrepancy_eq_sum]
  have hsum :
      (∑ j ∈ Finset.range n,
        ((if u ≤ Int.fract (α * (j + 1 : ℕ)) ∧
            Int.fract (α * (j + 1 : ℕ)) < v then (1 : ℝ) else 0) - (v - u))) =
        ∑ j ∈ Finset.range n, (a ((j : ℤ) - k) - a j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [indicator_sub_length_eq_fract_sub _ _ _ hu huv hv]
    have hshift :
        α * (j + 1 : ℕ) - v =
          (α * ((((j : ℤ) - k : ℤ) : ℝ) + 1) - u) - (l : ℝ) := by
      have hvrel : v = u + (k : ℝ) * α + (l : ℝ) := by linarith
      rw [hvrel]
      push_cast
      ring
    rw [hshift, Int.fract_sub_intCast]
    simp [a]
  rw [hsum]
  simpa [sub_eq_add_neg] using shift_sum_bound a ha (-k) n

end Kesten
