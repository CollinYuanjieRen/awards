import Mathlib.Tactic

namespace Erdos441

/-- The explicit integer sets B(alpha,beta) from Chen, Section 3. -/
noncomputable def gridPoints (α β : ℝ) : Finset ℤ :=
  Finset.Icc 1 ⌊α * β⌋ ∪ Finset.Icc ⌈-min (α * β) (β / α - 1)⌉ 0

theorem mem_gridPoints (α β : ℝ) (z : ℤ) : z ∈ gridPoints α β ↔
    (1 ≤ (z : ℝ) ∧ (z : ℝ) ≤ α * β) ∨
      (-min (α * β) (β / α - 1) ≤ (z : ℝ) ∧ (z : ℝ) ≤ 0) := by
  simp only [gridPoints, Finset.mem_union, Finset.mem_Icc,
    Int.le_floor, Int.ceil_le]
  norm_cast

theorem grid_points_separation (α β γ : ℝ) (hα : 0 < α)
    (hαβ : α ≤ β) (hαγ : α ≤ γ) (a b : ℤ)
    (ha : a ∈ gridPoints α β) (hb : b ∈ gridPoints α γ) :
    |((a - b : ℤ) : ℝ)| ≤ β * γ := by
  have hβ : 0 ≤ β := le_trans (le_of_lt hα) hαβ
  have hγ : 0 ≤ γ := le_trans (le_of_lt hα) hαγ
  have hbg : α * β ≤ β * γ := by nlinarith [mul_nonneg hβ (sub_nonneg.mpr hαγ)]
  have hgb : α * γ ≤ β * γ := mul_le_mul_of_nonneg_right hαβ hγ
  have hmix (u v x y : ℝ) (hv : α ≤ v)
      (hx1 : 1 ≤ x) (hxu : x ≤ α * u)
      (hy : -min (α * v) (v / α - 1) ≤ y) : x - y ≤ u * v := by
    have huv : 0 ≤ (α * u - 1) * (v - α) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hv)
    have hbound : x - y ≤ α * u + v / α - 1 := by
      have hm := min_le_right (α * v) (v / α - 1)
      linarith
    have hd : v / α * α = v := div_mul_cancel₀ v (ne_of_gt hα)
    have ht : α * u + v / α - 1 ≤ u * v := by
      nlinarith
    exact le_trans hbound ht
  rw [mem_gridPoints] at ha hb
  push_cast
  rw [abs_le]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · constructor <;> linarith
  · have hab := hmix β γ a b hαγ ha.1 ha.2 hb.1
    have hnonpos := hb.2
    constructor <;> linarith [mul_nonneg hβ hγ]
  · have hba := hmix γ β b a hαβ hb.1 hb.2 ha.1
    constructor <;> nlinarith [mul_nonneg hβ hγ]
  · have ham := min_le_left (α * β) (β / α - 1)
    have hbm := min_le_left (α * γ) (γ / α - 1)
    constructor <;> linarith

end Erdos441

#print axioms Erdos441.grid_points_separation
