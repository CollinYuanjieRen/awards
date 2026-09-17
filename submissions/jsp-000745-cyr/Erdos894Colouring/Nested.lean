import Erdos894Colouring.Definitions

/-! The nested-interval rotation lemma: a sequence growing by a factor at least `4` admits a
real `θ` all of whose multiples `θ * m i` have fractional part in `[1/4, 3/4]`. -/

namespace Erdos894

namespace NestedInterval

/-- The integer index of the nested interval at stage `i`: the interval at stage `i` is
`[(idx i + 1/4) / m i, (idx i + 3/4) / m i]`. -/
noncomputable def idx (m : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => ⌊(m (i + 1) : ℝ) * (((idx m i : ℝ) + 1 / 4) / (m i : ℝ))⌋ + 1

/-- Left endpoint of the `i`-th interval. -/
noncomputable def lo (m : ℕ → ℕ) (i : ℕ) : ℝ := ((idx m i : ℝ) + 1 / 4) / (m i : ℝ)

/-- Right endpoint of the `i`-th interval. -/
noncomputable def hi (m : ℕ → ℕ) (i : ℕ) : ℝ := ((idx m i : ℝ) + 3 / 4) / (m i : ℝ)

theorem idx_succ (m : ℕ → ℕ) (i : ℕ) :
    idx m (i + 1) = ⌊(m (i + 1) : ℝ) * lo m i⌋ + 1 := rfl

theorem cast_pos {m : ℕ → ℕ} (hm : ∀ i, 0 < m i) (i : ℕ) : (0 : ℝ) < (m i : ℝ) := by
  exact_mod_cast hm i

theorem mul_lo {m : ℕ → ℕ} (hm : ∀ i, 0 < m i) (i : ℕ) :
    (m i : ℝ) * lo m i = (idx m i : ℝ) + 1 / 4 := by
  have h : (m i : ℝ) ≠ 0 := ne_of_gt (cast_pos hm i)
  rw [lo]
  field_simp

theorem lo_le_hi {m : ℕ → ℕ} (hm : ∀ i, 0 < m i) (i : ℕ) : lo m i ≤ hi m i :=
  (div_le_div_iff_of_pos_right (cast_pos hm i)).2 (by linarith)

theorem lo_le_lo_succ {m : ℕ → ℕ} (hm : ∀ i, 0 < m i) (i : ℕ) : lo m i ≤ lo m (i + 1) := by
  have hM : (0 : ℝ) < (m (i + 1) : ℝ) := cast_pos hm (i + 1)
  have h1 : (m (i + 1) : ℝ) * lo m i < (idx m (i + 1) : ℝ) := by
    rw [idx_succ]
    push_cast
    exact Int.lt_floor_add_one _
  show lo m i ≤ ((idx m (i + 1) : ℝ) + 1 / 4) / (m (i + 1) : ℝ)
  rw [le_div_iff₀ hM]
  linarith

theorem hi_succ_le_hi {m : ℕ → ℕ} (hm : ∀ i, 0 < m i) (hgrow : ∀ i, 4 * m i ≤ m (i + 1))
    (i : ℕ) : hi m (i + 1) ≤ hi m i := by
  have hM' : (0 : ℝ) < (m i : ℝ) := cast_pos hm i
  have hM : (0 : ℝ) < (m (i + 1) : ℝ) := cast_pos hm (i + 1)
  have hg : 4 * (m i : ℝ) ≤ (m (i + 1) : ℝ) := by exact_mod_cast hgrow i
  have h2 : (idx m (i + 1) : ℝ) ≤ (m (i + 1) : ℝ) * lo m i + 1 := by
    have := Int.floor_le ((m (i + 1) : ℝ) * lo m i)
    rw [idx_succ]
    push_cast
    linarith
  have h3 : (m (i + 1) : ℝ) * ((m i : ℝ) * lo m i)
      = (m (i + 1) : ℝ) * ((idx m i : ℝ) + 1 / 4) := by rw [mul_lo hm i]
  have h4 : (idx m (i + 1) : ℝ) * (m i : ℝ)
      ≤ ((m (i + 1) : ℝ) * lo m i + 1) * (m i : ℝ) :=
    mul_le_mul_of_nonneg_right h2 hM'.le
  show ((idx m (i + 1) : ℝ) + 3 / 4) / (m (i + 1) : ℝ)
      ≤ ((idx m i : ℝ) + 3 / 4) / (m i : ℝ)
  rw [div_le_div_iff₀ hM hM']
  nlinarith [h3, h4, hg, hM'.le]

end NestedInterval

open NestedInterval in
theorem exists_rotation_of_four_mul_le (m : ℕ → ℕ) (hm : ∀ i, 0 < m i)
    (hgrow : ∀ i, 4 * m i ≤ m (i + 1)) :
    ∃ θ : ℝ, ∀ i, 1 / 4 ≤ Int.fract (θ * m i) ∧ Int.fract (θ * m i) ≤ 3 / 4 := by
  have hmono : Monotone (lo m) := monotone_nat_of_le_succ (lo_le_lo_succ hm)
  have hanti : Antitone (hi m) := antitone_nat_of_succ_le (hi_succ_le_hi hm hgrow)
  have hcross : ∀ i j, lo m i ≤ hi m j := by
    intro i j
    calc lo m i ≤ lo m (max i j) := hmono (le_max_left i j)
      _ ≤ hi m (max i j) := lo_le_hi hm _
      _ ≤ hi m j := hanti (le_max_right i j)
  have hbdd : BddAbove (Set.range (lo m)) := by
    refine ⟨hi m 0, ?_⟩
    rintro x ⟨i, rfl⟩
    exact hcross i 0
  refine ⟨⨆ k, lo m k, fun i => ?_⟩
  set θ : ℝ := ⨆ k, lo m k with hθ
  have hlow : ((idx m i : ℝ) + 1 / 4) / (m i : ℝ) ≤ θ := le_ciSup hbdd i
  have hhigh : θ ≤ ((idx m i : ℝ) + 3 / 4) / (m i : ℝ) := ciSup_le fun j => hcross j i
  have hpos : (0 : ℝ) < (m i : ℝ) := cast_pos hm i
  have hl : (idx m i : ℝ) + 1 / 4 ≤ θ * (m i : ℝ) := (div_le_iff₀ hpos).1 hlow
  have hr : θ * (m i : ℝ) ≤ (idx m i : ℝ) + 3 / 4 := (le_div_iff₀ hpos).1 hhigh
  have hfract : Int.fract (θ * (m i : ℝ)) = θ * (m i : ℝ) - (idx m i : ℝ) := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, idx m i, by ring⟩
  rw [hfract]
  constructor <;> linarith

end Erdos894
