import Mathlib

/-!
# Erdős Problem 1147: definitions

For a real number `x`, `nd x` is the distance from `x` to the nearest integer (written `‖x‖` in
the literature).  A set `A ⊆ ℕ` is an *asymptotic additive basis of order 2* when every
sufficiently large natural number is a sum of two elements of `A` (Konieczny's convention for
"basis of order 2"; the reading "every positive integer" is vacuous for sets of positive integers,
since `1` is not a sum of two of them, and is therefore not used).  The set displayed in Erdős Problem 1147 is
`{n ≥ 1 : ‖α n²‖ < 1 / log n}`; the recurrence set with threshold function `ε` is
`{n ≥ 1 : ‖α n²‖ ≤ ε n}`.
-/

open Filter

namespace Erdos1147

/-- Distance from `x` to the nearest integer. -/
noncomputable def nd (x : ℝ) : ℝ := |x - round x|

theorem nd_nonneg (x : ℝ) : 0 ≤ nd x := abs_nonneg _

theorem nd_le_half (x : ℝ) : nd x ≤ 1 / 2 := by
  exact abs_sub_round x

/-- The nearest integer is at least as close as any other integer. -/
theorem nd_le_abs_sub_int (x : ℝ) (m : ℤ) : nd x ≤ |x - m| := by
  exact round_le x m

theorem nd_add_int (x : ℝ) (m : ℤ) : nd (x + m) = nd x := by
  rw [nd, nd, round_add_intCast]
  congr 1
  push_cast
  ring

theorem nd_sub_int (x : ℝ) (m : ℤ) : nd (x - m) = nd x := by
  have h : nd (x + ((-m : ℤ) : ℝ)) = nd x := nd_add_int x (-m)
  rwa [Int.cast_neg, ← sub_eq_add_neg] at h

/-- Reflecting a real number does not increase its distance to the nearest integer. -/
private theorem nd_neg_le (x : ℝ) : nd (-x) ≤ nd x := by
  have h : nd (-x) ≤ |(-x) - ((-round x : ℤ) : ℝ)| := nd_le_abs_sub_int (-x) (-round x)
  have key : |(-x) - ((-round x : ℤ) : ℝ)| = nd x := by
    rw [nd, ← abs_neg (x - (round x : ℝ))]
    congr 1
    push_cast
    ring
  rwa [key] at h

theorem nd_neg (x : ℝ) : nd (-x) = nd x := by
  refine le_antisymm (nd_neg_le x) ?_
  have h : nd (- -x) ≤ nd (-x) := nd_neg_le (-x)
  rwa [neg_neg] at h

theorem nd_add_le (x y : ℝ) : nd (x + y) ≤ nd x + nd y := by
  have h : nd (x + y) ≤ |x + y - ((round x + round y : ℤ) : ℝ)| :=
    nd_le_abs_sub_int (x + y) (round x + round y)
  have e : x + y - ((round x + round y : ℤ) : ℝ)
      = (x - (round x : ℝ)) + (y - (round y : ℝ)) := by
    push_cast
    ring
  rw [e] at h
  exact h.trans (abs_add_le _ _)

theorem nd_sub_le (x y : ℝ) : nd (x - y) ≤ nd x + nd y := by
  have h : nd (x + -y) ≤ nd x + nd (-y) := nd_add_le x (-y)
  rwa [← sub_eq_add_neg, nd_neg] at h

/-- `nd` is `1`-Lipschitz. -/
theorem nd_le_nd_add_abs_sub (x y : ℝ) : nd x ≤ nd y + |x - y| := by
  have h : nd x ≤ |x - (round y : ℝ)| := nd_le_abs_sub_int x (round y)
  have key : |x - (round y : ℝ)| ≤ |x - y| + |y - (round y : ℝ)| := abs_sub_le x y _
  have hy : nd y = |y - (round y : ℝ)| := rfl
  linarith

theorem nd_eq_zero_iff (x : ℝ) : nd x = 0 ↔ ∃ m : ℤ, x = m := by
  constructor
  · intro h
    rw [nd, abs_eq_zero, sub_eq_zero] at h
    exact ⟨round x, h⟩
  · rintro ⟨m, rfl⟩
    rw [nd, round_intCast, sub_self, abs_zero]

/-- Every integer is at distance at least `1 / 2` from `1 / 2`. -/
private theorem half_le_abs_half_sub_intCast (m : ℤ) : (1 : ℝ) / 2 ≤ |1 / 2 - (m : ℝ)| := by
  rcases le_or_gt m 0 with hm | hm
  · have hm' : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Points of the form `1/2 + t` with `|t| ≤ 1/2` are at distance at least `1/2 - |t|`
from the integers. -/
theorem half_sub_abs_le_nd_half_add (t : ℝ) (ht : |t| ≤ 1 / 2) : 1 / 2 - |t| ≤ nd (1 / 2 + t) := by
  have hle : 0 ≤ 1 / 2 - |t| := by linarith
  have h1 : (1 : ℝ) / 2 ≤ |1 / 2 - ((round (1 / 2 + t) : ℤ) : ℝ)| :=
    half_le_abs_half_sub_intCast _
  have h2 : |1 / 2 - ((round (1 / 2 + t) : ℤ) : ℝ)|
      ≤ |1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)| + |t| := by
    have e : (1 : ℝ) / 2 - ((round (1 / 2 + t) : ℤ) : ℝ)
        = (1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)) + (-t) := by ring
    calc |1 / 2 - ((round (1 / 2 + t) : ℤ) : ℝ)|
        = |(1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)) + (-t)| := by rw [e]
      _ ≤ |1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)| + |(-t)| := abs_add_le _ _
      _ = |1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)| + |t| := by rw [abs_neg]
  have h3 : nd (1 / 2 + t) = |1 / 2 + t - ((round (1 / 2 + t) : ℤ) : ℝ)| := rfl
  linarith

/-- For an odd integer `m`, `m / 2` differs from `1 / 2` by an integer. -/
theorem nd_odd_div_two_add (m : ℤ) (hm : Odd m) (t : ℝ) :
    nd ((m : ℝ) / 2 + t) = nd (1 / 2 + t) := by
  obtain ⟨k, rfl⟩ := hm
  have e : ((2 * k + 1 : ℤ) : ℝ) / 2 + t = (1 / 2 + t) + ((k : ℤ) : ℝ) := by
    push_cast
    ring
  rw [e]
  exact nd_add_int _ _

/-- Every sufficiently large natural number is a sum of two elements of `A`. -/
def IsAsymptoticBasis2 (A : Set ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ m : ℕ, n₀ ≤ m → ∃ a ∈ A, ∃ b ∈ A, a + b = m

theorem IsAsymptoticBasis2.mono {A B : Set ℕ} (hAB : A ⊆ B) (hA : IsAsymptoticBasis2 A) :
    IsAsymptoticBasis2 B := by
  obtain ⟨n₀, h⟩ := hA
  exact ⟨n₀, fun m hm => by
    obtain ⟨a, ha, b, hb, hab⟩ := h m hm
    exact ⟨a, hAB ha, b, hAB hb, hab⟩⟩

/-- The recurrence set `{n ≥ 1 : ‖α n²‖ ≤ ε n}`. -/
def recSet (α : ℝ) (ε : ℕ → ℝ) : Set ℕ := {n | 1 ≤ n ∧ nd (α * (n : ℝ) ^ 2) ≤ ε n}

/-- The set displayed in Erdős Problem 1147: `{n ≥ 1 : ‖α n²‖ < 1 / log n}`. -/
def erdosSet (α : ℝ) : Set ℕ := {n | 1 ≤ n ∧ nd (α * (n : ℝ) ^ 2) < 1 / Real.log n}

theorem erdosSet_subset_recSet (α : ℝ) : erdosSet α ⊆ recSet α (fun n => 1 / Real.log n) :=
  fun _ h => ⟨h.1, h.2.le⟩

end Erdos1147
