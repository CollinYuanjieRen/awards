import Mathlib

/-!
# JSP-000799 / Erdős #960 — trigonometric ingredients

The construction places points on the nodal cubic at parameters `cot (iπ/M)`, `0 < i < M`.
This file proves the facts needed about those cotangents:

* `cot_angle_injOn`: `i ↦ cot (iπ/M)` is injective on `{i | 0 < i ∧ i < M}`;
* `cot_criterion`: `cot θᵢ cot θⱼ + cot θⱼ cot θₖ + cot θₖ cot θᵢ = 1 ↔ M ∣ i + j + k`,

the latter via the three-angle identity
`sin (a+b+c) = sin a sin b sin c (cot a cot b + cot b cot c + cot c cot a − 1)`.
-/

namespace Erdos960

/-- The angle `iπ/M`. -/
noncomputable def angle (M i : ℕ) : ℝ := (i : ℝ) * Real.pi / M

private theorem cast_pos_of_lt {M i : ℕ} (hM : i < M) : (0 : ℝ) < M := by
  have : 0 < M := lt_of_le_of_lt (Nat.zero_le i) hM
  exact_mod_cast this

private theorem angle_pos {M i : ℕ} (h0 : 0 < i) (hM : i < M) : 0 < angle M i := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast h0
  exact div_pos (mul_pos hi0 Real.pi_pos) (cast_pos_of_lt hM)

private theorem angle_lt_pi {M i : ℕ} (hM : i < M) : angle M i < Real.pi := by
  have hM0 : (0 : ℝ) < M := cast_pos_of_lt hM
  have hlt : (i : ℝ) < M := by exact_mod_cast hM
  have hpi := Real.pi_pos
  rw [angle, div_lt_iff₀ hM0]
  nlinarith

theorem sin_angle_pos {M i : ℕ} (h0 : 0 < i) (hM : i < M) : 0 < Real.sin (angle M i) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos h0 hM) (angle_lt_pi hM)

private theorem cot_eq_tan_pi_div_two_sub (x : ℝ) :
    Real.cot x = Real.tan (Real.pi / 2 - x) := by
  rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]

/-- `cot` is injective on the angles `iπ/M`, `0 < i < M`. -/
theorem cot_angle_injOn (M : ℕ) :
    Set.InjOn (fun i : ℕ => Real.cot (angle M i)) {i : ℕ | 0 < i ∧ i < M} := by
  intro i hi j hj hij
  obtain ⟨hi0, hiM⟩ := hi
  obtain ⟨hj0, hjM⟩ := hj
  have mem : ∀ {a : ℝ}, 0 < a → a < Real.pi →
      Real.pi / 2 - a ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro a ha ha'
    constructor <;> linarith
  have htan : Real.tan (Real.pi / 2 - angle M i) = Real.tan (Real.pi / 2 - angle M j) := by
    simpa [cot_eq_tan_pi_div_two_sub] using hij
  have hang : angle M i = angle M j := by
    have := Real.injOn_tan (mem (angle_pos hi0 hiM) (angle_lt_pi hiM))
      (mem (angle_pos hj0 hjM) (angle_lt_pi hjM)) htan
    linarith
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt (cast_pos_of_lt hiM)
  rw [angle, angle, div_eq_div_iff hMne hMne] at hang
  have h1 : (i : ℝ) * Real.pi = (j : ℝ) * Real.pi := mul_right_cancel₀ hMne hang
  have h2 : (i : ℝ) = j := mul_right_cancel₀ Real.pi_ne_zero h1
  exact_mod_cast h2

/-- The three-angle identity: `sin(a+b+c) = sin a sin b sin c (cot a cot b + cot b cot c + cot c cot a − 1)`
whenever the three sines are nonzero. -/
theorem sin_add_add_eq_mul_cot (a b c : ℝ) (ha : Real.sin a ≠ 0) (hb : Real.sin b ≠ 0)
    (hc : Real.sin c ≠ 0) :
    Real.sin (a + b + c) = Real.sin a * Real.sin b * Real.sin c *
      (Real.cot a * Real.cot b + Real.cot b * Real.cot c + Real.cot c * Real.cot a - 1) := by
  rw [Real.sin_add, Real.sin_add, Real.cos_add, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    Real.cot_eq_cos_div_sin]
  field_simp
  ring

/-- `sin((i+j+k)π/M) = 0` iff `M ∣ i + j + k`. -/
theorem sin_angle_sum_eq_zero_iff {M i j k : ℕ} (hM : 0 < M) :
    Real.sin (angle M i + angle M j + angle M k) = 0 ↔ (i + j + k) % M = 0 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hM0
  have hsum : angle M i + angle M j + angle M k = ((i + j + k : ℕ) : ℝ) * Real.pi / M := by
    simp only [angle]
    push_cast
    ring
  rw [hsum, Real.sin_eq_zero_iff, ← Nat.dvd_iff_mod_eq_zero, ← Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (n : ℝ) * Real.pi * M = (((i + j + k : ℕ) : ℝ) * Real.pi / M) * M := by rw [hn]
    rw [div_mul_cancel₀ _ hMne] at h2
    have h3 : ((n : ℝ) * M) * Real.pi = ((i + j + k : ℕ) : ℝ) * Real.pi := by
      linear_combination h2
    have h4 : (n : ℝ) * M = ((i + j + k : ℕ) : ℝ) := mul_right_cancel₀ Real.pi_ne_zero h3
    have h5 : ((i + j + k : ℕ) : ℝ) = (M : ℝ) * (n : ℝ) := by linarith [h4]
    exact_mod_cast h5
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h5 : ((i + j + k : ℕ) : ℝ) = (M : ℝ) * (n : ℝ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hn
    rw [h5]
    field_simp

/-- The collinearity criterion in index form. -/
theorem cot_criterion {M i j k : ℕ} (hM : 0 < M) (hi : 0 < i ∧ i < M) (hj : 0 < j ∧ j < M)
    (hk : 0 < k ∧ k < M) :
    Real.cot (angle M i) * Real.cot (angle M j) + Real.cot (angle M j) * Real.cot (angle M k) +
      Real.cot (angle M k) * Real.cot (angle M i) = 1 ↔ (i + j + k) % M = 0 := by
  have hsi := sin_angle_pos hi.1 hi.2
  have hsj := sin_angle_pos hj.1 hj.2
  have hsk := sin_angle_pos hk.1 hk.2
  have key := sin_add_add_eq_mul_cot (angle M i) (angle M j) (angle M k)
    (ne_of_gt hsi) (ne_of_gt hsj) (ne_of_gt hsk)
  rw [← sin_angle_sum_eq_zero_iff (i := i) (j := j) (k := k) hM, key, mul_eq_zero, mul_eq_zero,
    mul_eq_zero]
  constructor
  · intro h
    exact Or.inr (sub_eq_zero.mpr h)
  · rintro (((h | h) | h) | h)
    · exact absurd h (ne_of_gt hsi)
    · exact absurd h (ne_of_gt hsj)
    · exact absurd h (ne_of_gt hsk)
    · exact sub_eq_zero.mp h

end Erdos960

