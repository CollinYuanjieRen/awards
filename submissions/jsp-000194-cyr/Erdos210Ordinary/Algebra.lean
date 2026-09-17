import Erdos210Ordinary.Definitions

/-!
# Erdős Problem 210 — the algebraic core

Two purely algebraic ingredients of the main argument.

* `exists_pivot` is the *sign lemma*: among three distinct nonzero reals `α i` there is a pivot
  index `i` such that exactly one of the two remaining ratios `α j / α i` lies in `(0, 1)`.
* `crossing_identity` computes, for a point `x`, a point `p`, a direction `u` and reals
  `α₁, αⱼ, γ`, the product of the two determinants that decide on which side of the line through
  `p₄ := p + γ • ((x + α₁ • u) - p)` and `pⱼ := x + αⱼ • u` the points `p` and `x` lie.
* `oppSide_of_pivot` reads off from that identity that the line `p₄ pⱼ` strictly separates `p`
  from `x` in the two relevant sign configurations.

This file only depends on `Definitions.lean`; the small algebraic facts it needs are proved here
as `private` lemmas.
-/

namespace Erdos210

/-! ### Ratios in `(0, 1)` -/

/-- A ratio `y / x` lies in `(0, 1)` exactly when `x` and `y` have the same sign and `|y| < |x|`. -/
private lemma ratio_iff {x y : ℝ} (hx : x ≠ 0) :
    (0 < y / x ∧ y / x < 1) ↔ (0 < x * y ∧ |y| < |x|) := by
  have hax : 0 < |x| := abs_pos.mpr hx
  have hx2 : 0 < x * x := mul_self_pos.mpr hx
  obtain ⟨t, rfl⟩ : ∃ t : ℝ, y = t * x := ⟨y / x, (div_mul_cancel₀ y hx).symm⟩
  rw [mul_div_cancel_right₀ t hx, abs_mul]
  constructor
  · rintro ⟨h1, h2⟩
    have habs : |t| < 1 := abs_lt.mpr ⟨by linarith, h2⟩
    refine ⟨?_, ?_⟩
    · have : x * (t * x) = t * (x * x) := by ring
      rw [this]
      exact mul_pos h1 hx2
    · nlinarith
  · rintro ⟨h1, h2⟩
    have habs : |t| < 1 := by nlinarith
    rw [abs_lt] at habs
    refine ⟨?_, habs.2⟩
    nlinarith [mul_self_pos.mpr hx]

/-- Two distinct reals of the same sign have distinct absolute values. -/
private lemma abs_lt_or_abs_lt {a b : ℝ} (hab : 0 < a * b) (h : a ≠ b) :
    |b| < |a| ∨ |a| < |b| := by
  rcases lt_trichotomy |b| |a| with h1 | h1 | h1
  · exact Or.inl h1
  · exfalso
    rcases abs_eq_abs.mp h1.symm with h2 | h2
    · exact h h2
    · rw [h2] at hab; nlinarith [sq_nonneg b]
  · exact Or.inr h1

/-- The pivot property: `y / x ∈ (0, 1)` but `z / x ∉ (0, 1)`. -/
private def Piv (x y z : ℝ) : Prop :=
  (0 < y / x ∧ y / x < 1) ∧ ¬ (0 < z / x ∧ z / x < 1)

private lemma piv_of_abs {x y z : ℝ} (hx : x ≠ 0) (h1 : 0 < x * y) (h2 : |y| < |x|)
    (h3 : x * z < 0 ∨ |x| ≤ |z|) : Piv x y z := by
  refine ⟨(ratio_iff hx).mpr ⟨h1, h2⟩, ?_⟩
  rw [ratio_iff hx]
  rintro ⟨h4, h5⟩
  rcases h3 with h3 | h3
  · linarith
  · linarith

/-- The pivot exists once we know one same-sign pair, ordered by absolute value. -/
private lemma piv_aux {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : 0 < a * b)
    (h : |b| < |a|) (hbc : b ≠ c) :
    Piv a b c ∨ Piv c b a ∨ Piv b c a := by
  rcases lt_trichotomy (a * c) 0 with h1 | h1 | h1
  · exact Or.inl (piv_of_abs ha hab h (Or.inl h1))
  · exact absurd h1 (mul_ne_zero ha hc)
  · rcases le_or_gt |a| |c| with h2 | h2
    · exact Or.inl (piv_of_abs ha hab h (Or.inr h2))
    · have hbc' : 0 < b * c := by
        nlinarith [mul_pos hab h1, mul_self_pos.mpr ha]
      rcases abs_lt_or_abs_lt hbc' hbc with h3 | h3
      · exact Or.inr (Or.inr (piv_of_abs hb hbc' h3 (Or.inr h.le)))
      · exact Or.inr (Or.inl (piv_of_abs hc (by linarith [mul_comm b c]) h3 (Or.inr h2.le)))

/-- Among three distinct nonzero reals one is a pivot. -/
private lemma pivot_of_three {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    Piv a b c ∨ Piv a c b ∨ Piv b a c ∨ Piv b c a ∨ Piv c a b ∨ Piv c b a := by
  have hsign : 0 < a * b ∨ 0 < a * c ∨ 0 < b * c := by
    rcases ha.lt_or_gt with h | h <;> rcases hb.lt_or_gt with h' | h' <;>
      rcases hc.lt_or_gt with h'' | h'' <;>
      first
        | exact Or.inl (by nlinarith)
        | exact Or.inr (Or.inl (by nlinarith))
        | exact Or.inr (Or.inr (by nlinarith))
  rcases hsign with h | h | h
  · rcases abs_lt_or_abs_lt h hab with h1 | h1
    · rcases piv_aux ha hb hc h h1 hbc with H | H | H <;> tauto
    · rcases piv_aux hb ha hc (by linarith [mul_comm a b]) h1 hac with H | H | H <;> tauto
  · rcases abs_lt_or_abs_lt h hac with h1 | h1
    · rcases piv_aux ha hc hb h h1 hbc.symm with H | H | H <;> tauto
    · rcases piv_aux hc ha hb (by linarith [mul_comm a c]) h1 hab with H | H | H <;> tauto
  · rcases abs_lt_or_abs_lt h hbc with h1 | h1
    · rcases piv_aux hb hc ha h h1 hac.symm with H | H | H <;> tauto
    · rcases piv_aux hc hb ha (by linarith [mul_comm b c]) h1 hab.symm with H | H | H <;>
        tauto

/-- Sign lemma: among three distinct nonzero reals there is a pivot `α i` such that exactly one of
the other two lies strictly between `0` and `α i`. -/
theorem exists_pivot (α : Fin 3 → ℝ) (h0 : ∀ i, α i ≠ 0) (hinj : Function.Injective α) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (0 < α j / α i ∧ α j / α i < 1) ∧ ¬ (0 < α k / α i ∧ α k / α i < 1) := by
  have H := pivot_of_three (h0 0) (h0 1) (h0 2) (hinj.ne (by simp)) (hinj.ne (by simp))
    (hinj.ne (by simp))
  rcases H with ⟨H1, H2⟩ | ⟨H1, H2⟩ | ⟨H1, H2⟩ | ⟨H1, H2⟩ | ⟨H1, H2⟩ | ⟨H1, H2⟩
  · exact ⟨0, 1, 2, by simp, by simp, by simp, H1, H2⟩
  · exact ⟨0, 2, 1, by simp, by simp, by simp, H1, H2⟩
  · exact ⟨1, 0, 2, by simp, by simp, by simp, H1, H2⟩
  · exact ⟨1, 2, 0, by simp, by simp, by simp, H1, H2⟩
  · exact ⟨2, 0, 1, by simp, by simp, by simp, H1, H2⟩
  · exact ⟨2, 1, 0, by simp, by simp, by simp, H1, H2⟩

/-! ### The crossing identity -/

/-- The crossing identity. -/
theorem crossing_identity (x p u : ℝ × ℝ) (α₁ αⱼ γ : ℝ) :
    D (p + γ • ((x + α₁ • u) - p)) (x + αⱼ • u) p * D (p + γ • ((x + α₁ • u) - p)) (x + αⱼ • u) x
      = - (D x (x + u) p) ^ 2 * (γ * (1 - γ)) * (αⱼ * (αⱼ - α₁)) := by
  simp only [D, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  ring

/-- If the ratio `αⱼ / α₁` misses `(0, 1)`, then `αⱼ * (αⱼ - α₁)` is positive. -/
private lemma mul_sub_pos_of_not_ratio {α₁ αⱼ : ℝ} (h1 : α₁ ≠ 0) (hj : αⱼ ≠ 0) (hne : αⱼ ≠ α₁)
    (h : ¬ (0 < αⱼ / α₁ ∧ αⱼ / α₁ < 1)) : 0 < αⱼ * (αⱼ - α₁) := by
  obtain ⟨t, rfl⟩ : ∃ t : ℝ, αⱼ = t * α₁ := ⟨αⱼ / α₁, (div_mul_cancel₀ αⱼ h1).symm⟩
  rw [mul_div_cancel_right₀ t h1] at h
  have ht0 : t ≠ 0 := by rintro rfl; simp at hj
  have ht1 : t ≠ 1 := by rintro rfl; simp at hne
  have hq : 0 < t * (t - 1) := by
    rcases ht0.lt_or_gt with ht | ht
    · nlinarith
    · have h1t : 1 ≤ t := not_lt.mp fun hlt => h ⟨ht, hlt⟩
      have := lt_of_le_of_ne h1t (Ne.symm ht1)
      nlinarith
  have key : t * α₁ * (t * α₁ - α₁) = (t * (t - 1)) * (α₁ * α₁) := by ring
  rw [key]
  exact mul_pos hq (mul_self_pos.mpr h1)

/-- If the ratio `αⱼ / α₁` lies in `(0, 1)`, then `αⱼ * (αⱼ - α₁)` is negative. -/
private lemma mul_sub_neg_of_ratio {α₁ αⱼ : ℝ} (h1 : α₁ ≠ 0)
    (h : 0 < αⱼ / α₁ ∧ αⱼ / α₁ < 1) : αⱼ * (αⱼ - α₁) < 0 := by
  obtain ⟨t, rfl⟩ : ∃ t : ℝ, αⱼ = t * α₁ := ⟨αⱼ / α₁, (div_mul_cancel₀ αⱼ h1).symm⟩
  rw [mul_div_cancel_right₀ t h1] at h
  have key : t * α₁ * (t * α₁ - α₁) = (t * (t - 1)) * (α₁ * α₁) := by ring
  rw [key]
  exact mul_neg_of_neg_of_pos (by nlinarith [h.1, h.2]) (mul_self_pos.mpr h1)

/-- Pivot form of the core step: the line `p₄ pⱼ` strictly separates `p` from `x`. -/
theorem oppSide_of_pivot (x p u : ℝ × ℝ) (α₁ αⱼ γ : ℝ) (hΔ : D x (x + u) p ≠ 0)
    (h1 : α₁ ≠ 0) (hj : αⱼ ≠ 0) (hne : αⱼ ≠ α₁) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1)
    (hcase : (0 < γ ∧ γ < 1 ∧ ¬ (0 < αⱼ / α₁ ∧ αⱼ / α₁ < 1)) ∨
             (¬ (0 ≤ γ ∧ γ ≤ 1) ∧ (0 < αⱼ / α₁ ∧ αⱼ / α₁ < 1))) :
    OppSide (p + γ • ((x + α₁ • u) - p)) (x + αⱼ • u) p x := by
  have hΔ2 : 0 < D x (x + u) p ^ 2 := (sq_nonneg _).lt_of_ne (pow_ne_zero 2 hΔ).symm
  have hmain : 0 < (γ * (1 - γ)) * (αⱼ * (αⱼ - α₁)) := by
    rcases hcase with ⟨hg0, hg1, hnot⟩ | ⟨hg, hyes⟩
    · exact mul_pos (mul_pos hg0 (by linarith)) (mul_sub_pos_of_not_ratio h1 hj hne hnot)
    · refine mul_pos_of_neg_of_neg ?_ (mul_sub_neg_of_ratio h1 hyes)
      rcases lt_or_ge γ 0 with hg' | hg'
      · nlinarith
      · have : 1 < γ := not_le.mp fun hle => hg ⟨hg', hle⟩
        nlinarith
  have hpos := mul_pos hΔ2 hmain
  -- `hγ0` and `hγ1` are recorded for the caller's convenience; `hcase` already pins `γ` down.
  have _hγ : γ ≠ 0 ∧ γ ≠ 1 := ⟨hγ0, hγ1⟩
  simp only [OppSide, crossing_identity]
  nlinarith [hpos]

end Erdos210
