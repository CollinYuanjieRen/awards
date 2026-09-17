import Erdos210Ordinary.Definitions

/-!
# Erdős Problem 210 — basic affine geometry of `D`, `OnLine`, `SameSide`, `OppSide`

`D a b ·` is an affine functional on `ℝ × ℝ` (`D_affine`); its zero set is the line through `a`
and `b` and its two strict sign classes are the open half-planes.  This file collects the
elementary algebraic facts used everywhere later: the symmetries of `D`, the parametrisation of a
line, the fact that a line is determined by any two of its points, the intermediate-value step
turning `OppSide` into an actual crossing point, and the convexity/openness of a strict side.
-/

namespace Erdos210

theorem D_swap (a b c : ℝ × ℝ) : D b a c = - D a b c := by
  simp only [D]; ring

theorem D_cyclic (a b c : ℝ × ℝ) : D b c a = D a b c := by
  simp only [D]; ring

theorem D_self_left (a c : ℝ × ℝ) : D a a c = 0 := by
  simp only [D]; ring

theorem D_left (a b : ℝ × ℝ) : D a b a = 0 := by
  simp only [D]; ring

theorem D_right (a b : ℝ × ℝ) : D a b b = 0 := by
  simp only [D]; ring

theorem onLine_comm {a b z : ℝ × ℝ} : OnLine a b z ↔ OnLine b a z := by
  simp only [OnLine, D]
  constructor <;> intro h <;> linarith

theorem onLine_left (a b : ℝ × ℝ) : OnLine a b a := D_left a b

theorem onLine_right (a b : ℝ × ℝ) : OnLine a b b := D_right a b

theorem D_affine (a b z w : ℝ × ℝ) (t : ℝ) :
    D a b (z + t • (w - z)) = (1 - t) * D a b z + t * D a b w := by
  simp only [D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

theorem onLine_param (a b : ℝ × ℝ) (s : ℝ) : OnLine a b (a + s • (b - a)) := by
  simp only [OnLine, D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

theorem exists_param_of_onLine {a b z : ℝ × ℝ} (hab : a ≠ b) (hz : OnLine a b z) :
    ∃ s : ℝ, z = a + s • (b - a) := by
  simp only [OnLine, D] at hz
  by_cases h1 : b.1 - a.1 = 0
  · have hb1 : b.1 = a.1 := by linarith
    have h2 : b.2 - a.2 ≠ 0 := by
      intro h2
      exact hab (Prod.ext (by linarith) (by linarith))
    have hz1 : z.1 = a.1 := by
      have h3 : (b.2 - a.2) * (z.1 - a.1) = 0 := by rw [h1] at hz; linarith
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h h2
      · linarith
    refine ⟨(z.2 - a.2) / (b.2 - a.2), Prod.ext ?_ ?_⟩
    · simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      rw [hb1, hz1]; ring
    · simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      rw [div_mul_cancel₀ _ h2]; ring
  · refine ⟨(z.1 - a.1) / (b.1 - a.1), Prod.ext ?_ ?_⟩
    · simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      rw [div_mul_cancel₀ _ h1]; ring
    · simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith [hz]

theorem D_param (a b w : ℝ × ℝ) (s s' : ℝ) :
    D (a + s • (b - a)) (a + s' • (b - a)) w = (s' - s) * D a b w := by
  simp only [D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

/-- A line is determined by any two of its points. -/
theorem onLine_iff_of_onLine {a b z z' : ℝ × ℝ} (hab : a ≠ b) (hz : OnLine a b z)
    (hz' : OnLine a b z') (hzz' : z ≠ z') (w : ℝ × ℝ) : OnLine z z' w ↔ OnLine a b w := by
  obtain ⟨s, rfl⟩ := exists_param_of_onLine hab hz
  obtain ⟨s', rfl⟩ := exists_param_of_onLine hab hz'
  have hss : s' - s ≠ 0 := by
    intro h
    exact hzz' (by rw [show s = s' by linarith])
  simp only [OnLine, D_param, mul_eq_zero, hss, false_or]

/-- Two lines sharing two distinct points coincide. -/
theorem onLine_iff_of_two {a b c d z z' : ℝ × ℝ} (hab : a ≠ b) (hcd : c ≠ d)
    (h1 : OnLine a b z) (h2 : OnLine a b z') (h3 : OnLine c d z) (h4 : OnLine c d z')
    (hzz' : z ≠ z') (w : ℝ × ℝ) : OnLine a b w ↔ OnLine c d w := by
  rw [← onLine_iff_of_onLine hab h1 h2 hzz' w, onLine_iff_of_onLine hcd h3 h4 hzz' w]

/-- Strictly opposite sides ⇒ the line crosses the open segment. -/
theorem exists_cross_of_oppSide {a b z w : ℝ × ℝ} (h : OppSide a b z w) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ OnLine a b (z + t • (w - z)) := by
  simp only [OppSide] at h
  have hd : D a b z - D a b w ≠ 0 := by
    intro h0
    have hzw : D a b z = D a b w := by linarith
    rw [hzw] at h
    exact absurd h (not_lt.2 (mul_self_nonneg _))
  have key : D a b z / (D a b z - D a b w) * (D a b z - D a b w) = D a b z :=
    div_mul_cancel₀ _ hd
  refine ⟨D a b z / (D a b z - D a b w), ?_, ?_, ?_⟩
  · rcases mul_neg_iff.mp h with ⟨hp, hn⟩ | ⟨hn, hp⟩ <;> nlinarith [key]
  · rcases mul_neg_iff.mp h with ⟨hp, hn⟩ | ⟨hn, hp⟩ <;> nlinarith [key]
  · simp only [OnLine, D_affine]
    field_simp
    ring

theorem sameSide_segment {a b p z w : ℝ × ℝ} (hz : SameSide a b p z) (hw : SameSide a b p w)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : SameSide a b p (z + t • (w - z)) := by
  simp only [SameSide] at hz hw ⊢
  rw [D_affine]
  have e : D a b p * ((1 - t) * D a b z + t * D a b w)
      = (1 - t) * (D a b p * D a b z) + t * (D a b p * D a b w) := by ring
  rw [e]
  rcases eq_or_lt_of_le ht1 with rfl | h1
  · linarith
  · have h1' : 0 < 1 - t := by linarith
    nlinarith

/-- Strict sides are open along any direction. -/
theorem sameSide_small {a b p w : ℝ × ℝ} (hw : SameSide a b p w) (e : ℝ × ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → SameSide a b p (w + t • e) := by
  simp only [SameSide] at hw ⊢
  set A := D a b w with hAdef
  set L := D a b (w + e) - D a b w with hLdef
  have key : ∀ t : ℝ, D a b (w + t • e) = A + t * L := by
    intro t
    simp only [hAdef, hLdef, D, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hw
    exact lt_irrefl 0 hw
  have hden : (0 : ℝ) < |L| + 1 := by positivity
  refine ⟨|A| / (|L| + 1), div_pos (abs_pos.2 hA0) hden, ?_⟩
  intro t ht
  rw [lt_div_iff₀ hden] at ht
  have hb : |t * L| < |A| := by
    rw [abs_mul]
    nlinarith [abs_nonneg t, abs_nonneg L, ht]
  rw [key t]
  rcases lt_or_gt_of_ne hA0 with hA | hA
  · have h2 : |t * L| < -A := by rwa [abs_of_neg hA] at hb
    have h3 : t * L < -A := lt_of_abs_lt h2
    have hP : D a b p < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg hP (by linarith)
  · have h2 : |t * L| < A := by rwa [abs_of_pos hA] at hb
    have h3 : -A < t * L := neg_lt_of_abs_lt h2
    have hP : 0 < D a b p := by nlinarith
    exact mul_pos hP (by linarith)

theorem sameSide_comm {a b z w : ℝ × ℝ} : SameSide a b z w ↔ SameSide a b w z := by
  simp only [SameSide]
  rw [mul_comm]

theorem sameSide_swap {a b z w : ℝ × ℝ} : SameSide b a z w ↔ SameSide a b z w := by
  have h1 : D b a z = - D a b z := D_swap a b z
  have h2 : D b a w = - D a b w := D_swap a b w
  simp only [SameSide, h1, h2, neg_mul_neg]

theorem not_onLine_of_sameSide {a b z w : ℝ × ℝ} (h : SameSide a b z w) : ¬ OnLine a b w := by
  simp only [SameSide] at h
  intro h0
  rw [OnLine] at h0
  rw [h0, mul_zero] at h
  exact lt_irrefl 0 h

end Erdos210
