import Erdos210Ordinary.Basic

/-!
# Erdős Problem 210 — no double vision

Phase 3 (iii).  Suppose `p` and `p'` lie strictly on the same side of the line `a b`, and each of
them "sees" a point of that line through the other's line of sight: `x` and `x'` are two points of
`line(a, b)` lying strictly on the same side of `line(a, p')` as `p`, resp. of `line(a, p)` as `p'`,
and `x`, `x'` lie on the same side of the vertex `a` (`0 < s * s'` for the parameters).  This is
impossible: writing `Q = D a p' p`, `A = D a b p`, `A' = D a b p'`, the two side conditions read
`0 < Q * (-s * A')` and `0 < (-Q) * (-s' * A)`, whose product is `-(s * s') * (A * A') * Q ^ 2 > 0`,
contradicting `0 < s * s'` and `0 < A * A'`.

The same statement at the vertex `b` is `no_double_vision'`.  The companion combinatorial gadgets
`piece` (which of the three pieces of `line(a, b) \ {a, b}` a parameter lands in) and
`pos_mul_of_decide_eq'` (agreeing `Bool` signs give a positive product) record the two "same key"
consequences used by the charging argument.
-/

namespace Erdos210

/-- The algebraic core of (iii): two opposite-sign visibility conditions cannot hold together. -/
private theorem vision_aux {Q A A' s s' : ℝ} (h1 : 0 < Q * (-s * A'))
    (h2 : 0 < -Q * (-s' * A)) (hss : 0 < s * s') (hside : 0 < A * A') : False := by
  have key : 0 < Q * (-s * A') * (-Q * (-s' * A)) := mul_pos h1 h2
  have hEq : Q * (-s * A') * (-Q * (-s' * A)) = -(s * s' * (A * A') * Q ^ 2) := by ring
  have hnn : 0 ≤ s * s' * (A * A') * Q ^ 2 :=
    mul_nonneg (mul_pos hss hside).le (sq_nonneg Q)
  rw [hEq] at key
  linarith

/-- (iii) vertex `a` form -/
theorem no_double_vision {a b p p' x x' : ℝ × ℝ} {s s' : ℝ} (hx : x = a + s • (b - a))
    (hx' : x' = a + s' • (b - a)) (hss : 0 < s * s') (hside : 0 < D a b p * D a b p')
    (h1 : SameSide a p' p x) (h2 : SameSide a p p' x') : False := by
  subst hx
  subst hx'
  have e1 : D a p' (a + s • (b - a)) = -s * D a b p' := by
    simp only [D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  have e2 : D a p (a + s' • (b - a)) = -s' * D a b p := by
    simp only [D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  have e3 : D a p p' = - D a p' p := by
    simp only [D]; ring
  simp only [SameSide, e1] at h1
  simp only [SameSide, e2, e3] at h2
  exact vision_aux h1 h2 hss hside

/-- (iii) vertex `b` form: `x = b + s • (b - a)`, `x' = b + s' • (b - a)` -/
theorem no_double_vision' {a b p p' x x' : ℝ × ℝ} {s s' : ℝ} (hx : x = b + s • (b - a))
    (hx' : x' = b + s' • (b - a)) (hss : 0 < s * s') (hside : 0 < D a b p * D a b p')
    (h1 : SameSide b p' p x) (h2 : SameSide b p p' x') : False := by
  subst hx
  subst hx'
  have e1 : D b p' (b + s • (b - a)) = -s * D a b p' := by
    simp only [D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  have e2 : D b p (b + s' • (b - a)) = -s' * D a b p := by
    simp only [D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  have e3 : D b p p' = - D b p' p := by
    simp only [D]; ring
  simp only [SameSide, e1] at h1
  simp only [SameSide, e2, e3] at h2
  exact vision_aux h1 h2 hss hside

/-- the three pieces of a line minus two of its points -/
noncomputable def piece (s : ℝ) : Fin 3 := if s < 0 then 0 else if s < 1 then 1 else 2

private theorem piece_neg {s : ℝ} (h : s < 0) : piece s = 0 := by
  unfold piece
  split_ifs
  rfl

private theorem piece_mid {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : piece s = 1 := by
  unfold piece
  split_ifs <;> first | rfl | (exfalso; linarith)

private theorem piece_gt {s : ℝ} (h : 1 < s) : piece s = 2 := by
  unfold piece
  split_ifs <;> first | rfl | (exfalso; linarith)

/-- A parameter distinct from `0` and `1` lies in exactly one of the three pieces. -/
private theorem piece_trichotomy {s : ℝ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s < 0 ∨ (0 < s ∧ s < 1) ∨ 1 < s := by
  rcases lt_or_gt_of_ne hs0 with h | h
  · exact Or.inl h
  · rcases lt_or_gt_of_ne hs1 with h' | h'
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    · exact Or.inr (Or.inr h')

theorem piece_eq_imp {s s' : ℝ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs0' : s' ≠ 0) (hs1' : s' ≠ 1)
    (h : piece s = piece s') : 0 < s * s' ∧ 0 < (s - 1) * (s' - 1) := by
  rcases piece_trichotomy hs0 hs1 with h1 | ⟨h1a, h1b⟩ | h1 <;>
    rcases piece_trichotomy hs0' hs1' with h2 | ⟨h2a, h2b⟩ | h2
  · exact ⟨mul_pos_of_neg_of_neg h1 h2,
      mul_pos_of_neg_of_neg (by linarith) (by linarith)⟩
  · rw [piece_neg h1, piece_mid h2a h2b] at h; exact absurd h (by simp)
  · rw [piece_neg h1, piece_gt h2] at h; exact absurd h (by simp)
  · rw [piece_mid h1a h1b, piece_neg h2] at h; exact absurd h (by simp)
  · exact ⟨mul_pos h1a h2a, mul_pos_of_neg_of_neg (by linarith) (by linarith)⟩
  · rw [piece_mid h1a h1b, piece_gt h2] at h; exact absurd h (by simp)
  · rw [piece_gt h1, piece_neg h2] at h; exact absurd h (by simp)
  · rw [piece_gt h1, piece_mid h2a h2b] at h; exact absurd h (by simp)
  · exact ⟨mul_pos (by linarith) (by linarith), mul_pos (by linarith) (by linarith)⟩

/-- Bool sign agreement gives a positive product -/
theorem pos_mul_of_decide_eq' {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : decide (0 < u) = decide (0 < v)) : 0 < u * v := by
  rw [decide_eq_decide] at h
  rcases lt_trichotomy u 0 with hu' | hu' | hu'
  · have hv0 : ¬ (0 < v) := fun hv' => absurd (h.2 hv') (not_lt.2 hu'.le)
    exact mul_pos_of_neg_of_neg hu' (lt_of_le_of_ne (not_lt.1 hv0) hv)
  · exact absurd hu' hu
  · exact mul_pos hu' (h.1 hu')

end Erdos210
