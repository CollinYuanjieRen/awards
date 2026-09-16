import Mathlib

/-!
# Separating closed segments in the plane by affine functionals

Every non-crossing claim in the straight-line drawings of `K₄` and of the bipyramids is
reduced to the sign of an affine functional `lineFun a b c : ℝ × ℝ → ℝ` on the endpoints of the
segments involved.  This file records the few general facts needed.
-/

open Set

/-- The affine functional `p ↦ a * p.1 + b * p.2 + c` on the plane. -/
def lineFun (a b c : ℝ) (p : ℝ × ℝ) : ℝ :=
  a * p.1 + b * p.2 + c

/-- On a segment, an affine functional is a convex combination of its endpoint values. -/
theorem lineFun_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hz : z ∈ segment ℝ p q) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      lineFun a b c z = (1 - t) * lineFun a b c p + t * lineFun a b c q ∧
      z = (1 - t) • p + t • q := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  refine ⟨t, ht0, ht1, ?_, rfl⟩
  simp only [lineFun, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- If both endpoint values are nonnegative, so is every value on the segment. -/
theorem lineFun_nonneg_of_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hp : 0 ≤ lineFun a b c p)
    (hq : 0 ≤ lineFun a b c q) (hz : z ∈ segment ℝ p q) : 0 ≤ lineFun a b c z := by
  obtain ⟨t, ht0, ht1, hzt, -⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  rw [hzt]
  exact add_nonneg (mul_nonneg (sub_nonneg.2 ht1) hp) (mul_nonneg ht0 hq)

/-- If both endpoint values are nonpositive, so is every value on the segment. -/
theorem lineFun_nonpos_of_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hp : lineFun a b c p ≤ 0)
    (hq : lineFun a b c q ≤ 0) (hz : z ∈ segment ℝ p q) : lineFun a b c z ≤ 0 := by
  obtain ⟨t, ht0, ht1, hzt, -⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  rw [hzt]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 ht1) hp)
    (mul_nonpos_of_nonneg_of_nonpos ht0 hq)

/-- If both endpoint values are positive, so is every value on the segment. -/
theorem lineFun_pos_of_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hp : 0 < lineFun a b c p)
    (hq : 0 < lineFun a b c q) (hz : z ∈ segment ℝ p q) : 0 < lineFun a b c z := by
  obtain ⟨t, ht0, ht1, hzt, -⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  rw [hzt]
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · simpa using hp
  · have h1 := mul_nonneg (sub_nonneg.2 ht1) hp.le
    have h2 := mul_pos htpos hq
    linarith

/-- If both endpoint values vanish, the functional vanishes on the segment. -/
theorem lineFun_eq_zero_of_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hp : lineFun a b c p = 0)
    (hq : lineFun a b c q = 0) (hz : z ∈ segment ℝ p q) : lineFun a b c z = 0 := by
  obtain ⟨t, ht0, ht1, hzt, -⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  rw [hzt, hp, hq, mul_zero, mul_zero, add_zero]

/-- If the functional vanishes at `p` and is positive at `q`, it is positive on the segment
away from `p`. -/
theorem lineFun_pos_of_mem_segment_of_ne {a b c : ℝ} {p q z : ℝ × ℝ} (hp : lineFun a b c p = 0)
    (hq : 0 < lineFun a b c q) (hz : z ∈ segment ℝ p q) (hzp : z ≠ p) : 0 < lineFun a b c z := by
  obtain ⟨t, ht0, ht1, hzt, hzeq⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  have ht : t ≠ 0 := by
    rintro rfl
    apply hzp
    rw [hzeq]
    simp
  rw [hzt, hp, mul_zero, zero_add]
  exact mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hq

/-- If the functional vanishes at `p` and is nonzero at `q`, it is nonzero on the segment
away from `p`. -/
theorem lineFun_ne_zero_of_mem_segment_of_ne {a b c : ℝ} {p q z : ℝ × ℝ}
    (hp : lineFun a b c p = 0) (hq : lineFun a b c q ≠ 0) (hz : z ∈ segment ℝ p q) (hzp : z ≠ p) :
    lineFun a b c z ≠ 0 := by
  obtain ⟨t, ht0, ht1, hzt, hzeq⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  have ht : t ≠ 0 := by
    rintro rfl
    apply hzp
    rw [hzeq]
    simp
  rw [hzt, hp, mul_zero, zero_add]
  exact mul_ne_zero ht hq

/-- Two segments are disjoint when a functional is positive on one and nonpositive on the
other. -/
theorem segment_disjoint_of_pos_of_nonpos {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : 0 < lineFun a b c p) (hq : 0 < lineFun a b c q) (hr : lineFun a b c r ≤ 0)
    (hs : lineFun a b c s ≤ 0) : Disjoint (segment ℝ p q) (segment ℝ r s) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  have h1 := lineFun_pos_of_mem_segment hp hq hz1
  have h2 := lineFun_nonpos_of_mem_segment hr hs hz2
  exact absurd h1 (not_lt.2 h2)

/-- If a functional vanishes at `p`, is positive at `q`, and is nonpositive on the segment
`[r, s]`, then `[p, q]` meets `[r, s]` at most in `p`. -/
theorem segment_inter_segment_subset_singleton {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : lineFun a b c p = 0) (hq : 0 < lineFun a b c q) (hr : lineFun a b c r ≤ 0)
    (hs : lineFun a b c s ≤ 0) : segment ℝ p q ∩ segment ℝ r s ⊆ {p} := by
  intro z ⟨hz1, hz2⟩
  rw [Set.mem_singleton_iff]
  by_contra hzp
  have h1 := lineFun_pos_of_mem_segment_of_ne hp hq hz1 hzp
  have h2 := lineFun_nonpos_of_mem_segment hr hs hz2
  exact absurd h1 (not_lt.2 h2)

/-- If a functional vanishes at `p`, is nonzero at `q`, and vanishes on the segment `[r, s]`,
then `[p, q]` meets `[r, s]` at most in `p`. -/
theorem segment_inter_segment_subset_singleton_of_ne_zero {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : lineFun a b c p = 0) (hq : lineFun a b c q ≠ 0) (hr : lineFun a b c r = 0)
    (hs : lineFun a b c s = 0) : segment ℝ p q ∩ segment ℝ r s ⊆ {p} := by
  intro z ⟨hz1, hz2⟩
  rw [Set.mem_singleton_iff]
  by_contra hzp
  have h1 := lineFun_ne_zero_of_mem_segment_of_ne hp hq hz1 hzp
  exact h1 (lineFun_eq_zero_of_mem_segment hr hs hz2)

/-- A point where a functional is positive does not lie on a segment where it is nonpositive. -/
theorem notMem_segment_of_pos_of_nonpos {a b c : ℝ} {p q z : ℝ × ℝ} (hz : 0 < lineFun a b c z)
    (hp : lineFun a b c p ≤ 0) (hq : lineFun a b c q ≤ 0) : z ∉ segment ℝ p q := by
  intro h
  exact absurd (lineFun_nonpos_of_mem_segment hp hq h) (not_le.2 hz)

/-- A point where a functional is nonzero does not lie on a segment where it vanishes. -/
theorem notMem_segment_of_ne_zero {a b c : ℝ} {p q z : ℝ × ℝ} (hz : lineFun a b c z ≠ 0)
    (hp : lineFun a b c p = 0) (hq : lineFun a b c q = 0) : z ∉ segment ℝ p q := by
  intro h
  exact hz (lineFun_eq_zero_of_mem_segment hp hq h)
