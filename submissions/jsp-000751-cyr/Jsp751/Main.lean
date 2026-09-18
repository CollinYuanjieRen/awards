import Jsp751.Lemmas
import Jsp751.Algebra
import Jsp751.Rank

/-!
# JSP-000751 / Erdős #903 — assembly

We put the combinatorial lemmas (`Jsp751/Lemmas.lean`), the algebraic identity for the entries of
`Q` (`Jsp751/Algebra.lean`) and the abstract rank lemma (`Jsp751/Rank.lean`) together.

Assume `v = p ^ 2 + p + 1 < b < v + p`.  Pick a point `x₀` of degree exactly `p + 1` and let
`F := through block x₀` be the `p + 1` blocks through it.  Two distinct blocks of `F` meet exactly
in `x₀`, so the principal submatrix of `Q` on `F` is
`diagonal β - (1 / d x₀) • J + α • a aᵀ`, where `β i = 1 - ∑_{x ∈ block i, x ≠ x₀} 1 / d x`.
By (L1) and (L3) each `β i ≥ 0`.

* If every `β i > 0`, the abstract rank lemma gives `rank Q_F ≥ p`, while `rank Q_F + v ≤ b < v + p`
  forces `rank Q_F ≤ p - 1`.
* Otherwise `β i = 0` for some `i ∈ F`, which forces `d x = p`, i.e. `degree x = p + 1`, for every
  `x ∈ block i`; then (L2) gives `b = v`, contradicting `v < b`.
-/

open Finset Matrix

namespace Erdos903

/-! ### The diagonal vector `β` and the shape of the principal submatrix of `Q` -/

section General

variable {v b : ℕ}

/-- `β i = 1 - ∑_{x ∈ block i, x ≠ x₀} 1 / d x`, the diagonal of the principal submatrix of `Q`
on the blocks through `x₀` after the rank-one part and the all-ones part are split off. -/
noncomputable def beta (block : Fin b → Finset (Fin v)) (x₀ : Fin v) (i : Fin b) : ℝ :=
  1 - ∑ x ∈ (block i).erase x₀, 1 / d block x

theorem beta_eq (block : Fin b → Finset (Fin v)) (x₀ : Fin v) (i : Fin b) :
    beta block x₀ i = 1 - ∑ x ∈ (block i).erase x₀, 1 / d block x := rfl

variable {block : Fin b → Finset (Fin v)}

/-- Two distinct blocks through a common point `x₀` meet exactly in `x₀`. -/
theorem inter_eq_singleton (h : IsLinearSpace block) {i j : Fin b} {x₀ : Fin v} (hij : i ≠ j)
    (hi : x₀ ∈ block i) (hj : x₀ ∈ block j) : block i ∩ block j = {x₀} := by
  have hmem : x₀ ∈ block i ∩ block j := Finset.mem_inter.2 ⟨hi, hj⟩
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, ?_⟩
  intro y hy
  exact Finset.card_le_one.1 (block_inter_card_le_one h hij) y hy x₀ hmem

/-- Splitting `x₀` off the sum defining `a i`. -/
theorem sum_block_eq_add {i : Fin b} {x₀ : Fin v} (hi : x₀ ∈ block i) :
    ∑ x ∈ block i, 1 / d block x
      = 1 / d block x₀ + ∑ x ∈ (block i).erase x₀, 1 / d block x :=
  (Finset.add_sum_erase (block i) (fun x => 1 / d block x) hi).symm

/-- The key identity: on the blocks through `x₀`, the principal submatrix of `Q` is
`diagonal β - (1 / d x₀) • J + α • a aᵀ`. -/
theorem Q_submatrix_eq (h : IsLinearSpace block) (hdeg : ∀ x, 2 ≤ degree block x) (x₀ : Fin v) :
    (Q block).submatrix (Subtype.val : ↥(through block x₀) → Fin b)
        (Subtype.val : ↥(through block x₀) → Fin b)
      = Matrix.diagonal (fun t : ↥(through block x₀) => beta block x₀ (t : Fin b))
        - (1 / d block x₀) • Matrix.of (fun (_ _ : ↥(through block x₀)) => (1 : ℝ))
        + α block • Matrix.vecMulVec (fun t : ↥(through block x₀) => a block (t : Fin b))
            (fun t : ↥(through block x₀) => a block (t : Fin b)) := by
  ext t s
  have ht : x₀ ∈ block (t : Fin b) := mem_through_iff.1 t.2
  have hs : x₀ ∈ block (s : Fin b) := mem_through_iff.1 s.2
  rw [Matrix.submatrix_apply, Q_apply block h hdeg, Matrix.add_apply, Matrix.sub_apply,
    Matrix.diagonal_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, smul_eq_mul, beta_eq]
  by_cases hts : t = s
  · subst hts
    rw [Finset.inter_self, sum_block_eq_add ht]
    simp only [ite_true]
    ring
  · have hne : (t : Fin b) ≠ (s : Fin b) := fun hc => hts (Subtype.ext hc)
    rw [ite_eq_right hts, ite_eq_right hne, inter_eq_singleton h hne ht hs,
      Finset.sum_singleton]
    ring

end General

/-! ### The two cases -/

section Gap

variable (p : ℕ) {b : ℕ} {block : Fin b → Finset (Fin (p ^ 2 + p + 1))}
  (h : IsLinearSpace block) (hb1 : p ^ 2 + p + 1 < b) (hb2 : b < p ^ 2 + p + 1 + p)
include h hb1 hb2

/-- Every point has degree at least `p + 1 ≥ 3`, so in particular at least `2`. -/
theorem two_le_degree (x : Fin (p ^ 2 + p + 1)) : 2 ≤ degree block x := by
  have h1 := degree_ge p h hb1 hb2 x
  have h2 := two_le_p p hb1 hb2
  omega

omit h in
theorem cast_p_pos : (0 : ℝ) < (p : ℝ) := by
  have h2 := two_le_p p hb1 hb2
  have : (0 : ℕ) < p := by omega
  exact_mod_cast this

/-- `d x = degree x - 1 ≥ p`. -/
theorem p_le_d (x : Fin (p ^ 2 + p + 1)) : (p : ℝ) ≤ d block x := by
  have h1 := degree_ge p h hb1 hb2 x
  have h2 : ((p : ℝ) + 1) ≤ (degree block x : ℝ) := by
    have : ((p + 1 : ℕ) : ℝ) ≤ (degree block x : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  rw [d]
  linarith

theorem inv_d_le (x : Fin (p ^ 2 + p + 1)) : 1 / d block x ≤ 1 / (p : ℝ) :=
  one_div_le_one_div_of_le (cast_p_pos p hb1 hb2) (p_le_d p h hb1 hb2 x)

/-- There are at most `p` points in `block i` besides `x₀`, each contributing at most `1 / p`. -/
theorem card_erase_mul_inv_le {i : Fin b} {x₀ : Fin (p ^ 2 + p + 1)} (hi : x₀ ∈ block i) :
    (#((block i).erase x₀) : ℝ) * (1 / (p : ℝ)) ≤ 1 := by
  have hp0 := cast_p_pos p hb1 hb2
  have hcard : #((block i).erase x₀) ≤ p := by
    rw [Finset.card_erase_of_mem hi]
    have := card_block_le p h hb1 hb2 i
    omega
  have h2 : (#((block i).erase x₀) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hcard
  have h3 : (#((block i).erase x₀) : ℝ) * (1 / (p : ℝ)) ≤ (p : ℝ) * (1 / (p : ℝ)) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have h4 : (p : ℝ) * (1 / (p : ℝ)) = 1 := by
    field_simp
  linarith

theorem sum_erase_le_one {i : Fin b} {x₀ : Fin (p ^ 2 + p + 1)} (hi : x₀ ∈ block i) :
    ∑ x ∈ (block i).erase x₀, 1 / d block x ≤ 1 := by
  have h1 := Finset.sum_le_card_nsmul ((block i).erase x₀) (fun x => 1 / d block x) (1 / (p : ℝ))
    fun x _ => inv_d_le p h hb1 hb2 x
  rw [nsmul_eq_mul] at h1
  exact h1.trans (card_erase_mul_inv_le p h hb1 hb2 hi)

/-- (L1) + (L3): the diagonal entries `β i` are nonnegative. -/
theorem beta_nonneg {i : Fin b} {x₀ : Fin (p ^ 2 + p + 1)} (hi : x₀ ∈ block i) :
    0 ≤ beta block x₀ i := by
  rw [beta_eq]
  have := sum_erase_le_one p h hb1 hb2 hi
  linarith

/-- If `β i = 0` then every point of `block i` other than `x₀` has degree exactly `p + 1`:
the sum of at most `p` terms, each at most `1 / p`, equals `1`. -/
theorem degree_eq_of_beta_eq_zero {i : Fin b} {x₀ : Fin (p ^ 2 + p + 1)} (hi : x₀ ∈ block i)
    (hz : beta block x₀ i = 0) {y : Fin (p ^ 2 + p + 1)} (hy : y ∈ (block i).erase x₀) :
    degree block y = p + 1 := by
  have hp0 := cast_p_pos p hb1 hb2
  have hsum : ∑ x ∈ (block i).erase x₀, 1 / d block x = 1 := by
    rw [beta_eq] at hz; linarith
  -- every term is exactly `1 / p`
  have hterm : 1 / d block y = 1 / (p : ℝ) := by
    by_contra hne
    have hlt : 1 / d block y < 1 / (p : ℝ) :=
      lt_of_le_of_ne (inv_d_le p h hb1 hb2 y) hne
    have hstrict : ∑ x ∈ (block i).erase x₀, 1 / d block x
        < ∑ _x ∈ (block i).erase x₀, (1 / (p : ℝ)) :=
      Finset.sum_lt_sum (fun x _ => inv_d_le p h hb1 hb2 x) ⟨y, hy, hlt⟩
    rw [Finset.sum_const, nsmul_eq_mul] at hstrict
    have := card_erase_mul_inv_le p h hb1 hb2 hi
    linarith
  -- hence `d y = p`, i.e. `degree y = p + 1`
  have hdy : d block y = (p : ℝ) := by
    have hd : d block y ≠ 0 := d_ne_zero block (two_le_degree p h hb1 hb2) y
    field_simp at hterm
    linarith
  have hcast : ((degree block y : ℕ) : ℝ) = ((p + 1 : ℕ) : ℝ) := by
    rw [d] at hdy
    push_cast
    linarith
  exact Nat.cast_injective hcast

/-- The gap is empty: there is no linear space on `p ^ 2 + p + 1` points with
`p ^ 2 + p + 1 < b < p ^ 2 + p + 1 + p` blocks. -/
theorem gap_false : False := by
  have hp := two_le_p p hb1 hb2
  have hdeg := two_le_degree p h hb1 hb2
  obtain ⟨x₀, hx₀⟩ := exists_degree_eq p h hb1 hb2
  have hcardF : Fintype.card ↥(through block x₀) = p + 1 := by
    rw [Fintype.card_coe]
    exact hx₀
  by_cases hpos : ∀ t : ↥(through block x₀), 0 < beta block x₀ (t : Fin b)
  · have key := card_le_rank_add_one (n := ↥(through block x₀))
      (fun t => beta block x₀ (t : Fin b)) hpos (α block) (alpha_nonneg block hdeg)
      (fun t => a block (t : Fin b)) (1 / d block x₀)
    rw [← Q_submatrix_eq h hdeg x₀, hcardF] at key
    have hrk := rank_Q_submatrix_le block h hdeg (through block x₀)
    omega
  · push Not at hpos
    obtain ⟨t, ht⟩ := hpos
    have hmem : x₀ ∈ block (t : Fin b) := mem_through_iff.1 t.2
    have hz : beta block x₀ (t : Fin b) = 0 :=
      le_antisymm ht (beta_nonneg p h hb1 hb2 hmem)
    have hall : ∀ x ∈ block (t : Fin b), degree block x = p + 1 := by
      intro x hx
      by_cases hxx : x = x₀
      · subst hxx; exact hx₀
      · exact degree_eq_of_beta_eq_zero p h hb1 hb2 hmem hz (Finset.mem_erase.2 ⟨hxx, hx⟩)
    have hb := b_eq_of_block_all_degree p h hb1 hb2 (t : Fin b) hall
    omega

end Gap

/-! ### The roots -/

/-- **Erdős #903, the gap statement** (Erdős–Fowler–Sós–Wilson, Theorem 2): for `v = p² + p + 1`
there is no linear space with `v` points and `v < b < p² + 2p + 1` blocks. -/
theorem no_design_in_gap (p b : ℕ) (block : Fin b → Finset (Fin (p ^ 2 + p + 1)))
    (h : IsLinearSpace block) : ¬ (p ^ 2 + p + 1 < b ∧ b < p ^ 2 + 2 * p + 1) := by
  rintro ⟨hb1, hb2⟩
  rw [show p ^ 2 + 2 * p + 1 = p ^ 2 + p + 1 + p from by ring] at hb2
  exact gap_false p h hb1 hb2

/-- **Erdős #903, general form**: a linear space on `p² + p + 1` points with more than
`p² + p + 1` blocks has at least `p² + p + 1 + p` blocks (`p` arbitrary). -/
theorem erdos_903_general (p b : ℕ) (block : Fin b → Finset (Fin (p ^ 2 + p + 1)))
    (h : IsLinearSpace block) (hb : p ^ 2 + p + 1 < b) : p ^ 2 + p + 1 + p ≤ b := by
  have hno := no_design_in_gap p b block h
  have hnot : ¬ (b < p ^ 2 + 2 * p + 1) := fun hlt => hno ⟨hb, hlt⟩
  have heq : p ^ 2 + 2 * p + 1 = p ^ 2 + p + 1 + p := by ring
  omega

/-- **Erdős #903** as stated on erdosproblems.com: for `n = p² + p + 1` with `p` a prime power,
a block design (linear space) with `t > n` blocks has `t ≥ n + p`. -/
theorem erdos_903 (p b : ℕ) (hp : IsPrimePow p) (block : Fin b → Finset (Fin (p ^ 2 + p + 1)))
    (h : IsLinearSpace block) (hb : p ^ 2 + p + 1 < b) : p ^ 2 + p + 1 + p ≤ b :=
  have _ := hp
  erdos_903_general p b block h hb

end Erdos903
