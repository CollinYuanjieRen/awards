import CameronErdos.Fourier.Basic

/-!
# Granularizations, good lengths and the smoothing function `g`

This file formalizes the definitions and elementary lemmas of Green,
*The Cameron–Erdős conjecture* (2004), §3 (see `ref/green-cameron-erdos-0304058.pdf`, pp. 3–4):
the partition of `ZMod p` into arithmetic progressions of common difference `d`, the
granularization `A'` of a set `A`, the notion of a *good length*, and the smoothing function
`g` together with Green's inequalities (6) and (7).
-/

namespace CameronErdos

open Finset

variable {p : ℕ} [NeZero p]

/-! ### The block length `L = ⌈p/M⌉` -/

/-- `L p M = ⌈p/M⌉`, the (maximal) length of the progressions `I i`. -/
noncomputable def L (p M : ℕ) : ℕ := ⌈(p : ℝ) / (M : ℝ)⌉₊

lemma L_pos (hM : 0 < M) : 0 < L p M := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [L, Nat.lt_ceil, Nat.cast_zero]
  have : (0:ℝ) < p := by exact_mod_cast hp
  positivity

/-! ### The progressions `I i` -/

/-- The `i`-th block of least residues, `{λ : ip/M ≤ λ̄ < (i+1)p/M}` (natural division). -/
def baseBlock (p : ℕ) [NeZero p] (M i : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun lam : ZMod p => i * p / M ≤ lam.val ∧ lam.val < (i + 1) * p / M

/-- Green's progression `I i = {λ d : ip/M ≤ λ̄ < (i+1)p/M}`. -/
def block {p : ℕ} [NeZero p] (d : ZMod p) (M i : ℕ) : Finset (ZMod p) :=
  (baseBlock p M i).image fun lam => lam * d

lemma mem_baseBlock {M i : ℕ} {lam : ZMod p} :
    lam ∈ baseBlock p M i ↔ i * p / M ≤ lam.val ∧ lam.val < (i + 1) * p / M := by
  simp [baseBlock]

lemma mem_block {d : ZMod p} {M i : ℕ} {x : ZMod p} :
    x ∈ block d M i ↔ ∃ lam ∈ baseBlock p M i, lam * d = x := by
  simp [block]

/-- Counting the elements of `ZMod p` whose least residue lies in `[a, b)`, `b ≤ p`. -/
lemma card_filter_val_Ico {a b : ℕ} (hb : b ≤ p) :
    (Finset.univ.filter fun lam : ZMod p => a ≤ lam.val ∧ lam.val < b).card = b - a := by
  rw [← Nat.card_Ico a b]
  refine Finset.card_nbij' (fun lam => lam.val) (fun m => (m : ZMod p)) ?_ ?_ ?_ ?_
  · intro lam hlam
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hlam
    simp only [Finset.mem_coe, Finset.mem_Ico]
    exact hlam
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_Ico] at hm
    have hmp : m < p := lt_of_lt_of_le hm.2 hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      ZMod.val_cast_of_lt hmp]
    exact hm
  · intro lam _
    exact ZMod.natCast_rightInverse lam
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_Ico] at hm
    exact ZMod.val_cast_of_lt (lt_of_lt_of_le hm.2 hb)

lemma card_baseBlock {M i : ℕ} (hM : 0 < M) (hi : i < M) :
    (baseBlock p M i).card = (i + 1) * p / M - i * p / M := by
  have hb : (i + 1) * p / M ≤ p := by
    have h1 : (i + 1) * p ≤ M * p := Nat.mul_le_mul_right _ hi
    calc (i + 1) * p / M ≤ M * p / M := Nat.div_le_div_right h1
      _ = p := by rw [Nat.mul_div_cancel_left _ hM]
  exact card_filter_val_Ico hb

/-! ### Arithmetic of the block lengths -/

lemma nat_div_diff_lt (u q M : ℕ) (hq : 0 < q) (hM : 0 < M) :
    ((u + q) / M - u / M - 1) * M < q := by
  have h1 : u / M * M ≤ u := Nat.div_mul_le_self _ _
  have h2 : u < (u / M + 1) * M := (Nat.div_lt_iff_lt_mul hM).mp (Nat.lt_succ_self _)
  have h3 : (u + q) / M * M ≤ u + q := Nat.div_mul_le_self _ _
  have h4 : u + q < ((u + q) / M + 1) * M := (Nat.div_lt_iff_lt_mul hM).mp (Nat.lt_succ_self _)
  revert h1 h2 h3 h4
  generalize u / M = a
  generalize (u + q) / M = b
  intro h1 h2 h3 h4
  rcases Nat.lt_or_ge b (a + 1) with h | h
  · have hz : b - a - 1 = 0 := by omega
    rw [hz]
    simpa using hq
  · obtain ⟨c, hc⟩ : ∃ c, b = a + 1 + c := ⟨b - a - 1, by omega⟩
    have hca : b - a - 1 = c := by omega
    rw [hca]
    subst hc
    nlinarith [h2, h3]

lemma lt_nat_div_diff_succ (u q M : ℕ) (hM : 0 < M) :
    q < ((u + q) / M - u / M + 1) * M := by
  have h1 : u / M * M ≤ u := Nat.div_mul_le_self _ _
  have h4 : u + q < ((u + q) / M + 1) * M := (Nat.div_lt_iff_lt_mul hM).mp (Nat.lt_succ_self _)
  have hab : u / M ≤ (u + q) / M := Nat.div_le_div_right (Nat.le_add_right _ _)
  revert h1 h4 hab
  generalize u / M = a
  generalize (u + q) / M = b
  intro h1 h4 hab
  obtain ⟨c, hc⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  have hca : b - a = c := by omega
  rw [hca]
  subst hc
  nlinarith [h1, h4]

/-! ### Cardinalities of the blocks -/

omit [NeZero p] in
lemma mul_isUnit_injective {d : ZMod p} (hd : IsUnit d) :
    Function.Injective fun x : ZMod p => x * d := hd.mul_left_injective

omit [NeZero p] in
lemma mul_isUnit_surjective {d : ZMod p} (hd : IsUnit d) :
    Function.Surjective fun x : ZMod p => x * d := by
  intro y
  obtain ⟨u, rfl⟩ := hd
  exact ⟨y * ↑u⁻¹, by simp [mul_assoc]⟩

lemma card_block {d : ZMod p} (hd : IsUnit d) (M i : ℕ) :
    (block d M i).card = (baseBlock p M i).card :=
  Finset.card_image_of_injective _ (mul_isUnit_injective hd)

/-- Each progression has at most `L = ⌈p/M⌉` elements. -/
lemma block_card_le {d : ZMod p} (hd : IsUnit d) {M i : ℕ} (hM : 0 < M) (hi : i < M) :
    (block d M i).card ≤ L p M := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hM' : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  rw [card_block hd, card_baseBlock hM hi]
  have key : ((i * p + p) / M - i * p / M - 1) * M < p := nat_div_diff_lt (i * p) p M hp hM
  have hrw : (i + 1) * p = i * p + p := by ring
  rw [hrw]
  have hc : ((i * p + p) / M - i * p / M - 1 : ℕ) < L p M := by
    rw [L, Nat.lt_ceil, lt_div_iff₀ hM']
    exact_mod_cast key
  omega

/-- Each progression has at least `L − 1` elements. -/
lemma block_card_ge {d : ZMod p} (hd : IsUnit d) {M i : ℕ} (hM : 0 < M) (hi : i < M) :
    L p M - 1 ≤ (block d M i).card := by
  have hM' : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  rw [card_block hd, card_baseBlock hM hi]
  have key : p < ((i * p + p) / M - i * p / M + 1) * M := lt_nat_div_diff_succ (i * p) p M hM
  have hrw : (i + 1) * p = i * p + p := by ring
  rw [hrw]
  have hc : L p M ≤ ((i * p + p) / M - i * p / M + 1 : ℕ) := by
    rw [L, Nat.ceil_le, div_le_iff₀ hM']
    exact_mod_cast key.le
  omega

/-! ### The blocks partition `ZMod p` -/

lemma baseBlock_disjoint {M i j : ℕ} (hij : i ≠ j) :
    Disjoint (baseBlock p M i) (baseBlock p M j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [mem_baseBlock] at hx hy
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : (i + 1) * p / M ≤ j * p / M :=
      Nat.div_le_div_right (Nat.mul_le_mul_right p h)
    omega
  · have hle : (j + 1) * p / M ≤ i * p / M :=
      Nat.div_le_div_right (Nat.mul_le_mul_right p h)
    omega

/-- Distinct progressions are disjoint. -/
lemma block_disjoint {d : ZMod p} (hd : IsUnit d) {M i j : ℕ} (hij : i ≠ j) :
    Disjoint (block d M i) (block d M j) :=
  (Finset.disjoint_image (mul_isUnit_injective hd)).mpr (baseBlock_disjoint hij)

lemma biUnion_baseBlock_eq_univ (M : ℕ) (hM : 0 < M) :
    (Finset.range M).biUnion (baseBlock p M) = Finset.univ := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  refine Finset.eq_univ_of_forall fun x => ?_
  rw [Finset.mem_biUnion]
  set v := x.val with hv
  have hvp : v < p := ZMod.val_lt x
  set i := ((v + 1) * M - 1) / p with hi
  have hw1 : 1 ≤ (v + 1) * M := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hA : i * p ≤ (v + 1) * M - 1 := Nat.div_mul_le_self _ _
  have hB : (v + 1) * M - 1 < (i + 1) * p := (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
  have hiM : i < M := by
    rw [hi, Nat.div_lt_iff_lt_mul hp]
    have h2 : (v + 1) * M ≤ p * M := Nat.mul_le_mul_right M hvp
    calc (v + 1) * M - 1 < (v + 1) * M :=
          Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hw1) Nat.zero_lt_one
      _ ≤ p * M := h2
      _ = M * p := by ring
  refine ⟨i, Finset.mem_range.mpr hiM, ?_⟩
  rw [mem_baseBlock, ← hv]
  constructor
  · have : i * p / M < v + 1 := by
      rw [Nat.div_lt_iff_lt_mul hM]
      omega
    omega
  · have : v + 1 ≤ (i + 1) * p / M := by
      rw [Nat.le_div_iff_mul_le hM]
      omega
    omega

/-- The progressions `I i`, `i < M`, cover `ZMod p`. -/
lemma biUnion_block_eq_univ {d : ZMod p} (hd : IsUnit d) (M : ℕ) (hM : 0 < M) :
    (Finset.range M).biUnion (block d M) = Finset.univ := by
  refine Finset.eq_univ_of_forall fun y => ?_
  obtain ⟨x, hx⟩ := mul_isUnit_surjective hd y
  have huniv := biUnion_baseBlock_eq_univ (p := p) M hM
  have hxmem : x ∈ (Finset.range M).biUnion (baseBlock p M) := by
    rw [huniv]; exact Finset.mem_univ x
  rw [Finset.mem_biUnion] at hxmem
  obtain ⟨i, hi, hxi⟩ := hxmem
  rw [Finset.mem_biUnion]
  exact ⟨i, hi, mem_block.mpr ⟨x, hxi, hx⟩⟩

/-- The block sizes add up to `p`. -/
lemma sum_card_block {d : ZMod p} (hd : IsUnit d) (M : ℕ) (hM : 0 < M) :
    ∑ i ∈ Finset.range M, (block d M i).card = p := by
  have hdisj : ∀ i ∈ Finset.range M, ∀ j ∈ Finset.range M, i ≠ j →
      Disjoint (block d M i) (block d M j) := fun i _ j _ hij => block_disjoint hd hij
  have := Finset.card_biUnion hdisj
  rw [biUnion_block_eq_univ hd M hM] at this
  rw [← this, Finset.card_univ, ZMod.card]

/-! ### The granularization `A'` -/

/-- The set of indices of progressions in which `A` has relative density at least `ε₁`. -/
noncomputable def denseIdx (A : Finset (ZMod p)) (d : ZMod p) (M : ℕ) (ε₁ : ℝ) : Finset ℕ :=
  (Finset.range M).filter
    fun i => ε₁ * ((block d M i).card : ℝ) ≤ ((A ∩ block d M i).card : ℝ)

lemma mem_denseIdx {A : Finset (ZMod p)} {d : ZMod p} {M : ℕ} {ε₁ : ℝ} {i : ℕ} :
    i ∈ denseIdx A d M ε₁ ↔
      i < M ∧ ε₁ * ((block d M i).card : ℝ) ≤ ((A ∩ block d M i).card : ℝ) := by
  simp [denseIdx]

/-- Green's granularization `A' = ⋃_{i ∈ T} I i`. -/
noncomputable def granularization (A : Finset (ZMod p)) (d : ZMod p) (M : ℕ) (ε₁ : ℝ) :
    Finset (ZMod p) :=
  (denseIdx A d M ε₁).biUnion (block d M)

/-- Green (3) (in the form used in Proposition 6): the points of `A` lying in sparse
progressions number at most `ε₁ p`. -/
theorem card_sdiff_granularization_le {A : Finset (ZMod p)} {d : ZMod p} (hd : IsUnit d)
    {M : ℕ} (hM : 0 < M) {ε₁ : ℝ} (hε : 0 ≤ ε₁) :
    ((A \ granularization A d M ε₁).card : ℝ) ≤ ε₁ * p := by
  classical
  set S : Finset ℕ := (Finset.range M) \ denseIdx A d M ε₁ with hS
  have hsub : A \ granularization A d M ε₁ ⊆ S.biUnion fun i => A ∩ block d M i := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxu : x ∈ (Finset.range M).biUnion (block d M) := by
      rw [biUnion_block_eq_univ hd M hM]; exact Finset.mem_univ x
    rw [Finset.mem_biUnion] at hxu
    obtain ⟨i, hiM, hxi⟩ := hxu
    have hiT : i ∉ denseIdx A d M ε₁ := by
      intro hiT
      exact hx.2 (Finset.mem_biUnion.mpr ⟨i, hiT, hxi⟩)
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_sdiff.mpr ⟨hiM, hiT⟩, Finset.mem_inter.mpr ⟨hx.1, hxi⟩⟩
  have hstep1 : ((A \ granularization A d M ε₁).card : ℝ)
      ≤ ((S.biUnion fun i => A ∩ block d M i).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hstep2 : ((S.biUnion fun i => A ∩ block d M i).card : ℝ)
      ≤ ∑ i ∈ S, ((A ∩ block d M i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have hstep3 : ∑ i ∈ S, ((A ∩ block d M i).card : ℝ)
      ≤ ∑ i ∈ S, ε₁ * ((block d M i).card : ℝ) := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [hS, Finset.mem_sdiff] at hi
    have hnd : ¬ (ε₁ * ((block d M i).card : ℝ) ≤ ((A ∩ block d M i).card : ℝ)) := by
      intro hle
      exact hi.2 (mem_denseIdx.mpr ⟨Finset.mem_range.mp hi.1, hle⟩)
    exact (not_le.mp hnd).le
  have hstep4 : ∑ i ∈ S, ε₁ * ((block d M i).card : ℝ)
      ≤ ∑ i ∈ Finset.range M, ε₁ * ((block d M i).card : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (by rw [hS]; exact Finset.sdiff_subset) ?_
    intro i _ _
    positivity
  have hstep5 : ∑ i ∈ Finset.range M, ε₁ * ((block d M i).card : ℝ) = ε₁ * p := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← Nat.cast_sum, sum_card_block hd M hM]
  linarith

/-! ### Distance to the nearest integer -/

/-- `distInt t = ‖t‖`, the distance from the real number `t` to the nearest integer. -/
noncomputable def distInt (t : ℝ) : ℝ := |t - round t|

lemma distInt_nonneg (t : ℝ) : 0 ≤ distInt t := abs_nonneg _

lemma distInt_le_half (t : ℝ) : distInt t ≤ 1 / 2 := abs_sub_round t

/-- `‖t‖` is at most the distance from `t` to any given integer. -/
lemma distInt_le_abs_sub_int (t : ℝ) (n : ℤ) : distInt t ≤ |t - (n : ℝ)| := by
  rcases le_or_gt (1 / 2 : ℝ) |t - (n : ℝ)| with h | h
  · exact le_trans (distInt_le_half t) h
  · have habs := abs_lt.mp h
    have hround : round t = n := by
      rw [round_eq]
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> linarith [habs.1, habs.2]
    rw [distInt, hround]

/-- `‖n t‖ ≤ |n| ‖t‖` for integers `n`. -/
lemma distInt_int_mul_le (n : ℤ) (t : ℝ) :
    distInt ((n : ℝ) * t) ≤ |(n : ℝ)| * distInt t := by
  have h := distInt_le_abs_sub_int ((n : ℝ) * t) (n * round t)
  have he : |(n : ℝ) * t - ((n * round t : ℤ) : ℝ)| = |(n : ℝ)| * distInt t := by
    rw [distInt, ← abs_mul]
    push_cast
    ring_nf
  linarith [h, he.le, he.ge]

/-- `1 − cos 2πt ≤ 2π² ‖t‖²`. -/
lemma one_sub_cos_le (t : ℝ) :
    1 - Real.cos (2 * Real.pi * t) ≤ 2 * Real.pi ^ 2 * distInt t ^ 2 := by
  set n : ℤ := round t with hn
  set s : ℝ := t - (n : ℝ) with hs
  have hcos : Real.cos (2 * Real.pi * t) = Real.cos (2 * Real.pi * s) := by
    have hrw : 2 * Real.pi * s + (n : ℝ) * (2 * Real.pi) = 2 * Real.pi * t := by
      rw [hs]; ring
    rw [← hrw, Real.cos_add_int_mul_two_pi]
  have hpyth := Real.sin_sq_add_cos_sq (Real.pi * s)
  have h2 : Real.cos (2 * Real.pi * s) = 1 - 2 * Real.sin (Real.pi * s) ^ 2 := by
    have hrw : 2 * Real.pi * s = 2 * (Real.pi * s) := by ring
    rw [hrw, Real.cos_two_mul]
    nlinarith [hpyth]
  have hsin : Real.sin (Real.pi * s) ^ 2 ≤ (Real.pi * s) ^ 2 := Real.sin_sq_le_sq
  have hd : distInt t ^ 2 = s ^ 2 := by rw [distInt, ← hn, ← hs, sq_abs]
  rw [hcos, h2, hd]
  nlinarith [hsin]

/-! ### Good lengths -/

/-- Green's parameter `δ = ε₁² ε₂ ε₃^{1/2} α^{-1/2} / 16`, where `α = |A|/p`. -/
noncomputable def delta (A : Finset (ZMod p)) (ε₁ ε₂ ε₃ : ℝ) : ℝ :=
  ε₁ ^ 2 * ε₂ * Real.sqrt ε₃ / (16 * Real.sqrt ((A.card : ℝ) / (p : ℝ)))

lemma delta_pos {A : Finset (ZMod p)} (hA : A.Nonempty) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) : 0 < delta A ε₁ ε₂ ε₃ := by
  have hp : (0:ℝ) < p := by
    have := Nat.pos_of_ne_zero (NeZero.ne p); exact_mod_cast this
  have hcard : (0:ℝ) < A.card := by
    have := Finset.card_pos.mpr hA; exact_mod_cast this
  have hα : (0:ℝ) < (A.card : ℝ) / (p : ℝ) := div_pos hcard hp
  have hs : 0 < Real.sqrt ((A.card : ℝ) / (p : ℝ)) := Real.sqrt_pos.mpr hα
  have hs3 : 0 < Real.sqrt ε₃ := Real.sqrt_pos.mpr h₃
  rw [delta]
  positivity

/-- The set `R = {r ≠ 0 : |Â(r)| ≥ δ p}` of large Fourier coefficients. -/
noncomputable def R (A : Finset (ZMod p)) (δ : ℝ) : Finset (ZMod p) :=
  Finset.univ.filter fun r => r ≠ 0 ∧ δ * (p : ℝ) ≤ ‖fourier (indicator A) r‖

lemma mem_R {A : Finset (ZMod p)} {δ : ℝ} {r : ZMod p} :
    r ∈ R A δ ↔ r ≠ 0 ∧ δ * (p : ℝ) ≤ ‖fourier (indicator A) r‖ := by
  simp [R]

/-- `d` is a good length for `A` with respect to the parameters `ε₁, ε₂, ε₃`
(Green (4)): `‖dr/p‖ ≤ (1/4L) (δp/|Â(r)|)^{1/2}` for every `r ∈ R`. -/
def IsGoodLength (A : Finset (ZMod p)) (d : ZMod p) (M : ℕ) (ε₁ ε₂ ε₃ : ℝ) : Prop :=
  ∀ r ∈ R A (delta A ε₁ ε₂ ε₃),
    distInt (((d * r).val : ℝ) / (p : ℝ))
      ≤ (1 / (4 * (L p M : ℝ))) *
          Real.sqrt (delta A ε₁ ε₂ ε₃ * (p : ℝ) / ‖fourier (indicator A) r‖)

/-! ### A symmetric-interval summation lemma -/

omit [NeZero p] in
lemma sum_Icc_symm (n : ℕ) (f : ℤ → ℝ) (hf : ∀ j : ℤ, f (-j) = f j) :
    ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f j
      = f 0 + 2 * ∑ k ∈ Finset.range n, f ((k : ℤ) + 1) := by
  have hsplit : Finset.Icc (-(n : ℤ)) (n : ℤ)
      = Finset.Icc (-(n : ℤ)) 0 ∪ Finset.Icc 1 (n : ℤ) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc (-(n : ℤ)) 0) (Finset.Icc 1 (n : ℤ)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  have h1 : ∑ j ∈ Finset.Icc (-(n : ℤ)) 0, f j = ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ), f j := by
    refine Finset.sum_nbij' (fun j => -j) (fun j => -j) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a _; ring
    · intro a _; ring
    · intro a _; exact (hf a).symm
  have hins : Finset.Icc (0 : ℤ) (n : ℤ) = insert 0 (Finset.Icc 1 (n : ℤ)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h0 : (0 : ℤ) ∉ Finset.Icc (1 : ℤ) (n : ℤ) := by simp
  have h2 : ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ), f j = f 0 + ∑ j ∈ Finset.Icc 1 (n : ℤ), f j := by
    rw [hins, Finset.sum_insert h0]
  have h3 : ∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), f j = ∑ k ∈ Finset.range n, f ((k : ℤ) + 1) := by
    refine Finset.sum_nbij' (fun j : ℤ => (j - 1).toNat) (fun k : ℕ => (k : ℤ) + 1) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      omega
    · intro k _
      simp
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      congr 1
      omega
  rw [hsplit, Finset.sum_union hdisj, h1, h2, h3]
  ring

/-! ### The smoothing function `g` -/

/-- Green's smoothing function
`g(x) = (2L−1)^{-1} Σ_{|j| ≤ L−1} e(jdx/p)`, written as a (real) sum of cosines. -/
noncomputable def g (d : ZMod p) (M : ℕ) (x : ZMod p) : ℝ :=
  (1 / (2 * (L p M : ℝ) - 1)) *
    ∑ j ∈ Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1),
      Real.cos (2 * Real.pi * (j : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ))

lemma two_L_sub_one_pos {M : ℕ} (hM : 0 < M) : (0:ℝ) < 2 * (L p M : ℝ) - 1 := by
  have hL : 1 ≤ L p M := L_pos (p := p) hM
  have : (1:ℝ) ≤ (L p M : ℝ) := by exact_mod_cast hL
  linarith

lemma card_Icc_L {M : ℕ} (hM : 0 < M) :
    (Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1)).card = 2 * L p M - 1 := by
  have hL : 1 ≤ L p M := L_pos (p := p) hM
  rw [Int.card_Icc]
  omega

/-- The one-sided form of `g`: `(2L−1) g(x) = 1 + 2 Σ_{k < L−1} cos(2π(k+1)dx/p)`. -/
lemma g_eq {M : ℕ} (hM : 0 < M) (d : ZMod p) (x : ZMod p) :
    g d M x = (1 / (2 * (L p M : ℝ) - 1)) *
      (1 + 2 * ∑ k ∈ Finset.range (L p M - 1),
        Real.cos (2 * Real.pi * ((k : ℝ) + 1) * (((d * x).val : ℕ) : ℝ) / (p : ℝ))) := by
  have hL : 1 ≤ L p M := L_pos (p := p) hM
  have hcast : ((L p M - 1 : ℕ) : ℤ) = (L p M : ℤ) - 1 := by omega
  set f : ℤ → ℝ := fun j =>
    Real.cos (2 * Real.pi * (j : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)) with hf
  have hfeven : ∀ j : ℤ, f (-j) = f j := by
    intro j
    rw [hf]
    simp only
    rw [show 2 * Real.pi * ((-j : ℤ) : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)
        = -(2 * Real.pi * ((j : ℤ) : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)) by push_cast; ring,
      Real.cos_neg]
  have hsymm := sum_Icc_symm (L p M - 1) f hfeven
  rw [hcast] at hsymm
  rw [g, hsymm]
  norm_num [hf]

lemma g_zero {M : ℕ} (hM : 0 < M) (d : ZMod p) : g d M 0 = 1 := by
  have hL : 1 ≤ L p M := L_pos (p := p) hM
  have hden := two_L_sub_one_pos (p := p) hM
  have hcast : ((L p M - 1 : ℕ) : ℝ) = (L p M : ℝ) - 1 := by
    have : ((L p M - 1 : ℕ) : ℤ) = (L p M : ℤ) - 1 := by omega
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
  rw [g_eq hM]
  simp only [mul_zero, ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hcast]
  field_simp
  ring

lemma abs_g_le_one {M : ℕ} (hM : 0 < M) (d : ZMod p) (x : ZMod p) : |g d M x| ≤ 1 := by
  have hden := two_L_sub_one_pos (p := p) hM
  have hL : 1 ≤ L p M := L_pos (p := p) hM
  have hbound : |∑ j ∈ Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1),
      Real.cos (2 * Real.pi * (j : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ))|
      ≤ 2 * (L p M : ℝ) - 1 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle : ∀ j ∈ Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1),
        |Real.cos (2 * Real.pi * (j : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ))| ≤ 1 :=
      fun j _ => Real.abs_cos_le_one _
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hle) ?_
    rw [card_Icc_L hM, nsmul_eq_mul, mul_one]
    have : ((2 * L p M - 1 : ℕ) : ℝ) = 2 * (L p M : ℝ) - 1 := by
      have : ((2 * L p M - 1 : ℕ) : ℤ) = 2 * (L p M : ℤ) - 1 := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    rw [this]
  rw [g, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * (L p M : ℝ) - 1))]
  rw [div_mul_eq_mul_div, one_mul, div_le_one hden]
  exact hbound

lemma g_le_one {M : ℕ} (hM : 0 < M) (d : ZMod p) (x : ZMod p) : g d M x ≤ 1 :=
  (abs_le.mp (abs_g_le_one hM d x)).2

lemma neg_one_le_g {M : ℕ} (hM : 0 < M) (d : ZMod p) (x : ZMod p) : -1 ≤ g d M x :=
  (abs_le.mp (abs_g_le_one hM d x)).1

omit [NeZero p] in
lemma sum_range_succ_sq_le (n : ℕ) :
    ∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 / 6 := by
  induction n with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith [ih, Nat.cast_nonneg (α := ℝ) m]

/-- Green (7): `1 − g(x) ≤ (2π²L²/3) ‖dx/p‖²`. -/
theorem one_sub_g_le {M : ℕ} (hM : 0 < M) (d : ZMod p) (x : ZMod p) :
    1 - g d M x ≤ 2 * Real.pi ^ 2 * (L p M : ℝ) ^ 2 / 3 *
      distInt ((((d * x).val : ℕ) : ℝ) / (p : ℝ)) ^ 2 := by
  have hL : 1 ≤ L p M := L_pos (p := p) hM
  have hden := two_L_sub_one_pos (p := p) hM
  have hnr : ((L p M - 1 : ℕ) : ℝ) = (L p M : ℝ) - 1 := by
    have h : ((L p M - 1 : ℕ) : ℤ) = (L p M : ℤ) - 1 := by omega
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  set θ : ℝ := (((d * x).val : ℕ) : ℝ) / (p : ℝ) with hθ
  set D : ℝ := distInt θ with hDdef
  have hD0 : 0 ≤ D := distInt_nonneg _
  have hterm : ∀ k ∈ Finset.range (L p M - 1),
      1 - Real.cos (2 * Real.pi * ((k : ℝ) + 1) * (((d * x).val : ℕ) : ℝ) / (p : ℝ))
        ≤ 2 * Real.pi ^ 2 * (((k : ℝ) + 1) ^ 2 * D ^ 2) := by
    intro k _
    have harg : 2 * Real.pi * ((k : ℝ) + 1) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)
        = 2 * Real.pi * (((k : ℝ) + 1) * θ) := by rw [hθ]; ring
    rw [harg]
    have h1 := one_sub_cos_le (((k : ℝ) + 1) * θ)
    have h2 : distInt (((k : ℝ) + 1) * θ) ≤ ((k : ℝ) + 1) * D := by
      have h3 := distInt_int_mul_le ((k : ℤ) + 1) θ
      have h4 : ((((k : ℤ) + 1 : ℤ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [h4, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k : ℝ) + 1)] at h3
      exact h3
    have h5 : distInt (((k : ℝ) + 1) * θ) ^ 2 ≤ (((k : ℝ) + 1) * D) ^ 2 :=
      pow_le_pow_left₀ (distInt_nonneg _) h2 2
    nlinarith [h1, h5, Real.pi_pos, sq_nonneg Real.pi]
  set S : ℝ := ∑ k ∈ Finset.range (L p M - 1),
      Real.cos (2 * Real.pi * ((k : ℝ) + 1) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)) with hS
  have hsum : ((L p M - 1 : ℕ) : ℝ) - S
      ≤ 2 * Real.pi ^ 2 * D ^ 2 *
        ((2 * ((L p M - 1 : ℕ) : ℝ) + 1) * (((L p M - 1 : ℕ) : ℝ) + 1) ^ 2 / 6) := by
    have h : ∑ k ∈ Finset.range (L p M - 1),
        (1 - Real.cos (2 * Real.pi * ((k : ℝ) + 1) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)))
        ≤ 2 * Real.pi ^ 2 * D ^ 2 *
          ((2 * ((L p M - 1 : ℕ) : ℝ) + 1) * (((L p M - 1 : ℕ) : ℝ) + 1) ^ 2 / 6) := by
      calc ∑ k ∈ Finset.range (L p M - 1),
          (1 - Real.cos (2 * Real.pi * ((k : ℝ) + 1) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)))
          ≤ ∑ k ∈ Finset.range (L p M - 1), 2 * Real.pi ^ 2 * (((k : ℝ) + 1) ^ 2 * D ^ 2) :=
            Finset.sum_le_sum hterm
        _ = 2 * Real.pi ^ 2 * D ^ 2 * ∑ k ∈ Finset.range (L p M - 1), ((k : ℝ) + 1) ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ 2 * Real.pi ^ 2 * D ^ 2 *
            ((2 * ((L p M - 1 : ℕ) : ℝ) + 1) * (((L p M - 1 : ℕ) : ℝ) + 1) ^ 2 / 6) :=
            mul_le_mul_of_nonneg_left (sum_range_succ_sq_le _) (by positivity)
    rwa [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      ← hS] at h
  have hkey : 1 - g d M x
      = (2 / (2 * (L p M : ℝ) - 1)) * (((L p M - 1 : ℕ) : ℝ) - S) := by
    rw [g_eq hM, ← hS, hnr]
    field_simp
    ring
  rw [hkey]
  have hfac : (0:ℝ) ≤ 2 / (2 * (L p M : ℝ) - 1) := by positivity
  calc (2 / (2 * (L p M : ℝ) - 1)) * (((L p M - 1 : ℕ) : ℝ) - S)
      ≤ (2 / (2 * (L p M : ℝ) - 1)) * (2 * Real.pi ^ 2 * D ^ 2 *
          ((2 * ((L p M - 1 : ℕ) : ℝ) + 1) * (((L p M - 1 : ℕ) : ℝ) + 1) ^ 2 / 6)) :=
        mul_le_mul_of_nonneg_left hsum hfac
    _ = 2 * Real.pi ^ 2 * (L p M : ℝ) ^ 2 / 3 * D ^ 2 := by
        rw [hnr]
        field_simp
        ring

/-! ### Green (6) -/

/-- Green (6): if `d` is a good length for `A`, then `|Â(x)| |1 − g(x)²| ≤ δ p` for every `x`. -/
theorem norm_fourier_mul_abs_one_sub_g_sq_le {A : Finset (ZMod p)} (hA : A.Nonempty)
    {d : ZMod p} {M : ℕ} (hM : 0 < M) {ε₁ ε₂ ε₃ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    (hgood : IsGoodLength A d M ε₁ ε₂ ε₃) (x : ZMod p) :
    ‖fourier (indicator A) x‖ * |1 - g d M x ^ 2| ≤ delta A ε₁ ε₂ ε₃ * (p : ℝ) := by
  have hp0 : (0:ℝ) < (p : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne p); exact_mod_cast this
  have hδ : 0 < delta A ε₁ ε₂ ε₃ := delta_pos hA h₁ h₂ h₃
  have hδp : 0 < delta A ε₁ ε₂ ε₃ * (p : ℝ) := by positivity
  have hG1 := g_le_one hM d x
  have hG2 := neg_one_le_g hM d x
  have hN0 : (0:ℝ) ≤ ‖fourier (indicator A) x‖ := norm_nonneg _
  have hπ : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  by_cases hx : x ∈ R A (delta A ε₁ ε₂ ε₃)
  · have hmem := mem_R.mp hx
    have hN : 0 < ‖fourier (indicator A) x‖ := lt_of_lt_of_le hδp hmem.2
    have hLr : (1:ℝ) ≤ (L p M : ℝ) := by exact_mod_cast L_pos (p := p) hM
    have hD := hgood x hx
    have hsq : Real.sqrt (delta A ε₁ ε₂ ε₃ * (p : ℝ) / ‖fourier (indicator A) x‖) ^ 2
        = delta A ε₁ ε₂ ε₃ * (p : ℝ) / ‖fourier (indicator A) x‖ :=
      Real.sq_sqrt (by positivity)
    have hD2 : distInt ((((d * x).val : ℕ) : ℝ) / (p : ℝ)) ^ 2
        ≤ (1 / (4 * (L p M : ℝ))) ^ 2 *
            (delta A ε₁ ε₂ ε₃ * (p : ℝ) / ‖fourier (indicator A) x‖) := by
      have h := pow_le_pow_left₀ (distInt_nonneg _) hD 2
      rwa [mul_pow, hsq] at h
    have h7 := one_sub_g_le hM d x
    have habs2 : |1 - g d M x ^ 2| ≤ 2 * (1 - g d M x) := by
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    have hstep1 : ‖fourier (indicator A) x‖ * |1 - g d M x ^ 2|
        ≤ ‖fourier (indicator A) x‖ *
            (2 * (2 * Real.pi ^ 2 * (L p M : ℝ) ^ 2 / 3 *
              distInt ((((d * x).val : ℕ) : ℝ) / (p : ℝ)) ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hN0
      linarith [habs2, h7]
    have hstep2 : ‖fourier (indicator A) x‖ *
        (2 * (2 * Real.pi ^ 2 * (L p M : ℝ) ^ 2 / 3 *
          distInt ((((d * x).val : ℕ) : ℝ) / (p : ℝ)) ^ 2))
        ≤ ‖fourier (indicator A) x‖ *
            (2 * (2 * Real.pi ^ 2 * (L p M : ℝ) ^ 2 / 3 *
              ((1 / (4 * (L p M : ℝ))) ^ 2 *
                (delta A ε₁ ε₂ ε₃ * (p : ℝ) / ‖fourier (indicator A) x‖)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hN0
      have hc : (0:ℝ) ≤ 2 * (2 * Real.pi ^ 2 * (L p M : ℝ) ^ 2 / 3) := by positivity
      nlinarith [hD2, Real.pi_pos, sq_nonneg (L p M : ℝ)]
    have heq : ‖fourier (indicator A) x‖ *
        (2 * (2 * Real.pi ^ 2 * (L p M : ℝ) ^ 2 / 3 *
          ((1 / (4 * (L p M : ℝ))) ^ 2 *
            (delta A ε₁ ε₂ ε₃ * (p : ℝ) / ‖fourier (indicator A) x‖))))
        = Real.pi ^ 2 / 12 * (delta A ε₁ ε₂ ε₃ * (p : ℝ)) := by
      have hL0 : (L p M : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    have hlast : Real.pi ^ 2 / 12 * (delta A ε₁ ε₂ ε₃ * (p : ℝ))
        ≤ delta A ε₁ ε₂ ε₃ * (p : ℝ) := by nlinarith [hδp, hπ]
    linarith [hstep1, hstep2, heq.le, heq.ge, hlast]
  · rw [mem_R, not_and_or] at hx
    rcases hx with hx | hx
    · have hx0 : x = 0 := by simpa using hx
      subst hx0
      rw [g_zero hM]
      simp only [one_pow, sub_self, abs_zero, mul_zero]
      exact hδp.le
    · replace hx := not_le.mp hx
      have habs1 : |1 - g d M x ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith
      nlinarith [hx.le, habs1, hN0, abs_nonneg (1 - g d M x ^ 2)]

/-! ### The Fourier transform of the progression `P` -/

/-- `e(jy) = exp(2πi j ȳ / p)` for integers `j`. -/
lemma stdAddChar_intCast_mul (j : ℤ) (y : ZMod p) :
    (ZMod.stdAddChar ((j : ZMod p) * y) : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * ((y.val : ℕ) : ℂ)) / (p : ℂ)) := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  obtain ⟨k, hk⟩ : ∃ k : ℤ,
      ((((j : ZMod p) * y).val : ℕ) : ℤ) - j * (y.val : ℤ) = k * (p : ℤ) := by
    have h0 : ((((((j : ZMod p) * y).val : ℕ) : ℤ) - j * (y.val : ℤ) : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id]
      ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    obtain ⟨k, hk⟩ := h0
    exact ⟨k, by rw [hk]; ring⟩
  rw [stdAddChar_eq_exp]
  have harg : (2 * Real.pi * Complex.I * ((((j : ZMod p) * y).val : ℕ) : ℂ) / (p : ℂ))
      = 2 * Real.pi * Complex.I * ((j : ℂ) * ((y.val : ℕ) : ℂ)) / (p : ℂ)
        + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    have hk' : ((((j : ZMod p) * y).val : ℕ) : ℂ)
        = (j : ℂ) * ((y.val : ℕ) : ℂ) + (k : ℂ) * (p : ℂ) := by
      have h := congrArg (fun z : ℤ => (z : ℂ)) hk
      push_cast at h
      linear_combination h
    rw [hk']
    field_simp
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

omit [NeZero p] in
lemma sum_Icc_symm_odd (n : ℕ) (f : ℤ → ℝ) (hf : ∀ j : ℤ, f (-j) = -f j) :
    ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f j = 0 := by
  have h : ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f j
      = ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f (-j) := by
    refine Finset.sum_nbij' (fun j => -j) (fun j => -j) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a _; ring
    · intro a _; ring
    · intro a _; simp
  have h2 : ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f (-j)
      = -∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hf j
  linarith [h, h2]

lemma fourier_indicator_eq (A : Finset (ZMod p)) (r : ZMod p) :
    fourier (indicator A) r = ∑ y ∈ A, (ZMod.stdAddChar (y * r) : ℂ) := by
  simp only [fourier_apply, indicator_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- `Σ_{|j| ≤ L−1} e(jdx/p) = (2L−1) g(x)`; in particular the sum is real. -/
lemma sum_stdAddChar_Icc {M : ℕ} (hM : 0 < M) (d x : ZMod p) :
    ∑ j ∈ Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1),
      (ZMod.stdAddChar ((j : ZMod p) * (d * x)) : ℂ)
      = (((2 * (L p M : ℝ) - 1) * g d M x : ℝ) : ℂ) := by
  have hL : 1 ≤ L p M := L_pos (p := p) hM
  have hden := two_L_sub_one_pos (p := p) hM
  have hcast : ((L p M - 1 : ℕ) : ℤ) = (L p M : ℤ) - 1 := by omega
  have hterm : ∀ j : ℤ, (ZMod.stdAddChar ((j : ZMod p) * (d * x)) : ℂ)
      = ((Real.cos (2 * Real.pi * (j : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)) : ℝ) : ℂ)
        + ((Real.sin (2 * Real.pi * (j : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)) : ℝ) : ℂ)
          * Complex.I := by
    intro j
    rw [stdAddChar_intCast_mul]
    have harg : 2 * (Real.pi : ℂ) * Complex.I * ((j : ℂ) * ((((d * x).val : ℕ)) : ℂ)) / (p : ℂ)
        = ((2 * Real.pi * (j : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hsin : ∑ j ∈ Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1),
      Real.sin (2 * Real.pi * (j : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)) = 0 := by
    rw [← hcast]
    refine sum_Icc_symm_odd (L p M - 1) _ ?_
    intro j
    rw [show 2 * Real.pi * ((-j : ℤ) : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)
        = -(2 * Real.pi * ((j : ℤ) : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ)) by push_cast; ring,
      Real.sin_neg]
  have hcos : ∑ j ∈ Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1),
      Real.cos (2 * Real.pi * (j : ℝ) * (((d * x).val : ℕ) : ℝ) / (p : ℝ))
      = (2 * (L p M : ℝ) - 1) * g d M x := by
    rw [g, ← mul_assoc, mul_one_div, div_self hden.ne', one_mul]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Complex.ofReal_sum,
    ← Finset.sum_mul, ← Complex.ofReal_sum, hsin, hcos]
  simp

/-! ### The progression `P` -/

/-- Green's progression `P = {−(L−1)d, …, 0, d, …, (L−1)d}`. -/
noncomputable def Pset (d : ZMod p) (M : ℕ) : Finset (ZMod p) :=
  (Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1)).image fun j : ℤ => (j : ZMod p) * d

lemma injOn_Pset {d : ZMod p} (hd : IsUnit d) {M : ℕ} (hM : 0 < M) (hLp : 2 * L p M - 1 ≤ p) :
    ∀ j ∈ Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1),
      ∀ k ∈ Finset.Icc (-((L p M : ℤ) - 1)) ((L p M : ℤ) - 1),
        (j : ZMod p) * d = (k : ZMod p) * d → j = k := by
  have hL : 1 ≤ L p M := L_pos (p := p) hM
  intro j hj k hk hjk
  simp only [Finset.mem_Icc] at hj hk
  have hcast : ((j : ZMod p)) = ((k : ZMod p)) := mul_isUnit_injective hd hjk
  have hdvd : ((p : ℕ) : ℤ) ∣ (j - k) := by
    have h0 : (((j - k : ℤ)) : ZMod p) = 0 := by push_cast [hcast]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  have hlt : |j - k| < ((p : ℕ) : ℤ) := by
    have hpz : 2 * (L p M : ℤ) - 1 ≤ (p : ℤ) := by omega
    rw [abs_lt]
    omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  omega

lemma card_Pset {d : ZMod p} (hd : IsUnit d) {M : ℕ} (hM : 0 < M) (hLp : 2 * L p M - 1 ≤ p) :
    (Pset d M).card = 2 * L p M - 1 := by
  rw [Pset, Finset.card_image_of_injOn, card_Icc_L hM]
  intro j hj k hk hjk
  exact injOn_Pset hd hM hLp j (by simpa using hj) k (by simpa using hk) hjk

/-- The Fourier transform of `P`: `1̂_P(x) = (2L − 1) g(x)`. -/
theorem fourier_indicator_Pset {d : ZMod p} (hd : IsUnit d) {M : ℕ} (hM : 0 < M)
    (hLp : 2 * L p M - 1 ≤ p) (x : ZMod p) :
    fourier (indicator (Pset d M)) x = (((2 * (L p M : ℝ) - 1) * g d M x : ℝ) : ℂ) := by
  rw [fourier_indicator_eq, Pset,
    Finset.sum_image (injOn_Pset hd hM hLp)]
  rw [← sum_stdAddChar_Icc hM d x]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc]

/-- Green's identity `(A ∗ P)^(x) = Â(x) (2L − 1) g(x)`. -/
theorem fourier_conv_indicator_Pset {d : ZMod p} (hd : IsUnit d) {M : ℕ} (hM : 0 < M)
    (hLp : 2 * L p M - 1 ≤ p) (f : ZMod p → ℂ) (x : ZMod p) :
    fourier (conv f (indicator (Pset d M))) x
      = fourier f x * (((2 * (L p M : ℝ) - 1) * g d M x : ℝ) : ℂ) := by
  rw [fourier_conv, fourier_indicator_Pset hd hM hLp]

end CameronErdos

#print axioms CameronErdos.L_pos
#print axioms CameronErdos.mem_baseBlock
#print axioms CameronErdos.mem_block
#print axioms CameronErdos.card_filter_val_Ico
#print axioms CameronErdos.card_baseBlock
#print axioms CameronErdos.nat_div_diff_lt
#print axioms CameronErdos.lt_nat_div_diff_succ
#print axioms CameronErdos.mul_isUnit_injective
#print axioms CameronErdos.mul_isUnit_surjective
#print axioms CameronErdos.card_block
#print axioms CameronErdos.block_card_le
#print axioms CameronErdos.block_card_ge
#print axioms CameronErdos.baseBlock_disjoint
#print axioms CameronErdos.block_disjoint
#print axioms CameronErdos.biUnion_baseBlock_eq_univ
#print axioms CameronErdos.biUnion_block_eq_univ
#print axioms CameronErdos.sum_card_block
#print axioms CameronErdos.mem_denseIdx
#print axioms CameronErdos.card_sdiff_granularization_le
#print axioms CameronErdos.distInt_nonneg
#print axioms CameronErdos.distInt_le_half
#print axioms CameronErdos.distInt_le_abs_sub_int
#print axioms CameronErdos.distInt_int_mul_le
#print axioms CameronErdos.one_sub_cos_le
#print axioms CameronErdos.delta_pos
#print axioms CameronErdos.mem_R
#print axioms CameronErdos.sum_Icc_symm
#print axioms CameronErdos.two_L_sub_one_pos
#print axioms CameronErdos.card_Icc_L
#print axioms CameronErdos.g_eq
#print axioms CameronErdos.g_zero
#print axioms CameronErdos.abs_g_le_one
#print axioms CameronErdos.g_le_one
#print axioms CameronErdos.neg_one_le_g
#print axioms CameronErdos.sum_range_succ_sq_le
#print axioms CameronErdos.one_sub_g_le
#print axioms CameronErdos.norm_fourier_mul_abs_one_sub_g_sq_le
#print axioms CameronErdos.stdAddChar_intCast_mul
#print axioms CameronErdos.sum_Icc_symm_odd
#print axioms CameronErdos.fourier_indicator_eq
#print axioms CameronErdos.sum_stdAddChar_Icc
#print axioms CameronErdos.injOn_Pset
#print axioms CameronErdos.card_Pset
#print axioms CameronErdos.fourier_indicator_Pset
#print axioms CameronErdos.fourier_conv_indicator_Pset
