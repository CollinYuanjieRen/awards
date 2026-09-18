import CameronErdos.Part1.Granularization

/-!
# Green's Proposition 3

This file formalizes Proposition 3 of Green, *The Cameron–Erdős conjecture* (2004)
(see arXiv math/0304058, pp. 4–5):

> Suppose that `d` is a good length for `A`.  Then the granularization `A'` has the property
> that `A + A` contains all `x` for which `(A' ∗ A')(x) ≥ ε₂ p`, with at most `ε₃ p` exceptions.

The route is Green's:

* `aOne A d M n = |A ∩ (n + P)| / |P|` with `P = {j d : |j| ≤ L − 1}`; its Fourier transform is
  `Â(x) g(x)` (`fourier_aOne`).
* Two applications of Parseval give Green (8)–(9):
  `Σ_n |(A ∗ A)(n) − (a₁ ∗ a₁)(n)|² ≤ α δ² p³` (`sum_sq_conv_sub_le`).
* For `n ∈ A'` the block containing `n` is dense and is contained in `n + P`, so
  `a₁(n) ≥ ε₁ (L−1)/(2L−1) ≥ ε₁/4` (`aOne_ge_on_granularization`).
* Hence each bad `n` contributes at least `(ε₁² ε₂ p/16)²` to the left-hand side of (9), and the
  choice of `δ` turns this into the bound `ε₃ p` (`bad_card_le`).

## A remark on hypotheses

Step 2 needs `L ≥ 2`, i.e. `M < p`: if `L = 1` the blocks are singletons, `P = {0}` and
`a₁ = 1_A`, so the constant `ε₁/4` is only available under an extra assumption such as
`ε₁ ≤ 4`.  We therefore carry the hypothesis `M < p` in `aOne_ge_on_granularization` and
`bad_card_le`.  (This is harmless: `M` is a fixed parameter and `p` is large in all
applications.)
-/

namespace CameronErdos

open Finset

variable {p : ℕ} [NeZero p]

/-! ### Real indicators and real convolution

Green's `a₁` and the representation functions are real valued, so we mirror the small
complex-valued API of `CameronErdos.Fourier.Basic` on `ℝ`.
-/

/-- The `ℝ`-valued indicator function of a finite subset of `ZMod p`. -/
def rIndicator (A : Finset (ZMod p)) : ZMod p → ℝ := fun x => if x ∈ A then 1 else 0

/-- Real convolution: `(f ∗ g)(x) = Σ_y f(y) g(x − y)`. -/
noncomputable def rconv (f g : ZMod p → ℝ) : ZMod p → ℝ := fun x => ∑ y : ZMod p, f y * g (x - y)

omit [NeZero p] in
@[simp] lemma rIndicator_apply (A : Finset (ZMod p)) (x : ZMod p) :
    rIndicator A x = if x ∈ A then 1 else 0 := rfl

omit [NeZero p] in
lemma rIndicator_nonneg (A : Finset (ZMod p)) (x : ZMod p) : 0 ≤ rIndicator A x := by
  rw [rIndicator_apply]; split_ifs <;> norm_num

omit [NeZero p] in
lemma ofReal_rIndicator (A : Finset (ZMod p)) (x : ZMod p) :
    ((rIndicator A x : ℝ) : ℂ) = indicator A x := by
  rw [rIndicator_apply, indicator_apply]; split_ifs <;> simp

lemma rconv_apply (f g : ZMod p → ℝ) (x : ZMod p) :
    rconv f g x = ∑ y : ZMod p, f y * g (x - y) := rfl

/-- The real convolution is the real part of the complex one. -/
lemma ofReal_rconv (f g : ZMod p → ℝ) (x : ZMod p) :
    ((rconv f g x : ℝ) : ℂ) = conv (fun y => ((f y : ℝ) : ℂ)) (fun y => ((g y : ℝ) : ℂ)) x := by
  rw [rconv_apply, conv_apply, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun y _ => by push_cast; ring

lemma rconv_nonneg {f g : ZMod p → ℝ} (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (x : ZMod p) :
    0 ≤ rconv f g x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (hf y) (hg (x - y))

lemma rconv_le_rconv {f g f' g' : ZMod p → ℝ} (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y)
    (hff : ∀ y, f y ≤ f' y) (hgg : ∀ y, g y ≤ g' y) (x : ZMod p) :
    rconv f g x ≤ rconv f' g' x :=
  Finset.sum_le_sum fun y _ =>
    mul_le_mul (hff y) (hgg (x - y)) (hg (x - y)) ((hf y).trans (hff y))

lemma rconv_const_mul (c : ℝ) (f g : ZMod p → ℝ) (x : ZMod p) :
    rconv (fun y => c * f y) (fun y => c * g y) x = c ^ 2 * rconv f g x := by
  rw [rconv_apply, rconv_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-! ### Representation functions -/

/-- `rep S x` is the number of representations `x = s + s'` with `s, s' ∈ S`. -/
def rep (S : Finset (ZMod p)) (x : ZMod p) : ℕ :=
  ((S ×ˢ S).filter fun q => q.1 + q.2 = x).card

lemma conv_indicator_eq_rep (S : Finset (ZMod p)) (x : ZMod p) :
    conv (indicator S) (indicator S) x = ((rep S x : ℕ) : ℂ) := conv_indicator S S x

/-- The real convolution of two indicators is the representation count. -/
lemma rconv_rIndicator (A B : Finset (ZMod p)) (x : ZMod p) :
    rconv (rIndicator A) (rIndicator B) x
      = ((((A ×ˢ B).filter fun q => q.1 + q.2 = x).card : ℕ) : ℝ) := by
  have h := ofReal_rconv (rIndicator A) (rIndicator B) x
  simp only [ofReal_rIndicator] at h
  rw [conv_indicator] at h
  exact_mod_cast h

lemma rconv_rIndicator_eq_rep (S : Finset (ZMod p)) (x : ZMod p) :
    rconv (rIndicator S) (rIndicator S) x = ((rep S x : ℕ) : ℝ) := rconv_rIndicator S S x

/-- The other standard form of `1_A ∗ 1_B`: `Σ_y 1_A(y) 1_B(x − y) = #{a ∈ A : x − a ∈ B}`. -/
lemma rconv_rIndicator_filter (A B : Finset (ZMod p)) (x : ZMod p) :
    rconv (rIndicator A) (rIndicator B) x = ((A.filter fun y => x - y ∈ B).card : ℝ) := by
  rw [rconv_apply]
  have hy : ∀ y : ZMod p, rIndicator A y * rIndicator B (x - y)
      = if y ∈ A.filter fun y => x - y ∈ B then (1 : ℝ) else 0 := by
    intro y
    simp only [rIndicator_apply, Finset.mem_filter]
    by_cases h1 : y ∈ A <;> by_cases h2 : x - y ∈ B <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hy y, Finset.sum_ite_mem,
    Finset.univ_inter]
  simp

/-! ### Elementary properties of `fourier` -/

lemma fourier_sub (f g : ZMod p → ℂ) (r : ZMod p) :
    fourier (fun x => f x - g x) r = fourier f r - fourier g r := by
  simp only [fourier_apply, sub_mul]
  rw [Finset.sum_sub_distrib]

lemma fourier_div_const (f : ZMod p → ℂ) (c : ℂ) (r : ZMod p) :
    fourier (fun x => f x / c) r = fourier f r / c := by
  simp only [fourier_apply, div_mul_eq_mul_div]
  rw [Finset.sum_div]

/-! ### Green's averaged function `a₁` -/

/-- Green's function `a₁(n) = |P|⁻¹ (A ∗ P)(n) = |A ∩ (n + P)| / |P|`, where
`P = {−(L−1)d, …, (L−1)d}` and `|P| = 2L − 1`. -/
noncomputable def aOne (A : Finset (ZMod p)) (d : ZMod p) (M : ℕ) : ZMod p → ℝ :=
  fun n => rconv (rIndicator A) (rIndicator (Pset d M)) n / (2 * (L p M : ℝ) - 1)

lemma aOne_nonneg {A : Finset (ZMod p)} {d : ZMod p} {M : ℕ} (hM : 0 < M) (n : ZMod p) :
    0 ≤ aOne A d M n := by
  have hden := two_L_sub_one_pos (p := p) hM
  exact div_nonneg (rconv_nonneg (rIndicator_nonneg _) (rIndicator_nonneg _) n) hden.le

/-- `â₁(x) = Â(x) g(x)`. -/
theorem fourier_aOne {A : Finset (ZMod p)} {d : ZMod p} (hd : IsUnit d) {M : ℕ} (hM : 0 < M)
    (hLp : 2 * L p M - 1 ≤ p) (x : ZMod p) :
    fourier (fun n => ((aOne A d M n : ℝ) : ℂ)) x
      = fourier (indicator A) x * ((g d M x : ℝ) : ℂ) := by
  have hden : (2 * (L p M : ℝ) - 1) ≠ 0 := (two_L_sub_one_pos (p := p) hM).ne'
  have hden' : (((2 * (L p M : ℝ) - 1 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden
  have hfun : (fun n => ((aOne A d M n : ℝ) : ℂ))
      = fun n => conv (indicator A) (indicator (Pset d M)) n
          / (((2 * (L p M : ℝ) - 1 : ℝ)) : ℂ) := by
    funext n
    rw [aOne, Complex.ofReal_div, ofReal_rconv]
    simp only [ofReal_rIndicator]
  rw [hfun, fourier_div_const, fourier_conv_indicator_Pset hd hM hLp, Complex.ofReal_mul]
  field_simp

/-! ### Green (8)–(9) -/

/-- Green (9): `Σ_n |(A ∗ A)(n) − (a₁ ∗ a₁)(n)|² ≤ α δ² p³` where `α = |A|/p`. -/
theorem sum_sq_conv_sub_le {A : Finset (ZMod p)} (hA : A.Nonempty) {d : ZMod p} (hd : IsUnit d)
    {M : ℕ} (hM : 0 < M) (hLp : 2 * L p M - 1 ≤ p) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) (hgood : IsGoodLength A d M ε₁ ε₂ ε₃) :
    ∑ n : ZMod p, ‖conv (indicator A) (indicator A) n
        - conv (fun y => ((aOne A d M y : ℝ) : ℂ)) (fun y => ((aOne A d M y : ℝ) : ℂ)) n‖ ^ 2
      ≤ ((A.card : ℝ) / (p : ℝ)) * delta A ε₁ ε₂ ε₃ ^ 2 * (p : ℝ) ^ 3 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne p); exact_mod_cast this
  set a1 : ZMod p → ℂ := fun y => ((aOne A d M y : ℝ) : ℂ) with ha1
  set F : ZMod p → ℂ := fun n => conv (indicator A) (indicator A) n - conv a1 a1 n with hFdef
  have hFhat : ∀ x : ZMod p,
      fourier F x = fourier (indicator A) x ^ 2 * (1 - ((g d M x : ℝ) : ℂ) ^ 2) := by
    intro x
    rw [hFdef, fourier_sub, fourier_conv, fourier_conv, ha1, fourier_aOne hd hM hLp]
    ring
  have hnorm : ∀ x : ZMod p,
      ‖fourier F x‖ = ‖fourier (indicator A) x‖ ^ 2 * |1 - g d M x ^ 2| := by
    intro x
    rw [hFhat, norm_mul, norm_pow,
      show (1 - ((g d M x : ℝ) : ℂ) ^ 2) = (((1 - g d M x ^ 2 : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hind : ∑ n : ZMod p, ‖indicator A n‖ ^ 2 = (A.card : ℝ) := by
    have hn : ∀ n : ZMod p, ‖indicator A n‖ ^ 2 = if n ∈ A then (1 : ℝ) else 0 := by
      intro n; rw [norm_indicator_apply]; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl fun n (_ : n ∈ Finset.univ) => hn n, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hbound : ∀ x : ZMod p, ‖fourier F x‖ ^ 2
      ≤ (delta A ε₁ ε₂ ε₃ * (p : ℝ)) ^ 2 * ‖fourier (indicator A) x‖ ^ 2 := by
    intro x
    have h6 := norm_fourier_mul_abs_one_sub_g_sq_le hA hM h₁ h₂ h₃ hgood x
    rw [hnorm, show (‖fourier (indicator A) x‖ ^ 2 * |1 - g d M x ^ 2|) ^ 2
        = (‖fourier (indicator A) x‖ * |1 - g d M x ^ 2|) ^ 2 * ‖fourier (indicator A) x‖ ^ 2 by
      ring]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h6 2) (sq_nonneg _)
  have hsum : ∑ x : ZMod p, ‖fourier F x‖ ^ 2
      ≤ (delta A ε₁ ε₂ ε₃ * (p : ℝ)) ^ 2 * ((p : ℝ) * (A.card : ℝ)) := by
    calc ∑ x : ZMod p, ‖fourier F x‖ ^ 2
        ≤ ∑ x : ZMod p, (delta A ε₁ ε₂ ε₃ * (p : ℝ)) ^ 2 * ‖fourier (indicator A) x‖ ^ 2 :=
          Finset.sum_le_sum fun x _ => hbound x
      _ = (delta A ε₁ ε₂ ε₃ * (p : ℝ)) ^ 2 * ∑ x : ZMod p, ‖fourier (indicator A) x‖ ^ 2 := by
          rw [← Finset.mul_sum]
      _ = (delta A ε₁ ε₂ ε₃ * (p : ℝ)) ^ 2 * ((p : ℝ) * (A.card : ℝ)) := by
          rw [parseval, hind]
  refine le_of_mul_le_mul_left ?_ hp0
  calc (p : ℝ) * ∑ n : ZMod p, ‖F n‖ ^ 2
      = ∑ x : ZMod p, ‖fourier F x‖ ^ 2 := (parseval F).symm
    _ ≤ (delta A ε₁ ε₂ ε₃ * (p : ℝ)) ^ 2 * ((p : ℝ) * (A.card : ℝ)) := hsum
    _ = (p : ℝ) * (((A.card : ℝ) / (p : ℝ)) * delta A ε₁ ε₂ ε₃ ^ 2 * (p : ℝ) ^ 3) := by
        field_simp

/-! ### Step 2: `a₁ ≥ ε₁/4` on the granularization -/

omit [NeZero p] in
lemma two_le_L {M : ℕ} (hM : 0 < M) (hMp : M < p) : 2 ≤ L p M := by
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMp' : (M : ℝ) < (p : ℝ) := by exact_mod_cast hMp
  have hlt : (1 : ℝ) < (p : ℝ) / (M : ℝ) := by
    rw [lt_div_iff₀ hM']; linarith
  have h1 : 1 < L p M := by
    rw [L, Nat.lt_ceil]
    simpa using hlt
  omega

/-- The block containing a point `n` is contained in `n + P`: this is the geometric input of
Step 2 of Green's proof. -/
lemma block_sub_filter {A : Finset (ZMod p)} {d : ZMod p} (hd : IsUnit d) {M i : ℕ}
    (hM : 0 < M) (hiM : i < M) {n : ZMod p} (hni : n ∈ block d M i) :
    A ∩ block d M i ⊆ A.filter fun y => n - y ∈ Pset d M := by
  have hcardle : (block d M i).card ≤ L p M := block_card_le hd hM hiM
  have hcardeq : (block d M i).card = (i + 1) * p / M - i * p / M := by
    rw [card_block hd, card_baseBlock hM hiM]
  obtain ⟨mu, hmu, hmun⟩ := mem_block.mp hni
  rw [mem_baseBlock] at hmu
  intro a ha
  rw [Finset.mem_inter] at ha
  obtain ⟨haA, hab⟩ := ha
  obtain ⟨lam, hlam, hlama⟩ := mem_block.mp hab
  rw [mem_baseBlock] at hlam
  rw [Finset.mem_filter]
  refine ⟨haA, ?_⟩
  have hcard1 : (i + 1) * p / M - i * p / M ≤ L p M := by rw [← hcardeq]; exact hcardle
  have hL1 : 1 ≤ L p M := L_pos (p := p) hM
  refine Finset.mem_image.mpr ⟨(mu.val : ℤ) - (lam.val : ℤ), ?_, ?_⟩
  · rw [Finset.mem_Icc]
    omega
  · have hc : (((mu.val : ℤ) - (lam.val : ℤ) : ℤ) : ZMod p) = mu - lam := by
      push_cast
      rw [ZMod.natCast_rightInverse mu, ZMod.natCast_rightInverse lam]
    rw [hc, sub_mul, hmun, hlama]

/-- Step 2 (Green, p. 5): if `n` lies in the granularization `A'` then `a₁(n) ≥ ε₁/4`. -/
theorem aOne_ge_on_granularization {A : Finset (ZMod p)} {d : ZMod p} (hd : IsUnit d)
    {M : ℕ} (hM : 0 < M) (hMp : M < p) {ε₁ : ℝ} (hε₁ : 0 ≤ ε₁)
    {n : ZMod p} (hn : n ∈ granularization A d M ε₁) :
    ε₁ / 4 ≤ aOne A d M n := by
  have hL2 : 2 ≤ L p M := two_le_L hM hMp
  have hLr : (2 : ℝ) ≤ (L p M : ℝ) := by exact_mod_cast hL2
  have hden : (0 : ℝ) < 2 * (L p M : ℝ) - 1 := by linarith
  rw [granularization, Finset.mem_biUnion] at hn
  obtain ⟨i, hi, hni⟩ := hn
  obtain ⟨hiM, hdense⟩ := mem_denseIdx.mp hi
  have hsub := block_sub_filter (A := A) hd hM hiM hni
  have hcards : ((A ∩ block d M i).card : ℝ) ≤ ((A.filter fun y => n - y ∈ Pset d M).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hge : (L p M : ℝ) - 1 ≤ ((block d M i).card : ℝ) := by
    have h := block_card_ge hd hM hiM
    have : ((L p M - 1 : ℕ) : ℝ) ≤ ((block d M i).card : ℝ) := by exact_mod_cast h
    have hcast : ((L p M - 1 : ℕ) : ℝ) = (L p M : ℝ) - 1 := by
      have h' : ((L p M - 1 : ℕ) : ℤ) = (L p M : ℤ) - 1 := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h'
    linarith [hcast ▸ this]
  have hnum : ε₁ * ((L p M : ℝ) - 1) ≤ ((A.filter fun y => n - y ∈ Pset d M).card : ℝ) := by
    have h1 : ε₁ * ((L p M : ℝ) - 1) ≤ ε₁ * ((block d M i).card : ℝ) :=
      mul_le_mul_of_nonneg_left hge hε₁
    linarith [hdense, hcards]
  rw [aOne, rconv_rIndicator_filter, le_div_iff₀ hden]
  nlinarith [hnum, hε₁, hLr]

/-- The pointwise form of Step 2: `a₁ ≥ (ε₁/4) 1_{A'}`. -/
theorem aOne_ge_mul_rIndicator {A : Finset (ZMod p)} {d : ZMod p} (hd : IsUnit d)
    {M : ℕ} (hM : 0 < M) (hMp : M < p) {ε₁ : ℝ} (hε₁ : 0 ≤ ε₁) (y : ZMod p) :
    ε₁ / 4 * rIndicator (granularization A d M ε₁) y ≤ aOne A d M y := by
  rw [rIndicator_apply]
  split_ifs with hy
  · rw [mul_one]; exact aOne_ge_on_granularization hd hM hMp hε₁ hy
  · rw [mul_zero]; exact aOne_nonneg hM y

/-! ### `δ²` -/

lemma delta_sq {A : Finset (ZMod p)} (hA : A.Nonempty) {ε₁ ε₂ ε₃ : ℝ} (h₃ : 0 ≤ ε₃) :
    delta A ε₁ ε₂ ε₃ ^ 2 = ε₁ ^ 4 * ε₂ ^ 2 * ε₃ / (256 * ((A.card : ℝ) / (p : ℝ))) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne p); exact_mod_cast this
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    have := Finset.card_pos.mpr hA; exact_mod_cast this
  have hα : (0 : ℝ) < (A.card : ℝ) / (p : ℝ) := div_pos hcard hp0
  have hs : Real.sqrt ((A.card : ℝ) / (p : ℝ)) ^ 2 = (A.card : ℝ) / (p : ℝ) := Real.sq_sqrt hα.le
  have hs3 : Real.sqrt ε₃ ^ 2 = ε₃ := Real.sq_sqrt h₃
  rw [delta, div_pow,
    show (ε₁ ^ 2 * ε₂ * Real.sqrt ε₃) ^ 2 = ε₁ ^ 4 * ε₂ ^ 2 * Real.sqrt ε₃ ^ 2 by ring,
    show (16 * Real.sqrt ((A.card : ℝ) / (p : ℝ))) ^ 2
        = 256 * Real.sqrt ((A.card : ℝ) / (p : ℝ)) ^ 2 by ring,
    hs3, hs]

/-! ### Proposition 3 -/

/-- **Green, Proposition 3.**  Let `d` be a good length for the nonempty set `A ⊆ ZMod p`
and let `A'` be the granularization of `A`.  Then `A + A` contains every `x` with
`(A' ∗ A')(x) ≥ ε₂ p`, with at most `ε₃ p` exceptions. -/
theorem bad_card_le {A : Finset (ZMod p)} (hA : A.Nonempty) {d : ZMod p} (hd : IsUnit d)
    {M : ℕ} (hM : 0 < M) (hMp : M < p) (hLp : 2 * L p M - 1 ≤ p) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) (hgood : IsGoodLength A d M ε₁ ε₂ ε₃) :
    ((Finset.univ.filter fun x : ZMod p =>
        ε₂ * (p : ℝ) ≤ ((rep (granularization A d M ε₁) x : ℕ) : ℝ) ∧ rep A x = 0).card : ℝ)
      ≤ ε₃ * (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne p); exact_mod_cast this
  set A' : Finset (ZMod p) := granularization A d M ε₁ with hA'
  set B : Finset (ZMod p) := Finset.univ.filter fun x : ZMod p =>
    ε₂ * (p : ℝ) ≤ ((rep A' x : ℕ) : ℝ) ∧ rep A x = 0 with hB
  set a1 : ZMod p → ℂ := fun y => ((aOne A d M y : ℝ) : ℂ) with ha1
  set F : ZMod p → ℂ := fun n => conv (indicator A) (indicator A) n - conv a1 a1 n with hFdef
  -- Each bad point contributes at least `(ε₁² ε₂ p / 16)²`.
  have hlow : ∀ n ∈ B, (ε₁ ^ 2 * ε₂ * (p : ℝ) / 16) ^ 2 ≤ ‖F n‖ ^ 2 := by
    intro n hn
    rw [hB, Finset.mem_filter] at hn
    obtain ⟨-, hrep', hrepA⟩ := hn
    have hzero : conv (indicator A) (indicator A) n = 0 := by
      rw [conv_indicator_eq_rep, hrepA]; norm_num
    have hconv : conv a1 a1 n = ((rconv (aOne A d M) (aOne A d M) n : ℝ) : ℂ) := by
      rw [ha1, ofReal_rconv]
    have hnn : 0 ≤ rconv (aOne A d M) (aOne A d M) n :=
      rconv_nonneg (aOne_nonneg hM) (aOne_nonneg hM) n
    have hnormF : ‖F n‖ = rconv (aOne A d M) (aOne A d M) n := by
      rw [hFdef]
      simp only
      rw [hzero, hconv, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnn]
    have hstep : ε₁ ^ 2 / 16 * ((rep A' n : ℕ) : ℝ) ≤ rconv (aOne A d M) (aOne A d M) n := by
      have hmono : rconv (fun y => ε₁ / 4 * rIndicator A' y) (fun y => ε₁ / 4 * rIndicator A' y) n
          ≤ rconv (aOne A d M) (aOne A d M) n := by
        refine rconv_le_rconv (fun y => ?_) (fun y => ?_) (fun y => ?_) (fun y => ?_) n
        · exact mul_nonneg (by linarith) (rIndicator_nonneg _ _)
        · exact mul_nonneg (by linarith) (rIndicator_nonneg _ _)
        · exact aOne_ge_mul_rIndicator hd hM hMp h₁.le y
        · exact aOne_ge_mul_rIndicator hd hM hMp h₁.le y
      rw [rconv_const_mul, rconv_rIndicator_eq_rep] at hmono
      have hrw : (ε₁ / 4) ^ 2 = ε₁ ^ 2 / 16 := by ring
      rwa [hrw] at hmono
    have hfin : ε₁ ^ 2 * ε₂ * (p : ℝ) / 16 ≤ rconv (aOne A d M) (aOne A d M) n := by
      have h1' : ε₁ ^ 2 / 16 * (ε₂ * (p : ℝ)) ≤ ε₁ ^ 2 / 16 * ((rep A' n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hrep' (by positivity)
      nlinarith [hstep, h1']
    rw [hnormF]
    exact pow_le_pow_left₀ (by positivity) hfin 2
  -- Sum over bad points and compare with Green (9).
  have hBsum : (B.card : ℝ) * (ε₁ ^ 2 * ε₂ * (p : ℝ) / 16) ^ 2 ≤ ∑ n : ZMod p, ‖F n‖ ^ 2 := by
    calc (B.card : ℝ) * (ε₁ ^ 2 * ε₂ * (p : ℝ) / 16) ^ 2
        = ∑ _n ∈ B, (ε₁ ^ 2 * ε₂ * (p : ℝ) / 16) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ B, ‖F n‖ ^ 2 := Finset.sum_le_sum hlow
      _ ≤ ∑ n : ZMod p, ‖F n‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => by positivity
  have h9 := sum_sq_conv_sub_le hA hd hM hLp h₁ h₂ h₃ hgood
  -- Substitute the value of `δ²`.
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    have := Finset.card_pos.mpr hA; exact_mod_cast this
  have hα : (0 : ℝ) < (A.card : ℝ) / (p : ℝ) := div_pos hcard hp0
  have hval : ((A.card : ℝ) / (p : ℝ)) * delta A ε₁ ε₂ ε₃ ^ 2 * (p : ℝ) ^ 3
      = (ε₃ * (p : ℝ)) * (ε₁ ^ 4 * ε₂ ^ 2 * (p : ℝ) ^ 2 / 256) := by
    rw [delta_sq hA h₃.le]
    field_simp
  have hc : (0 : ℝ) < ε₁ ^ 4 * ε₂ ^ 2 * (p : ℝ) ^ 2 / 256 := by positivity
  refine le_of_mul_le_mul_right ?_ hc
  calc (B.card : ℝ) * (ε₁ ^ 4 * ε₂ ^ 2 * (p : ℝ) ^ 2 / 256)
      = (B.card : ℝ) * (ε₁ ^ 2 * ε₂ * (p : ℝ) / 16) ^ 2 := by ring
    _ ≤ ∑ n : ZMod p, ‖F n‖ ^ 2 := hBsum
    _ ≤ ((A.card : ℝ) / (p : ℝ)) * delta A ε₁ ε₂ ε₃ ^ 2 * (p : ℝ) ^ 3 := h9
    _ = (ε₃ * (p : ℝ)) * (ε₁ ^ 4 * ε₂ ^ 2 * (p : ℝ) ^ 2 / 256) := hval

end CameronErdos

#print axioms CameronErdos.rIndicator_apply
#print axioms CameronErdos.rIndicator_nonneg
#print axioms CameronErdos.ofReal_rIndicator
#print axioms CameronErdos.rconv_apply
#print axioms CameronErdos.ofReal_rconv
#print axioms CameronErdos.rconv_nonneg
#print axioms CameronErdos.rconv_le_rconv
#print axioms CameronErdos.rconv_const_mul
#print axioms CameronErdos.conv_indicator_eq_rep
#print axioms CameronErdos.rconv_rIndicator
#print axioms CameronErdos.rconv_rIndicator_eq_rep
#print axioms CameronErdos.rconv_rIndicator_filter
#print axioms CameronErdos.fourier_sub
#print axioms CameronErdos.fourier_div_const
#print axioms CameronErdos.aOne_nonneg
#print axioms CameronErdos.fourier_aOne
#print axioms CameronErdos.sum_sq_conv_sub_le
#print axioms CameronErdos.two_le_L
#print axioms CameronErdos.block_sub_filter
#print axioms CameronErdos.aOne_ge_on_granularization
#print axioms CameronErdos.aOne_ge_mul_rIndicator
#print axioms CameronErdos.delta_sq
#print axioms CameronErdos.bad_card_le
