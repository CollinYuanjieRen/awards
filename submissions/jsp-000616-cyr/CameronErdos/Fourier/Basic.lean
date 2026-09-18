import Mathlib

/-!
# Discrete Fourier analysis on `ZMod n` (Green's normalization)

This file sets up the small Fourier API used throughout the Cameron–Erdős formalization,
following Green, *The Cameron–Erdős conjecture* (2004), §3 (see
arXiv math/0304058, pp. 2–3).

## Normalization

Writing `e(θ) = exp(2πiθ)`, Green's transform of `f : ZMod n → ℂ` is
`f̂(r) = Σ_{x ∈ ZMod n} f(x) e(rx/n)`, i.e. **no** `1/n` factor and a **positive** sign in the
exponent.  Concretely, `ZMod.stdAddChar : AddChar (ZMod n) ℂ` sends `j mod n` to
`exp (2 * π * I * j / n)`, and we define

`CameronErdos.fourier f r = Σ x, f x * ZMod.stdAddChar (x * r)`.

Mathlib's `ZMod.dft` uses the opposite sign, `𝓕 Φ k = Σ j, stdAddChar (-(j * k)) • Φ j`, so the
two differ by a reflection of the frequency variable:
`fourier f r = ZMod.dft f (-r)` (`CameronErdos.fourier_eq_dft`).

With this normalization Parseval carries a factor of `n` on the *space* side:
`Σ_r |f̂(r)|² = n · Σ_x |f(x)|²`.

## Main definitions

* `CameronErdos.fourier` — the transform above (see `fourier_eq_exp` for the explicit
  exponential form).
* `CameronErdos.indicator A` — the `ℂ`-valued indicator of a `Finset (ZMod n)`.
* `CameronErdos.conv f g x = Σ_y f y * g (x - y)` — convolution.

## Main results

* `CameronErdos.fourier_indicator_zero` — `1̂_A(0) = #A`.
* `CameronErdos.sum_fourier_mul_conj` — polarized Parseval,
  `Σ_r f̂(r) conj(ĝ(r)) = n Σ_x f(x) conj(g(x))`.
* `CameronErdos.parseval` — `Σ_r ‖f̂(r)‖² = n Σ_x ‖f(x)‖²`.
* `CameronErdos.fourier_conv` — `(f ∗ g)^ = f̂ · ĝ`.
* `CameronErdos.conv_indicator` — `(1_A ∗ 1_B)(x) = #{(a,b) ∈ A ×ˢ B : a + b = x}`.
* `CameronErdos.norm_fourier_indicator_le` — `‖1̂_A(r)‖ ≤ #A`.
-/

namespace CameronErdos

open scoped ComplexConjugate

variable {n : ℕ} [NeZero n]

/-! ### The standard additive character -/

/-- Conjugation reflects the standard additive character. -/
lemma conj_stdAddChar (z : ZMod n) :
    conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
    AddChar.map_neg_eq_inv]

/-- The standard additive character takes values on the unit circle. -/
@[simp] lemma norm_stdAddChar (z : ZMod n) : ‖(ZMod.stdAddChar z : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Orthogonality: `Σ_r e(t r / n) = n` if `t = 0` and `0` otherwise. -/
lemma sum_stdAddChar_mul (t : ZMod n) :
    ∑ r : ZMod n, (ZMod.stdAddChar (t * r) : ℂ) = if t = 0 then (n : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod n) ℂ)) t
    (ZMod.isPrimitive_stdAddChar n)
  rw [ZMod.card] at h
  have h2 : ∑ r : ZMod n, (ZMod.stdAddChar (t * r) : ℂ)
      = ∑ x : ZMod n, (ZMod.stdAddChar (x * t) : ℂ) :=
    Finset.sum_congr rfl fun r _ => by rw [mul_comm]
  rw [h2, h]
  split_ifs <;> simp

/-! ### Definitions -/

/-- Green's discrete Fourier transform on `ZMod n`:
`f̂(r) = Σ_x f(x) e(rx/n)` with `e(θ) = exp(2πiθ)`. -/
noncomputable def fourier (f : ZMod n → ℂ) (r : ZMod n) : ℂ :=
  ∑ x : ZMod n, f x * ZMod.stdAddChar (x * r)

lemma fourier_apply (f : ZMod n → ℂ) (r : ZMod n) :
    fourier f r = ∑ x : ZMod n, f x * ZMod.stdAddChar (x * r) := rfl

/-- Explicit exponential form of the standard additive character:
`e(z) = exp (2πi z / n)`.  This pins down the normalization stated in the module docstring. -/
lemma stdAddChar_eq_exp (z : ZMod n) :
    (ZMod.stdAddChar z : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (z.val : ℕ) / n) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]

/-- Green's transform written out: `f̂(r) = Σ_x f(x) exp(2πi x r / n)`. -/
lemma fourier_eq_exp (f : ZMod n → ℂ) (r : ZMod n) :
    fourier f r
      = ∑ x : ZMod n, f x * Complex.exp (2 * Real.pi * Complex.I * (((x * r).val : ℕ)) / n) := by
  rw [fourier_apply]
  exact Finset.sum_congr rfl fun x _ => by rw [stdAddChar_eq_exp]

/-- Relation to Mathlib's `ZMod.dft`, which uses the opposite sign convention. -/
lemma fourier_eq_dft (f : ZMod n → ℂ) (r : ZMod n) : fourier f r = ZMod.dft f (-r) := by
  rw [ZMod.dft_apply, fourier_apply]
  exact Finset.sum_congr rfl fun x _ => by rw [smul_eq_mul, mul_neg, neg_neg, mul_comm]

/-- The `ℂ`-valued indicator function of a finite subset of `ZMod n`. -/
def indicator (A : Finset (ZMod n)) : ZMod n → ℂ := fun x => if x ∈ A then 1 else 0

/-- Convolution: `(f ∗ g)(x) = Σ_y f(y) g(x − y)`. -/
noncomputable def conv (f g : ZMod n → ℂ) : ZMod n → ℂ := fun x => ∑ y : ZMod n, f y * g (x - y)

lemma conv_apply (f g : ZMod n → ℂ) (x : ZMod n) :
    conv f g x = ∑ y : ZMod n, f y * g (x - y) := rfl

/-! ### Elementary properties -/

omit [NeZero n] in
@[simp] lemma indicator_apply (A : Finset (ZMod n)) (x : ZMod n) :
    indicator A x = if x ∈ A then 1 else 0 := rfl

omit [NeZero n] in
lemma norm_indicator_apply (A : Finset (ZMod n)) (x : ZMod n) :
    ‖indicator A x‖ = if x ∈ A then (1 : ℝ) else 0 := by
  rw [indicator_apply]; split_ifs <;> simp

omit [NeZero n] in
lemma conj_indicator (A : Finset (ZMod n)) (x : ZMod n) :
    conj (indicator A x) = indicator A x := by
  rw [indicator_apply]; split_ifs <;> simp

/-- Fourier coefficient at `0` is the total mass. -/
lemma fourier_zero (f : ZMod n → ℂ) : fourier f 0 = ∑ x : ZMod n, f x := by
  simp [fourier_apply]

/-- `1̂_A(0) = #A`. -/
theorem fourier_indicator_zero (A : Finset (ZMod n)) :
    fourier (indicator A) 0 = (A.card : ℂ) := by
  rw [fourier_zero]
  simp only [indicator_apply, Finset.sum_ite_mem, Finset.univ_inter]
  simp

/-- Conjugating the transform reflects the frequency. -/
lemma conj_fourier (f : ZMod n → ℂ) (r : ZMod n) :
    conj (fourier f r) = fourier (fun x => conj (f x)) (-r) := by
  rw [fourier_apply, fourier_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, conj_stdAddChar, mul_neg]

/-- For indicators (real-valued functions) conjugation is the same as negating the frequency. -/
lemma fourier_indicator_neg (A : Finset (ZMod n)) (r : ZMod n) :
    fourier (indicator A) (-r) = conj (fourier (indicator A) r) := by
  rw [conj_fourier]
  congr 1
  funext x
  exact (conj_indicator A x).symm

/-- `‖1̂_A(r)‖ ≤ #A`. -/
theorem norm_fourier_indicator_le (A : Finset (ZMod n)) (r : ZMod n) :
    ‖fourier (indicator A) r‖ ≤ (A.card : ℝ) := by
  rw [fourier_apply]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ x : ZMod n, ‖indicator A x * ZMod.stdAddChar (x * r)‖
      = if x ∈ A then (1 : ℝ) else 0 := by
    intro x; rw [norm_mul, norm_stdAddChar, mul_one, norm_indicator_apply]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => h1 x, Finset.sum_ite_mem,
    Finset.univ_inter]
  simp

/-! ### Parseval -/

/-- Polarized Parseval: `Σ_r f̂(r) conj(ĝ(r)) = n Σ_x f(x) conj(g(x))`. -/
theorem sum_fourier_mul_conj (f g : ZMod n → ℂ) :
    ∑ r : ZMod n, fourier f r * conj (fourier g r)
      = (n : ℂ) * ∑ x : ZMod n, f x * conj (g x) := by
  have key : ∀ r : ZMod n, fourier f r * conj (fourier g r)
      = ∑ x : ZMod n, ∑ y : ZMod n,
          (f x * conj (g y)) * ZMod.stdAddChar ((x - y) * r) := by
    intro r
    rw [fourier_apply, fourier_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have hc : conj (g y * ZMod.stdAddChar (y * r))
        = conj (g y) * ZMod.stdAddChar (-(y * r)) := by
      rw [map_mul, conj_stdAddChar]
    have hch : ZMod.stdAddChar (x * r) * ZMod.stdAddChar (-(y * r))
        = ZMod.stdAddChar ((x - y) * r) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [hc, ← hch]
    ring
  calc ∑ r : ZMod n, fourier f r * conj (fourier g r)
      = ∑ r : ZMod n, ∑ x : ZMod n, ∑ y : ZMod n,
          (f x * conj (g y)) * ZMod.stdAddChar ((x - y) * r) :=
        Finset.sum_congr rfl fun r _ => key r
    _ = ∑ x : ZMod n, ∑ y : ZMod n, ∑ r : ZMod n,
          (f x * conj (g y)) * ZMod.stdAddChar ((x - y) * r) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x : ZMod n, ∑ y : ZMod n,
          (f x * conj (g y)) * (if x - y = 0 then (n : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.mul_sum, sum_stdAddChar_mul]
    _ = (n : ℂ) * ∑ x : ZMod n, f x * conj (g x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hy : ∀ y : ZMod n, (f x * conj (g y)) * (if x - y = 0 then (n : ℂ) else 0)
            = if y = x then (n : ℂ) * (f x * conj (g x)) else 0 := by
          intro y
          by_cases h : y = x
          · subst h; simp [mul_comm]
          · have h' : ¬ (x - y = 0) := by
              simpa [sub_eq_zero, eq_comm] using h
            simp [h, h']
        rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hy y,
          Finset.sum_ite_eq' Finset.univ x]
        simp

/-- Parseval: `Σ_r ‖f̂(r)‖² = n Σ_x ‖f(x)‖²`. -/
theorem parseval (f : ZMod n → ℂ) :
    ∑ r : ZMod n, ‖fourier f r‖ ^ 2 = (n : ℝ) * ∑ x : ZMod n, ‖f x‖ ^ 2 := by
  have h := sum_fourier_mul_conj f f
  simp only [Complex.mul_conj'] at h
  exact_mod_cast h

/-! ### Convolution -/

/-- The transform of a convolution is the pointwise product. -/
theorem fourier_conv (f g : ZMod n → ℂ) (r : ZMod n) :
    fourier (conv f g) r = fourier f r * fourier g r := by
  have expand : fourier (conv f g) r
      = ∑ y : ZMod n, ∑ x : ZMod n, (f y * ZMod.stdAddChar (y * r))
          * (g (x - y) * ZMod.stdAddChar ((x - y) * r)) := by
    rw [fourier_apply]
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) =>
      show conv f g x * ZMod.stdAddChar (x * r)
          = ∑ y : ZMod n, (f y * ZMod.stdAddChar (y * r))
              * (g (x - y) * ZMod.stdAddChar ((x - y) * r)) by
        rw [conv_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        have hch : ZMod.stdAddChar (y * r) * ZMod.stdAddChar ((x - y) * r)
            = ZMod.stdAddChar (x * r) := by
          rw [← AddChar.map_add_eq_mul]
          congr 1
          ring
        rw [← hch]
        ring]
    exact Finset.sum_comm
  rw [expand, fourier_apply, fourier_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine (Fintype.sum_equiv (Equiv.addLeft y) _ _ fun z => ?_).symm
  simp only [Equiv.coe_addLeft]
  rw [add_sub_cancel_left]

/-! ### Convolution of indicators -/

/-- `(1_A ∗ 1_B)(x)` counts representations `x = a + b` with `a ∈ A`, `b ∈ B`. -/
theorem conv_indicator (A B : Finset (ZMod n)) (x : ZMod n) :
    conv (indicator A) (indicator B) x
      = ((((A ×ˢ B).filter fun p => p.1 + p.2 = x).card : ℕ) : ℂ) := by
  have step1 : conv (indicator A) (indicator B) x
      = ((A.filter fun y => x - y ∈ B).card : ℂ) := by
    rw [conv_apply]
    have hy : ∀ y : ZMod n, indicator A y * indicator B (x - y)
        = if y ∈ A.filter fun y => x - y ∈ B then (1 : ℂ) else 0 := by
      intro y
      simp only [indicator_apply, Finset.mem_filter]
      by_cases h1 : y ∈ A <;> by_cases h2 : x - y ∈ B <;> simp [h1, h2]
    rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hy y, Finset.sum_ite_mem,
      Finset.univ_inter]
    simp
  rw [step1]
  congr 1
  refine Finset.card_nbij' (fun y => (y, x - y)) (fun p => p.1) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hy ⊢
    exact ⟨⟨hy.1, hy.2⟩, by ring⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
    refine ⟨hp.1.1, ?_⟩
    have h2 : x - p.1 = p.2 := by rw [← hp.2]; ring
    rw [h2]
    exact hp.1.2
  · intro y _; rfl
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    have h2 : x - p.1 = p.2 := by rw [← hp.2]; ring
    show ((p.1, x - p.1) : ZMod n × ZMod n) = p
    rw [h2]

end CameronErdos

#print axioms CameronErdos.conj_stdAddChar
#print axioms CameronErdos.norm_stdAddChar
#print axioms CameronErdos.sum_stdAddChar_mul
#print axioms CameronErdos.stdAddChar_eq_exp
#print axioms CameronErdos.fourier_eq_exp
#print axioms CameronErdos.fourier_eq_dft
#print axioms CameronErdos.fourier_zero
#print axioms CameronErdos.fourier_indicator_zero
#print axioms CameronErdos.conj_fourier
#print axioms CameronErdos.fourier_indicator_neg
#print axioms CameronErdos.norm_fourier_indicator_le
#print axioms CameronErdos.sum_fourier_mul_conj
#print axioms CameronErdos.parseval
#print axioms CameronErdos.fourier_conv
#print axioms CameronErdos.conv_indicator
