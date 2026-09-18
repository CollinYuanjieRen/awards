import CameronErdos.Part1.Granularization
import CameronErdos.Part1.Params

/-!
# Green's Proposition 5: existence of a good length

This file formalizes Proposition 5 of Green, *The Cameron–Erdős conjecture* (2004)
(`ref/green-cameron-erdos-0304058.pdf`, p. 6): if `p` is large compared with `4L` raised to
the power `256 α² ε₁^{-4} ε₂^{-2} ε₃^{-1}`, then `A ⊆ ZMod p` admits a nonzero *good length*
`d` in the sense of `CameronErdos.IsGoodLength`.

The argument is split into three independent pieces.

* `exists_goodLength_of_prod_lt` — a **pure pigeonhole** statement: writing
  `θ r = (1/4L) (δp/|Â(r)|)^{1/2}` for the tolerance demanded by `IsGoodLength` and
  `m r = ⌈1/θ r⌉`, a good length exists as soon as `∏_{r ∈ R} m r < p`.
* `prod_mSize_le` — a **crude analytic bound**: `∏_{r ∈ R} m r ≤ (8 L E^{1/4})^E` where
  `E = 256 ε₁^{-4} ε₂^{-2} ε₃^{-1}`.  Each factor is at most `2/θ r ≤ 8 L E^{1/4}` and
  `#R ≤ α/δ² ≤ E` by Parseval.  (This replaces Green's AM–GM plus monotonicity-in-`k` step
  and simultaneously absorbs the loss coming from the ceiling in `m r`.)
* `exists_goodLength` — the combination, and `eventually_exists_goodLength` — its
  instantiation at the parameters of `CameronErdos.Part1.Params`.
-/

namespace CameronErdos

open Finset Filter

/-! ## The exponent `E = 256 ε₁^{-4} ε₂^{-2} ε₃^{-1}` -/

/-- The exponent occurring in Green's Proposition 5 (with the factor `α² ≤ 1` absorbed).
This is definitionally `CameronErdos.E N` at the parameters of `Params.lean`. -/
noncomputable def Eprop5 (ε₁ ε₂ ε₃ : ℝ) : ℝ :=
  256 * ε₁ ^ (-4 : ℤ) * ε₂ ^ (-2 : ℤ) * ε₃ ^ (-1 : ℤ)

lemma Eprop5_eq {ε₁ ε₂ ε₃ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) :
    Eprop5 ε₁ ε₂ ε₃ = 256 / (ε₁ ^ 4 * ε₂ ^ 2 * ε₃) := by
  have h1 : ε₁ ≠ 0 := ne_of_gt h₁
  have h2 : ε₂ ≠ 0 := ne_of_gt h₂
  have h3 : ε₃ ≠ 0 := ne_of_gt h₃
  simp only [Eprop5, zpow_neg, zpow_one]
  rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, show ((4 : ℤ)) = ((4 : ℕ) : ℤ) from rfl,
    zpow_natCast, zpow_natCast]
  field_simp

lemma Eprop5_pos {ε₁ ε₂ ε₃ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) :
    0 < Eprop5 ε₁ ε₂ ε₃ := by
  rw [Eprop5_eq h₁ h₂ h₃]; positivity

lemma one_le_Eprop5 {ε₁ ε₂ ε₃ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    (h₁' : ε₁ ≤ 1) (h₂' : ε₂ ≤ 1) (h₃' : ε₃ ≤ 1) : (1 : ℝ) ≤ Eprop5 ε₁ ε₂ ε₃ := by
  rw [Eprop5_eq h₁ h₂ h₃, le_div_iff₀ (by positivity)]
  have e1 : ε₁ ^ 4 ≤ 1 := pow_le_one₀ h₁.le h₁'
  have e2 : ε₂ ^ 2 ≤ 1 := pow_le_one₀ h₂.le h₂'
  have e1' : (0:ℝ) ≤ ε₁ ^ 4 := by positivity
  have e2' : (0:ℝ) ≤ ε₂ ^ 2 := by positivity
  nlinarith [h₃.le, mul_nonneg e1' e2']

section Core

variable {p : ℕ} [NeZero p]

/-! ## The tolerance `θ` and the pigeonhole box sizes `m` -/

/-- The tolerance appearing in the definition of a good length:
`θ_r = (1/4L) (δ p / |Â(r)|)^{1/2}`. -/
noncomputable def theta (A : Finset (ZMod p)) (M : ℕ) (ε₁ ε₂ ε₃ : ℝ) (r : ZMod p) : ℝ :=
  (1 / (4 * (L p M : ℝ))) *
    Real.sqrt (delta A ε₁ ε₂ ε₃ * (p : ℝ) / ‖fourier (indicator A) r‖)

lemma isGoodLength_iff {A : Finset (ZMod p)} {d : ZMod p} {M : ℕ} {ε₁ ε₂ ε₃ : ℝ} :
    IsGoodLength A d M ε₁ ε₂ ε₃ ↔
      ∀ r ∈ R A (delta A ε₁ ε₂ ε₃),
        distInt (((d * r).val : ℝ) / (p : ℝ)) ≤ theta A M ε₁ ε₂ ε₃ r := Iff.rfl

/-- The number of boxes used for the frequency `r` in the pigeonhole argument. -/
noncomputable def mSize (A : Finset (ZMod p)) (M : ℕ) (ε₁ ε₂ ε₃ : ℝ) (r : ZMod p) : ℕ :=
  ⌈1 / theta A M ε₁ ε₂ ε₃ r⌉₊

lemma cast_pos_p : (0 : ℝ) < (p : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)

lemma norm_fourier_pos_of_mem_R {A : Finset (ZMod p)} {δ : ℝ} (hδ : 0 < δ) {r : ZMod p}
    (hr : r ∈ R A δ) : 0 < ‖fourier (indicator A) r‖ :=
  lt_of_lt_of_le (by have := cast_pos_p (p := p); positivity) (mem_R.mp hr).2

lemma theta_pos {A : Finset (ZMod p)} {M : ℕ} (hM : 0 < M) {ε₁ ε₂ ε₃ : ℝ}
    (hδ : 0 < delta A ε₁ ε₂ ε₃) {r : ZMod p} (hr : r ∈ R A (delta A ε₁ ε₂ ε₃)) :
    0 < theta A M ε₁ ε₂ ε₃ r := by
  have hp : (0:ℝ) < (p:ℝ) := cast_pos_p
  have hL : (0:ℝ) < (L p M : ℝ) := by exact_mod_cast L_pos (p := p) hM
  have hn := norm_fourier_pos_of_mem_R hδ hr
  have hs : 0 < Real.sqrt (delta A ε₁ ε₂ ε₃ * (p:ℝ) / ‖fourier (indicator A) r‖) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [theta]
  exact mul_pos (by positivity) hs

lemma mSize_pos {A : Finset (ZMod p)} {M : ℕ} (hM : 0 < M) {ε₁ ε₂ ε₃ : ℝ}
    (hδ : 0 < delta A ε₁ ε₂ ε₃) {r : ZMod p} (hr : r ∈ R A (delta A ε₁ ε₂ ε₃)) :
    0 < mSize A M ε₁ ε₂ ε₃ r := by
  rw [mSize, Nat.lt_ceil, Nat.cast_zero]
  exact one_div_pos.mpr (theta_pos hM hδ hr)

lemma one_div_mSize_le_theta {A : Finset (ZMod p)} {M : ℕ} (hM : 0 < M) {ε₁ ε₂ ε₃ : ℝ}
    (hδ : 0 < delta A ε₁ ε₂ ε₃) {r : ZMod p} (hr : r ∈ R A (delta A ε₁ ε₂ ε₃)) :
    1 / ((mSize A M ε₁ ε₂ ε₃ r : ℕ) : ℝ) ≤ theta A M ε₁ ε₂ ε₃ r := by
  have hθ := theta_pos hM hδ hr
  have h1 : (0:ℝ) < 1 / theta A M ε₁ ε₂ ε₃ r := one_div_pos.mpr hθ
  have h2 : 1 / theta A M ε₁ ε₂ ε₃ r ≤ ((mSize A M ε₁ ε₂ ε₃ r : ℕ) : ℝ) := Nat.le_ceil _
  have h3 := one_div_le_one_div_of_le h1 h2
  rwa [one_div_one_div] at h3

/-! ## (a) The pigeonhole step -/

/-- **Pigeonhole.**  If the product of the box counts `m r = ⌈1/θ_r⌉` over the large
frequencies `r ∈ R` is smaller than `p`, then `A` has a nonzero good length. -/
theorem exists_goodLength_of_prod_lt {A : Finset (ZMod p)} {M : ℕ} {ε₁ ε₂ ε₃ : ℝ}
    (hA : A.Nonempty) (hM : 0 < M) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    (hprod : ∏ r ∈ R A (delta A ε₁ ε₂ ε₃), mSize A M ε₁ ε₂ ε₃ r < p) :
    ∃ d : ZMod p, d ≠ 0 ∧ IsGoodLength A d M ε₁ ε₂ ε₃ := by
  classical
  have hδ : 0 < delta A ε₁ ε₂ ε₃ := delta_pos hA h₁ h₂ h₃
  have hpR : (0:ℝ) < (p:ℝ) := cast_pos_p
  set S : Finset (ZMod p) := R A (delta A ε₁ ε₂ ε₃) with hSdef
  set m : ZMod p → ℕ := fun r => mSize A M ε₁ ε₂ ε₃ r with hmdef
  have hmpos : ∀ r ∈ S, 0 < m r := fun r hr => mSize_pos hM hδ hr
  -- the pigeonhole map
  have hlt : ∀ (x : ZMod p) (r : {q : ZMod p // q ∈ S}),
      ⌊(m r.1 : ℝ) * (((x * r.1).val : ℕ) : ℝ) / (p:ℝ)⌋₊ < m r.1 := by
    intro x r
    have hmp : (0:ℝ) < (m r.1 : ℝ) := by exact_mod_cast hmpos r.1 r.2
    have hv : (((x * r.1).val : ℕ) : ℝ) < (p:ℝ) := by exact_mod_cast ZMod.val_lt (x * r.1)
    have hv0 : (0:ℝ) ≤ (((x * r.1).val : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [Nat.floor_lt (by positivity), div_lt_iff₀ hpR]
    exact mul_lt_mul_of_pos_left hv hmp
  have hcard : Fintype.card (∀ r : {q : ZMod p // q ∈ S}, Fin (m r.1))
      < Fintype.card (ZMod p) := by
    rw [ZMod.card, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_coe_sort S m]
    exact hprod
  obtain ⟨x, y, hxy, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun x : ZMod p => fun r : {q : ZMod p // q ∈ S} =>
      (⟨⌊(m r.1 : ℝ) * (((x * r.1).val : ℕ) : ℝ) / (p:ℝ)⌋₊, hlt x r⟩ : Fin (m r.1))) hcard
  refine ⟨x - y, sub_ne_zero.mpr hxy, ?_⟩
  intro r hr
  show distInt ((((x - y) * r).val : ℝ) / (p : ℝ)) ≤ theta A M ε₁ ε₂ ε₃ r
  have hmp : (0:ℝ) < (m r : ℝ) := by exact_mod_cast hmpos r hr
  -- the two least residues land in the same box
  have hj : ⌊(m r : ℝ) * (((x * r).val : ℕ) : ℝ) / (p:ℝ)⌋₊
      = ⌊(m r : ℝ) * (((y * r).val : ℕ) : ℝ) / (p:ℝ)⌋₊ := by
    have h := congrFun hfeq ⟨r, hr⟩
    simpa using h
  have hnn : ∀ z : ZMod p, (0:ℝ) ≤ (m r : ℝ) * (((z * r).val : ℕ) : ℝ) / (p:ℝ) := by
    intro z; positivity
  have hax := Nat.floor_le (hnn x)
  have hax' := Nat.lt_floor_add_one ((m r : ℝ) * (((x * r).val : ℕ) : ℝ) / (p:ℝ))
  have hby := Nat.floor_le (hnn y)
  have hby' := Nat.lt_floor_add_one ((m r : ℝ) * (((y * r).val : ℕ) : ℝ) / (p:ℝ))
  rw [← hj] at hby hby'
  have hdiff : |(m r : ℝ) * (((x * r).val : ℕ) : ℝ) / (p:ℝ)
      - (m r : ℝ) * (((y * r).val : ℕ) : ℝ) / (p:ℝ)| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have habs : |(((x * r).val : ℕ) : ℝ) / (p:ℝ) - (((y * r).val : ℕ) : ℝ) / (p:ℝ)|
      < 1 / (m r : ℝ) := by
    have he : (m r : ℝ) * (((x * r).val : ℕ) : ℝ) / (p:ℝ)
        - (m r : ℝ) * (((y * r).val : ℕ) : ℝ) / (p:ℝ)
        = (m r : ℝ) * ((((x * r).val : ℕ) : ℝ) / (p:ℝ) - (((y * r).val : ℕ) : ℝ) / (p:ℝ)) := by
      ring
    rw [he, abs_mul, abs_of_pos hmp] at hdiff
    rw [lt_div_iff₀ hmp]
    linarith
  -- the least residue of `(x-y)r` differs from the difference by a multiple of `p`
  obtain ⟨e, he⟩ : ((p:ℤ)) ∣ ((((x * r).val : ℕ) : ℤ) - (((y * r).val : ℕ) : ℤ))
      - ((((x - y) * r).val : ℕ) : ℤ) := by
    have hcast : ((((((x - y) * r).val : ℕ) : ℤ)) : ZMod p)
        = (((((x * r).val : ℕ) : ℤ) - ((((y * r).val : ℕ)) : ℤ) : ℤ) : ZMod p) := by
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id]
      ring
    exact ((ZMod.intCast_eq_intCast_iff _ _ _).mp hcast).dvd
  have heR : ((((x - y) * r).val : ℕ) : ℝ) / (p:ℝ) - ((-e : ℤ) : ℝ)
      = (((x * r).val : ℕ) : ℝ) / (p:ℝ) - (((y * r).val : ℕ) : ℝ) / (p:ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) he
    push_cast at h
    field_simp
    push_cast
    linarith
  calc distInt ((((x - y) * r).val : ℝ) / (p : ℝ))
      ≤ |((((x - y) * r).val : ℕ) : ℝ) / (p:ℝ) - ((-e : ℤ) : ℝ)| :=
        distInt_le_abs_sub_int _ (-e)
    _ = |(((x * r).val : ℕ) : ℝ) / (p:ℝ) - (((y * r).val : ℕ) : ℝ) / (p:ℝ)| := by rw [heR]
    _ ≤ 1 / (m r : ℝ) := habs.le
    _ ≤ theta A M ε₁ ε₂ ε₃ r := one_div_mSize_le_theta hM hδ hr

/-! ## (b) The analytic bound on the product -/

lemma card_le_cast_p (A : Finset (ZMod p)) : (A.card : ℝ) ≤ (p : ℝ) := by
  have h : A.card ≤ p := by
    have h' := Finset.card_le_univ A
    rwa [ZMod.card] at h'
  exact_mod_cast h

/-- `α δ² E = 1`, where `α = |A|/p`, `δ` is Green's parameter and `E = 256 ε₁^{-4}ε₂^{-2}ε₃^{-1}`. -/
lemma alpha_mul_delta_sq_mul_Eprop5 {A : Finset (ZMod p)} (hA : A.Nonempty) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) :
    ((A.card : ℝ) / (p : ℝ)) * delta A ε₁ ε₂ ε₃ ^ 2 * Eprop5 ε₁ ε₂ ε₃ = 1 := by
  have hp : (0:ℝ) < (p:ℝ) := cast_pos_p
  have hcard : (0:ℝ) < (A.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hα : (0:ℝ) < (A.card:ℝ) / (p:ℝ) := div_pos hcard hp
  have hs : Real.sqrt ((A.card:ℝ) / (p:ℝ)) ^ 2 = (A.card:ℝ) / (p:ℝ) := Real.sq_sqrt hα.le
  have h3s : Real.sqrt ε₃ ^ 2 = ε₃ := Real.sq_sqrt h₃.le
  have hd : delta A ε₁ ε₂ ε₃ ^ 2 = ε₁ ^ 4 * ε₂ ^ 2 * ε₃ / (256 * ((A.card:ℝ) / (p:ℝ))) := by
    rw [delta, div_pow,
      show (ε₁ ^ 2 * ε₂ * Real.sqrt ε₃) ^ 2 = (ε₁ ^ 2) ^ 2 * ε₂ ^ 2 * Real.sqrt ε₃ ^ 2 by ring,
      h3s,
      show (16 * Real.sqrt ((A.card:ℝ) / (p:ℝ))) ^ 2
        = 256 * Real.sqrt ((A.card:ℝ) / (p:ℝ)) ^ 2 by ring, hs]
    ring
  have h1 : ε₁ ≠ 0 := ne_of_gt h₁
  have h2 : ε₂ ≠ 0 := ne_of_gt h₂
  have h3 : ε₃ ≠ 0 := ne_of_gt h₃
  rw [hd, Eprop5_eq h₁ h₂ h₃]
  field_simp

/-- Each pigeonhole box count is at most `8 L E^{1/4}`. -/
lemma mSize_le_bound {A : Finset (ZMod p)} (hA : A.Nonempty) {M : ℕ} (hM : 0 < M)
    {ε₁ ε₂ ε₃ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    {r : ZMod p} (hr : r ∈ R A (delta A ε₁ ε₂ ε₃)) :
    ((mSize A M ε₁ ε₂ ε₃ r : ℕ) : ℝ)
      ≤ 8 * (L p M : ℝ) * Eprop5 ε₁ ε₂ ε₃ ^ ((1:ℝ)/4) := by
  have hp : (0:ℝ) < (p:ℝ) := cast_pos_p
  have hδ : 0 < delta A ε₁ ε₂ ε₃ := delta_pos hA h₁ h₂ h₃
  have hδne : delta A ε₁ ε₂ ε₃ ≠ 0 := ne_of_gt hδ
  have hL1 : (1:ℝ) ≤ (L p M : ℝ) := by exact_mod_cast L_pos (p := p) hM
  have hLne : (L p M : ℝ) ≠ 0 := by linarith
  have hn : 0 < ‖fourier (indicator A) r‖ := norm_fourier_pos_of_mem_R hδ hr
  have hnorm : delta A ε₁ ε₂ ε₃ * (p:ℝ) ≤ ‖fourier (indicator A) r‖ := (mem_R.mp hr).2
  have hdp : (0:ℝ) < delta A ε₁ ε₂ ε₃ * (p:ℝ) := by positivity
  have hcard : (0:ℝ) < (A.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hα : (0:ℝ) < (A.card:ℝ) / (p:ℝ) := div_pos hcard hp
  have hα1 : (A.card:ℝ) / (p:ℝ) ≤ 1 := by
    rw [div_le_one hp]; exact card_le_cast_p A
  have hEpos : 0 < Eprop5 ε₁ ε₂ ε₃ := Eprop5_pos h₁ h₂ h₃
  set s : ℝ := Real.sqrt (delta A ε₁ ε₂ ε₃ * (p:ℝ) / ‖fourier (indicator A) r‖) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs1 : s ≤ 1 := by
    have hdiv1 : delta A ε₁ ε₂ ε₃ * (p:ℝ) / ‖fourier (indicator A) r‖ ≤ 1 := by
      rw [div_le_one hn]; exact hnorm
    calc s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hdiv1
      _ = 1 := Real.sqrt_one
  -- `1/θ = 4 L / s`
  have hθ : theta A M ε₁ ε₂ ε₃ r = (1 / (4 * (L p M : ℝ))) * s := rfl
  have hinvθ : 1 / theta A M ε₁ ε₂ ε₃ r = 4 * (L p M : ℝ) * s⁻¹ := by
    rw [hθ]; field_simp
  have hsinv1 : (1:ℝ) ≤ s⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs0]; simpa using hs1
  have hone : (1:ℝ) ≤ 1 / theta A M ε₁ ε₂ ε₃ r := by
    rw [hinvθ]; nlinarith
  -- `m ≤ 2/θ = 8 L / s`
  have hm2 : ((mSize A M ε₁ ε₂ ε₃ r : ℕ) : ℝ) ≤ 8 * (L p M : ℝ) * s⁻¹ := by
    have hc := Nat.ceil_lt_add_one
      (show (0:ℝ) ≤ 1 / theta A M ε₁ ε₂ ε₃ r by linarith)
    rw [mSize]
    rw [hinvθ] at hc hone ⊢
    linarith
  -- `1/s = √(|Â(r)|/(δ p)) ≤ √(α/δ) ≤ √(√E) = E^{1/4}`
  have hsinv : s⁻¹ = Real.sqrt (‖fourier (indicator A) r‖ / (delta A ε₁ ε₂ ε₃ * (p:ℝ))) := by
    rw [hsdef, ← Real.sqrt_inv, inv_div]
  have hstep1 : ‖fourier (indicator A) r‖ / (delta A ε₁ ε₂ ε₃ * (p:ℝ))
      ≤ ((A.card:ℝ) / (p:ℝ)) / delta A ε₁ ε₂ ε₃ := by
    have hrw : ((A.card:ℝ) / (p:ℝ)) / delta A ε₁ ε₂ ε₃
        = (A.card:ℝ) / (delta A ε₁ ε₂ ε₃ * (p:ℝ)) := by
      field_simp
    rw [hrw, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (norm_fourier_indicator_le A r) (inv_nonneg.mpr hdp.le)
  have hstep2 : ((A.card:ℝ) / (p:ℝ)) / delta A ε₁ ε₂ ε₃ ≤ Real.sqrt (Eprop5 ε₁ ε₂ ε₃) := by
    have hkey := alpha_mul_delta_sq_mul_Eprop5 hA h₁ h₂ h₃
    have hEd : Eprop5 ε₁ ε₂ ε₃ * delta A ε₁ ε₂ ε₃ ^ 2 = 1 / ((A.card:ℝ) / (p:ℝ)) := by
      rw [eq_div_iff (ne_of_gt hα)]; linear_combination hkey
    have hsq : (((A.card:ℝ) / (p:ℝ)) / delta A ε₁ ε₂ ε₃) ^ 2 ≤ Eprop5 ε₁ ε₂ ε₃ := by
      rw [div_pow, div_le_iff₀ (pow_pos hδ 2), hEd, le_div_iff₀ hα]
      nlinarith [hα, hα1]
    calc ((A.card:ℝ) / (p:ℝ)) / delta A ε₁ ε₂ ε₃
        = Real.sqrt ((((A.card:ℝ) / (p:ℝ)) / delta A ε₁ ε₂ ε₃) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Eprop5 ε₁ ε₂ ε₃) := Real.sqrt_le_sqrt hsq
  have hquart : Real.sqrt (Real.sqrt (Eprop5 ε₁ ε₂ ε₃)) = Eprop5 ε₁ ε₂ ε₃ ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hEpos.le]
    norm_num
  have hfinal : s⁻¹ ≤ Eprop5 ε₁ ε₂ ε₃ ^ ((1:ℝ)/4) := by
    rw [hsinv, ← hquart]
    exact Real.sqrt_le_sqrt (hstep1.trans hstep2)
  calc ((mSize A M ε₁ ε₂ ε₃ r : ℕ) : ℝ) ≤ 8 * (L p M : ℝ) * s⁻¹ := hm2
    _ ≤ 8 * (L p M : ℝ) * Eprop5 ε₁ ε₂ ε₃ ^ ((1:ℝ)/4) := by
        have : (0:ℝ) ≤ 8 * (L p M : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_left hfinal this

/-- Parseval bounds the number of large Fourier coefficients: `#R ≤ α/δ² = α² E ≤ E`. -/
lemma card_R_le_Eprop5 {A : Finset (ZMod p)} (hA : A.Nonempty) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) :
    (((R A (delta A ε₁ ε₂ ε₃)).card : ℕ) : ℝ) ≤ Eprop5 ε₁ ε₂ ε₃ := by
  classical
  have hp : (0:ℝ) < (p:ℝ) := cast_pos_p
  have hδ : 0 < delta A ε₁ ε₂ ε₃ := delta_pos hA h₁ h₂ h₃
  have hcard : (0:ℝ) < (A.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hα : (0:ℝ) < (A.card:ℝ) / (p:ℝ) := div_pos hcard hp
  have hα1 : (A.card:ℝ) / (p:ℝ) ≤ 1 := by rw [div_le_one hp]; exact card_le_cast_p A
  have hEpos : 0 < Eprop5 ε₁ ε₂ ε₃ := Eprop5_pos h₁ h₂ h₃
  set k : ℕ := (R A (delta A ε₁ ε₂ ε₃)).card with hkdef
  -- Parseval
  have hsum : ∑ x : ZMod p, ‖indicator A x‖ ^ 2 = (A.card : ℝ) := by
    have hx : ∀ x : ZMod p, ‖indicator A x‖ ^ 2 = if x ∈ A then (1:ℝ) else 0 := by
      intro x; rw [norm_indicator_apply]; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hx x, Finset.sum_ite_mem,
      Finset.univ_inter]
    simp
  have hpars : ∑ r : ZMod p, ‖fourier (indicator A) r‖ ^ 2 = (p : ℝ) * (A.card : ℝ) := by
    rw [parseval (indicator A), hsum]
  have hsub : ∑ r ∈ R A (delta A ε₁ ε₂ ε₃), ‖fourier (indicator A) r‖ ^ 2
      ≤ ∑ r : ZMod p, ‖fourier (indicator A) r‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by positivity)
  have hlow : (k : ℝ) * (delta A ε₁ ε₂ ε₃ * (p:ℝ)) ^ 2
      ≤ ∑ r ∈ R A (delta A ε₁ ε₂ ε₃), ‖fourier (indicator A) r‖ ^ 2 := by
    have h := Finset.sum_le_sum (f := fun _ : ZMod p => (delta A ε₁ ε₂ ε₃ * (p:ℝ)) ^ 2)
      (g := fun r : ZMod p => ‖fourier (indicator A) r‖ ^ 2)
      (s := R A (delta A ε₁ ε₂ ε₃))
      (fun r hr => pow_le_pow_left₀ (by positivity) (mem_R.mp hr).2 2)
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hcount : (k : ℝ) * (delta A ε₁ ε₂ ε₃ * (p:ℝ)) ^ 2 ≤ (p:ℝ) * (A.card : ℝ) := by
    rw [← hpars]; linarith
  have h1 : (k : ℝ) * delta A ε₁ ε₂ ε₃ ^ 2 ≤ (A.card:ℝ) / (p:ℝ) := by
    have hp2 : (0:ℝ) < (p:ℝ) ^ 2 := by positivity
    refine le_of_mul_le_mul_right ?_ hp2
    calc (k : ℝ) * delta A ε₁ ε₂ ε₃ ^ 2 * (p:ℝ) ^ 2
        = (k : ℝ) * (delta A ε₁ ε₂ ε₃ * (p:ℝ)) ^ 2 := by ring
      _ ≤ (p:ℝ) * (A.card : ℝ) := hcount
      _ = (A.card:ℝ) / (p:ℝ) * (p:ℝ) ^ 2 := by field_simp
  have hkey := alpha_mul_delta_sq_mul_Eprop5 hA h₁ h₂ h₃
  have hmul := mul_le_mul_of_nonneg_right h1 (mul_pos hα hEpos).le
  have e1 : (k : ℝ) * delta A ε₁ ε₂ ε₃ ^ 2 * (((A.card:ℝ) / (p:ℝ)) * Eprop5 ε₁ ε₂ ε₃)
      = (k : ℝ) * (((A.card:ℝ) / (p:ℝ)) * delta A ε₁ ε₂ ε₃ ^ 2 * Eprop5 ε₁ ε₂ ε₃) := by ring
  rw [e1, hkey, mul_one] at hmul
  have hαsq : ((A.card:ℝ) / (p:ℝ)) * (((A.card:ℝ) / (p:ℝ)) * Eprop5 ε₁ ε₂ ε₃)
      ≤ Eprop5 ε₁ ε₂ ε₃ := by
    nlinarith [mul_nonneg (mul_nonneg hEpos.le (sub_nonneg.mpr hα1))
      (show (0:ℝ) ≤ 1 + (A.card:ℝ) / (p:ℝ) by linarith)]
  linarith

/-- **The crude analytic bound.**  `∏_{r ∈ R} m r ≤ (8 L E^{1/4})^E`. -/
theorem prod_mSize_le {A : Finset (ZMod p)} (hA : A.Nonempty) {M : ℕ} (hM : 0 < M)
    {ε₁ ε₂ ε₃ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    (h₁' : ε₁ ≤ 1) (h₂' : ε₂ ≤ 1) (h₃' : ε₃ ≤ 1) :
    ((∏ r ∈ R A (delta A ε₁ ε₂ ε₃), mSize A M ε₁ ε₂ ε₃ r : ℕ) : ℝ)
      ≤ (8 * (L p M : ℝ) * Eprop5 ε₁ ε₂ ε₃ ^ ((1:ℝ)/4)) ^ Eprop5 ε₁ ε₂ ε₃ := by
  classical
  have hL1 : (1:ℝ) ≤ (L p M : ℝ) := by exact_mod_cast L_pos (p := p) hM
  have hEpos : 0 < Eprop5 ε₁ ε₂ ε₃ := Eprop5_pos h₁ h₂ h₃
  have hE1 : (1:ℝ) ≤ Eprop5 ε₁ ε₂ ε₃ := one_le_Eprop5 h₁ h₂ h₃ h₁' h₂' h₃'
  have hq1 : (1:ℝ) ≤ Eprop5 ε₁ ε₂ ε₃ ^ ((1:ℝ)/4) :=
    Real.one_le_rpow hE1 (by norm_num)
  set B : ℝ := 8 * (L p M : ℝ) * Eprop5 ε₁ ε₂ ε₃ ^ ((1:ℝ)/4) with hBdef
  have hB1 : (1:ℝ) ≤ B := by rw [hBdef]; nlinarith
  set k : ℕ := (R A (delta A ε₁ ε₂ ε₃)).card with hkdef
  have hprod : ((∏ r ∈ R A (delta A ε₁ ε₂ ε₃), mSize A M ε₁ ε₂ ε₃ r : ℕ) : ℝ) ≤ B ^ k := by
    rw [Nat.cast_prod]
    calc ∏ r ∈ R A (delta A ε₁ ε₂ ε₃), ((mSize A M ε₁ ε₂ ε₃ r : ℕ) : ℝ)
        ≤ ∏ _r ∈ R A (delta A ε₁ ε₂ ε₃), B :=
          Finset.prod_le_prod (fun i _ => by positivity)
            (fun r hr => mSize_le_bound hA hM h₁ h₂ h₃ hr)
      _ = B ^ k := by rw [Finset.prod_const]
  refine hprod.trans ?_
  rw [← Real.rpow_natCast B k]
  exact Real.rpow_le_rpow_of_exponent_le hB1 (card_R_le_Eprop5 hA h₁ h₂ h₃)

/-- **Green's Proposition 5.**  If `p > (8 L E^{1/4})^E` then `A` has a nonzero good length. -/
theorem exists_goodLength {A : Finset (ZMod p)} {M : ℕ} {ε₁ ε₂ ε₃ : ℝ}
    (hA : A.Nonempty) (hM : 0 < M) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    (h₁' : ε₁ ≤ 1) (h₂' : ε₂ ≤ 1) (h₃' : ε₃ ≤ 1)
    (hp : (8 * (L p M : ℝ) * Eprop5 ε₁ ε₂ ε₃ ^ ((1:ℝ)/4)) ^ Eprop5 ε₁ ε₂ ε₃ < (p : ℝ)) :
    ∃ d : ZMod p, d ≠ 0 ∧ IsGoodLength A d M ε₁ ε₂ ε₃ := by
  refine exists_goodLength_of_prod_lt hA hM h₁ h₂ h₃ ?_
  have h := (prod_mSize_le hA hM h₁ h₂ h₃ h₁' h₂' h₃').trans_lt hp
  exact_mod_cast h

end Core

/-! ## (c) The instance at Green's parameters -/

section ParamsInstance

/-- `log x ≤ 24 x^{1/24}` (apply `log y ≤ 2 √y` to `y = x^{1/12}`). -/
private theorem log_le_rpow_24 {x : ℝ} (hx : 0 < x) : Real.log x ≤ 24 * x ^ ((1:ℝ)/24) := by
  have hx12 : (0:ℝ) < x ^ ((1:ℝ)/12) := Real.rpow_pos_of_pos hx _
  have h1 : Real.log (x ^ ((1:ℝ)/12)) = 1/12 * Real.log x := Real.log_rpow hx _
  have h3 : (x ^ ((1:ℝ)/12)) ^ ((1:ℝ)/2) = x ^ ((1:ℝ)/24) := by
    rw [← Real.rpow_mul hx.le]; norm_num
  have h2 := log_le_two_rpow hx12
  rw [h1, h3] at h2
  linarith

/-- The facts about `x = log N` driving `eventually_prop5_hypothesis8`.  The last inequality
holds because `10/11 + 1/12 = 131/132 < 1` and `10/11 + 1/24 = 251/264 < 1`. -/
private theorem eventually_log_params8 :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ x ∧ Real.log 2 + x ^ ((1:ℝ)/12) ≤ x ∧
        424673280 * x ^ ((10:ℝ)/11) *
          ((Real.log 72 + Real.log 424673280 / 4) + x ^ ((1:ℝ)/12)
            + 6 * x ^ ((1:ℝ)/24)) ≤ x := by
  have h1 := eventually_rpow_le_half 1 (show (1:ℝ)/12 < 1 by norm_num)
  have hA := eventually_rpow_le_half
    (3/2 * 424673280 * (Real.log 72 + Real.log 424673280 / 4))
    (show (10:ℝ)/11 < 1 by norm_num)
  have hB := eventually_rpow_le_half (3/2 * 424673280 : ℝ) (show (131:ℝ)/132 < 1 by norm_num)
  have hC := eventually_rpow_le_half (3/2 * 6 * 424673280 : ℝ)
    (show (251:ℝ)/264 < 1 by norm_num)
  filter_upwards [h1, hA, hB, hC, eventually_ge_atTop (2 * Real.log 2),
    eventually_ge_atTop (1:ℝ)] with x hx1 hxA hxB hxC hx4 hx5
  have hxpos : (0:ℝ) < x := by linarith
  refine ⟨hx5, by linarith, ?_⟩
  have e1 : x ^ ((10:ℝ)/11) * x ^ ((1:ℝ)/12) = x ^ ((131:ℝ)/132) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have e2 : x ^ ((10:ℝ)/11) * x ^ ((1:ℝ)/24) = x ^ ((251:ℝ)/264) := by
    rw [← Real.rpow_add hxpos]; norm_num
  calc 424673280 * x ^ ((10:ℝ)/11) *
        ((Real.log 72 + Real.log 424673280 / 4) + x ^ ((1:ℝ)/12) + 6 * x ^ ((1:ℝ)/24))
      = 424673280 * (Real.log 72 + Real.log 424673280 / 4) * x ^ ((10:ℝ)/11)
        + 424673280 * x ^ ((131:ℝ)/132) + 6 * 424673280 * x ^ ((251:ℝ)/264) := by
        rw [← e1, ← e2]; ring
    _ ≤ x := by linarith

/-- **`Lem_ParamChoice`, first half, in the form needed for Proposition 5.**  For all large `N`
and every `p ∈ [2N, 4N]`, `(8 L E^{1/4})^E < p`. -/
theorem eventually_prop5_hypothesis8 :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 2 * N ≤ p → p ≤ 4 * N →
      (8 * (LN N p : ℝ) * (E N) ^ ((1:ℝ)/4)) ^ (E N) < (p : ℝ) := by
  filter_upwards [eventually_ge_atTop 3, tendsto_log_nat.eventually eventually_log_params8]
    with N hN3 hxf
  obtain ⟨hx1, hx2, hx3⟩ := hxf
  intro p hp1 hp2
  have hN2 : 2 ≤ N := by omega
  have hNR : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN3
  have hxpos : (0:ℝ) < Real.log N := log_natCast_pos hN2
  have hupos : (0:ℝ) < Real.exp (Real.log N ^ ((1:ℝ)/12)) := Real.exp_pos _
  have hu1 : (1:ℝ) ≤ Real.exp (Real.log N ^ ((1:ℝ)/12)) :=
    Real.one_le_exp (Real.rpow_nonneg hxpos.le _)
  have hT2 := two_le_MN_arg hN3 hx2
  have hMlow := MN_lower hT2
  have hMpos : (0:ℝ) < (MN N : ℝ) := by linarith
  have hMposN : 0 < MN N := by exact_mod_cast hMpos
  have hppos : 0 < p := by omega
  have hpR : (p:ℝ) ≤ 4 * (N:ℝ) := by exact_mod_cast hp2
  have hLlt : (LN N p : ℝ) < (p:ℝ) / (MN N : ℝ) + 1 := by
    rw [LN]; exact Nat.ceil_lt_add_one (by positivity)
  have hdiv : (p:ℝ) / (MN N : ℝ) ≤ 8 * Real.exp (Real.log N ^ ((1:ℝ)/12)) := by
    rw [div_le_iff₀ hMpos]
    have h8 : 8 * Real.exp (Real.log N ^ ((1:ℝ)/12)) *
        ((N:ℝ) * Real.exp (-(Real.log N ^ ((1:ℝ)/12))) / 2) = 4 * (N:ℝ) := by
      rw [Real.exp_neg]; field_simp; norm_num
    have key := mul_le_mul_of_nonneg_left hMlow
      (show (0:ℝ) ≤ 8 * Real.exp (Real.log N ^ ((1:ℝ)/12)) by positivity)
    rw [h8] at key
    linarith
  have hLle : (LN N p : ℝ) ≤ 9 * Real.exp (Real.log N ^ ((1:ℝ)/12)) := by linarith
  have hL1R : (1:ℝ) ≤ (LN N p : ℝ) := by exact_mod_cast LN_ge_one hMposN hppos
  have h8Lpos : (0:ℝ) < 8 * (LN N p : ℝ) := by linarith
  have hEeq : E N = 424673280 * Real.log N ^ ((10:ℝ)/11) := E_eq hN2
  have hx10 : (1:ℝ) ≤ Real.log N ^ ((10:ℝ)/11) := Real.one_le_rpow hx1 (by norm_num)
  have hEpos : (0:ℝ) < E N := by rw [hEeq]; linarith
  have hlog8L : Real.log (8 * (LN N p : ℝ)) ≤ Real.log 72 + Real.log N ^ ((1:ℝ)/12) := by
    have h1 : 8 * (LN N p : ℝ) ≤ 72 * Real.exp (Real.log N ^ ((1:ℝ)/12)) := by linarith
    have h2 := Real.log_le_log h8Lpos h1
    rwa [Real.log_mul (by norm_num) (ne_of_gt hupos), Real.log_exp] at h2
  have hlogE : Real.log (E N) ≤ Real.log 424673280 + 24 * Real.log N ^ ((1:ℝ)/24) := by
    rw [hEeq, Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hxpos _)),
      Real.log_rpow hxpos]
    have h := log_le_rpow_24 hxpos
    linarith [Real.log_nonneg hx1]
  have hbase : (0:ℝ) < 8 * (LN N p : ℝ) * (E N) ^ ((1:ℝ)/4) :=
    mul_pos h8Lpos (Real.rpow_pos_of_pos hEpos _)
  have hlogbase : Real.log (8 * (LN N p : ℝ) * (E N) ^ ((1:ℝ)/4))
      ≤ (Real.log 72 + Real.log 424673280 / 4) + Real.log N ^ ((1:ℝ)/12)
        + 6 * Real.log N ^ ((1:ℝ)/24) := by
    rw [Real.log_mul (ne_of_gt h8Lpos) (ne_of_gt (Real.rpow_pos_of_pos hEpos _)),
      Real.log_rpow hEpos]
    linarith
  have hkey : Real.log (8 * (LN N p : ℝ) * (E N) ^ ((1:ℝ)/4)) * E N ≤ Real.log N := by
    have h1 := mul_le_mul_of_nonneg_right hlogbase hEpos.le
    have h2 : ((Real.log 72 + Real.log 424673280 / 4) + Real.log N ^ ((1:ℝ)/12)
          + 6 * Real.log N ^ ((1:ℝ)/24)) * E N
        = 424673280 * Real.log N ^ ((10:ℝ)/11) *
          ((Real.log 72 + Real.log 424673280 / 4) + Real.log N ^ ((1:ℝ)/12)
            + 6 * Real.log N ^ ((1:ℝ)/24)) := by
      rw [hEeq]; ring
    rw [h2] at h1
    linarith
  rw [Real.rpow_def_of_pos hbase]
  have h1 : Real.exp (Real.log (8 * (LN N p : ℝ) * (E N) ^ ((1:ℝ)/4)) * E N)
      ≤ Real.exp (Real.log N) := Real.exp_le_exp.2 hkey
  have h2 : Real.exp (Real.log N) = (N:ℝ) := Real.exp_log (by linarith)
  have h3 : (2:ℝ) * (N:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp1
  linarith

/-- **Green's Proposition 5 at Green's parameters.**  For all large `N`, every prime-sized
`p ∈ [2N, 4N]` and every nonempty `A ⊆ ZMod p`, there is a nonzero good length. -/
theorem eventually_exists_goodLength :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 2 * N ≤ p → p ≤ 4 * N → ∀ [NeZero p],
      ∀ A : Finset (ZMod p), A.Nonempty →
        ∃ d : ZMod p, d ≠ 0 ∧ IsGoodLength A d (MN N) (eps1 N) (eps2 N) (eps3 N) := by
  filter_upwards [eventually_ge_atTop 3, eventually_MN_pos, eventually_prop5_hypothesis8,
    tendsto_log_nat.eventually (eventually_ge_atTop (1:ℝ))] with N hN3 hMN hhyp hlog1
  intro p hp1 hp2 _ A hA
  have hN2 : 2 ≤ N := by omega
  have hε : 0 < epsN N := epsN_pos hN2
  have hε1 : epsN N ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hlog1 (by norm_num)
  have h1 : 0 < eps1 N := hε
  have h2 : 0 < eps2 N := by rw [eps2]; positivity
  have h3 : 0 < eps3 N := by rw [eps3]; positivity
  have h1' : eps1 N ≤ 1 := hε1
  have h2' : eps2 N ≤ 1 := by
    rw [eps2]; nlinarith
  have h3' : eps3 N ≤ 1 := by
    rw [eps3]; nlinarith
  exact exists_goodLength hA hMN h1 h2 h3 h1' h2' h3' (hhyp p hp1 hp2)

end ParamsInstance


/-! ## Axiom audit -/

#print axioms Eprop5_eq
#print axioms Eprop5_pos
#print axioms one_le_Eprop5
#print axioms isGoodLength_iff
#print axioms cast_pos_p
#print axioms norm_fourier_pos_of_mem_R
#print axioms theta_pos
#print axioms mSize_pos
#print axioms one_div_mSize_le_theta
#print axioms exists_goodLength_of_prod_lt
#print axioms card_le_cast_p
#print axioms alpha_mul_delta_sq_mul_Eprop5
#print axioms mSize_le_bound
#print axioms card_R_le_Eprop5
#print axioms prod_mSize_le
#print axioms exists_goodLength
#print axioms log_le_rpow_24
#print axioms eventually_log_params8
#print axioms eventually_prop5_hypothesis8
#print axioms eventually_exists_goodLength

end CameronErdos
