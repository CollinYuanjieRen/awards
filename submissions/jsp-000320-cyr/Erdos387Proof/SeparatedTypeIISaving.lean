import Erdos387Proof.SeparatedTypeIICauchy

/-! Explicit six-over-base saving for the actual dyadic Type-II sum.
The norm-two window normalization is retained as an external factor2. -/

namespace Erdos387Proof.SeparatedTypeIISaving

open scoped BigOperators
open Erdos387 Erdos387.CoverBPZ SeparatedCertificatePhase SeparatedTypeIICauchy
open SeparatedProductWindow MaskedReciprocalPhase

/-- Polynomial form of the Cauchy simplification. Multiplying by t avoids
any approximate replacement of an integer quotient. -/
theorem cauchy_polynomial_le_six (c d L U Q t : ℝ)
    (_hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (hL0 : 0 ≤ L) (hU0 : 0 ≤ U) (_hQ0 : 0 ≤ Q)
    (ht : 0 < t) (hc : c ≤ U) (hd : d ≤ U) (htU : t ≤ 2*U) (hUL : U*L ≤ Q) :
    L*(c*L+c*d*(4*L/t)) ≤ 6*Q^2/t := by
  have hct : c*t ≤ 2*U^2 := by
    calc
      c*t ≤ U*(2*U) := mul_le_mul hc htU ht.le hU0
      _ = _ := by ring
  have hcd : c*d ≤ U^2 := by
    simpa only [pow_two] using mul_le_mul hc hd hd0 hU0
  have hsum : c*t+4*c*d ≤ 6*U^2 := by nlinarith
  have hsquare : (U*L)^2 ≤ Q^2 := pow_le_pow_left₀ (mul_nonneg hU0 hL0) hUL 2
  apply (le_div_iff₀ ht).mpr
  calc
    _ = (c*t+4*c*d)*L^2 := by field_simp
    _ ≤ (6*U^2)*L^2 := mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ ≤ 6*Q^2 := by nlinarith

/-- Concrete integer floors and card bounds imply the numeric saving. -/
theorem cauchy_nat_bound (Q U t c : ℕ) (ht : 0 < t) (htU : t ≤ 2*U) (hc : c ≤ U) :
    ((Q/U-Q/(4*U) : ℕ) : ℝ)*
      ((c : ℝ)*((Q/U-Q/(4*U) : ℕ) : ℝ) +
        (c : ℝ)*((c-1 : ℕ) : ℝ)*(4*((Q/U-Q/(4*U) : ℕ) : ℝ)/(t : ℝ))) ≤
      6*(Q : ℝ)^2/(t : ℝ) := by
  have hUL : U*(Q/U-Q/(4*U)) ≤ Q :=
    (Nat.mul_le_mul_left U (Nat.sub_le _ _)).trans (by
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self Q U)
  apply cauchy_polynomial_le_six (U := (U : ℝ)) <;> try positivity
  · exact_mod_cast hc
  · exact_mod_cast (Nat.sub_le c 1).trans hc
  · exact_mod_cast htU
  · exact_mod_cast hUL

theorem base_le_y (t k : ℕ) (ht : 1 ≤ t) : t ≤ BPZScale.y t k := by
  have he : 1 ≤ BPZScale.yExp k := by
    unfold BPZScale.yExp
    have : 0 < 3^k := by positivity
    omega
  simpa only [BPZScale.y, pow_one] using Nat.pow_le_pow_right ht he

theorem dyadicUnits_gt_y (y M j u : ℕ) (hy : 1 ≤ y) (hu : u ∈ dyadicUnits y M j) : y < u := by
  classical
  obtain ⟨hi,_⟩ := Finset.mem_filter.mp hu
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨hl,hs⟩ := (mem_stoppedLeaves y l).mp hl
  exact ((SeparatedBuchstabDecomposition.e5_leaf_domain y hy l hl).2 hs).1

theorem nonempty_dyadic_scale (y M j : ℕ) (hy : 1 ≤ y)
    (hne : (dyadicUnits y M j).Nonempty) : y < 2*2^j ∧ 2^j ≤ y^2 := by
  obtain ⟨u,hu⟩ := hne
  have hd := dyadicUnits_data y M j u hy hu
  constructor
  · have hhi : u < 2*2^j := by simpa only [pow_succ, Nat.mul_comm] using hd.2.2.2.2
    exact (dyadicUnits_gt_y y M j u hy hu).trans hhi
  · exact hd.2.2.2.1.trans hd.2.1

/-- The actual unit-filtered stopped-leaf sum with both original
single-variable coefficients explicit. -/
noncomputable def dyadicBilinear (M Q y j : ℕ) [NeZero M]
    (c : ℤ) (χ : AddChar ℤ ℂ) (α β : ℕ → ℂ) : ℂ :=
  ∑ u ∈ dyadicUnits y M j, ∑ m ∈ Finset.Ioc (Q/(4*2^j)) (Q/2^j),
    α u*β m*(χ ((u : ℤ)*m)*seq M c 0 [] ((u : ℤ)*m))

theorem dyadicBilinear_eq_zero_of_empty (M Q y j : ℕ) [NeZero M]
    (c : ℤ) (χ : AddChar ℤ ℂ) (α β : ℕ → ℂ) (he : dyadicUnits y M j = ∅) :
    dyadicBilinear M Q y j c χ α β = 0 := by simp [dyadicBilinear,he]

theorem dyadicBilinear_eq_zero_of_scale_gt (M Q y j : ℕ) [NeZero M]
    (c : ℤ) (χ : AddChar ℤ ℂ) (α β : ℕ → ℂ) (hQ : Q < 2^j) :
    dyadicBilinear M Q y j c χ α β = 0 := by
  simp [dyadicBilinear,Nat.div_eq_of_lt hQ]

/-- Uniform nonexceptional saving on EVERY actual dyadic block. Empty
blocks and scales larger than Q are handled internally. -/
theorem norm_dyadicBilinear_sq_le_six
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 6*2^S.k ≤ t) (hg : g ≤ t) (hM : refinementModulus S ≤ t)
    (Q j : ℕ) (hQ : C.q C.i₀ ≤ Q)
    (b : ℕ) (hb : ∀ i, i ≠ C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j)) ≠ 0)
    (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1)
    (α β : ℕ → ℂ)
    (hα : ∀ u ∈ dyadicUnits (BPZScale.y t S.k) C.modulus j, ‖α u‖ ≤ 1)
    (hβ : ∀ m ∈ Finset.Ioc (Q/(4*2^j)) (Q/2^j), ‖β m‖ ≤ 1) :
    ‖dyadicBilinear C.modulus Q (BPZScale.y t S.k) j
      (h*((b : ℤ)-C.i₀.val)) χ α β‖^2 ≤ 6*(Q : ℝ)^2/(t : ℝ) := by
  classical
  have ht1 : 1 ≤ t := by
    have : 1 ≤ 2^S.k := Nat.one_le_pow _ _ (by omega)
    omega
  have hy : 1 ≤ BPZScale.y t S.k := ht1.trans (base_le_y t S.k ht1)
  by_cases he : dyadicUnits (BPZScale.y t S.k) C.modulus j = ∅
  · rw [dyadicBilinear_eq_zero_of_empty _ _ _ _ _ _ _ _ he]
    simp only [norm_zero, zero_pow (by omega : 2 ≠ 0)]
    positivity
  by_cases hUQ : 2^j ≤ Q
  · have hscale := nonempty_dyadic_scale (BPZScale.y t S.k) C.modulus j hy (Finset.nonempty_iff_ne_empty.mpr he)
    have htc : t ≤ 2*2^j := (base_le_y t S.k ht1).trans hscale.1.le
    have hc := certificate_typeII_sq_le C ht hg hM Q (2^j) hQ (by positivity) hUQ hscale.2
      (dyadicUnits (BPZScale.y t S.k) C.modulus j)
      (fun u hu => (dyadicUnits_data _ _ _ _ hy hu).2.1)
      (fun u hu => (dyadicUnits_data _ _ _ _ hy hu).2.2.1)
      b hb h χ hχ α β hα hβ
    simp only [hh, if_false] at hc
    exact hc.trans (cauchy_nat_bound Q (2^j) t _ (by omega) htc
      (card_dyadicUnits_le (BPZScale.y t S.k) C.modulus j))
  · rw [dyadicBilinear_eq_zero_of_scale_gt _ _ _ _ _ _ _ _ (by omega)]
    simp only [norm_zero, zero_pow (by omega : 2 ≠ 0)]
    positivity

/-- The external factor2 from window-left normalization costs exactly4
in squared norm. It is not silently discarded. -/
theorem norm_two_mul_sq_le_twentyFour (z : ℂ) (Q t : ℕ)
    (hz : ‖z‖^2 ≤ 6*(Q : ℝ)^2/(t : ℝ)) :
    ‖(2 : ℂ)*z‖^2 ≤ 24*(Q : ℝ)^2/(t : ℝ) := by
  have hh := mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 4)
  rw [norm_mul]
  norm_num
  calc
    (2*‖z‖)^2 = 4*‖z‖^2 := by ring
    _ ≤ 4*(6*(Q : ℝ)^2/(t : ℝ)) := hh
    _ = 24*(Q : ℝ)^2/(t : ℝ) := by ring

end Erdos387Proof.SeparatedTypeIISaving
