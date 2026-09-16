import Erdos387Proof.ConvenientMomentDecay

/-! Normalization of the concrete complementary-vector moment.
All dyadic orders are covered by a single eventual threshold, chosen after k.
The Fourier separator and prefix weights enter only through their proved finite
loss budget. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientNormalizedMoment
open Erdos387 Erdos387.CoverBPZ Filter
open ConvenientMomentBoxes ConvenientMomentBound ConvenientMomentApplicability
open ConvenientMomentEstimate ConvenientMomentDecay MediumOscillatoryDecay MediumMainTermDecay
open scoped Topology BigOperators

noncomputable def outsideLoss (C : ℝ) (a b c d e f N k : ℕ) : ℝ :=
  C*(loss a b c d N k : ℝ)*((N : ℝ)+1)^f*
    (1+Real.log (SubpowerScale.X N k))^e

theorem outsideLoss_nonneg {C : ℝ} (hC : 0 ≤ C) (a b c d e f N k : ℕ) :
    0 ≤ outsideLoss C a b c d e f N k := by
  have hX : (1 : ℝ) ≤ SubpowerScale.X N k := by exact_mod_cast SubpowerScale.X_pos N k
  have hlog := Real.log_nonneg hX
  unfold outsideLoss
  positivity

/-- Simultaneous in the bounded dyadic order and in every actual Brun support
product. The fixed constants are absorbed before N is selected. -/
theorem eventually_moment_budget_le_base_sq {B K : ℕ}
    (S : BPZSection6Input B K) (C : ℝ) (hC : 0 ≤ C) (a b c d e f : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ ell ≤ S.k^100,
      ∀ g ≤ SubpowerScale.z N S.k^(2*N),
        outsideLoss C a b c d e f N S.k^(2*ell)*
          (2 : ℝ)^(ell+2)*(refinementModulus S : ℝ)^(2*ell+1)*g*
          ((S.k^(N^2) : ℕ) : ℝ)^(2*ell) /
          (refinedDensity S (SubpowerScale.z N S.k))^(2*ell) ≤
          (SubpowerScale.base N S.k : ℝ)^2 := by
  have hk : 0 < S.k := by have := S.hk3; omega
  have hall : ∀ ell ∈ Finset.range (S.k^100+1), ∀ᶠ N : ℕ in atTop,
      ∀ g ≤ SubpowerScale.z N S.k^(2*N),
        outsideLoss C a b c d e f N S.k^(2*ell)*
          (2 : ℝ)^(ell+2)*(refinementModulus S : ℝ)^(2*ell+1)*g*
          ((S.k^(N^2) : ℕ) : ℝ)^(2*ell) /
          (refinedDensity S (SubpowerScale.z N S.k))^(2*ell) ≤
          (SubpowerScale.base N S.k : ℝ)^2 := by
    intro ell _
    let C0 := C^(2*ell)*(2 : ℝ)^(ell+2)*(refinementModulus S : ℝ)^(2*ell+1)
    have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
    filter_upwards [eventually_core_loss_div_density_le_base S a b c d (2*ell),
      eventually_log_polynomial_le_base hk C0 hC0 (f*(2*ell)) (e*(2*ell))]
      with N hcore hpoly
    intro g hg
    have hV := MediumMainTermDecay.refinedDensity_pos S (SubpowerScale.z N S.k)
    calc
      _ = (C0*((N : ℝ)+1)^(f*(2*ell))*
            (1+Real.log (SubpowerScale.X N S.k))^(e*(2*ell))) *
          ((loss a b c d N S.k : ℝ)^(2*ell)*((S.k^(N^2) : ℕ) : ℝ)^(2*ell)*g /
            (refinedDensity S (SubpowerScale.z N S.k))^(2*ell)) := by
        unfold outsideLoss
        dsimp [C0]
        simp only [mul_pow,pow_mul,div_eq_mul_inv]
        ring
      _ ≤ (SubpowerScale.base N S.k : ℝ)*(SubpowerScale.base N S.k : ℝ) := by
        exact mul_le_mul hpoly (hcore g hg) (by positivity) (by positivity)
      _ = _ := (pow_two _).symm
  filter_upwards [(Finset.eventually_all _).mpr hall] with N hN
  intro ell hell
  exact hN ell (Finset.mem_range.mpr (by omega))

/-- Exact algebraic rescaling; the use-site supplies both inequalities from
its concrete moment and its proved finite loss budget. -/
theorem rescale_moment_bound (A R F X V M m g b : ℝ) (ell : ℕ)
    (hF : 0 ≤ F) (hX : 0 < X) (hV : 0 < V) (hM : 0 < M) (hb : 0 ≤ b)
    (hA : A^(2*ell)*R ≤ 2^(ell+2)*M*g*m^(2*ell)*b*X^(2*ell))
    (hbudget : F^(2*ell)*2^(ell+2)*M^(2*ell+1)*g*m^(2*ell)/V^(2*ell) ≤ b^2) :
    (F*A/(X*V/M))^(2*ell)*R ≤ b^3 := by
  let t := F^(2*ell)*M^(2*ell)/(X^(2*ell)*V^(2*ell))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  calc
    _ = t*(A^(2*ell)*R) := by
      dsimp [t]
      simp only [div_pow,mul_pow]
      field_simp [ne_of_gt hX, ne_of_gt hV, ne_of_gt hM]
    _ ≤ t*(2^(ell+2)*M*g*m^(2*ell)*b*X^(2*ell)) :=
      mul_le_mul_of_nonneg_left hA ht
    _ = (F^(2*ell)*2^(ell+2)*M^(2*ell+1)*g*m^(2*ell)/V^(2*ell))*b := by
      dsimp [t]
      rw [pow_succ M (2*ell)]
      field_simp [ne_of_gt hX, ne_of_gt hV, ne_of_gt hM]
    _ ≤ b^2*b := mul_le_mul_of_nonneg_right hbudget hb
    _ = _ := by ring

theorem base_four_le_y (N k : ℕ) :
    SubpowerScale.base N k^4 ≤ SubpowerScale.y N k := by
  unfold SubpowerScale.y BPZScale.y
  apply Nat.pow_le_pow_right
  · unfold SubpowerScale.base
    positivity
  · unfold BPZScale.yExp
    have : 1 ≤ 3^k := Nat.one_le_pow _ 3 (by omega)
    omega

/-- Removing the retained dyadic R factor leaves a full inverse base. -/
theorem pow_le_inv_base_of_mul_R_le (x R b : ℝ) (q : ℕ)
    (_hx : 0 ≤ x) (hb : 0 < b) (hR : b^4 ≤ R)
    (h : x^q*R ≤ b^3) : x^q ≤ 1/b := by
  have hRp : 0 < R := (pow_pos hb 4).trans_le hR
  calc
    _ ≤ b^3/R := (le_div_iff₀ hRp).mpr h
    _ ≤ b^3/b^4 := div_le_div_of_nonneg_left (by positivity) (by positivity) hR
    _ = _ := by field_simp [ne_of_gt hb]

/-- The normalized actual moment on a nonempty dyadic family. Its sole
finite loss inequality is supplied eventually by the preceding theorem. -/
theorem actual_normalized_pow_le_inv_base {B K N g : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) (e r s a : ℕ) (h : ℤ) [NeZero g]
    (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (rCut sCut : ActualIndex S N i → ℕ) (beta : ActualIndex S N i → ℕ → ℂ)
    (hB : 0 < B) (hN : 0 < N)
    (hthreshold : uniformMomentThreshold S.k ≤ N)
    (hkz : S.k ≤ SubpowerScale.z N S.k) (hh : h ≠ 0)
    (hH : h.natAbs ≤ MediumFourierTailDecay.height N S.k)
    (hshort : (2*SubpowerScale.medium N S.k+1)*MediumFourierTailDecay.height N S.k ≤
      (SubpowerScale.X N S.k/2)/(B*SubpowerScale.medium N S.k))
    (hbeta : ∀ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
      ∀ v ∈ variableBox g s (sCut c) c, ‖beta c v‖ ≤ 1)
    (hne : (activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s).Nonempty)
    (F : ℝ) (hF : 0 ≤ F)
    (hbudget : F^(2*ConvenientMomentSaving.dyadicMoment e s)*
      (2 : ℝ)^(ConvenientMomentSaving.dyadicMoment e s+2)*
      (refinementModulus S : ℝ)^(2*ConvenientMomentSaving.dyadicMoment e s+1)*g*
      ((S.k^(N^2) : ℕ) : ℝ)^(2*ConvenientMomentSaving.dyadicMoment e s) /
      (refinedDensity S (SubpowerScale.z N S.k))^(2*ConvenientMomentSaving.dyadicMoment e s) ≤
      (SubpowerScale.base N S.k : ℝ)^2) :
    (F*firstMoment S N i e r s a h hg hsupport rCut sCut beta /
      ((SubpowerScale.X N S.k : ℝ)*refinedDensity S (SubpowerScale.z N S.k)/refinementModulus S))^
      (2*ConvenientMomentSaving.dyadicMoment e s) ≤ 1/(SubpowerScale.base N S.k : ℝ) := by
  have hell := active_moment_data hB hN hshort hne
  have hmoment := firstMoment_pow_mul_R_le S i e r s a h hg hsupport rCut sCut beta
    hB hN (by omega : 1 ≤ ConvenientMomentSaving.dyadicMoment e s) hell.2.1
    hthreshold hkz hh hH hshort hbeta hell.2.2.1
  have hprod := active_scale_product_le_X hne
  push_cast at hmoment
  have hX : (0 : ℝ) < SubpowerScale.X N S.k := by
    unfold SubpowerScale.X BPZScale.X SubpowerScale.base
    positivity
  have hV := MediumMainTermDecay.refinedDensity_pos S (SubpowerScale.z N S.k)
  have hM : (0 : ℝ) < refinementModulus S := by exact_mod_cast refinementModulus_pos S
  have hb : (0 : ℝ) < SubpowerScale.base N S.k := by unfold SubpowerScale.base; positivity
  have hraw : firstMoment S N i e r s a h hg hsupport rCut sCut beta^
      (2*ConvenientMomentSaving.dyadicMoment e s)*(2 : ℝ)^r ≤
      2^(ConvenientMomentSaving.dyadicMoment e s+2)*refinementModulus S*g*
      ((S.k^(N^2) : ℕ) : ℝ)^(2*ConvenientMomentSaving.dyadicMoment e s)*
      SubpowerScale.base N S.k*(SubpowerScale.X N S.k : ℝ)^(2*ConvenientMomentSaving.dyadicMoment e s) := by
    push_cast
    apply hmoment.trans
    have hp : (2 : ℝ)^e*2^r*2^s ≤ SubpowerScale.X N S.k := by exact_mod_cast hprod
    gcongr
  have hnormalized := rescale_moment_bound _ ((2 : ℝ)^r) F _ _ _ _ _ _
    (ConvenientMomentSaving.dyadicMoment e s) hF hX hV hM hb.le hraw hbudget
  apply pow_le_inv_base_of_mul_R_le _ ((2 : ℝ)^r) _ _ (by
    apply div_nonneg
    · apply mul_nonneg hF
      unfold firstMoment
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    · positivity) hb _ hnormalized
  exact_mod_cast (base_four_le_y N S.k).trans hell.2.2.2

/-- An inverse-base moment bound is uniformly small for all bounded moment
orders; this avoids choosing a separate threshold for each dyadic box. -/
theorem eventually_small_of_pow_le_inv_base (k Q : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ q ≤ Q, ∀ x : ℝ,
      x^q ≤ 1/(SubpowerScale.base N k : ℝ) → x < epsilon := by
  let delta := min epsilon 1
  have hdelta : 0 < delta := lt_min hepsilon (by norm_num)
  have hdeltaOne : delta ≤ 1 := min_le_right _ _
  have hdeltaEps : delta ≤ epsilon := min_le_left _ _
  have hdq : 0 < delta^Q := pow_pos hdelta Q
  filter_upwards [eventually_polynomial_le_base k 0 (2/delta^Q)] with N hbound
  simp only [pow_zero,mul_one] at hbound
  have hb : (0 : ℝ) < SubpowerScale.base N k := by unfold SubpowerScale.base; positivity
  have hsmall : 1/(SubpowerScale.base N k : ℝ) < delta^Q := by
    have ht := (div_le_iff₀ hdq).mp hbound
    apply (div_lt_iff₀ hb).mpr
    nlinarith
  intro q hq x hx
  by_contra hn
  have hdx : delta ≤ x := hdeltaEps.trans (le_of_not_gt hn)
  have hp : delta^Q ≤ x^q :=
    (pow_le_pow_of_le_one hdelta.le hdeltaOne hq).trans
      (pow_le_pow_left₀ hdelta.le hdx q)
  linarith

/-- Uniform decay of the actual first moment, with every fixed finite loss
budget. The eventual threshold precedes all Brun supports, frequencies,
complementary vectors, dyadic boxes, and independent Abel prefixes. -/
theorem eventually_actual_normalized_small {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B)
    (C : ℝ) (hC : 0 ≤ C) (aa bb cc dd ee ff : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : ℕ) [NeZero g],
      ∀ (hg : Squarefree g)
        (hsupport : ∀ p ∈ g.primeFactors,
          max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k),
      g ≤ SubpowerScale.z N S.k^(2*N) →
      ∀ (i : Fin S.k) (e r s a : ℕ) (h : ℤ),
      h ≠ 0 → h.natAbs ≤ MediumFourierTailDecay.height N S.k →
      ∀ (rCut sCut : ActualIndex S N i → ℕ) (beta : ActualIndex S N i → ℕ → ℂ),
      (∀ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
        ∀ v ∈ variableBox g s (sCut c) c, ‖beta c v‖ ≤ 1) →
      outsideLoss C aa bb cc dd ee ff N S.k*
        firstMoment S N i e r s a h hg hsupport rCut sCut beta /
        ((SubpowerScale.X N S.k : ℝ)*refinedDensity S (SubpowerScale.z N S.k)/refinementModulus S)
        < epsilon := by
  classical
  have hk : 0 < S.k := by have := S.hk3; omega
  filter_upwards [eventually_moment_budget_le_base_sq S C hC aa bb cc dd ee ff,
    eventually_small_of_pow_le_inv_base S.k (2*S.k^100) hepsilon,
    eventually_ge_atTop (1 : ℕ),eventually_ge_atTop (uniformMomentThreshold S.k),
    SubpowerScale.eventually_const_le_z hk S.k,
    eventually_height_mul_medium_le_floor hB hk] with N hbudget hsmall hN hthreshold hkz hshort
  intro g _ hg hs hgG i e r s a h hh hH rCut sCut beta hbeta
  by_cases hne : (activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
    (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s).Nonempty
  · have hell := active_moment_data hB hN hshort hne
    have hp := actual_normalized_pow_le_inv_base S i e r s a h hg hs rCut sCut beta
      hB hN hthreshold hkz hh hH hshort hbeta hne
      (outsideLoss C aa bb cc dd ee ff N S.k)
      (outsideLoss_nonneg hC aa bb cc dd ee ff N S.k)
      (hbudget _ hell.2.1 g hgG)
    exact hsmall _ (by omega) _ hp
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [firstMoment,hempty,Finset.sum_empty,mul_zero,zero_div]
    exact hepsilon

end Erdos387Proof.ConvenientNormalizedMoment
