import Erdos387Proof.ConvenientPhaseData
import Erdos387Proof.ConvenientMomentSaving
import Erdos387Proof.MediumFourierTailDecay

/-! Uniform actual-scale shortness and a single threshold for every dyadic
moment order. All thresholds precede the choice of certificate and frequency. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientMomentApplicability
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open ConvenientCertificateEnlargement MediumFourierTailDecay Filter
open scoped Topology

/-- The actual near-product window and the selected-factor upper cutoff
supply the lower complementary-product bound. -/
theorem certificate_complement_lower {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X}
    (hB : 0 < B) (ht : t ∈ ConvenientCertificateEnlargement.certificates S X z y medium i) :
    1+(X/2)/(B*medium) ≤ t.1.val.otherValue i := by
  classical
  obtain ⟨_,_,hnear,_,hf⟩ := Finset.mem_filter.mp ht
  have hm : 0 < medium := (t.1.val.positive i).trans_le (hf i).1
  have hprod : X/2 < (B*medium)*t.1.val.otherValue i := by
    calc
      X/2 < B*t.1.val.value := hnear
      _ = B*(t.1.val.factor i*t.1.val.otherValue i) := by
        rw [t.1.val.factor_mul_otherValue]
      _ ≤ (B*medium)*t.1.val.otherValue i := by
        rw [mul_assoc]
        gcongr
        exact (hf i).1
  have hdiv : (X/2)/(B*medium) < t.1.val.otherValue i :=
    (Nat.div_lt_iff_lt_mul (Nat.mul_pos hB hm)).mpr (by simpa [mul_comm] using hprod)
  omega

/-- Explicit integer exponent comparison; medium squared leaves a large
fixed-power gap below X. -/
theorem base_sq_mul_medium_sq_le_X (N : ℕ) {k : ℕ} (hk : 0 < k) :
    SubpowerScale.base N k^2*SubpowerScale.medium N k^2 ≤ SubpowerScale.X N k := by
  have hb : 1 ≤ SubpowerScale.base N k := by
    unfold SubpowerScale.base
    exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  change SubpowerScale.base N k^2*(SubpowerScale.base N k^BPZScale.mediumExp k)^2 ≤ SubpowerScale.base N k^BPZScale.xExp k
  rw [← pow_mul,← pow_add]
  apply Nat.pow_le_pow_right hb
  have hc : 0 < 3^k*k^100 := by positivity
  unfold BPZScale.mediumExp BPZScale.xExp
  nlinarith

/-- Enough room for every frequency in the actual finite cutoff. -/
theorem eventually_height_mul_medium_le_floor {B k : ℕ} (hB : 0 < B) (hk : 0 < k) :
    ∀ᶠ N : ℕ in atTop,
      (2*SubpowerScale.medium N k+1)*height N k ≤ (SubpowerScale.X N k/2)/(B*SubpowerScale.medium N k) := by
  filter_upwards [eventually_const_le_base k (6*B),
    eventually_height_pow_mul_support_le_base k 1 0] with N hBbase hH
  simp only [pow_one,zero_mul,pow_zero,mul_one] at hH
  have hm : 0 < SubpowerScale.medium N k := by
    unfold SubpowerScale.medium BPZScale.medium SubpowerScale.base
    positivity
  have hm3 : 2*SubpowerScale.medium N k+1 ≤ 3*SubpowerScale.medium N k := by omega
  have hprod : (2*SubpowerScale.medium N k+1)*height N k*
      (B*SubpowerScale.medium N k)*2 ≤ SubpowerScale.X N k := by
    calc
      _ = 2*B*SubpowerScale.medium N k*(2*SubpowerScale.medium N k+1)*height N k := by ring
      _ ≤ 2*B*SubpowerScale.medium N k*(3*SubpowerScale.medium N k)*height N k := by gcongr
      _ = (6*B)*height N k*SubpowerScale.medium N k^2 := by ring
      _ ≤ SubpowerScale.base N k*SubpowerScale.base N k*SubpowerScale.medium N k^2 := by gcongr
      _ = SubpowerScale.base N k^2*SubpowerScale.medium N k^2 := by ring
      _ ≤ SubpowerScale.X N k := base_sq_mul_medium_sq_le_X N hk
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos hB hm)).mpr
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mpr hprod

/-- Strict moment shortness is a finite consequence of the frequency bound.
The frequency must be nonzero; no such claim is made at the zero mode. -/
theorem shortness_of_floor_bound {D a H m F : ℕ}
    (hD : 1+F ≤ D) (hbudget : (2*m+1)*H ≤ F) (ha : 0 < a) (haH : a ≤ H) :
    2*m < D/Nat.gcd D a := by
  have hDpos : 0 < D := by omega
  have hgpos : 0 < Nat.gcd D a := Nat.gcd_pos_of_pos_left a hDpos
  have hga : Nat.gcd D a ≤ H := (Nat.gcd_le_right D ha).trans haH
  have hmul : (2*m+1)*Nat.gcd D a ≤ D :=
    (Nat.mul_le_mul_left _ hga).trans (hbudget.trans (by omega))
  have hdiv : 2*m+1 ≤ D/Nat.gcd D a := (Nat.le_div_iff_mul_le hgpos).mpr hmul
  omega

/-- One eventual condition covers all actual certificates and all nonzero
integer frequencies, before either is chosen. -/
theorem eventually_certificate_shortness {B K : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, ∀ i : Fin S.k,
      ∀ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i,
      ∀ h : ℤ, h≠0 → h.natAbs ≤ height N S.k →
        2*SubpowerScale.medium N S.k < t.1.val.otherValue i/Nat.gcd (t.1.val.otherValue i) h.natAbs := by
  have hk : 0 < S.k := by have := S.hk3; omega
  filter_upwards [eventually_height_mul_medium_le_floor hB hk] with N hN
  intro i t ht h hh hH
  exact shortness_of_floor_bound (certificate_complement_lower hB ht) hN
    (Int.natAbs_pos.mpr hh) hH

/-- The moment API needs a nonzero modulus even at the unused index D=0.
Positive complementary products retain the exact CRT modulus. -/
def momentModulus (M g D : ℕ) : ℕ := if D=0 then 1 else M*D*g

instance momentModulus_neZero (M g D : ℕ) [NeZero M] [NeZero g] :
    NeZero (momentModulus M g D) := by
  constructor
  unfold momentModulus
  split_ifs with hD
  · norm_num
  · exact Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne M) hD) (NeZero.ne g)

theorem momentModulus_eq {M g D : ℕ} (hD : 0 < D) :
    momentModulus M g D=M*D*g := by
  simp only [momentModulus,if_neg hD.ne']

theorem dvd_momentModulus {M g D : ℕ} (hD : 0 < D) :
    D ∣ momentModulus M g D := by
  rw [momentModulus_eq hD]
  exact (dvd_mul_left D M).trans (dvd_mul_right (M*D) g)

/-- A finite maximum is selected once for all possible dyadic moment orders. -/
def uniformMomentThreshold (k : ℕ) : ℕ :=
  (Finset.range (k^100+1)).sup (SubpowerScale.reciprocalMomentThreshold k)

theorem reciprocalMomentThreshold_le_uniform {k ell : ℕ} (hell : ell ≤ k^100) :
    SubpowerScale.reciprocalMomentThreshold k ell ≤ uniformMomentThreshold k :=
  Finset.le_sup (Finset.mem_range.mpr (by omega))

theorem eventually_all_moment_thresholds (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ ell ≤ k^100, SubpowerScale.reciprocalMomentThreshold k ell ≤ N := by
  filter_upwards [eventually_ge_atTop (uniformMomentThreshold k)] with N hN
  intro ell hell
  exact (reciprocalMomentThreshold_le_uniform hell).trans hN

/-- The same threshold applies uniformly as the dyadic boxes vary. -/
theorem eventually_dyadic_moment_thresholds {k : ℕ} (hk : 0 < k) :
    ∀ᶠ N : ℕ in atTop, ∀ e s : ℕ,
      e ≤ ConvenientMomentSaving.xLog N k → ConvenientMomentSaving.yLog N k ≤ s →
      SubpowerScale.reciprocalMomentThreshold k (ConvenientMomentSaving.dyadicMoment e s) ≤ N := by
  filter_upwards [eventually_all_moment_thresholds k,eventually_ge_atTop (1 : ℕ)] with N hN hpos
  intro e s he hs
  exact hN _ (ConvenientMomentSaving.dyadicMoment_le_k_pow (by omega) hk he hs)

end Erdos387Proof.ConvenientMomentApplicability
