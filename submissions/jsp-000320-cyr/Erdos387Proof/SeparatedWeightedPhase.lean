import Erdos387Proof.SeparatedBuchstabAssembly
import Erdos387Proof.WeightedIntervalCut

/-! The proved full-interval rough phase bound with the actual tent weight
and an exact sharp interval mask. No shorter-interval cancellation is used. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedWeightedPhase
open Erdos387 Erdos387.CoverBPZ SeparatedCertificatePhase
open SeparatedBuchstabAssembly SeparatedBuchstabDecomposition
open MaskedReciprocalPhase FourierVariation WeightedIntervalCut
open scoped BigOperators

noncomputable def roughBound (k t Q : ℕ) : ℝ :=
  (4*(Q : ℝ)/(t : ℝ))*(1+Real.log (BPZScale.y t k)) +
  ((Nat.log2 ((BPZScale.y t k)^2)+1 : ℕ) : ℝ)*
    (1+Real.log (2*(Q : ℝ)+1))*(1+Real.log (2*(BPZScale.y t k : ℝ)+1))*
      (2*Real.sqrt (6*(Q : ℝ)^2/(t : ℝ)))

/-- The original near-divisor witness bounds the tent weight uniformly on
the containing dyadic interval. The modulus is the actual anchor conductor. -/
theorem certificate_tent_ratio_le {B K n y medium second gap g X Q : ℕ}
    {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n y medium second gap g)
    (hnear : X/2<B*C.E.value) (hQ : C.q C.i₀≤Q) :
    (X : ℝ)/(C.modulus*(Q/2+1) : ℕ)≤4*B := by
  have hg : 0<g := by
    by_contra h
    have hg0 : g=0 := by omega
    have hm := C.modulus_pos
    simp only [CertificatePhaseData.modulus,hg0,zero_mul] at hm
    omega
  have hval : C.E.value≤C.modulus*C.q C.i₀ := by
    rw [C.modulus_mul_removed]
    exact (Nat.le_mul_of_pos_left _ hg).trans
      (Nat.le_mul_of_pos_right _ (refinementModulus_pos S))
  have hX : X≤2*B*C.modulus*Q := by
    have hx : X<C.E.value*B*2 := by
      simpa only [mul_comm,mul_left_comm,mul_assoc] using
        ((Nat.div_lt_iff_lt_mul (by norm_num : 0<(2 : ℕ))).mp hnear)
    have h₁ := Nat.mul_le_mul_left (2*B) hval
    have h₂ := Nat.mul_le_mul_left (2*B*C.modulus) hQ
    exact hx.le.trans (by nlinarith)
  have hQ2 : Q≤2*(Q/2+1) := by omega
  have hbound : X≤4*B*(C.modulus*(Q/2+1)) := by
    exact hX.trans (by nlinarith [Nat.mul_le_mul_left (2*B*C.modulus) hQ2])
  have hden : (0 : ℝ)<(C.modulus*(Q/2+1) : ℕ) := by
    exact_mod_cast Nat.mul_pos C.modulus_pos (by omega : 0<Q/2+1)
  apply (div_le_iff₀ hden).mpr
  exact_mod_cast hbound

theorem norm_tent_rough_cut_le
    {B K n t medium g : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (ht : 6*2^S.k≤t) (hg : g≤t) (hM : refinementModulus S≤t)
    (X Q lo hi : ℕ) (hQ : C.q C.i₀≤Q) (hX : 0<X) (hlo : lo≤hi)
    (b : ℕ) (hb : ∀ i, i≠C.i₀ → Nat.ModEq (C.E.factor i) b i.val)
    (h : ℤ) (hh : (h : ZMod (C.q C.j))≠0) {R H : ℝ}
    (hR : 0≤R) (hH : 0≤H) (hhH : |(h : ℝ)|≤H) (hiX : C.i₀.val≤X)
    (hbound : (X : ℝ)/(C.modulus*(Q/2+1) : ℕ)≤R) :
    ‖∑ v ∈ Finset.Ioc (Q/2) Q, if lo<v ∧ v≤hi then
      tentWeight X h (-C.i₀.val) (C.modulus*v : ℕ)⁻¹ *
        (roughIndicator (BPZScale.y t S.k) v*
          seq C.modulus ((-h)*((b : ℤ)-C.i₀.val)) 0 [] (v : ℤ)) else 0‖ ≤
      (4*(8*R+128*H*R^2))*(Real.log (Q-Q/2+1 : ℕ)+1)*roughBound S.k t Q := by
  have hend : Q/2+(Q-Q/2)=Q := Nat.add_sub_of_le (Nat.div_le_self _ _)
  have hchar : ∀ χ : AddChar ℤ ℂ, (∀ a, ‖χ a‖=1) →
      ‖∑ v ∈ Finset.Ioc (Q/2) (Q/2+(Q-Q/2)), χ (v : ℤ)*
        (roughIndicator (BPZScale.y t S.k) v*
          seq C.modulus ((-h)*((b : ℤ)-C.i₀.val)) 0 [] (v : ℤ))‖≤roughBound S.k t Q := by
    intro χ hχ
    rw [hend]
    simpa only [roughBound,mul_left_comm] using
      norm_rough_phase_le C ht hg hM Q hQ b hb (-h)
        (by simpa only [Int.cast_neg] using neg_ne_zero.mpr hh) χ hχ
  have hidx : |-(C.i₀.val : ℤ)|≤(X : ℤ) := by
    rw [abs_neg,abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast hiX
  have hw := norm_tent_cut_Ioc_le X C.modulus (Q/2) (Q-Q/2) lo hi h (-C.i₀.val)
    (fun v => roughIndicator (BPZScale.y t S.k) v*
      seq C.modulus ((-h)*((b : ℤ)-C.i₀.val)) 0 [] (v : ℤ))
    hX C.modulus_pos hR hH hhH hidx hlo hbound hchar
  simpa only [hend] using hw

end Erdos387Proof.SeparatedWeightedPhase
