import Erdos387Proof.IntegerFourierWindow
import Erdos387Proof.MediumCertificateZeroMode
import Erdos387Proof.MediumComplementMass
import Erdos387Proof.MediumEndpointError
import Erdos387Proof.MediumComplementBounds

/-! Finite Fourier truncation for the actual compatible roots. The concrete
sum of tail bounds retains the distinguished-coordinate, certificate,
prime-subset and local-root multiplicities. -/

namespace Erdos387Proof.MediumFourierTail

open Erdos387 IntegerSieveResidues IntegerClassFourier TentFourier
open MediumCertificateZeroMode MediumCertificateCover MediumComplementGrouping
open MediumFactorWindow MediumSieveSmoothing
open scoped BigOperators

noncomputable def residuePartial (X Q v k b H : ℕ) [NeZero Q] [NeZero v]
    (hcop : Nat.Coprime Q v) : ℝ :=
  ∑ a ∈ localAssignmentResidues v k,
    (∑ h : ZMod (Q * v) with h.valMinAbs.natAbs ≤ H,
      ZMod.stdAddChar (-h * (simultaneousResidue hcop b a : ZMod (Q * v))) *
        TentFourier.coefficient X (Q * v) h).re

theorem abs_residueMass_sub_partial_le {X Q v k b H : ℕ} [NeZero Q] [NeZero v]
    (hX : 0 < X) (hH : 0 < H) (hv : Squarefree v) (hcop : Nat.Coprime Q v)
    (hlarge : ∀ p ∈ v.primeFactors, k < p) :
    |residueMass X v k (fun n => Int.ModEq (Q : ℤ) n (b : ℤ)) -
        residuePartial X Q v k b H hcop| ≤
      (k : ℝ) ^ v.primeFactors.card * ((Q * v : ℕ) : ℝ) / (2 * X * H) := by
  classical
  rw [residueMass_eq_sum_classMass]
  unfold residuePartial
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _a ∈ localAssignmentResidues v k, ((Q * v : ℕ) : ℝ) / (2 * X * H) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [classMass_eq_progressionMass X Q v a b hcop
        ((ConstrainedSieveResidues.mem_localAssignmentResidues_iff hv).mp ha).1]
      have h := norm_progressionMass_sub_partialSum_le hX hH
        (simultaneousResidue hcop b a : ZMod (Q * v))
      have hr := Complex.abs_re_le_norm ((progressionMass X (Q * v)
          (simultaneousResidue hcop b a : ZMod (Q * v)) : ℂ) -
          ∑ h : ZMod (Q * v) with h.valMinAbs.natAbs ≤ H,
            ZMod.stdAddChar (-h * (simultaneousResidue hcop b a : ZMod (Q * v))) *
              TentFourier.coefficient X (Q * v) h)
      simpa only [Complex.sub_re, Complex.ofReal_re] using hr.trans h
    _ = _ := by simp [card_localAssignmentResidues hlarge]; ring

/-- The partial sum uses a common integer window whenever there is no
frequency aliasing. No interval-length restriction on the tent is needed. -/
theorem residuePartial_eq_integer {X Q v k b H : ℕ} [NeZero Q] [NeZero v]
    (hcop : Nat.Coprime Q v) (hHq : 2 * H < Q * v) :
    residuePartial X Q v k b H hcop =
      ∑ a ∈ localAssignmentResidues v k,
        (∑ h ∈ IntegerFourierWindow.window H,
          ZMod.stdAddChar (-(h : ZMod (Q * v)) *
            (simultaneousResidue hcop b a : ZMod (Q * v))) *
              TentFourier.coefficient X (Q * v) (h : ZMod (Q * v))).re := by
  unfold residuePartial
  apply Finset.sum_congr rfl
  intro a ha
  rw [IntegerFourierWindow.sum_modular_window_eq_integer hHq]

noncomputable def certificatePartial {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (v H : ℕ) [NeZero v]
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v) : ℝ := by
  let : NeZero (CoverBPZ.refinementModulus S * C.val.value) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos).ne'⟩
  exact residuePartial X (CoverBPZ.refinementModulus S * C.val.value) v S.k
    (simultaneousResidue C.property (CoverBPZ.refinementResidue S) C.val.crtResidue) H hcop

noncomputable def certificateIntegerPartial {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (v H : ℕ) [NeZero v]
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v) : ℝ := by
  let : NeZero (CoverBPZ.refinementModulus S * C.val.value) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos).ne'⟩
  exact ∑ a ∈ localAssignmentResidues v S.k,
    (∑ h ∈ IntegerFourierWindow.window H,
      ZMod.stdAddChar (-(h : ZMod (CoverBPZ.refinementModulus S * C.val.value * v)) *
        (simultaneousResidue hcop
          (simultaneousResidue C.property (CoverBPZ.refinementResidue S) C.val.crtResidue)
          a : ZMod (CoverBPZ.refinementModulus S * C.val.value * v))) *
      TentFourier.coefficient X (CoverBPZ.refinementModulus S * C.val.value * v)
        (h : ZMod (CoverBPZ.refinementModulus S * C.val.value * v))).re

theorem certificatePartial_eq_integer {B K X v H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X) [NeZero v]
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v)
    (hHq : 2 * H < CoverBPZ.refinementModulus S * C.val.value * v) :
    certificatePartial C v H hcop = certificateIntegerPartial C v H hcop := by
  let : NeZero (CoverBPZ.refinementModulus S * C.val.value) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos).ne'⟩
  exact residuePartial_eq_integer hcop hHq

noncomputable def certificateTailBound {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) (g H : ℕ) : ℝ :=
  (S.k : ℝ) ^ (g / Nat.gcd g (C.val.factor i)).primeFactors.card *
    ((CoverBPZ.refinementModulus S * C.val.value *
      (g / Nat.gcd g (C.val.factor i)) : ℕ) : ℝ) / (2 * X * H)

/-- Actual gcd-compatible sieve roots; no tail estimate is a premise. -/
theorem abs_certificateMass_sub_partial_le {B K X g H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) [NeZero (g / Nat.gcd g (C.val.factor i))]
    (hX : 0 < X) (hH : 0 < H) (hg : Squarefree g)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) g)
    (hlarge : ∀ p ∈ g.primeFactors, S.k < p) :
    |residueMass X g S.k (integerClass C) -
      certificatePartial C (g / Nat.gcd g (C.val.factor i)) H
        (gcd_quotient_coprime_classModulus C i hg hcop)| ≤
      certificateTailBound C i g H := by
  let : NeZero (CoverBPZ.refinementModulus S * C.val.value) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos).ne'⟩
  have hvdvd : g / Nat.gcd g (C.val.factor i) ∣ g :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have heq : integerClass C = (fun n =>
      Int.ModEq (CoverBPZ.refinementModulus S * C.val.value : ℕ) n
        (simultaneousResidue C.property (CoverBPZ.refinementResidue S) C.val.crtResidue : ℤ)) := by
    funext n
    exact propext (integerClass_iff_combined C n)
  rw [residueMass_certificate_eq_gcd_quotient C i hg, heq]
  exact abs_residueMass_sub_partial_le hX hH (hg.squarefree_of_dvd hvdvd)
    (gcd_quotient_coprime_classModulus C i hg hcop)
    (fun p hp => hlarge p (Nat.primeFactors_mono hvdvd hg.ne_zero hp))

theorem card_factors_le (B X D M medium large : ℕ) :
    (factors B X D M medium large).card ≤ X / D := by
  classical
  have hsub : factors B X D M medium large ⊆ Finset.Ioc 0 (X / D) := by
    intro d hd
    exact Finset.mem_Ioc.mpr ⟨factor_pos_of_mem hd,
      ((Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).2).trans (min_le_right _ _)⟩
  simpa using Finset.card_le_card hsub

/-- Counts actual certificates through the full complementary vector, not
just its product. The latter may have multiple vector factorizations. -/
theorem card_certificates_le {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k) (hB : 0 < B) :
    ((certificates S X z medium large i).card : ℝ) ≤
      (X : ℝ) * roughReciprocalMass z X ^ (S.k - 1) := by
  classical
  calc
    _ = ∑ C ∈ certificates S X z medium large i, (1 : ℝ) := by simp
    _ = ∑ c ∈ (vectors S X z medium large i).attach,
        ∑ _d ∈ factors B X ((representative c).val.otherValue i)
          (CoverBPZ.refinementModulus S) medium large, (1 : ℝ) :=
      sum_certificates_eq_sum_factors i hB _
    _ ≤ ∑ c ∈ (vectors S X z medium large i).attach,
        (X : ℝ) * (1 / (representative c).val.otherValue i) := by
      apply Finset.sum_le_sum
      intro c hc
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hn := card_factors_le B X ((representative c).val.otherValue i)
        (CoverBPZ.refinementModulus S) medium large
      calc
        _ ≤ ((X / (representative c).val.otherValue i : ℕ) : ℝ) := by exact_mod_cast hn
        _ ≤ (X : ℝ) / (representative c).val.otherValue i := Nat.cast_div_le
        _ = _ := by ring
    _ = (X : ℝ) * ∑ c ∈ (vectors S X z medium large i).attach,
        (1 : ℝ) / (representative c).val.otherValue i := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (MediumComplementMass.sum_reciprocal_representatives_le i) (by positivity)

/-- Concrete per-certificate upper envelope for every modulus of bounded
prime-factor count and size. -/
theorem certificateTailBound_le {B K X g H L G : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) (hX : 0 < X) (hH : 0 < H) (hg : 0 < g)
    (hval : C.val.value ≤ X) (hgL : g.primeFactors.card ≤ L) (hgG : g ≤ G) :
    certificateTailBound C i g H ≤
      (S.k : ℝ)^L * CoverBPZ.refinementModulus S * G / (2 * H) := by
  have hk : (1 : ℝ) ≤ S.k := by exact_mod_cast (show 1 ≤ S.k by have := S.hk3; omega)
  have hvdvd : g / Nat.gcd g (C.val.factor i) ∣ g :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hvL : (g / Nat.gcd g (C.val.factor i)).primeFactors.card ≤ L :=
    (Finset.card_le_card (Nat.primeFactors_mono hvdvd hg.ne')).trans hgL
  have hvG : g / Nat.gcd g (C.val.factor i) ≤ G := (Nat.div_le_self _ _).trans hgG
  have hq : CoverBPZ.refinementModulus S * C.val.value *
      (g / Nat.gcd g (C.val.factor i)) ≤ CoverBPZ.refinementModulus S * X * G := by gcongr
  have hqR : ((CoverBPZ.refinementModulus S * C.val.value *
      (g / Nat.gcd g (C.val.factor i)) : ℕ) : ℝ) ≤
        CoverBPZ.refinementModulus S * (X : ℝ) * G := by exact_mod_cast hq
  unfold certificateTailBound
  calc
    _ ≤ (S.k : ℝ)^L * (CoverBPZ.refinementModulus S * (X : ℝ) * G) / (2 * X * H) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (pow_le_pow_right₀ hk hvL) hqR (by positivity) (by positivity)
    _ = _ := by
      have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
      field_simp

/-- The full concrete tail envelope before introducing a cutoff scale. -/
noncomputable def totalTailEnvelope (k M X z L H : ℕ) : ℝ :=
  (k : ℝ) * M * X * (L + 1 : ℕ) * (z : ℝ) ^ (2 * L) * (k : ℝ)^L *
    roughReciprocalMass z X ^ (k - 1) / (2 * H)

/-- Every coordinate, actual certificate, truncated prime subset, and local
root is counted. No analytic tail estimate is assumed in this sum bound. -/
theorem sum_certificateTailBound_le {B K X z medium large L H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (P : Finset ℕ)
    (hB : 0 < B) (hX : 0 < X) (hH : 0 < H) (hz : 1 ≤ z)
    (hP : ∀ p ∈ P, p.Prime) (hPz : P ⊆ Finset.range z) :
    (∑ i : Fin S.k, ∑ C ∈ certificates S X z medium large i,
      ∑ T ∈ P.powerset, if T.card ≤ L then
        certificateTailBound C i (∏ p ∈ T, p) H else 0) ≤
      totalTailEnvelope S.k (CoverBPZ.refinementModulus S) X z L H := by
  classical
  let E : ℝ := (S.k : ℝ)^L * CoverBPZ.refinementModulus S * (z : ℝ)^L / (2 * H)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hper (i : Fin S.k) (C : RefinedTupleCertificate S X)
      (hC : C ∈ certificates S X z medium large i) :
      (∑ T ∈ P.powerset, if T.card ≤ L then
        certificateTailBound C i (∏ p ∈ T, p) H else 0) ≤
        ((L + 1 : ℕ) : ℝ) * (z : ℝ)^L * E := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ _T ∈ P.powerset.filter (fun T => T.card ≤ L), E := by
        apply Finset.sum_le_sum
        intro T hT
        obtain ⟨hTP, hTL⟩ := Finset.mem_filter.mp hT
        have hsub := Finset.mem_powerset.mp hTP
        have hprime : ∀ p ∈ T, p.Prime := fun p hp => hP p (hsub hp)
        have hgpos : 0 < ∏ p ∈ T, p := Finset.prod_pos (fun p hp => (hprime p hp).pos)
        have hgL : (∏ p ∈ T, p).primeFactors.card ≤ L := by
          simpa [Nat.primeFactors_prod hprime] using hTL
        have hgG : (∏ p ∈ T, p) ≤ z ^ L := by
          calc
            _ ≤ ∏ _p ∈ T, z := Finset.prod_le_prod (fun p hp => Nat.zero_le _) (fun p hp =>
              (Finset.mem_range.mp (hPz (hsub hp))).le)
            _ = z ^ T.card := by simp
            _ ≤ z ^ L := Nat.pow_le_pow_right hz hTL
        simpa [E] using certificateTailBound_le C i hX hH hgpos
          (Finset.mem_filter.mp hC).2.1 hgL hgG
      _ = ((P.powerset.filter (fun T => T.card ≤ L)).card : ℝ) * E := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast MediumEndpointError.card_truncated_powerset_le hPz hz) hE
  have hR : 0 ≤ roughReciprocalMass z X := by unfold roughReciprocalMass; positivity
  calc
    _ ≤ ∑ i : Fin S.k, ∑ _C ∈ certificates S X z medium large i,
        ((L + 1 : ℕ) : ℝ) * (z : ℝ)^L * E := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (hper i)
    _ ≤ ∑ _i : Fin S.k, ((X : ℝ) * roughReciprocalMass z X ^ (S.k - 1)) *
        (((L + 1 : ℕ) : ℝ) * (z : ℝ)^L * E) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (card_certificates_le i hB) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold totalTailEnvelope
      dsimp [E]
      rw [show (z : ℝ) ^ (2 * L) = (z : ℝ)^L * (z : ℝ)^L by
        rw [two_mul, pow_add]]
      ring

/-- Positivity of the residual modulus follows from positivity of the
squarefree sieve product; it is not an extra analytic assumption. -/
theorem gcdQuotient_pos {g d : ℕ} (hg : 0 < g) : 0 < g / Nat.gcd g d :=
  Nat.div_pos (Nat.le_of_dvd hg (Nat.gcd_dvd_left g d)) (Nat.gcd_pos_of_pos_left d hg)

/-- Total function for the actual prime-window approximation. Its values
outside the summation domain are immaterial and set to zero. -/
noncomputable def windowCertificatePartial {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k)
    (C : RefinedTupleCertificate S X) (z medium large H : ℕ) (T : Finset ℕ) : ℝ := by
  classical
  exact if hC : C ∈ certificates S X z medium large i then
    if hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset then
      let g := ∏ p ∈ T, p
      have hg : Squarefree g := MediumSignedMainTerm.primeSubsetProduct_squarefree
        (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1) (Finset.mem_powerset.mp hT)
      letI : NeZero (g / Nat.gcd g (C.val.factor i)) :=
        ⟨(gcdQuotient_pos (Nat.pos_of_ne_zero hg.ne_zero)).ne'⟩
      certificatePartial C (g / Nat.gcd g (C.val.factor i)) H
        (gcd_quotient_coprime_classModulus C i hg
          (MediumComplementBounds.window_product_coprime_complement hC hT).symm)
    else 0
  else 0

theorem abs_windowCertificateMass_sub_partial_le {B K X z medium large H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {C : RefinedTupleCertificate S X} {T : Finset ℕ}
    (hX : 0 < X) (hH : 0 < H)
    (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset) :
    |residueMass X (∏ p ∈ T, p) S.k (integerClass C) -
        windowCertificatePartial i C z medium large H T| ≤
      certificateTailBound C i (∏ p ∈ T, p) H := by
  classical
  have hg : Squarefree (∏ p ∈ T, p) := MediumSignedMainTerm.primeSubsetProduct_squarefree
    (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1) (Finset.mem_powerset.mp hT)
  let : NeZero ((∏ p ∈ T, p) / Nat.gcd (∏ p ∈ T, p) (C.val.factor i)) :=
    ⟨(gcdQuotient_pos (Nat.pos_of_ne_zero hg.ne_zero)).ne'⟩
  have hcop := (MediumComplementBounds.window_product_coprime_complement hC hT).symm
  have hlarge : ∀ p ∈ (∏ p ∈ T, p).primeFactors, S.k < p := by
    have hprime : ∀ p ∈ T, p.Prime := fun p hp =>
      (MediumSieveEuler.mem_windowPrimes.mp (Finset.mem_powerset.mp hT hp)).1
    rw [Nat.primeFactors_prod hprime]
    intro p hp
    have hlow := (MediumSieveEuler.mem_windowPrimes.mp (Finset.mem_powerset.mp hT hp)).2.1
    have hk := S.hk3
    omega
  simpa only [windowCertificatePartial, dif_pos hC, dif_pos hT] using
    abs_certificateMass_sub_partial_le C i hX hH hg hcop hlarge

/-- The actual signed prime-window approximation has the fully summed tail
bound. All compatibility and root-count hypotheses are discharged from the
actual medium certificate and prime window. -/
theorem abs_signed_mass_sub_windowPartial_le {B K X z medium large L H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    (hB : 0 < B) (hX : 0 < X) (hH : 0 < H) (hz : 1 ≤ z) :
    |∑ i : Fin S.k, ∑ C ∈ certificates S X z medium large i,
      ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        MediumSignedMainTerm.coefficient L T *
          (residueMass X (∏ p ∈ T, p) S.k (integerClass C) -
            windowCertificatePartial i C z medium large H T)| ≤
      totalTailEnvelope S.k (CoverBPZ.refinementModulus S) X z L H := by
  classical
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans _ (sum_certificateTailBound_le (S := S) (medium := medium) (large := large) (L := L)
    (MediumSieveEuler.windowPrimes S.k z)
    hB hX hH hz (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
      (fun p hp => Finset.mem_range.mpr (MediumSieveEuler.mem_windowPrimes.mp hp).2.2))
  apply Finset.sum_le_sum
  intro i hi
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro C hC
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  by_cases hTL : T.card ≤ L
  · rw [MediumSignedMainTerm.coefficient, if_pos hTL, abs_mul, abs_pow]
    simpa only [abs_neg, abs_one, one_pow, one_mul, if_pos hTL] using
      abs_windowCertificateMass_sub_partial_le hX hH hC hT
  · simp [MediumSignedMainTerm.coefficient, hTL]

end Erdos387Proof.MediumFourierTail
