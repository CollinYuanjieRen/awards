import Erdos387Proof.ConvenientBoxIdentity
import Erdos387Proof.ConvenientBoxEnvelope
import Erdos387Proof.ConvenientNormalizedMoment
import Erdos387Proof.ConvenientFibreFourier
import Erdos387Proof.ConvenientDyadicReduction
import Erdos387Proof.MediumFrequencyBudget

/-! Outer summation of the actual convenient partial Fourier remainder. -/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientOuterPartial

open Erdos387 Erdos387.CoverBPZ
open ConvenientCertificateCover ConvenientComplementGrouping ConvenientSplitFibre
open ConvenientMomentBoxes ConvenientMomentBound ConvenientMomentApplicability
open ConvenientWeightedMoment ConvenientWeightedBox ConvenientBoxIdentity
open ConvenientDyadicReduction ConvenientFibreFourier ConvenientNormalizedMoment
open MediumFourierTailDecay MediumSubpowerReduction Filter
open scoped BigOperators Topology

/-- The local-residue and nonzero-frequency sum of the masked summand of one
ordered split pair. -/
noncomputable def maskedBox {B K N g : ℕ} (S : BPZSection6Input B K) (i : Fin S.k)
    [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (H : ℕ) (c : ActualIndex S N i) (p : ℕ × ℕ) : ℝ :=
  ∑ a ∈ localAssignmentResidues g S.k,
    ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
      (boxSummand S i a h hg hsupport c p).re

set_option linter.style.haveILetI false in
/-- The complement-fixed bilinear partial of one ordered split pair is the
totalised masked box summand. -/
theorem complementMaskedPartial_eq {B K N : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k}
    (c : ActualIndex S N i)
    (p : {p // p ∈ splitPairFibreOf i (Certificates S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
      (SubpowerScale.medium N S.k) i) c.val})
    {T : Finset ℕ}
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset)
    [NeZero (∏ q ∈ T, q)] (hg : Squarefree (∏ q ∈ T, q))
    (hsupport : ∀ q ∈ (∏ q ∈ T, q).primeFactors,
      max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k) (H : ℕ) :
    complementMaskedPartial c p H T = maskedBox S i hg hsupport H c p.val := by
  classical
  have ht := fibreCertificate_mem p
  have hdata := ConvenientPhaseData.sieve_applicability ht hg hsupport
  have hpair := fibreCertificate_pair p
  have hD : (fibreCertificate p).1.val.otherValue i = product c := by
    rw [product_eq_otherValue]
    exact otherValue_eq_of_factors_eq_off_index _ _ i
      (fibreCertificate_off_factors p)
  have hr0 : 0 < p.val.1 := by
    simpa only [hpair] using (ConvenientPhaseData.split_pos ht).1
  have hs0 : 0 < p.val.2 := by
    simpa only [hpair] using (ConvenientPhaseData.split_pos ht).2
  have hcop : p.val.1.Coprime (modulus S (∏ q ∈ T, q) (product c)) := by
    rw [modulus, momentModulus_eq (product_data c).1]
    simpa only [hpair, hD] using hdata.2.2.2.2.2.1
  haveI : NeZero p.val.1 := ⟨hr0.ne'⟩
  haveI : NeZero (refinementModulus S *
      (complementRepresentative c).1.val.otherValue i * ∏ q ∈ T, q) := by
    rw [← modulus_eq S (g := ∏ q ∈ T, q) c]
    infer_instance
  unfold complementMaskedPartial
  rw [dif_pos hT]
  unfold maskedBox
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun h _ => ?_
  rw [boxSummand_eq S i a h hg hsupport c hs0 hcop]
  refine congrArg Complex.re ?_
  exact (MediumFibreFourier.maskedFourierSummand_congr _ _ _ _ _ _ _ _ _ h _ hs0
    (modulus_eq S c) rfl).symm

/-- Inside one dyadic box the local-residue and frequency sums may be pulled
outside, and the exact boxed fibre becomes the weighted double box. -/
theorem sum_maskedBox_boxedPairs {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (H r s : ℕ) (c : ActualIndex S N i) :
    (∑ p ∈ boxedPairs c r s, maskedBox S i hg hsupport H c p)
      = ∑ a ∈ localAssignmentResidues g S.k,
          ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
            (boxSum S i r s a h hg hsupport c).re := by
  classical
  unfold maskedBox
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  exact boxedPairs_sum_eq_boxSum S i r s a h hg hsupport c _ (fun _ _ => rfl)

/-- The complete outer identity for one coordinate and one Brun prime
subset: the actual finite nonzero Fourier partial over all enlarged
certificates is the dyadically partitioned weighted double-box sum. -/
theorem sum_certificates_partialRemainder_eq {B K N : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) {T : Finset ℕ}
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset)
    [NeZero (∏ q ∈ T, q)] (hg : Squarefree (∏ q ∈ T, q))
    (hsupport : ∀ q ∈ (∏ q ∈ T, q).primeFactors,
      max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (hX : 0 < SubpowerScale.X N S.k)
    (hwin : ∀ t ∈ ConvenientCertificateEnlargement.certificates S
        (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
        (SubpowerScale.medium N S.k) i,
      2*height N S.k < refinementModulus S*t.1.val.value*(∏ q ∈ T, q)) :
    (∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i,
      ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (height N S.k) T)
      = ∑ dl ∈ dyadicIndices (SubpowerScale.X N S.k),
          ∑ a ∈ localAssignmentResidues (∏ q ∈ T, q) S.k,
          ∑ h ∈ (IntegerFourierWindow.window (height N S.k)).erase 0,
            ∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
                (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i dl.1 dl.2.1 dl.2.2,
              (boxSum S i dl.2.1 dl.2.2 a h hg hsupport c).re := by
  classical
  calc
    (∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i,
      ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (height N S.k) T)
        = ∑ c ∈ (complementVectorsOf i (Certificates S (SubpowerScale.X N S.k)
              (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
              (SubpowerScale.medium N S.k) i)).attach,
            ∑ p ∈ (splitPairFibreOf i (Certificates S (SubpowerScale.X N S.k)
                (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
                (SubpowerScale.medium N S.k) i) c.val).attach,
              ConvenientPartialFourier.partialRemainder i (fibreCertificate p)
                (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
                (SubpowerScale.medium N S.k) (height N S.k) T :=
        sum_family_eq_sum_complements_splitPairs i _
          (fun t ht => ConvenientCertificateEnlargement.factor_eq ht) _
    _ = ∑ c ∈ (complementVectorsOf i (Certificates S (SubpowerScale.X N S.k)
            (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
            (SubpowerScale.medium N S.k) i)).attach,
          ∑ p ∈ splitPairDomain c,
            maskedBox S i hg hsupport (height N S.k) c p := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hfib := sum_fibre_partialRemainder_eq_complementMaskedPartial c hT hX
          (fun p => hwin _ (fibreCertificate_mem p)) (fun _ => (1 : ℝ))
        simp only [one_mul] at hfib
        rw [hfib]
        rw [Finset.sum_congr rfl
          (fun p _ => complementMaskedPartial_eq c p hT hg hsupport (height N S.k)),
          Finset.sum_attach, splitPairFibreOf_eq_splitPairDomain]
    _ = ∑ dl ∈ dyadicIndices (SubpowerScale.X N S.k),
          ∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
              (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i dl.1 dl.2.1 dl.2.2,
            ∑ p ∈ boxedPairs c dl.2.1 dl.2.2,
              maskedBox S i hg hsupport (height N S.k) c p :=
        sum_eq_sum_dyadic i (fun t => maskedBox S i hg hsupport (height N S.k) t.1 t.2)
    _ = _ := by
        refine Finset.sum_congr rfl fun dl _ => ?_
        rw [Finset.sum_congr rfl (fun c _ =>
          sum_maskedBox_boxedPairs S i hg hsupport (height N S.k) dl.2.1 dl.2.2 c)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]

/-- Two is a crude but sufficient replacement for `1/log 2`. -/
theorem natLog_succ_le (X : ℕ) (hX : 0 < X) :
    ((Nat.log 2 X : ℝ)+1) ≤ 2*(1+Real.log (X : ℝ)) := by
  have h1 : (2 : ℕ)^(Nat.log 2 X) ≤ X := Nat.pow_log_le_self 2 hX.ne'
  have h2 : ((2 : ℝ))^(Nat.log 2 X) ≤ (X : ℝ) := by exact_mod_cast h1
  have h3 : (Nat.log 2 X : ℝ)*Real.log 2 ≤ Real.log (X : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2
  have h4 : (1 : ℝ)/2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h5 : (0 : ℝ) ≤ (Nat.log 2 X : ℝ) := Nat.cast_nonneg _
  have h6 : (Nat.log 2 X : ℝ)*(1/2) ≤ (Nat.log 2 X : ℝ)*Real.log 2 :=
    mul_le_mul_of_nonneg_left h4.le h5
  linarith

/-- One dyadic box, one local residue and one nonzero frequency: the exact
separated envelope against a uniform first-moment bound. -/
theorem sum_norm_boxSum_le {B K N g : ℕ} (S : BPZSection6Input B K) (i : Fin S.k)
    (e r s a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (hB : 0 < B) (hindex : i.val ≤ SubpowerScale.X N S.k)
    (hmX : SubpowerScale.medium N S.k ≤ SubpowerScale.X N S.k)
    (hX : 0 < SubpowerScale.X N S.k) (hm : 0 < SubpowerScale.medium N S.k)
    (hh : h.natAbs ≤ height N S.k) (mu : ℝ)
    (hmoment : ∀ (rCut sCut : ActualIndex S N i → ℕ)
        (beta : ActualIndex S N i → ℕ → ℂ),
      (∀ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
        ∀ v ∈ variableBox g s (sCut c) c, ‖beta c v‖ ≤ 1) →
      firstMoment S N i e r s a h hg hsupport rCut sCut beta ≤ mu)
    (hmu : 0 ≤ mu) :
    (∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
      ‖boxSum S i r s a h hg hsupport c‖) ≤
      (Real.log 25+3)^2*(1+Real.log (SubpowerScale.X N S.k : ℝ))^2*
        ((128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
          2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)*mu) := by
  classical
  obtain ⟨rCut,sCut,hcut⟩ := ConvenientBoxEnvelope.exists_cuts_sum_norm_boxSum_le
    S i e r s a h hg hsupport hB hindex hmX (height N S.k) hh
  have hVnn : (0 : ℝ) ≤ 128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
      2097152*(height N S.k : ℝ)^2*(B : ℝ)^3 := by positivity
  have hstep : (∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
      ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
        ‖separatorCoefficient B (SubpowerScale.X N S.k)
            (SubpowerScale.medium N S.k) 0 alpha beta‖*
          ((128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
            2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)*
            firstMoment S N i e r s a h hg hsupport (rCut alpha beta) (sCut alpha beta)
              (fun _ v => separatorTwist (SubpowerScale.X N S.k)
                (SubpowerScale.medium N S.k) alpha beta v))) ≤
      ∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
      ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
        ‖separatorCoefficient B (SubpowerScale.X N S.k)
            (SubpowerScale.medium N S.k) 0 alpha beta‖*
          ((128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
            2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)*mu) := by
    refine Finset.sum_le_sum fun alpha _ => Finset.sum_le_sum fun beta _ => ?_
    refine mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hmoment _ _ _ ?_) hVnn) (norm_nonneg _)
    intro c _ v _
    exact le_of_eq (norm_separatorTwist _ _ _ _ _)
  refine (hcut.trans hstep).trans ?_
  have hfac : (∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
      ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
        ‖separatorCoefficient B (SubpowerScale.X N S.k)
            (SubpowerScale.medium N S.k) 0 alpha beta‖*
          ((128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
            2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)*mu)) =
      (∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
        ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
          ‖separatorCoefficient B (SubpowerScale.X N S.k)
              (SubpowerScale.medium N S.k) 0 alpha beta‖)*
        ((128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
          2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)*mu) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun alpha _ => (Finset.sum_mul _ _ _).symm
  rw [hfac]
  exact mul_le_mul_of_nonneg_right (sum_norm_separatorCoefficient_le hX hm hmX)
    (by positivity)

/-- One coordinate and one Brun prime subset: the actual finite nonzero
Fourier partial over all enlarged certificates is bounded by the dyadic,
local-residue and frequency multiplicities times the separated envelope. -/
theorem abs_sum_certificates_partialRemainder_le {B K N : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) {T : Finset ℕ}
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset)
    (hTcard : T.card ≤ 2*N)
    [NeZero (∏ q ∈ T, q)] (hg : Squarefree (∏ q ∈ T, q))
    (hsupport : ∀ q ∈ (∏ q ∈ T, q).primeFactors,
      max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (hB : 0 < B) (hkX : S.k ≤ SubpowerScale.X N S.k)
    (hmX : SubpowerScale.medium N S.k ≤ SubpowerScale.X N S.k)
    (hX : 0 < SubpowerScale.X N S.k) (hm : 0 < SubpowerScale.medium N S.k)
    (hwin : ∀ t ∈ ConvenientCertificateEnlargement.certificates S
        (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
        (SubpowerScale.medium N S.k) i,
      2*height N S.k < refinementModulus S*t.1.val.value*(∏ q ∈ T, q))
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hmoment : ∀ (e r s a : ℕ) (h : ℤ), h ≠ 0 → h.natAbs ≤ height N S.k →
      ∀ (rCut sCut : ActualIndex S N i → ℕ) (beta : ActualIndex S N i → ℕ → ℂ),
      (∀ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
        ∀ v ∈ variableBox (∏ q ∈ T, q) s (sCut c) c, ‖beta c v‖ ≤ 1) →
      firstMoment S N i e r s a h hg hsupport rCut sCut beta ≤ mu) :
    |∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i,
      ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (height N S.k) T| ≤
      ((Nat.log 2 (SubpowerScale.X N S.k) : ℝ)+1)^3*
        (((S.k : ℝ)^(2*N))*(2*(height N S.k : ℝ)))*
        ((Real.log 25+3)^2*(1+Real.log (SubpowerScale.X N S.k : ℝ))^2*
          ((128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
            2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)*mu)) := by
  classical
  have hk : 0 < S.k := by have := S.hk3; omega
  have hVnn : (0 : ℝ) ≤ 128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
      2097152*(height N S.k : ℝ)^2*(B : ℝ)^3 := by positivity
  set E : ℝ := (Real.log 25+3)^2*(1+Real.log (SubpowerScale.X N S.k : ℝ))^2*
    ((128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
      2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)*mu) with hE
  have hEnn : 0 ≤ E := by
    rw [hE]; positivity
  rw [sum_certificates_partialRemainder_eq S i hT hg hsupport hX hwin]
  have hfreq : ∀ dl : ℕ × (ℕ × ℕ), ∀ a : ℕ,
      ∀ h ∈ (IntegerFourierWindow.window (height N S.k)).erase 0,
      |∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i dl.1 dl.2.1 dl.2.2,
        (boxSum S i dl.2.1 dl.2.2 a h hg hsupport c).re| ≤ E := by
    intro dl a h hh
    have hne : h ≠ 0 := Finset.ne_of_mem_erase hh
    have hle : h.natAbs ≤ height N S.k := by
      have hmem := Finset.mem_of_mem_erase hh
      simp only [IntegerFourierWindow.window, Finset.mem_Icc] at hmem
      omega
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun c _ => Complex.abs_re_le_norm _).trans ?_
    exact sum_norm_boxSum_le S i dl.1 dl.2.1 dl.2.2 a h hg hsupport hB
      ((Nat.le_of_lt i.isLt).trans hkX) hmX hX hm hle mu
      (fun rCut sCut beta hbeta => hmoment _ _ _ _ _ hne hle rCut sCut beta hbeta) hmu
  have hres : ∀ dl : ℕ × (ℕ × ℕ), ∀ a : ℕ,
      |∑ h ∈ (IntegerFourierWindow.window (height N S.k)).erase 0,
        ∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
            (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i dl.1 dl.2.1 dl.2.2,
          (boxSum S i dl.2.1 dl.2.2 a h hg hsupport c).re| ≤
        (2*(height N S.k : ℝ))*E := by
    intro dl a
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun h hh => hfreq dl a h hh).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, MediumFrequencyBudget.card_nonzero_window]
    push_cast
    exact le_rfl
  have hdl : ∀ dl : ℕ × (ℕ × ℕ),
      |∑ a ∈ localAssignmentResidues (∏ q ∈ T, q) S.k,
        ∑ h ∈ (IntegerFourierWindow.window (height N S.k)).erase 0,
          ∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
              (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i dl.1 dl.2.1 dl.2.2,
            (boxSum S i dl.2.1 dl.2.2 a h hg hsupport c).re| ≤
        ((S.k : ℝ)^(2*N))*((2*(height N S.k : ℝ))*E) := by
    intro dl
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => hres dl a).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hlarge : ∀ p ∈ (∏ q ∈ T, q).primeFactors, S.k < p := by
      intro p hp
      have := (hsupport p hp).1
      omega
    have hTeq : (∏ q ∈ T, q).primeFactors.card ≤ 2*N := by
      have hprime : ∀ p ∈ T, p.Prime := fun p hp =>
        (MediumSieveEuler.mem_windowPrimes.mp (Finset.mem_powerset.mp hT hp)).1
      rw [Nat.primeFactors_prod hprime]
      exact hTcard
    have hcard : (localAssignmentResidues (∏ q ∈ T, q) S.k).card ≤ S.k^(2*N) := by
      rw [card_localAssignmentResidues hlarge]
      exact Nat.pow_le_pow_right hk hTeq
    calc ((localAssignmentResidues (∏ q ∈ T, q) S.k).card : ℝ)
        ≤ ((S.k^(2*N) : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (S.k : ℝ)^(2*N) := by push_cast; ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun dl _ => hdl dl).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, card_dyadicIndices]
  have hcast : (((Nat.log 2 (SubpowerScale.X N S.k)+1)^3 : ℕ) : ℝ)
      = ((Nat.log 2 (SubpowerScale.X N S.k) : ℝ)+1)^3 := by push_cast; ring
  rw [hcast]
  ring_nf
  exact le_rfl

/-- The truncated Brun coefficient is a sign or zero. -/
theorem abs_coefficient_le_one (L : ℕ) (T : Finset ℕ) :
    |MediumSignedMainTerm.coefficient L T| ≤ 1 := by
  unfold MediumSignedMainTerm.coefficient
  split_ifs with h
  · simp [abs_pow]
  · simp

theorem medium_le_X (N k : ℕ) : SubpowerScale.medium N k ≤ SubpowerScale.X N k := by
  have hbase : 1 ≤ SubpowerScale.base N k := Nat.one_le_pow _ _ (by norm_num)
  have hexp : BPZScale.mediumExp k ≤ BPZScale.xExp k := by
    show 202*3^k*k^100 ≤ 600*3^k*k^100
    gcongr
    norm_num
  show SubpowerScale.base N k ^ BPZScale.mediumExp k ≤
    SubpowerScale.base N k ^ BPZScale.xExp k
  exact Nat.pow_le_pow_right hbase hexp

theorem medium_pos (N k : ℕ) : 0 < SubpowerScale.medium N k := by
  show 0 < SubpowerScale.base N k ^ BPZScale.mediumExp k
  exact Nat.pow_pos (Nat.one_le_pow _ _ (by norm_num))

theorem one_le_z (N k : ℕ) : 1 ≤ SubpowerScale.z N k := Nat.one_le_pow _ _ (by norm_num)

set_option maxHeartbeats 4000000 in
set_option linter.style.haveILetI false in
set_option linter.unnecessarySeqFocus false in
/-- **The outer bound.** -/
theorem eventually_abs_totalPartialRemainder_div_sieveScale_lt {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      |ConvenientPartialFourier.totalPartialRemainder S N| / sieveScale S N < epsilon := by
  classical
  have hk : 0 < S.k := by have := S.hk3; omega
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hkR : (0 : ℝ) < S.k := by exact_mod_cast hk
  have hlog25 : (0 : ℝ) < Real.log 25+3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 25); linarith
  set Cst : ℝ := 32*(S.k : ℝ)*(128*(B : ℝ)+40960*(B : ℝ)^2+2097152*(B : ℝ)^3)*
    (Real.log 25+3)^2 with hCst
  have hCpos : 0 < Cst := by rw [hCst]; positivity
  filter_upwards [ConvenientPartialFourier.eventually_certificate_window S hB,
    eventually_actual_normalized_small S hB Cst hCpos.le 3 2 0 0 5 1
      (show (0 : ℝ) < epsilon/2 by linarith),
    SubpowerScale.eventually_const_le_X hk S.k,
    SubpowerScale.eventually_const_le_z hk S.k] with N hwin hmom hkX hkz
  have hX : 0 < SubpowerScale.X N S.k := SubpowerScale.X_pos N S.k
  have hXR : (1 : ℝ) ≤ SubpowerScale.X N S.k := by exact_mod_cast hX
  have hlogX : (0 : ℝ) ≤ Real.log (SubpowerScale.X N S.k : ℝ) := Real.log_nonneg hXR
  have hmX := medium_le_X N S.k
  have hm := medium_pos N S.k
  have hz1 := one_le_z N S.k
  have hH1 : 1 ≤ height N S.k := height_pos N S.k
  have hHR : (1 : ℝ) ≤ (height N S.k : ℝ) := by exact_mod_cast hH1
  have hss : 0 < sieveScale S N := sieveScale_pos S N
  -- the fixed polynomial loss budget
  have hlossEq : ((MediumOscillatoryDecay.loss 3 2 0 0 N S.k : ℕ) : ℝ)
      = (height N S.k : ℝ)^3*(SubpowerScale.z N S.k : ℝ)^(4*N) := by
    simp only [MediumOscillatoryDecay.loss, Nat.zero_mul, pow_zero, mul_one,
      Nat.cast_mul, Nat.cast_pow]
  set Lam : ℝ := outsideLoss Cst 3 2 0 0 5 1 N S.k with hLamDef
  have hLamEq : Lam = Cst*((height N S.k : ℝ)^3*(SubpowerScale.z N S.k : ℝ)^(4*N))*
      ((N : ℝ)+1)^1*(1+Real.log (SubpowerScale.X N S.k : ℝ))^5 := by
    rw [hLamDef, outsideLoss, hlossEq]
  have hzR : (1 : ℝ) ≤ (SubpowerScale.z N S.k : ℝ) := by exact_mod_cast hz1
  have hLampos : 0 < Lam := by
    rw [hLamEq]
    have h1 : (0 : ℝ) < (height N S.k : ℝ)^3 := by positivity
    have h2 : (0 : ℝ) < (SubpowerScale.z N S.k : ℝ)^(4*N) := by positivity
    have h3 : (0 : ℝ) < (1+Real.log (SubpowerScale.X N S.k : ℝ))^5 := by positivity
    have h4 : (0 : ℝ) < ((N : ℝ)+1)^1 := by positivity
    positivity
  set mu : ℝ := epsilon/2*sieveScale S N/Lam with hmuDef
  have hmunn : 0 ≤ mu := by rw [hmuDef]; positivity
  -- one coordinate, one truncated Brun subset
  have hterm : ∀ i : Fin S.k,
      ∀ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
      T.card ≤ 2*N →
      |∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
          (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i,
        ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (height N S.k) T| ≤
        ((Nat.log 2 (SubpowerScale.X N S.k) : ℝ)+1)^3*
          (((S.k : ℝ)^(2*N))*(2*(height N S.k : ℝ)))*
          ((Real.log 25+3)^2*(1+Real.log (SubpowerScale.X N S.k : ℝ))^2*
            ((128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
              2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)*mu)) := by
    intro i T hT hTcard
    have hg := (ConvenientFourierTail.windowProduct_data hk hT).1
    have hsupport := (ConvenientFourierTail.windowProduct_data hk hT).2
    haveI : NeZero (∏ q ∈ T, q) := ⟨hg.ne_zero⟩
    have hgpos : 0 < ∏ q ∈ T, q := Nat.pos_of_ne_zero hg.ne_zero
    have hgle : (∏ q ∈ T, q) ≤ SubpowerScale.z N S.k^(2*N) := by
      calc (∏ q ∈ T, q) ≤ ∏ _q ∈ T, SubpowerScale.z N S.k :=
            Finset.prod_le_prod (fun p _ => Nat.zero_le _)
              (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp
                (Finset.mem_powerset.mp hT hp)).2.2.le)
        _ = SubpowerScale.z N S.k^T.card := by simp
        _ ≤ _ := Nat.pow_le_pow_right hz1 hTcard
    refine abs_sum_certificates_partialRemainder_le S i hT hTcard hg hsupport hB hkX
      hmX hX hm (fun t ht => hwin i t ht _ hgpos) mu hmunn ?_
    intro e r s a h hne hle rCut sCut beta hbeta
    have hlt := hmom (∏ q ∈ T, q) hg hsupport hgle i e r s a h hne hle rCut sCut beta hbeta
    have hss' : (SubpowerScale.X N S.k : ℝ)*
        MediumMainTermDecay.refinedDensity S (SubpowerScale.z N S.k)/
        (refinementModulus S : ℝ) = sieveScale S N := rfl
    rw [hss'] at hlt
    have h2 := (div_lt_iff₀ hss).mp hlt
    rw [hmuDef, le_div_iff₀ hLampos]
    calc firstMoment S N i e r s a h hg hsupport rCut sCut beta*Lam
        = Lam*firstMoment S N i e r s a h hg hsupport rCut sCut beta := mul_comm _ _
      _ ≤ epsilon/2*sieveScale S N := h2.le
  -- sum over the truncated Brun subsets
  have hPz : MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k) ⊆
      Finset.range (SubpowerScale.z N S.k) := fun p hp =>
    Finset.mem_range.mpr (MediumSieveEuler.mem_windowPrimes.mp hp).2.2
  set Bd : ℝ := ((Nat.log 2 (SubpowerScale.X N S.k) : ℝ)+1)^3*
    (((S.k : ℝ)^(2*N))*(2*(height N S.k : ℝ)))*
    ((Real.log 25+3)^2*(1+Real.log (SubpowerScale.X N S.k : ℝ))^2*
      ((128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
        2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)*mu)) with hBdDef
  have hBdnn : 0 ≤ Bd := by rw [hBdDef]; positivity
  have hinner : ∀ i : Fin S.k,
      |∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
          (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i,
        ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
          MediumSignedMainTerm.coefficient (2*N) T*
            ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
              (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (height N S.k) T| ≤
        ((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N))*Bd := by
    intro i
    have hcomm : (∑ t ∈ ConvenientCertificateEnlargement.certificates S
          (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
          (SubpowerScale.medium N S.k) i,
        ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
          MediumSignedMainTerm.coefficient (2*N) T*
            ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
              (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (height N S.k) T) =
        ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
          MediumSignedMainTerm.coefficient (2*N) T*
            ∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
              (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
              (SubpowerScale.medium N S.k) i,
            ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
              (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (height N S.k) T := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun T _ => by rw [Finset.mul_sum]
    rw [hcomm]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hzero : ∀ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
        T ∉ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset.filter
          (fun T => T.card ≤ 2*N) →
        |MediumSignedMainTerm.coefficient (2*N) T*
          ∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
            (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
            (SubpowerScale.medium N S.k) i,
          ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
            (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (height N S.k) T| = 0 := by
      intro T hTmem hnot
      have hTc : ¬ T.card ≤ 2*N := fun hc => hnot (Finset.mem_filter.mpr ⟨hTmem,hc⟩)
      simp [MediumSignedMainTerm.coefficient, hTc]
    rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero]
    calc
      _ ≤ ∑ _T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset.filter
            (fun T => T.card ≤ 2*N), Bd := by
          refine Finset.sum_le_sum fun T hTf => ?_
          obtain ⟨hTP,hTL⟩ := Finset.mem_filter.mp hTf
          rw [abs_mul]
          calc |MediumSignedMainTerm.coefficient (2*N) T| * |∑ t ∈ _, _|
              ≤ 1*|∑ t ∈ ConvenientCertificateEnlargement.certificates S
                  (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
                  (SubpowerScale.medium N S.k) i,
                ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
                  (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
                  (height N S.k) T| :=
                mul_le_mul_of_nonneg_right (abs_coefficient_le_one _ _) (abs_nonneg _)
            _ = _ := one_mul _
            _ ≤ Bd := hterm i T hTP hTL
      _ = ((((MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset.filter
            (fun T => T.card ≤ 2*N)).card : ℝ))*Bd := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N))*Bd := by
          refine mul_le_mul_of_nonneg_right ?_ hBdnn
          have hc := MediumEndpointError.card_truncated_powerset_le (L := 2*N) hPz hz1
          have hcast : ((((MediumSieveEuler.windowPrimes S.k
              (SubpowerScale.z N S.k)).powerset.filter
              (fun T => T.card ≤ 2*N)).card : ℝ)) ≤
              (((2*N+1)*SubpowerScale.z N S.k^(2*N) : ℕ) : ℝ) := by exact_mod_cast hc
          refine hcast.trans ?_
          push_cast
          ring_nf
          exact le_rfl
  -- the loss budget
  have hbudget : (S.k : ℝ)*(((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N))*
      (((Nat.log 2 (SubpowerScale.X N S.k) : ℝ)+1)^3*
        (((S.k : ℝ)^(2*N))*(2*(height N S.k : ℝ)))*
        ((Real.log 25+3)^2*(1+Real.log (SubpowerScale.X N S.k : ℝ))^2*
          (128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
            2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)))) ≤ Lam := by
    have e1 : (2*(N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by linarith
    have e2 : ((Nat.log 2 (SubpowerScale.X N S.k) : ℝ)+1)^3 ≤
        8*(1+Real.log (SubpowerScale.X N S.k : ℝ))^3 := by
      have h := natLog_succ_le _ hX
      calc ((Nat.log 2 (SubpowerScale.X N S.k) : ℝ)+1)^3
          ≤ (2*(1+Real.log (SubpowerScale.X N S.k : ℝ)))^3 :=
            pow_le_pow_left₀ (by positivity) h 3
        _ = 8*(1+Real.log (SubpowerScale.X N S.k : ℝ))^3 := by ring
    have e3 : (S.k : ℝ) ≤ (SubpowerScale.z N S.k : ℝ) := by exact_mod_cast hkz
    have e4 : (128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
        2097152*(height N S.k : ℝ)^2*(B : ℝ)^3) ≤
        (128*(B : ℝ)+40960*(B : ℝ)^2+2097152*(B : ℝ)^3)*(height N S.k : ℝ)^2 := by
      have hH2 : (1 : ℝ) ≤ (height N S.k : ℝ)^2 := by nlinarith
      have hHle : (height N S.k : ℝ) ≤ (height N S.k : ℝ)^2 := by nlinarith
      have t1 : 128*(B : ℝ) ≤ 128*(B : ℝ)*(height N S.k : ℝ)^2 := by
        nlinarith [hBR.le, hH2]
      have t2 : 40960*(height N S.k : ℝ)*(B : ℝ)^2 ≤
          40960*(B : ℝ)^2*(height N S.k : ℝ)^2 := by
        nlinarith [sq_nonneg (B : ℝ), hHle]
      have t3 : (128*(B : ℝ)+40960*(B : ℝ)^2+2097152*(B : ℝ)^3)*(height N S.k : ℝ)^2 =
          128*(B : ℝ)*(height N S.k : ℝ)^2+40960*(B : ℝ)^2*(height N S.k : ℝ)^2+
            2097152*(B : ℝ)^3*(height N S.k : ℝ)^2 := by ring
      have t4 : 2097152*(height N S.k : ℝ)^2*(B : ℝ)^3 =
          2097152*(B : ℝ)^3*(height N S.k : ℝ)^2 := by ring
      linarith
    calc
      _ ≤ (S.k : ℝ)*((2*((N : ℝ)+1))*(SubpowerScale.z N S.k : ℝ)^(2*N)*
            ((8*(1+Real.log (SubpowerScale.X N S.k : ℝ))^3)*
              (((SubpowerScale.z N S.k : ℝ)^(2*N))*(2*(height N S.k : ℝ)))*
              ((Real.log 25+3)^2*(1+Real.log (SubpowerScale.X N S.k : ℝ))^2*
                ((128*(B : ℝ)+40960*(B : ℝ)^2+2097152*(B : ℝ)^3)*
                  (height N S.k : ℝ)^2)))) := by
          gcongr
      _ = Lam := by
          rw [hLamEq, hCst]
          ring
  -- assemble
  have htotal : |ConvenientPartialFourier.totalPartialRemainder S N| ≤
      epsilon/2*sieveScale S N := by
    have hchain : |ConvenientPartialFourier.totalPartialRemainder S N| ≤
        (S.k : ℝ)*(((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N))*Bd) := by
      calc |ConvenientPartialFourier.totalPartialRemainder S N|
          ≤ ∑ i : Fin S.k,
            |∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
                (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
                (SubpowerScale.medium N S.k) i,
              ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
                MediumSignedMainTerm.coefficient (2*N) T*
                  ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k)
                    (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
                    (height N S.k) T| := by
            rw [ConvenientPartialFourier.totalPartialRemainder]
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin S.k, ((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N))*Bd :=
            Finset.sum_le_sum fun i _ => hinner i
        _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine hchain.trans ?_
    have hfactor : (S.k : ℝ)*(((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N))*Bd) =
        ((S.k : ℝ)*(((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N))*
          (((Nat.log 2 (SubpowerScale.X N S.k) : ℝ)+1)^3*
            (((S.k : ℝ)^(2*N))*(2*(height N S.k : ℝ)))*
            ((Real.log 25+3)^2*(1+Real.log (SubpowerScale.X N S.k : ℝ))^2*
              (128*(B : ℝ)+40960*(height N S.k : ℝ)*(B : ℝ)^2+
                2097152*(height N S.k : ℝ)^2*(B : ℝ)^3)))))*mu := by
      rw [hBdDef]; ring
    rw [hfactor]
    refine (mul_le_mul_of_nonneg_right hbudget hmunn).trans ?_
    rw [hmuDef]
    field_simp
    norm_num
  rw [div_lt_iff₀ hss]
  calc |ConvenientPartialFourier.totalPartialRemainder S N|
      ≤ epsilon/2*sieveScale S N := htotal
    _ < epsilon*sieveScale S N := by
        have : (0 : ℝ) < sieveScale S N := hss
        nlinarith

end Erdos387Proof.ConvenientOuterPartial
