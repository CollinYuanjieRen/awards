import Erdos387Proof.MediumFibreFourier
import Erdos387Proof.MediumOuterSummation

/-! Apply the completion shape to every actual gcd block, retaining the
full varying-factor interval before taking its norm. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumFibreBound

open Erdos387 Erdos387.CoverBPZ MediumCertificateCover MediumFactorWindow
open MediumFibreFourier MediumFourierReduction MediumOuterSummation
open MediumCompletionShape MediumFrequencyBudget IntegerSieveResidues
open MediumComplementFourier MediumWeightedPhase
open scoped BigOperators

def gcdBlockLength (B X D medium large u : ℕ) : ℕ :=
  upper X D large / u - lower B X D medium / u

noncomputable def gcdBlockMajorant
    (B X M D v u medium large H : ℕ) (h : ℤ) : ℝ :=
  (8 * ((6 * (B : ℝ)) / (M * v : ℕ)) +
      128 * H * ((6 * (B : ℝ)) / (M * v : ℕ))^2) *
    ((((gcdBlockLength B X D medium large u) / (M * (D * v)) + 1 : ℕ) : ℝ) *
      ((Real.log (M * (D * v) : ℕ) + 1) *
        ((4 : ℝ) ^ (D * v).primeFactors.card *
          Real.sqrt (D * v : ℝ) * Real.sqrt (v * h.natAbs : ℝ) * M)))

set_option linter.style.haveILetI false in
theorem norm_gcdFourierBlock_le
    {B K X z medium large H : ℕ}
    {S : BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X} {T : Finset ℕ}
    (hB : 0 < B) (hX : 0 < X) (hm : 0 < medium)
    (hz : 2 * S.k ≤ z) (hkX : S.k ≤ X)
    (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset)
    {u : ℕ} (huMem : u ∈ (∏ p ∈ T, p).divisors) :
    ‖gcdFourierBlock (H := H) hC hT u‖ ≤
      ∑ _a ∈ localAssignmentResidues ((∏ p ∈ T, p) / u) S.k,
        ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
          gcdBlockMajorant B X (refinementModulus S)
            (C.val.otherValue i) ((∏ p ∈ T, p) / u) u medium large H h := by
  classical
  let g := ∏ p ∈ T, p
  let v := g / u
  let M := refinementModulus S
  let D := C.val.otherValue i
  have hgSq : Squarefree g := MediumSignedMainTerm.primeSubsetProduct_squarefree
    (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
    (Finset.mem_powerset.mp hT)
  have hudvd : u ∣ g := Nat.dvd_of_mem_divisors huMem
  have hu0 : 0 < u := Nat.pos_of_mem_divisors huMem
  have hguv : g = u * v := (Nat.mul_div_cancel' hudvd).symm
  have hv0 : 0 < v := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hgSq.ne_zero) hudvd) hu0
  letI : NeZero u := ⟨hu0.ne'⟩
  letI : NeZero v := ⟨hv0.ne'⟩
  have hprime : ∀ p ∈ T, p.Prime := fun p hp =>
    (MediumSieveEuler.mem_windowPrimes.mp (Finset.mem_powerset.mp hT hp)).1
  have hsupport : ∀ p ∈ g.primeFactors, max (2 * S.k) 3 ≤ p ∧ p < z := by
    intro p hp
    rw [Nat.primeFactors_prod hprime] at hp
    obtain ⟨_, hp4, hpz⟩ := MediumSieveEuler.mem_windowPrimes.mp (Finset.mem_powerset.mp hT hp)
    have hk3 := S.hk3
    exact ⟨by omega, hpz⟩
  obtain ⟨hsq, hMdv, huDv, hlarge⟩ :=
    MediumReciprocalPhase.certificate_split_applicability hC hz hgSq hguv hsupport
  have hgcop : Nat.Coprime g (M * D) :=
    MediumComplementBounds.window_product_coprime_complement hC hT
  have huv : Nat.Coprime u v := by
    apply Nat.coprime_of_squarefree_mul
    rw [← hguv]
    exact hgSq
  have huQ : Nat.Coprime u (M * (D * v)) := by
    have huMD := hgcop.of_dvd_left hudvd
    simpa only [Nat.mul_assoc] using huMD.mul_right huv
  letI : NeZero M := ⟨(refinementModulus_pos S).ne'⟩
  letI : NeZero (D * v) := ⟨(Nat.mul_pos (C.val.otherValue_pos i) hv0).ne'⟩
  have hDv : Nat.Coprime (M * D) v :=
    (hgcop.of_dvd_left (Nat.div_dvd_of_dvd hudvd)).symm
  have hkz : S.k ≤ z := by omega
  have hi : |-(i.val : ℤ)| ≤ (X : ℤ) := by
    simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg i.val)]
    exact_mod_cast i.isLt.le.trans hkX
  simp only [gcdFourierBlock, dif_pos huMem]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro h hh
  have hhmem := Finset.mem_erase.mp hh
  have hhZ : |h| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hhmem.2)
  have hhR : |(h : ℝ)| ≤ (H : ℝ) := by exact_mod_cast hhZ
  have hdelta := MediumReciprocalPhase.gcd_combinedResidue_sub_index_eq_one (a := a) hC hkz hDv
  simpa only [gcdBlockMajorant, gcdBlockLength, M, D, g, v] using
    norm_sum_maskedFourierSummand_le_gcd B X M D v u medium hB hX
      (C.val.otherValue_pos i) (refinementModulus_pos S) hv0 hm hMdv hsq hlarge huQ
      (combinedResidue C i v a hDv) i.val h hhmem.1 hdelta
      (H : ℝ) (by positivity) hhR hi (upper X D large / u - lower B X D medium / u)

theorem blockLength_mul_other_le {B X D medium large u : ℕ} :
    gcdBlockLength B X D medium large u * D ≤ X := by
  have hlen : gcdBlockLength B X D medium large u ≤ X / D :=
    (Nat.sub_le _ _).trans ((Nat.div_le_self _ _).trans (min_le_right _ _))
  exact (Nat.mul_le_mul_right D hlen).trans (Nat.div_mul_le_self X D)

theorem gcdBlockMajorant_le {B K X z medium large H L W : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {C : RefinedTupleCertificate S X}
    {T : Finset ℕ} (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset)
    (hTL : T.card ≤ L) (hz : 1 ≤ z) (hH : 1 ≤ H)
    (hW : (C.val.otherValue i).primeFactors.card ≤ W)
    {u : ℕ} (hu : u ∈ (∏ p ∈ T, p).divisors)
    {h : ℤ} (hh : h ∈ (IntegerFourierWindow.window H).erase 0) :
    gcdBlockMajorant B X (refinementModulus S) (C.val.otherValue i)
      ((∏ p ∈ T, p) / u) u medium large H h ≤
        coefficient B (refinementModulus S) X z L W H * shape X (C.val.otherValue i) := by
  classical
  let g := ∏ p ∈ T, p
  let v := g / u
  have hp : ∀ p ∈ T, p.Prime := fun p hp =>
    (MediumSieveEuler.mem_windowPrimes.mp (Finset.mem_powerset.mp hT hp)).1
  have hg : 0 < g := Finset.prod_pos (fun p hpT => (hp p hpT).pos)
  have hudvd : u ∣ g := Nat.dvd_of_mem_divisors hu
  have hvdvd : v ∣ g := Nat.div_dvd_of_dvd hudvd
  have hv : 0 < v := Nat.div_pos (Nat.le_of_dvd hg hudvd) (Nat.pos_of_mem_divisors hu)
  have hvg : v ≤ g := Nat.div_le_self _ _
  have hgG : g ≤ z^L := by
    calc
      _ ≤ ∏ _p ∈ T, z := Finset.prod_le_prod (fun p hp => Nat.zero_le _)
        (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp (Finset.mem_powerset.mp hT hp)).2.2.le)
      _ = z^T.card := by simp
      _ ≤ z^L := Nat.pow_le_pow_right hz hTL
  have hvW : v.primeFactors.card ≤ L := by
    apply (Finset.card_le_card (Nat.primeFactors_mono hvdvd hg.ne')).trans
    simpa only [g, Nat.primeFactors_prod hp] using hTL
  have hD := C.val.otherValue_pos i
  have hDvW : (C.val.otherValue i * v).primeFactors.card ≤ W+L := by
    rw [Nat.primeFactors_mul hD.ne' hv.ne']
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hW hvW)
  have hhZ : |h| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp (Finset.mem_erase.mp hh).2)
  have hhN : h.natAbs ≤ H := by
    exact_mod_cast (show (h.natAbs : ℤ) ≤ H by simpa only [Int.natCast_natAbs] using hhZ)
  simpa only [gcdBlockMajorant, coefficient, Nat.cast_pow] using
    weighted_completion_le (B := B) (G := z^L) (W := W) (depth := L)
    (length := gcdBlockLength B X (C.val.otherValue i) medium large u)
    (refinementModulus_pos S) hD hv
    (MediumComplementBounds.otherValue_le_X hC) (hvg.trans hgG) hH hhN
    hDvW blockLength_mul_other_le

theorem abs_sum_partialRemainder_le {B K X z medium large H L W : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {C : RefinedTupleCertificate S X}
    {T : Finset ℕ}
    (hB : 0 < B) (hX : 0 < X) (hm : 0 < medium)
    (hz : 2*S.k ≤ z) (hkX : S.k ≤ X) (hH : 1 ≤ H) (hHX : 4*B*H ≤ X)
    (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset)
    (hTL : T.card ≤ L) (hW : (C.val.otherValue i).primeFactors.card ≤ W) :
    |∑ d ∈ factors B X (C.val.otherValue i) (refinementModulus S) medium large,
      partialRemainder (fromFactor C i medium large d) i z medium large H T| ≤
      (splitFrequencyCount (∏ p ∈ T, p) S.k H : ℝ) *
        coefficient B (refinementModulus S) X z L W H * shape X (C.val.otherValue i) := by
  classical
  have hz1 : 1 ≤ z := by have := S.hk3; omega
  rw [sum_partialRemainder_eq_re_gcdFourierBlocks hB hX hHX hC hT]
  calc
    _ ≤ ∑ u ∈ (∏ p ∈ T, p).divisors, |(gcdFourierBlock (H := H) hC hT u).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ (∏ p ∈ T, p).divisors,
        ∑ a ∈ localAssignmentResidues ((∏ p ∈ T, p)/u) S.k,
          ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
            gcdBlockMajorant B X (refinementModulus S) (C.val.otherValue i)
              ((∏ p ∈ T, p)/u) u medium large H h := by
      apply Finset.sum_le_sum
      intro u hu
      exact (Complex.abs_re_le_norm _).trans
        (norm_gcdFourierBlock_le hB hX hm hz hkX hC hT hu)
    _ ≤ ∑ u ∈ (∏ p ∈ T, p).divisors,
        ∑ _a ∈ localAssignmentResidues ((∏ p ∈ T, p)/u) S.k,
          ∑ _h ∈ (IntegerFourierWindow.window H).erase 0,
            coefficient B (refinementModulus S) X z L W H * shape X (C.val.otherValue i) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum (fun h hh => gcdBlockMajorant_le hC hT hTL hz1 hH hW hu hh)
    _ = _ := by
      simp only [splitFrequencyCount, Nat.cast_sum, Nat.cast_mul,
        Finset.sum_const, nsmul_eq_mul, Finset.sum_mul, mul_assoc]

end Erdos387Proof.MediumFibreBound
