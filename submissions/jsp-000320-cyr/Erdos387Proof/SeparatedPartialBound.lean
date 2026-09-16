import Erdos387Proof.SeparatedFibreBound
import Erdos387Proof.SeparatedPartialFourier
import Erdos387Proof.MediumFrequencyBudget

/-! Bound the actual certificate partial sum after grouping by full
complement, retained factor and dyadic block. The original local residues
and common nonzero frequency window are kept explicitly. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedPartialBound
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open SeparatedCertificateEnlargement SeparatedPrimeFibre SeparatedRetainedResidue
open SeparatedFibreBound ConvenientPartialFourier MediumPartialFourier
open scoped BigOperators

theorem partialRemainder_eq_actual {B K X z y medium second gap H : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {a : SplitCertificate S X} {T : Finset ℕ}
    (ha : a∈certificates S X z y medium second gap i)
    (hT : T∈(MediumSieveEuler.windowPrimes S.k z).powerset)
    (hX : 0<X) (hHq : 2*H<refinementModulus S*a.1.val.value*(∏ p∈T,p)) :
    let hd := ConvenientFourierTail.windowProduct_data (by have := S.hk3; omega) hT
    ConvenientPartialFourier.partialRemainder i a z 0 medium H T =
      ∑ b∈localAssignmentResidues (∏ p∈T,p) S.k,
        ∑ h∈(IntegerFourierWindow.window H).erase 0,
          (actualTerm ha hd.1 hd.2 b h).re := by
  classical
  have hk : 0<S.k := by have := S.hk3; omega
  have hd := ConvenientFourierTail.windowProduct_data hk hT
  let : NeZero (∏ p∈T,p) := ⟨hd.1.ne_zero⟩
  rw [ConvenientPartialFourier.partialRemainder_eq_nonzeroPartial
    (mem_generic_split_enlargement ha) hT hX hHq]
  unfold certificateNonzeroPartial nonzeroPartial actualTerm
  simp only [Complex.re_sum]

theorem abs_sum_certificate_partial_le
    {B K X z t medium H : ℕ} {S : BPZSection6Input B K} (i : Fin S.k)
    {T : Finset ℕ} (hT : T∈(MediumSieveEuler.windowPrimes S.k z).powerset)
    (hB : 0<B) (hX : 0<X) (hkX : S.k≤X)
    (hz : 2*S.k≤z) (hzy : z≤BPZScale.y t S.k)
    (ht : 6*2^S.k≤t) (hgt : (∏ p∈T,p)≤t) (hM : refinementModulus S≤t)
    (hH : 2≤H) (hHt : H^2≤t)
    (hwindow : ∀ a∈certificates S X z (BPZScale.y t S.k) medium
        (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) i,
      2*H<refinementModulus S*a.1.val.value*(∏ p∈T,p)) :
    |∑ a∈certificates S X z (BPZScale.y t S.k) medium
        (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) i,
      ConvenientPartialFourier.partialRemainder i a z 0 medium H T| ≤
      ((localAssignmentResidues (∏ p∈T,p) S.k).card*(2*H) : ℕ)*
        ∑ c∈(keys S X z (BPZScale.y t S.k) medium
          (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) i).attach,
          envelope B S.k t H (blockUpper (representative c).2.2) := by
  classical
  let A := certificates S X z (BPZScale.y t S.k) medium
    (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) i
  let J := keys S X z (BPZScale.y t S.k) medium
    (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) i
  let g := ∏ p∈T,p
  have hk : 0<S.k := by have := S.hk3; omega
  have hd := ConvenientFourierTail.windowProduct_data hk hT
  let F : SplitCertificate S X → ℕ → ℤ → ℂ := fun a b h =>
    if ha : a∈A then actualTerm ha hd.1 hd.2 b h else 0
  let E : ℝ := ∑ c∈J.attach,envelope B S.k t H (blockUpper (representative c).2.2)
  have hper (b : ℕ) (hb : b∈localAssignmentResidues g S.k)
      (h : ℤ) (hh : h∈(IntegerFourierWindow.window H).erase 0) :
      ‖∑ a∈A,F a b h‖≤E := by
    rw [sum_certificates_eq_fibres]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c hc
    have hcA := representative_mem c
    have heq : (∑ a∈fibre (z:=z) (y:=BPZScale.y t S.k) (medium:=medium)
          (second:=BPZScale.secondMin t S.k) (gap:=BPZScale.gap t S.k) (i:=i)
          (representative c),F a b h) =
        ∑ a∈(fibre (z:=z) (y:=BPZScale.y t S.k) (medium:=medium)
          (second:=BPZScale.secondMin t S.k) (gap:=BPZScale.gap t S.k) (i:=i)
          (representative c)).attach,actualTerm (Finset.mem_filter.mp a.property).1 hd.1 hd.2 b h := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro a ha
      exact dif_pos (Finset.mem_filter.mp a.property).1
    rw [heq]
    have hhmem := Finset.mem_erase.mp hh
    have habs : h.natAbs≤H := by
      have hIcc := Finset.mem_Icc.mp hhmem.2
      omega
    exact norm_sum_actualTerm_le (representative c) hcA hB hX (i.isLt.le.trans hkX)
      hz hzy ht hd.1 hgt hM hd.2 hH hHt b
      ((ConstrainedSieveResidues.mem_localAssignmentResidues_iff hd.1).mp hb).1 h hhmem.1 habs
  have heq : (∑ a∈A,ConvenientPartialFourier.partialRemainder i a z 0 medium H T)=
      (∑ b∈localAssignmentResidues g S.k,
        ∑ h∈(IntegerFourierWindow.window H).erase 0,∑ a∈A,F a b h).re := by
    simp only [Complex.re_sum]
    have hswap : (∑ b∈localAssignmentResidues g S.k,
        ∑ h∈(IntegerFourierWindow.window H).erase 0,∑ a∈A,(F a b h).re) =
        ∑ a∈A,∑ b∈localAssignmentResidues g S.k,
          ∑ h∈(IntegerFourierWindow.window H).erase 0,(F a b h).re := by
      calc (∑ b∈localAssignmentResidues g S.k,
            ∑ h∈(IntegerFourierWindow.window H).erase 0,∑ a∈A,(F a b h).re)
          = ∑ b∈localAssignmentResidues g S.k,
            ∑ a∈A,∑ h∈(IntegerFourierWindow.window H).erase 0,(F a b h).re :=
            Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    rw [hswap]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [F,dif_pos ha]
    exact partialRemainder_eq_actual ha hT hX (hwindow a ha)
  rw [heq]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b∈localAssignmentResidues g S.k,
        ∑ _h∈(IntegerFourierWindow.window H).erase 0,E := by
      apply Finset.sum_le_sum
      intro b hb
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun h hh => hper b hb h hh)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,MediumFrequencyBudget.card_nonzero_window,Nat.cast_mul]
      ring

end Erdos387Proof.SeparatedPartialBound
