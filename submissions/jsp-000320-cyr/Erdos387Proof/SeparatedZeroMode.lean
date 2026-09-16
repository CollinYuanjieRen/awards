import Erdos387Proof.SeparatedMainMass
import Erdos387Proof.ConvenientZeroMode

/-! Exact signed recombination of separated-error zero modes on the actual
nonnegative enlargement, with no dyadic partition loss. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedZeroMode
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open ConvenientZeroMode (certificateZero sum_certificateZero_eq_plainBrun)
open ConvenientMainDecay MediumSignedMainTerm SeparatedMainMass
open scoped BigOperators

noncomputable def totalZeroMass {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium second gap L : ℕ) : ℝ :=
  ∑ i : Fin S.k, ∑ t ∈ SeparatedCertificateEnlargement.certificates S X z y medium second gap i,
    ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
      coefficient L T*certificateZero t (∏ p ∈ T,p)

theorem totalZeroMass_eq {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium second gap L : ℕ) :
    totalZeroMass S X z y medium second gap L =
      ((3*(X : ℝ)+1)/refinementModulus S)*
        brunSubsetSum (MediumSieveEuler.windowPrimes S.k z) (plainAlpha S.k) L *
        ∑ i : Fin S.k, ∑ t ∈ SeparatedCertificateEnlargement.certificates S X z y medium second gap i,
          (1 : ℝ)/t.1.val.value := by
  unfold totalZeroMass
  simp_rw [sum_certificateZero_eq_plainBrun _ _ _
    (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem totalZeroMass_nonneg {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium second gap : ℕ) {L : ℕ} (hL : Even L) : 0 ≤ totalZeroMass S X z y medium second gap L := by
  rw [totalZeroMass_eq]
  have hb := plainBrun_nonneg S.k z hL
  positivity

theorem totalZeroMass_le {B K X z y medium second gap L : ℕ} (S : BPZSection6Input B K)
    {C : ℝ} {N : ℕ} (hC : 0<C)
    (hcheb : ∀ t : ℕ, N≤t → (Nat.primeCounting t : ℝ)≤C*t/Real.log t)
    (hzN : N≤z) (hz : 2≤z) (hB : 0<B) (hX : 0<X) (hL : Even L) :
    totalZeroMass S X z y medium second gap L ≤
      (24*B*C*S.k)*((X : ℝ)/refinementModulus S)*
        brunSubsetSum (MediumSieveEuler.windowPrimes S.k z) (plainAlpha S.k) L *
        (roughReciprocalMass z X^(S.k+1)/Real.log z) := by
  have hlog : 0<Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1<z by omega))
  have hbr := plainBrun_nonneg S.k z hL
  have hsum : (∑ i : Fin S.k, ∑ t ∈ SeparatedCertificateEnlargement.certificates S X z y medium second gap i,
      (1 : ℝ)/t.1.val.value) ≤
      S.k*((6*B*C/Real.log z)*roughReciprocalMass z X^(S.k+1)) := by
    calc
      _ ≤ ∑ _i : Fin S.k, (6*B*C/Real.log z)*roughReciprocalMass z X^(S.k+1) :=
        Finset.sum_le_sum (fun i _ => sum_certificates_reciprocal_le S i hC hcheb hzN hz hB)
      _ = _ := by simp
  have hmass : (3*(X : ℝ)+1)/refinementModulus S ≤ (4*(X : ℝ))/refinementModulus S := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hXR : (1 : ℝ)≤X := by exact_mod_cast hX
    linarith
  rw [totalZeroMass_eq]
  calc
    _ ≤ ((4*(X : ℝ))/refinementModulus S)*
        brunSubsetSum (MediumSieveEuler.windowPrimes S.k z) (plainAlpha S.k) L *
        (S.k*((6*B*C/Real.log z)*roughReciprocalMass z X^(S.k+1))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hmass hbr
      · exact hsum
      · positivity
      · positivity
    _ = _ := by ring

end Erdos387Proof.SeparatedZeroMode
