import Erdos387Proof.SeparatedFibrePhase
import Erdos387Proof.SeparatedWeightedPhase
import Erdos387Proof.SeparatedFrequencyWindow

/-! The finite weighted bound for an actual separated certificate fibre.
This consumes the exact domain/CRT identity, not a hypothesized phase saving.
-/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedFibreBound
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open SeparatedCertificateEnlargement SeparatedPrimeFibre SeparatedRetainedResidue
open SeparatedFibrePhase SeparatedWeightedPhase
open scoped BigOperators

noncomputable def envelope (B k t H Q : ℕ) : ℝ :=
  (4*(8*(4*(B : ℝ))+128*(H : ℝ)*(4*(B : ℝ))^2))*
    (Real.log (Q-Q/2+1 : ℕ)+1)*roughBound k t Q

theorem roughBound_nonneg (k t Q : ℕ) (ht : 0 < t) : 0 ≤ roughBound k t Q := by
  have hy : 1 ≤ BPZScale.y t k := by
    unfold BPZScale.y
    exact one_le_pow₀ (by omega : 1  ≤  t)
  have hyR : (1 : ℝ) ≤ BPZScale.y t k := by exact_mod_cast hy
  have hly := Real.log_nonneg hyR
  have hlQ : 0 ≤ Real.log (2*(Q : ℝ)+1) := Real.log_nonneg (by have hq : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q; linarith)
  have hly2 : 0 ≤ Real.log (2*(BPZScale.y t k : ℝ)+1) := Real.log_nonneg (by linarith)
  unfold roughBound
  positivity

theorem envelope_nonneg (B k t H Q : ℕ) (ht : 0 < t) : 0 ≤ envelope B k t H Q := by
  have hr := roughBound_nonneg k t Q ht
  have hl : 0 ≤ Real.log (Q-Q/2+1 : ℕ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q-Q/2+1))
  unfold envelope
  positivity

/-- Uniform over every nonzero signed frequency in the actual finite
height window. The original near anchor supplies R=4B; the terminal-prime
exception is excluded arithmetically, not assumed away. -/
theorem norm_sum_actualTerm_le
    {B K X z t medium g H : ℕ} {S : BPZSection6Input B K} {i : Fin S.k}
    (a : SplitCertificate S X)
    (ha : a∈certificates S X z (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) i)
    (hB : 0 < B) (hX : 0 < X) (hiX : i.val ≤ X)
    (hz : 2*S.k ≤ z) (hzy : z ≤ BPZScale.y t S.k)
    (ht : 6*2^S.k ≤ t) (hg : Squarefree g) (hgt : g ≤ t) (hM : refinementModulus S ≤ t)
    (hsupport : ∀ p∈g.primeFactors,max (2*S.k) 3 ≤ p ∧ p < z)
    (hH : 2 ≤ H) (hHt : H^2 ≤ t) (b : ℕ) (hb : b < g)
    (h : ℤ) (hh : h≠0) (hfreq : h.natAbs ≤ H) :
    ‖∑ v∈(fibre (z:=z) (y:=BPZScale.y t S.k) (medium:=medium)
      (second:=BPZScale.secondMin t S.k) (gap:=BPZScale.gap t S.k) (i:=i) a).attach,
      actualTerm (certificate_mem_of_mem_fibre v.property) hg hsupport b h‖  ≤ 
      envelope B S.k t H (blockUpper a.2.2) := by
  classical
  have htpos : 0 < t := by
    have h2 : 0 < 2^S.k := by positivity
    omega
  have hsecond : 1 ≤ BPZScale.secondMin t S.k := (by omega : 1 ≤ t).trans
    (SeparatedFrequencyWindow.base_le_secondMin t S.k (by omega) (by have := S.hk3; omega))
  obtain ⟨n,C,hi,hQ,hf,hmod,hnear⟩ := exists_anchor_phase_data_near a ha hz hsecond hg
    (fun p hp =>  (hsupport p hp).2)
  have hmod' : C.modulus=refinementModulus S*a.1.val.otherValue i*g*a.2.1 := by
    rw [hmod]
    ring
  let hd := sieve_data ha hg hsupport
  let gamma := retainedResidue a i g b hd.1 hd.2.1
  have hgamma : ∀ j, j≠C.i₀ → Nat.ModEq (C.E.factor j) gamma j.val := by
    intro j hji
    have hji' : j≠i := by simpa only [hi] using hji
    rw [hf j hji']
    exact retainedResidue_mod_factor a i g b hd.1 hd.2.1 j hji'
  have hfreqC := SeparatedFrequencyWindow.certificate_frequency_ne_zero C hH hHt h hh hfreq
  have hreal : |(h : ℝ)| ≤ (H : ℝ) := by
    have hc : (h.natAbs : ℝ) ≤ (H : ℝ) := by exact_mod_cast hfreq
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hc
  rw [sum_actualTerm_eq_whole_rough a ha hB hzy hg hsupport b hb h]
  by_cases hlo : lower a i ≤ upper a i medium
  · have hbound := norm_tent_rough_cut_le C ht hgt hM X (blockUpper a.2.2)
      (lower a i) (upper a i medium) hQ hX hlo gamma hgamma h hfreqC
      (R:=4*(B : ℝ)) (H:=(H : ℝ)) (by positivity) (by positivity) hreal
      (by simpa only [hi] using hiX) (certificate_tent_ratio_le C hnear hQ)
    simpa only [envelope,hmod',hi,gamma,hd] using hbound
  · have hzero (q : ℕ) : ¬(lower a i < q ∧ q ≤ upper a i medium) := by omega
    simp only [hzero,if_false,Finset.sum_const_zero,norm_zero]
    exact envelope_nonneg B S.k t H _ htpos

end Erdos387Proof.SeparatedFibreBound
