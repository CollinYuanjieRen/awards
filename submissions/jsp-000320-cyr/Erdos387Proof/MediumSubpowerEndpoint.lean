import Erdos387Proof.MediumComplementBounds
import Erdos387Proof.MediumEndpointAssembly
import Erdos387Proof.MediumEndpointDecay

/-! Close the arithmetic applicability of the endpoint envelope on the
actual subpower medium-certificate family. -/

namespace Erdos387Proof.MediumSubpowerEndpoint

open Erdos387 MediumComplementGrouping MediumComplementBounds
open MediumReciprocalPhase MediumFactorWindow
open scoped BigOperators

noncomputable def actualEndpointSum {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (N : ℕ) (i : Fin S.k) : ℝ :=
  ∑ c ∈ (vectors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) i).attach,
    ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
      if T.card ≤ 2 * N then
        MediumZeroMode.endpointError (∏ p ∈ T, p)
          (CoverBPZ.refinementModulus S * (representative c).val.otherValue i) S.k
          (lower B (SubpowerScale.X N S.k) ((representative c).val.otherValue i)
            (SubpowerScale.medium N S.k)) (3 * (SubpowerScale.X N S.k : ℝ) + 1)
      else 0

theorem actualEndpointSum_le {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    {N : ℕ} (hN : 0 < N) (i : Fin S.k) :
    actualEndpointSum S N i ≤
      MediumEndpointDecay.totalEndpointEnvelope S (CoverBPZ.refinementModulus S) N := by
  classical
  have hk : 0 < S.k := by have := S.hk3; omega
  have hz : 1 ≤ SubpowerScale.z N S.k := (SubpowerScale.two_le_z hN hk).trans' (by omega)
  have hm : 0 < SubpowerScale.medium N S.k := by
    unfold SubpowerScale.medium BPZScale.medium SubpowerScale.base
    positivity
  have hP : ∀ p ∈ MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k), p.Prime :=
    fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1
  have hPz : MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k) ⊆
      Finset.range (SubpowerScale.z N S.k) := by
    intro p hp
    exact Finset.mem_range.mpr (MediumSieveEuler.mem_windowPrimes.mp hp).2.2
  have hX : (3 * (SubpowerScale.X N S.k : ℝ) + 1) ≤
      4 * (SubpowerScale.X N S.k : ℝ) := by
    have hpos : (1 : ℝ) ≤ SubpowerScale.X N S.k := by
      exact_mod_cast SubpowerScale.X_pos N S.k
    linarith
  have h := MediumEndpointAssembly.sum_endpointErrors_le
    (X := SubpowerScale.X N S.k) (z := SubpowerScale.z N S.k)
    (medium := SubpowerScale.medium N S.k) (large := SubpowerScale.large N S.k)
    (L := 2 * N) (W := N ^ 2) S i
    (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)) hz hm hP hPz
    (fun c => certificate_otherValue_squarefree (representative_mem c))
    (fun c => subpower_primeFactors_card_le hN (representative_mem c)) (by positivity) hX
  change actualEndpointSum S N i ≤ _ at h
  apply h.trans_eq
  unfold MediumEndpointDecay.totalEndpointEnvelope
  push_cast
  ring

end Erdos387Proof.MediumSubpowerEndpoint
