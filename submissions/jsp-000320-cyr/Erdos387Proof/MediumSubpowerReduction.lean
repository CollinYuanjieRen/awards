import Erdos387Proof.MediumFiniteReduction
import Erdos387Proof.MediumSubpowerEndpoint
import Erdos387Proof.MediumBrunMainTermDecay

/-! The original medium-error count with every nonoscillatory contribution
bounded at its actual subpower parameters. The Fourier term stays explicit. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumSubpowerReduction

open Erdos387 Erdos387.CoverBPZ MediumFiniteReduction MediumComplementGrouping
open MediumMainTermDecay MediumBrunMainTermDecay MediumEndpointDecay
open Filter
open scoped BigOperators Topology

noncomputable def sieveScale {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  (SubpowerScale.X N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) /
    refinementModulus S

theorem sieveScale_pos {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    0 < sieveScale S N := by
  unfold sieveScale
  exact div_pos (mul_pos (by exact_mod_cast SubpowerScale.X_pos N S.k)
    (refinedDensity_pos S _)) (by exact_mod_cast refinementModulus_pos S)

noncomputable def mainEnvelope {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  (4 * (SubpowerScale.X N S.k : ℝ) / refinementModulus S) * Real.log (6 * (B : ℝ)) *
    brunSubsetSum
      (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k))
      (MediumSieveEuler.alpha S.k) (2 * N) *
        roughReciprocalMass
          (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) ^ (S.k - 1)

noncomputable def totalFourierError {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  ∑ i : Fin S.k, ∑ c ∈ (vectors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) i).attach,
    fourierError (representative c) i
      (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)) (2 * N)
      (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k)

/-- No Fourier cancellation estimate occurs among the premises. -/
theorem card_medium_le {B K N : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hN : 0 < N) (hz : 2 * S.k ≤ SubpowerScale.z N S.k) :
    ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
      RefinedMediumErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k)).card : ℝ) ≤
      S.k * (mainEnvelope S N + totalEndpointEnvelope S (refinementModulus S) N) +
        totalFourierError S N := by
  classical
  have hm : 0 < SubpowerScale.medium N S.k := by
    unfold SubpowerScale.medium BPZScale.medium SubpowerScale.base
    positivity
  have hL : Even (2 * N) := even_two_mul N
  have h := card_medium_le_sum_reduced (large := SubpowerScale.large N S.k)
    S hB hz (SubpowerScale.X_pos N S.k) hm hL
  apply h.trans
  have heach (i : Fin S.k) :
      (∑ c ∈ (vectors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) i).attach,
        (fibreMainTerm (representative c) i
          (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)) (2 * N)
          (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) +
        harmonicError (representative c) i
          (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)) (2 * N)
          (SubpowerScale.medium N S.k) +
        fourierError (representative c) i
          (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)) (2 * N)
          (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k))) ≤
        mainEnvelope S N + totalEndpointEnvelope S (refinementModulus S) N +
          ∑ c ∈ (vectors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
            (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) i).attach,
            fourierError (representative c) i
              (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)) (2 * N)
              (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) := by
    simp only [Finset.sum_add_distrib]
    exact add_le_add (add_le_add
      (MediumMainTermAssembly.sum_mainTerms_le S i hB (SubpowerScale.X_pos N S.k) hm hL)
      (MediumSubpowerEndpoint.actualEndpointSum_le S hN i)) le_rfl
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, totalFourierError, mul_add] using hs

theorem mainEnvelope_div_sieveScale {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    mainEnvelope S N / sieveScale S N =
      (4 * Real.log (6 * (B : ℝ))) * normalizedBrunMainFactor S N := by
  have hM : (refinementModulus S : ℝ) ≠ 0 := by exact_mod_cast (refinementModulus_pos S).ne'
  have hX : (SubpowerScale.X N S.k : ℝ) ≠ 0 := by
    exact_mod_cast (SubpowerScale.X_pos N S.k).ne'
  unfold mainEnvelope sieveScale normalizedBrunMainFactor
  field_simp

theorem normalizedBrunMainFactor_nonneg {B K : ℕ}
    (S : BPZSection6Input B K) (N : ℕ) : 0 ≤ normalizedBrunMainFactor S N := by
  have h := MediumSieveEuler.brun_window_bounds S.k (SubpowerScale.z N S.k) (even_two_mul N)
  have hBrun := h.1.le.trans h.2.1
  unfold normalizedBrunMainFactor
  exact div_nonneg (mul_nonneg hBrun (by unfold roughReciprocalMass; positivity))
    (refinedDensity_pos S _).le

theorem tendsto_normalizedBrunMainFactor_zero {B K : ℕ} (S : BPZSection6Input B K) :
    Tendsto (normalizedBrunMainFactor S) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_normalizedBrunMainFactor_le_inv_fifth S
  have hlim : Tendsto (fun N : ℕ => C / (N : ℝ)^5) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat.pow 5).const_mul C
    simpa [div_pow, div_eq_mul_inv] using h
  exact squeeze_zero' (Filter.Eventually.of_forall (normalizedBrunMainFactor_nonneg S)) hbound hlim

/-- All main and endpoint terms, including the sum over distinguished
coordinates, vanish relative to the original sieve scale. -/
theorem tendsto_nonoscillatory_div_sieveScale_zero {B K : ℕ} (S : BPZSection6Input B K) :
    Tendsto (fun N => (S.k : ℝ) *
      (mainEnvelope S N + totalEndpointEnvelope S (refinementModulus S) N) / sieveScale S N)
      atTop (𝓝 0) := by
  have hm := (tendsto_normalizedBrunMainFactor_zero S).const_mul (4 * Real.log (6 * (B : ℝ)))
  have he := tendsto_normalizedEndpointEnvelope_zero S (refinementModulus S)
  have hlim := (hm.add he).const_mul (S.k : ℝ)
  simp only [mul_zero, add_zero] at hlim
  convert hlim using 1
  ext N
  rw [mul_div_assoc, add_div, mainEnvelope_div_sieveScale]
  rw [show totalEndpointEnvelope S (refinementModulus S) N / sieveScale S N =
      normalizedEndpointEnvelope S (refinementModulus S) N from
        totalEndpointEnvelope_div_sieveScale S (refinementModulus_pos S) N]

end Erdos387Proof.MediumSubpowerReduction
