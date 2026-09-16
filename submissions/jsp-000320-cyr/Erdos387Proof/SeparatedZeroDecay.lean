import Erdos387Proof.SeparatedZeroMode
import Erdos387Proof.MediumSubpowerReduction

/-! Decay of the actual separated zero-mode sum relative to the original
refined sieve scale, with no analytic assumption on the final theorem. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedZeroDecay
open Erdos387 Erdos387.CoverBPZ SeparatedZeroMode ConvenientMainDecay
open MediumSubpowerReduction MediumMainTermDecay Filter
open scoped Topology

theorem tendsto_totalZeroMass_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0<B) :
    Tendsto (fun N => totalZeroMass S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
      (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) (2*N)/sieveScale S N)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hcheb⟩ := PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  have hk : 0<S.k := by have := S.hk3; omega
  have hlim := (ConvenientMainDecay.tendsto_normalizedMainFactor_zero S).const_mul (24*B*C*S.k)
  simp only [mul_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · exact Filter.Eventually.of_forall (fun N =>
      div_nonneg (totalZeroMass_nonneg S _ _ _ _ _ _ (even_two_mul N)) (sieveScale_pos S N).le)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hz : 2≤SubpowerScale.z N S.k := SubpowerScale.two_le_z (by omega) hk
    have h := totalZeroMass_le S (y := SubpowerScale.y N S.k) (medium := SubpowerScale.medium N S.k)
      (second := SubpowerScale.secondMin N S.k) (gap := SubpowerScale.gap N S.k) hC (N := 2) hcheb
      hz hz hB (SubpowerScale.X_pos N S.k)
      (even_two_mul N)
    apply (div_le_div_of_nonneg_right h (sieveScale_pos S N).le).trans_eq
    unfold ConvenientMainDecay.normalizedMainFactor sieveScale
    have hX : (0 : ℝ)<SubpowerScale.X N S.k := by exact_mod_cast SubpowerScale.X_pos N S.k
    have hM : (0 : ℝ)<refinementModulus S := by exact_mod_cast refinementModulus_pos S
    have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
    field_simp

end Erdos387Proof.SeparatedZeroDecay
