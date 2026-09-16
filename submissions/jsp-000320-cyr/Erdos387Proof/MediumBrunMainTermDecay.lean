import Mathlib
import Erdos387Proof.MediumMainTermDecay

/-!
# Decay of the actual even Brun medium main term

The depth is exactly `2*N`. The tail is controlled from the proved prime
reciprocal estimate and `log N = o(N)`, then the exact normalized Euler
bound is transferred to the actual even subset sum.
-/

namespace Erdos387Proof.MediumBrunMainTermDecay

open Erdos387 Erdos387.CoverBPZ MediumSieveEuler MediumMainTermDecay
open Filter
open scoped BigOperators Topology

theorem sum_alpha_le_primeReciprocal (k z : ℕ) :
    (∑ p ∈ windowPrimes k z, alpha k p) ≤
      ((k : ℝ) + 1) * PrimeReciprocal.primeReciprocalSum z := by
  calc
    _ ≤ ∑ p ∈ windowPrimes k z, ((k : ℝ) + 1) / p := by
      apply Finset.sum_le_sum
      intro p hp
      exact sub_le_self _ (by positivity)
    _ = ((k : ℝ) + 1) * ∑ p ∈ windowPrimes k z, (1 : ℝ) / p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have h := mem_windowPrimes.mp hp
        exact Nat.mem_primesLE.mpr ⟨h.2.2.le, h.1⟩
      · intro p _ _
        positivity

/-- Fixed-k logarithmic envelope derived from the actual prime sum. -/
theorem exists_sum_alpha_logarithmic_bound {k : ℕ} (hk : 0 < k) :
    ∃ a b : ℝ, ∀ N : ℕ, 0 < N →
      4 * (∑ p ∈ windowPrimes k (SubpowerScale.z N k), alpha k p) ≤
        a + b * Real.log (N : ℝ) := by
  obtain ⟨C, hC, hcheb⟩ := PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  let D : ℝ := 4 * ((k : ℝ) + 1) * (2 * C / Real.log 2)
  refine ⟨D * (1 + Real.log (BPZScale.xExp k : ℝ)), D * (2*k+3 : ℕ), ?_⟩
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (0 : ℝ) < BPZScale.xExp k := by
    unfold BPZScale.xExp
    positivity
  have hlog : Real.log ((Nat.log 2 (SubpowerScale.z N k) : ℕ) : ℝ) =
      Real.log (BPZScale.xExp k : ℝ) + (2*k+3 : ℕ) * Real.log (N : ℝ) := by
    rw [SubpowerScale.log_two_z]
    unfold SubpowerScale.roughPower
    push_cast
    rw [Real.log_mul hx.ne' (pow_ne_zero _ hNR.ne'), Real.log_pow]
    push_cast
    ring
  have hprime := PrimeReciprocal.primeReciprocalSum_le_one_add_log_log
    hC hcheb (SubpowerScale.z N k)
  have hsum := sum_alpha_le_primeReciprocal k (SubpowerScale.z N k)
  calc
    _ ≤ 4 * (((k : ℝ) + 1) *
        ((2 * C / Real.log 2) *
          (1 + Real.log ((Nat.log 2 (SubpowerScale.z N k) : ℕ) : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hsum.trans (mul_le_mul_of_nonneg_left hprime (by positivity))
    _ = _ := by rw [hlog]; dsimp [D]; push_cast; ring

/-- A fixed affine function of log N is eventually below any positive
linear function. This is the only limiting step in the relative tail bound. -/
theorem eventually_affine_log_le_linear (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, a + b * Real.log (N : ℝ) ≤ c * N := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / N) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn
  have ha : Tendsto (fun N : ℕ => a / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have hlim : Tendsto (fun N : ℕ => (a + b * Real.log (N : ℝ)) / N)
      atTop (𝓝 0) := by
    convert ha.add (hlog.const_mul b) using 1
    · ext N
      ring
    · simp
  filter_upwards [hlim.eventually (gt_mem_nhds hc), eventually_ge_atTop (1 : ℕ)] with N hbound hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact ((div_lt_iff₀ hNR).mp hbound).le

noncomputable def relativeTailFactor (k N : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2*N+1))⁻¹ *
    Real.exp (4 * ∑ p ∈ windowPrimes k (SubpowerScale.z N k), alpha k p)

/-- The actual depth `2*N` makes the previously proved relative tail at
most one, with no input tail assumption. -/
theorem eventually_relativeTailFactor_le_one {k : ℕ} (hk : 0 < k) :
    ∀ᶠ N : ℕ in atTop, relativeTailFactor k N ≤ 1 := by
  obtain ⟨a, b, hab⟩ := exists_sum_alpha_logarithmic_bound hk
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_affine_log_le_linear a b hlog2,
    eventually_ge_atTop (1 : ℕ)] with N hlin hN
  have hNpos : 0 < N := by omega
  have hmass := (hab N hNpos).trans hlin
  have hexpArg : 4 * (∑ p ∈ windowPrimes k (SubpowerScale.z N k), alpha k p) ≤
      (2*N+1 : ℕ) * Real.log 2 := by
    have hNR : (0 : ℝ) ≤ N := by positivity
    push_cast
    nlinarith
  have hexp := Real.exp_le_exp.mpr hexpArg
  have hpow : Real.exp ((2*N+1 : ℕ) * Real.log 2) = (2 : ℝ)^(2*N+1) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hpow] at hexp
  unfold relativeTailFactor
  calc
    _ ≤ ((2 : ℝ) ^ (2*N+1))⁻¹ * (2 : ℝ) ^ (2*N+1) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 1 := inv_mul_cancel₀ (by positivity)

/-- The actual even Brun subset sum is eventually at most twice its Euler
product on the chosen subpower scale. -/
theorem eventually_brunSum_le_two_euler {k : ℕ} (hk : 0 < k) :
    ∀ᶠ N : ℕ in atTop,
      brunSubsetSum (windowPrimes k (SubpowerScale.z N k)) (alpha k) (2*N) ≤
        2 * finiteEulerProduct (windowPrimes k (SubpowerScale.z N k)) (alpha k) := by
  filter_upwards [eventually_relativeTailFactor_le_one hk] with N htail
  have hwindow := brun_window_bounds k (SubpowerScale.z N k) (even_two_mul N)
  have hupper := hwindow.2.2
  change brunSubsetSum _ _ _ ≤ _ * (1 + relativeTailFactor k N) at hupper
  exact hupper.trans (by nlinarith [mul_nonneg hwindow.1.le (sub_nonneg.mpr htail)])

/-- Normalized actual even Brun main term, using exactly depth `2*N`. -/
noncomputable def normalizedBrunMainFactor {B K : ℕ}
    (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  (brunSubsetSum (windowPrimes S.k (SubpowerScale.z N S.k)) (alpha S.k) (2*N) *
    roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) ^ (S.k - 1)) /
      refinedDensity S (SubpowerScale.z N S.k)

/-- No analytical estimate appears as an input: the actual normalized
Brun main term has a derived fixed-k inverse-fifth-power upper bound. -/
theorem exists_normalizedBrunMainFactor_le_inv_fifth {B K : ℕ}
    (S : BPZSection6Input B K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      normalizedBrunMainFactor S N ≤ C / (N : ℝ)^5 := by
  obtain ⟨C, hC, hEuler⟩ := exists_normalizedMainFactor_le_inv_fifth S
  have hk : 0 < S.k := by have := S.hk3; omega
  refine ⟨2*C, by positivity, ?_⟩
  filter_upwards [eventually_brunSum_le_two_euler hk,
    eventually_ge_atTop (1 : ℕ)] with N hBrun hN
  have hNR : 0 < N := by omega
  have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
  have hmass : 0 ≤ roughReciprocalMass (SubpowerScale.z N S.k)
      (SubpowerScale.X N S.k) ^ (S.k-1) := by
    unfold roughReciprocalMass
    positivity
  calc
    normalizedBrunMainFactor S N ≤ 2 * normalizedMainFactor S N := by
      unfold normalizedBrunMainFactor normalizedMainFactor
      calc
        _ ≤ (2 * finiteEulerProduct (windowPrimes S.k (SubpowerScale.z N S.k))
            (alpha S.k) * roughReciprocalMass (SubpowerScale.z N S.k)
              (SubpowerScale.X N S.k) ^ (S.k-1)) /
                refinedDensity S (SubpowerScale.z N S.k) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBrun hmass) hV.le
        _ = _ := by ring
    _ ≤ 2 * (C / (N : ℝ)^5) := mul_le_mul_of_nonneg_left (hEuler N hNR) (by norm_num)
    _ = _ := by ring

end Erdos387Proof.MediumBrunMainTermDecay
