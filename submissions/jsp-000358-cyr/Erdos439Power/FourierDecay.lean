import Erdos439Power.CompleteRationalSums
import Erdos439Power.MinorArcs
import Erdos439Power.MajorArcs
import Erdos439Power.RationalReduction

open Filter
open scoped BigOperators
open Erdos439 Erdos439.PowerDecay Erdos438.Fourier

namespace Erdos439Power

lemma powerTerminalBaseNat_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 0 < L) :
    0 < powerTerminalBaseNat k L := by
  have hd : 0 < powerDerivative k := by unfold powerDerivative; positivity
  have hf : 0 < k.descFactorial (k - 1) := Nat.descFactorial_pos.mpr (Nat.sub_le _ _)
  unfold powerTerminalBaseNat
  positivity

/-- The all-degree normalized Fourier decay assertion, with no analytic
assumptions: the rational major/minor alternatives cover every frequency. -/
theorem hasNormalizedPowerFourierDecay (k : ℕ) (hk : 2 ≤ k) :
    HasNormalizedPowerFourierDecay k := by
  intro ε hε B
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨L, hL, hcomplete⟩ := exists_dilation_complete_sums k hk (ε / 2) hhalf
  let C := powerTerminalBaseNat k L
  have hC : 0 < C := powerTerminalBaseNat_pos k L hk hL
  obtain ⟨U, hU⟩ := exists_minorArc_threshold k hk ε hε
  obtain ⟨V, hV⟩ := eventually_atTop.mp (eventually_major_parameter_scalar_le k L C hhalf)
  let M := max 2 (max U (max V (B + 1)))
  have hM2 : 2 ≤ M := le_max_left _ _
  have hMU : U ≤ M := (le_max_left U _).trans (le_max_right _ _)
  have hMV : V ≤ M := (le_max_left V _).trans ((le_max_right U _).trans (le_max_right _ _))
  have hMB : B + 1 ≤ M := (le_max_right V _).trans ((le_max_right U _).trans (le_max_right _ _))
  have hMpow : M ≤ M ^ 4 := by
    calc
      M = M ^ 1 := by simp
      _ ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hN : 0 < M ^ 4 := by positivity
  have hsize : B < normalizedPower k L (M ^ 4) :=
    lt_of_lt_of_le (by omega) ((hMpow).trans (normalizedPower_index_le k L (M ^ 4)))
  refine ⟨L, M ^ 4, hL, hN, hsize, ?_⟩
  intro t ht ht0
  have htT : t < normalizedPower k L (M ^ 4) := Finset.mem_range.mp ht
  let Q := M ^ (4 * k - 1)
  have hQ2 : 2 ≤ Q := by
    calc
      2 ≤ M := hM2
      _ = M ^ 1 := by simp
      _ ≤ M ^ (4 * k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  let α : ℝ := (t : ℝ) / normalizedPower k L (M ^ 4)
  obtain ⟨a, b, hb, hbQ, hab, happ⟩ := dirichletApproximationReducedNat
    ((C : ℝ) * α) Q (by dsimp [α]; positivity) hQ2
  by_cases hMb : M < b
  · apply hU M hMU L hL t a b hab hMb hbQ
    convert happ using 1
    dsimp [α, C]
    congr 1
    ring
  · obtain ⟨A, q, hq, hqCb, hAq, _hratio, hqapprox⟩ :=
      exists_reduced_scaled_rational C b Q a α hC (by omega) (by omega) happ
    letI : NeZero q := ⟨by omega⟩
    have hqM : q ≤ C * M := hqCb.trans (Nat.mul_le_mul_left C (by omega))
    have hmean : 1 < q →
        ‖𝔼 x : ZMod q, polynomialPhase q A (normalizedPowerPolynomial k L) x‖ ≤ ε / 2 := by
      intro hq1
      exact hcomplete q A hq1 hAq
    have hmajor := norm_transform_le_major_parameter k L C M t q A (by omega) hM2 hq hqM
      htT ht0 (ε / 2) hhalf.le hmean hqapprox
    have hscalar := hV M hMV
    linarith

end Erdos439Power
