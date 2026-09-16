import Erdos439Power.MinorEnvelope
import Erdos439Power.MinorScalar

open Filter
open scoped BigOperators Topology
open Erdos439 Erdos439.PowerDecay Erdos438.Fourier

namespace Erdos439Power

/-- Minor-arc decay is uniform in the polynomial dilation. All estimates on
the right side of the rational-approximation hypothesis are explicit. -/
theorem exists_minorArc_threshold (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 0 < L → ∀ t a b : ℕ,
      a.Coprime b → M < b → b ≤ M ^ (4 * k - 1) →
      |(t : ℝ) * powerTerminalBaseNat k L / normalizedPower k L (M ^ 4) -
        (a : ℝ) / b| ≤ 1 / ((b : ℝ) * (M ^ (4 * k - 1) : ℕ)) →
      ‖transform (normalizedPower k L (M ^ 4))
        (fun s => (normalizedPowerWeight k L (M ^ 4) s : ℂ)) (-(t : ℤ))‖ ≤ ε := by
  let η : ℝ := ε / (2 * (2 : ℝ) ^ k)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, B, hB⟩ := exists_terminal_ratio_for_finiteWeylEnvelope (k - 1) η hη
  obtain ⟨V, hV⟩ := exists_uniform_divisor_power_le_subpower (k - 1) (by omega)
  obtain ⟨S, hS⟩ := eventually_atTop.mp (eventually_minorScalarH_le k hδ)
  refine ⟨max 2 (max B (max V S)), ?_⟩
  intro M hM L hL t a b ha hMb hbQ happ
  have hM2 : 2 ≤ M := (le_max_left _ _).trans hM
  have hMB : B ≤ M := (le_max_left B _).trans ((le_max_right _ _).trans hM)
  have hMV : V ≤ M := (le_max_left V S).trans
    ((le_max_right B _).trans ((le_max_right _ _).trans hM))
  have hMS : S ≤ M := (le_max_right V S).trans
    ((le_max_right B _).trans ((le_max_right _ _).trans hM))
  have hMpow : M ≤ M ^ 4 := by
    calc
      M = M ^ 1 := by simp
      _ ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hN0 : 0 < M ^ 4 := pow_pos (by omega) _
  have hQ : 2 * (M ^ 4) ^ (k - 1) ≤ M ^ (4 * k - 1) := by
    have hexp : 4 * k - 1 = 4 * (k - 1) + 3 := by omega
    rw [hexp, pow_add, pow_mul]
    have hM3 : 2 ≤ M ^ 3 := by
      calc
        2 ≤ M := hM2
        _ = M ^ 1 := by simp
        _ ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    calc
      2 * (M ^ 4) ^ (k - 1) ≤ M ^ 3 * (M ^ 4) ^ (k - 1) :=
        Nat.mul_le_mul_right _ hM3
      _ = (M ^ 4) ^ (k - 1) * M ^ 3 := mul_comm _ _
  have hterminal : powerTerminalProductMajorant k L (M ^ 4) t (M ^ 4) 1 (k - 1) ≤
      ((M ^ 4 : ℕ) : ℝ) ^ (k - 1) * (δ * (M ^ 4 : ℕ)) := by
    have he := powerTerminalProductMajorant_le_explicit k L (M ^ 4) t (M ^ 4)
      (k - 1) a b (M ^ (4 * k - 1)) (divisorSubpowerEnvelope (M ^ 4))
      (by omega) ha hQ happ (by unfold divisorSubpowerEnvelope; positivity)
      (hV (M ^ 4) (hMV.trans hMpow))
    have hscalar := minorScalar_terminal_bound k M b hk hM2 hMb hbQ
    dsimp only at hscalar
    have he' : powerTerminalProductMajorant k L (M ^ 4) t (M ^ 4) 1 (k - 1) ≤
        minorScalarH k M * ((M ^ 4 : ℕ) : ℝ) ^ ((k - 1) + 1) := by
      refine he.trans ?_
      simpa only [divisorSubpowerEnvelope, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm]
        using hscalar
    calc
      _ ≤ minorScalarH k M * ((M ^ 4 : ℕ) : ℝ) ^ ((k - 1) + 1) := he'
      _ ≤ δ * ((M ^ 4 : ℕ) : ℝ) ^ ((k - 1) + 1) :=
        mul_le_mul_of_nonneg_right (hS M hMS) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hpref := prefix_le_of_terminal_majorant k L (M ^ 4) t hk hL
    (δ * (M ^ 4 : ℕ)) (by positivity) hterminal
  have henv := hB (M ^ 4) (hMB.trans hMpow) (δ * (M ^ 4 : ℕ)) (by positivity) le_rfl
  have hfour := norm_transform_le_of_prefix k L (M ^ 4) t (by omega) hN0 η hη.le
    (fun m hm => (hpref m hm).trans henv)
  convert hfour using 1
  dsimp [η]
  field_simp

end Erdos439Power
