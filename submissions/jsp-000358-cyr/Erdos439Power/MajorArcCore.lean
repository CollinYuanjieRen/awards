import Erdos439Power.RationalPhaseBridge
import Erdos439Power.MeshQuadrature

open scoped BigOperators ComplexConjugate
open Erdos439 Erdos439.PowerDecay Erdos438.Fourier

namespace Erdos439Power

lemma norm_transform_eq_inv_norm_gap (k L N t : ℕ) (hN : 0 < N) :
    ‖transform (normalizedPower k L N)
      (fun s => (normalizedPowerWeight k L N s : ℂ)) (-(t : ℤ))‖ =
      (normalizedPower k L N : ℝ)⁻¹ * ‖gapPhaseSum k L N t‖ := by
  have hT : 0 < (normalizedPower k L N : ℝ) := by
    exact_mod_cast (show 0 < normalizedPower k L N by
      simpa only [normalizedPower_zero] using normalizedPower_strictMono k L hN)
  rw [transform_normalizedPowerWeight_eq k L N t hN, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]

lemma abs_major_phase (x : ℝ) : |-2 * Real.pi * x| = 2 * Real.pi * |x| := by
  rw [abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le]
  norm_num

lemma norm_weighted_realPhase_sum_le (k L N : ℕ) (β : ℝ) :
    ‖∑ n ∈ Finset.range N, (normalizedPowerGap k L n : ℂ) *
      realPhase (β * normalizedPower k L n)‖ ≤ normalizedPower k L N := by
  refine (norm_sum_le _ _).trans_eq ?_
  simp only [norm_mul, norm_realPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (normalizedPowerGap_pos _ _ _), sum_normalizedPowerGap]

theorem norm_gapPhaseSum_sub_main_le (k L N t q a : ℕ) [NeZero q]
    (hN : 0 < N) (hq : 0 < q) :
    let β : ℝ := -2 * Real.pi * ((t : ℝ) / normalizedPower k L N - (a : ℝ) / q)
    ‖gapPhaseSum k L N t -
      conj (𝔼 x : ZMod q, polynomialPhase q a (normalizedPowerPolynomial k L) x) *
        (∑ n ∈ Finset.range N, (normalizedPowerGap k L n : ℂ) *
          realPhase (β * normalizedPower k L n))‖ ≤
      (2 * q) * (2 * normalizedPowerGap k L N +
        |β| * normalizedPowerGap k L N * normalizedPower k L N) := by
  dsimp only
  have hT : 0 < normalizedPower k L N := by
    simpa only [normalizedPower_zero] using normalizedPower_strictMono k L hN
  have h := norm_periodic_main_term_error_le
    (fun n => conj (polynomialPhase q a (normalizedPowerPolynomial k L) (n : ZMod q)))
    q hq (periodic_conj_polynomialPhase q a _)
    (fun n => by simp) (normalizedPowerGap k L)
    (fun n => (normalizedPower k L n : ℝ)) N
    (-2 * Real.pi * ((t : ℝ) / normalizedPower k L N - (a : ℝ) / q))
    (fun n _ => (normalizedPowerGap_pos k L n).le)
    (monotone_nat_of_le_succ (normalizedPowerGap_mono k L))
    (fun i j hij => Nat.cast_le.mpr ((normalizedPower_strictMono k L).monotone hij))
  rw [periodicMean_conj_polynomialPhase] at h
  simp only [normalizedPower_zero, Nat.cast_zero, sub_zero] at h
  convert h using 1
  unfold gapPhaseSum
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  rw [phase_normalizedPower_factorization _ _ q a _ _ _ hT]
  ring

theorem norm_gapPhaseSum_le_main_add_error (k L N t q a : ℕ) [NeZero q]
    (hN : 0 < N) (hq : 0 < q) :
    let β : ℝ := -2 * Real.pi * ((t : ℝ) / normalizedPower k L N - (a : ℝ) / q)
    ‖gapPhaseSum k L N t‖ ≤
      ‖𝔼 x : ZMod q, polynomialPhase q a (normalizedPowerPolynomial k L) x‖ *
        normalizedPower k L N +
      (2 * q) * (2 * normalizedPowerGap k L N +
        |β| * normalizedPowerGap k L N * normalizedPower k L N) := by
  dsimp only
  let β : ℝ := -2 * Real.pi * ((t : ℝ) / normalizedPower k L N - (a : ℝ) / q)
  let A := conj (𝔼 x : ZMod q, polynomialPhase q a (normalizedPowerPolynomial k L) x) *
    (∑ n ∈ Finset.range N, (normalizedPowerGap k L n : ℂ) *
      realPhase (β * normalizedPower k L n))
  have hmain : ‖A‖ ≤
      ‖𝔼 x : ZMod q, polynomialPhase q a (normalizedPowerPolynomial k L) x‖ *
        normalizedPower k L N := by
    dsimp [A]
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_weighted_realPhase_sum_le k L N β) (norm_nonneg _)
  have herr := norm_gapPhaseSum_sub_main_le k L N t q a hN hq
  have ht : ‖gapPhaseSum k L N t‖ ≤ ‖gapPhaseSum k L N t - A‖ + ‖A‖ := by
    simpa using norm_add_le (gapPhaseSum k L N t - A) A
  linarith

/-- Denominator one has no main term at a nonzero Fourier frequency. -/
theorem norm_gapPhaseSum_le_at_integer (k L N t a : ℕ) (hN : 0 < N)
    (ht : t < normalizedPower k L N) (ht0 : t ≠ 0) :
    let β : ℝ := -2 * Real.pi * ((t : ℝ) / normalizedPower k L N - a)
    ‖gapPhaseSum k L N t‖ ≤
      |β| * normalizedPowerGap k L N * normalizedPower k L N := by
  dsimp only
  have hT : 0 < normalizedPower k L N := by
    simpa only [normalizedPower_zero] using normalizedPower_strictMono k L hN
  have hphase : ∀ s : ℕ,
      phase (normalizedPower k L N) (-(t : ℤ)) (s : ℤ) =
        realPhase ((-2 * Real.pi * ((t : ℝ) / normalizedPower k L N - a)) * s) := by
    intro s
    have h := phase_normalizedPower_factorization (normalizedPower k L N) t 1 a 1 1 s hT
    simpa [normalizedPower_one, conj_polynomialPhase_one] using h
  have hzero : (∑ s ∈ Finset.range (normalizedPower k L N),
      realPhase ((-2 * Real.pi * ((t : ℝ) / normalizedPower k L N - a)) * s)) = 0 := by
    simp_rw [← hphase]
    exact sum_phase_range_eq_zero _ t hT ht ht0
  have h := norm_mesh_quadrature_le k L N
    (fun s : ℕ => realPhase ((-2 * Real.pi * ((t : ℝ) / normalizedPower k L N - a)) * s))
    |(-2 * Real.pi * ((t : ℝ) / normalizedPower k L N - a))|
    (abs_nonneg _)
    (fun i j hij => norm_realPhase_mul_sub_le
      (-2 * Real.pi * ((t : ℝ) / normalizedPower k L N - a)) (i : ℝ) (j : ℝ)
      (by exact_mod_cast hij))
  rw [hzero, sub_zero] at h
  simpa only [gapPhaseSum, hphase] using h

end Erdos439Power
