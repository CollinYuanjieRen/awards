import MerLeanExperiment.SquareModulus
import MerLeanExperiment.SquareSubproducts
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ReciprocalSquares

/-- The logarithm of the square modulus at scale `M^10` is bounded by a
single explicit power of `M`. -/
theorem squareModulus_log_le_power
    (M : ℕ) (hM : 262144 ≤ M) :
    Real.log (squareModulus (M ^ 10) : ℝ) ≤ 120 * (M : ℝ) ^ 31 := by
  have hMpos : 0 < M := by omega
  have hmpos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hN : 2 ≤ M ^ 10 := by
    have hself : M ≤ M ^ 10 :=
      le_self_pow₀ (by omega) (by decide : (10 : ℕ) ≠ 0)
    omega
  have hbase := squareModulus_log_le (M ^ 10) hN
  have hlogM : Real.log (M : ℝ) ≤ (M : ℝ) := by
    have hlog := Real.log_le_sub_one_of_pos hmpos
    linarith
  calc
    Real.log (squareModulus (M ^ 10) : ℝ) ≤
        12 * ((M ^ 10 : ℕ) : ℝ) ^ 3 * Real.log ((M ^ 10 : ℕ) : ℝ) := hbase
    _ = 120 * (M : ℝ) ^ 30 * Real.log (M : ℝ) := by
      norm_num [Nat.cast_pow, Real.log_pow]
      ring
    _ ≤ 120 * (M : ℝ) ^ 30 * (M : ℝ) :=
      mul_le_mul_of_nonneg_left hlogM (by positivity)
    _ = 120 * (M : ℝ) ^ 31 := by ring

/-- A sufficiently strong logarithmic gap makes every Bernoulli atom smaller
than half the reciprocal Fourier modulus. -/
theorem squareD_atom_lt_half_modulus
    (M : ℕ) (hM : 262144 ≤ M) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hscale : 2904 ≤ (-Real.log q) * (M : ℝ) ^ 5) :
    q ^ (squareD (M ^ 10)).card <
      1 / (2 * (squareModulus (M ^ 10) : ℝ)) := by
  let D := squareD (M ^ 10)
  let μ : ℝ := squareModulus (M ^ 10)
  let lam : ℝ := -Real.log q
  have hMpos : 0 < M := by omega
  have hmpos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hμpos : 0 < μ := by
    dsimp [μ]
    exact_mod_cast squareModulus_pos (M ^ 10)
  have hlampos : 0 < lam := by
    dsimp [lam]
    exact neg_pos.mpr (Real.log_neg hq0 hq1)
  have hcardNat : M ^ 36 ≤ 24 * D.card := by
    dsimp [D]
    exact pow_thirtysix_le_twentyfour_squareD_card M hM
  have hcard : (M : ℝ) ^ 36 / 24 ≤ (D.card : ℝ) := by
    have hcast : (M : ℝ) ^ 36 ≤ 24 * (D.card : ℝ) := by
      exact_mod_cast hcardNat
    linarith
  have hscale' : 2904 ≤ lam * (M : ℝ) ^ 5 := by
    simpa only [lam] using hscale
  have hlambdaPow : 121 * (M : ℝ) ^ 31 ≤ lam * (M : ℝ) ^ 36 / 24 := by
    have hmul := mul_le_mul_of_nonneg_right hscale'
      (show (0 : ℝ) ≤ (M : ℝ) ^ 31 by positivity)
    calc
      121 * (M : ℝ) ^ 31 = 2904 * (M : ℝ) ^ 31 / 24 := by ring
      _ ≤ (lam * (M : ℝ) ^ 5) * (M : ℝ) ^ 31 / 24 := by linarith
      _ = lam * (M : ℝ) ^ 36 / 24 := by ring
  have hlambdaCard : 121 * (M : ℝ) ^ 31 ≤ lam * (D.card : ℝ) := by
    calc
      121 * (M : ℝ) ^ 31 ≤ lam * (M : ℝ) ^ 36 / 24 := hlambdaPow
      _ = lam * ((M : ℝ) ^ 36 / 24) := by ring
      _ ≤ lam * (D.card : ℝ) := mul_le_mul_of_nonneg_left hcard hlampos.le
  have hcardLog : (D.card : ℝ) * Real.log q ≤ -121 * (M : ℝ) ^ 31 := by
    dsimp [lam] at hlambdaCard
    nlinarith
  have hlogμ : Real.log μ ≤ 120 * (M : ℝ) ^ 31 := by
    dsimp [μ]
    exact squareModulus_log_le_power M hM
  have hexponent :
      Real.log μ + (D.card : ℝ) * Real.log q ≤ -(M : ℝ) ^ 31 := by
    linarith
  have hqpow : q ^ D.card = Real.exp ((D.card : ℝ) * Real.log q) := by
    calc
      q ^ D.card = (Real.exp (Real.log q)) ^ D.card := by rw [Real.exp_log hq0]
      _ = Real.exp ((D.card : ℝ) * Real.log q) :=
        (Real.exp_nat_mul (Real.log q) D.card).symm
  have hprodexp : μ * q ^ D.card =
      Real.exp (Real.log μ + (D.card : ℝ) * Real.log q) := by
    rw [hqpow, Real.exp_add, Real.exp_log hμpos]
  have hprodExpBound : μ * q ^ D.card ≤ Real.exp (-(M : ℝ) ^ 31) := by
    rw [hprodexp]
    exact Real.exp_le_exp.mpr hexponent
  have hmone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hmPowOne : (1 : ℝ) ≤ (M : ℝ) ^ 31 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hmone 31
  have hExpOne : Real.exp (-(M : ℝ) ^ 31) ≤ Real.exp (-1) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hExpHalf : Real.exp (-1) < (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) Real.exp_one_gt_two)
  have hprodHalf : μ * q ^ D.card < 1 / 2 :=
    hprodExpBound.trans_lt (hExpOne.trans_lt hExpHalf)
  dsimp [D, μ] at hprodHalf ⊢
  apply (lt_div_iff₀ (show (0 : ℝ) < 2 * squareModulus (M ^ 10) by positivity)).mpr
  nlinarith

end ReciprocalSquares
