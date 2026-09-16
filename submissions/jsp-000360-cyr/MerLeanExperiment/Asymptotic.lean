import MerLeanExperiment.UpperBound
import MerLeanExperiment.LowerBound
import Mathlib.Tactic

namespace Erdos441

/-- Chen's sharp asymptotic for the Erdős 441 extremal function. -/
theorem chen_asymptotic :
    Filter.Tendsto (fun N : ℕ => (g N : ℝ) / Real.sqrt ((9 / 8 : ℝ) * N))
      Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let c : ℝ := Real.sqrt (9 / 8 : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc2 : c ^ 2 = 9 / 8 := by
    dsimp [c]
    exact Real.sq_sqrt (by norm_num)
  obtain ⟨NU, hNU⟩ := chen_uniform_upper (epsilon * c / 2) (by positivity)
  let B : ℝ := 22 / (epsilon * c)
  let N0 : ℕ := max NU (max 1 ⌈B ^ 2⌉₊)
  refine ⟨N0, ?_⟩
  intro N hN
  have hNU_N : NU ≤ N := by
    dsimp [N0] at hN
    omega
  have hN1 : 1 ≤ N := by
    dsimp [N0] at hN
    omega
  have hNpos : 0 < N := by omega
  let R : ℝ := Real.sqrt (N : ℝ)
  have hR : 0 < R := by
    dsimp [R]
    exact Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have hR2 : R ^ 2 = (N : ℝ) := by
    dsimp [R]
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hBsq : B ^ 2 ≤ (N : ℝ) :=
    (Nat.le_ceil (B ^ 2)).trans
      (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hBR : B ≤ R := by nlinarith
  have hlarge : 22 ≤ epsilon * c * R := by
    calc
      (22 : ℝ) = epsilon * c * B := by
        dsimp [B]
        field_simp [hepsilon.ne', hc.ne']
      _ ≤ epsilon * c * R :=
        mul_le_mul_of_nonneg_left hBR (mul_pos hepsilon hc).le
  obtain ⟨A, hA, hcard⟩ := exists_extremal N
  have hu := hNU N hNU_N A hA
  rw [hcard] at hu
  have hupper : (g N : ℝ) ≤ (c + epsilon * c / 2) * R := by
    simpa only [c, R] using hu
  have hlNat := lower_squared_bound N
  have hl : (9 : ℝ) * N ≤ 8 * ((g N : ℝ) + 11) ^ 2 := by
    exact_mod_cast hlNat
  have hcR2 : (c * R) ^ 2 = (9 / 8 : ℝ) * N := by
    rw [mul_pow, hc2, hR2]
  have hsquares : (c * R) ^ 2 ≤ ((g N : ℝ) + 11) ^ 2 := by
    nlinarith
  have hlower : c * R ≤ (g N : ℝ) + 11 := by
    have hg0 : 0 ≤ (g N : ℝ) + 11 := by positivity
    have hcR0 : 0 ≤ c * R := (mul_pos hc hR).le
    nlinarith
  have hden : 0 < c * R := mul_pos hc hR
  have hratioLower : 1 - epsilon / 2 ≤ (g N : ℝ) / (c * R) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hratioUpper : (g N : ℝ) / (c * R) ≤ 1 + epsilon / 2 := by
    apply (div_le_iff₀ hden).2
    calc
      (g N : ℝ) ≤ (c + epsilon * c / 2) * R := hupper
      _ = (1 + epsilon / 2) * (c * R) := by ring
  have hsqrt : Real.sqrt ((9 / 8 : ℝ) * N) = c * R := by
    dsimp [c, R]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 / 8)]
  rw [hsqrt, Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith

end Erdos441

#print axioms Erdos441.chen_asymptotic
