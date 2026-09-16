import MerLeanExperiment.NetProbability
import MerLeanExperiment.PeriodicTransfer

namespace DiskDiscrepancy

/-- Concrete integral periods and meshes have polynomially many tested disks. -/
theorem exists_net_parameters {R : ℝ} (hR : 4 ≤ R) :
    ∃ L q K : ℕ, 0 < L ∧ 0 < q ∧ 0 < K ∧
      2 * R + 4 ≤ L ∧ R ≤ q ∧ (q : ℝ) * (R + 1) ≤ K ∧
      ((L * q : ℕ) : ℝ) ^ 2 * K ≤ 400 * R ^ 6 := by
  have hR0 : 0 < R := by linarith
  let q : ℕ := ⌈R⌉₊
  let L : ℕ := ⌈2 * R + 4⌉₊
  let K : ℕ := ⌈(q : ℝ) * (R + 1)⌉₊
  have hq : R ≤ q := Nat.le_ceil R
  have hL : 2 * R + 4 ≤ L := Nat.le_ceil _
  have hK : (q : ℝ) * (R + 1) ≤ K := Nat.le_ceil _
  have hq0 : 0 < q := Nat.ceil_pos.mpr hR0
  have hL0 : 0 < L := Nat.ceil_pos.mpr (by linarith)
  have hK0 : 0 < K := Nat.ceil_pos.mpr (by positivity)
  have hqbound : (q : ℝ) ≤ 2 * R := by
    have h := Nat.ceil_lt_add_one hR0.le
    dsimp [q]
    linarith
  have hLbound : (L : ℝ) ≤ 4 * R := by
    have h := Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * R + 4)
    dsimp [L]
    linarith
  have hKbound : (K : ℝ) ≤ 4 * R ^ 2 := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ (q : ℝ) * (R + 1))
    have hmul := mul_le_mul_of_nonneg_right hqbound (by linarith : 0 ≤ R + 1)
    dsimp [K]
    nlinarith
  refine ⟨L,q,K,hL0,hq0,hK0,hL,hq,hK,?_⟩
  have hLq : (L : ℝ) * q ≤ 8 * R ^ 2 := by
    have h := mul_le_mul hLbound hqbound (Nat.cast_nonneg q) (by positivity : 0 ≤ 4 * R)
    nlinarith [h]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (L : ℝ) * q) hLq 2
  have hprod := mul_le_mul hsq hKbound (Nat.cast_nonneg K) (by positivity : 0 ≤ (8 * R ^ 2) ^ 2)
  simp only [Nat.cast_mul]
  nlinarith [hprod, pow_nonneg hR0.le 6]

end DiskDiscrepancy
