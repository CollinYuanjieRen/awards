import Erdos574Cycles.Count

/-! # Erdős Problem 574 -/

namespace Erdos574

open Filter Topology

/-- `(3/2)^{4/3} ≤ 7/4`, since `(3/2)^4 = 81/16 ≤ 343/64 = (7/4)^3`. -/
private lemma rpow_three_half_le : (3 / 2 : ℝ) ^ ((4 : ℝ) / 3) ≤ 7 / 4 := by
  have e1 : (3 / 2 : ℝ) ^ ((4 : ℝ) / 3) = ((3 / 2 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_natCast (3 / 2 : ℝ) 4, ← Real.rpow_mul (by norm_num)]
    norm_num
  have e2 : (7 / 4 : ℝ) = ((7 / 4 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_natCast (7 / 4 : ℝ) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [e1, e2]
  exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)

/-- The denominator `(n/2)^{1 + 1/3}` at `n = 3x³` equals `(3/2)^{4/3} x⁴`. -/
private lemma den_eq (x : ℝ) (hx : 0 < x) :
    (3 * x ^ 3 / 2) ^ ((1 : ℝ) + 1 / ((3 : ℕ) : ℝ)) = (3 / 2 : ℝ) ^ ((4 : ℝ) / 3) * x ^ (4 : ℕ) := by
  have hexp : (1 : ℝ) + 1 / ((3 : ℕ) : ℝ) = (4 : ℝ) / 3 := by norm_num
  rw [hexp]
  have h1 : 3 * x ^ 3 / 2 = (3 / 2 : ℝ) * x ^ 3 := by ring
  rw [h1, Real.mul_rpow (by norm_num) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx.le]
  norm_num

/-- The Erdős–Simonovits claim fails for `k = 3`: along `n = 3q³` (`q` prime) the ratio
`ex(n; {C₅, C₆}) / (n/2)^{4/3}` is at least `2 (2/3)^{4/3} > 1`. -/
theorem not_claim_three : ¬ Claim 3 := by
  intro h
  unfold Claim at h
  -- Eventually the ratio is below `11/10`.
  have h2 := (tendsto_order.1 h).2 (11 / 10) (by norm_num)
  rw [eventually_atTop] at h2
  obtain ⟨N, hN⟩ := h2
  -- Choose a prime `q ≥ N` and take `n = 3q³`.
  obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes N
  have := Fact.mk hq
  have hq2 : 2 ≤ q := hq.two_le
  have hn : N ≤ 3 * q ^ 3 := by
    calc N ≤ q := hqN
      _ ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
      _ ≤ 3 * q ^ 3 := Nat.le_mul_of_pos_left _ (by norm_num)
  have key := hN (3 * q ^ 3) hn
  have hQ : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hQpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hcast : ((3 * q ^ 3 : ℕ) : ℝ) = 3 * (q : ℝ) ^ 3 := by push_cast; ring
  rw [hcast, den_eq (q : ℝ) hQpos] at key
  have hQ4 : (0 : ℝ) < (q : ℝ) ^ (4 : ℕ) := by positivity
  have hcpos : (0 : ℝ) < (3 / 2 : ℝ) ^ ((4 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have hdenpos : (0 : ℝ) < (3 / 2 : ℝ) ^ ((4 : ℝ) / 3) * (q : ℝ) ^ (4 : ℕ) := by positivity
  rw [div_lt_iff₀ hdenpos] at key
  -- The graph bound gives `2q⁴` edges, so the ratio is at least `2/(3/2)^{4/3} ≥ 8/7 > 11/10`.
  have hnum : (2 : ℝ) * (q : ℝ) ^ (4 : ℕ) ≤ ((exOddEven (3 * q ^ 3) 3 : ℕ) : ℝ) := by
    have hlow := exOddEven_lower q
    have h' : ((2 * q ^ 4 : ℕ) : ℝ) ≤ ((exOddEven (3 * q ^ 3) 3 : ℕ) : ℝ) := by exact_mod_cast hlow
    push_cast at h'
    linarith
  nlinarith [rpow_three_half_le, hQ4, hcpos]

/-- Erdős Problem 574 (Erdős–Simonovits), answered negatively: it is not true that
`ex(n; {C_{2k−1}, C_{2k}}) = (1 + o(1)) (n/2)^{1 + 1/k}` for every `k ≥ 2`. -/
theorem erdos_574 : ¬ ∀ k : ℕ, 2 ≤ k → Claim k :=
  fun h => not_claim_three (h 3 (by norm_num))

end Erdos574
