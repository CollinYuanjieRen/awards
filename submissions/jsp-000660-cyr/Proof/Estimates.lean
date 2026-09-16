import Mathlib
import Proof.Counting

/-!
# Real-number estimates

For `n ≥ 2 ^ 40` and `1 ≤ m ≤ n` the union-bound term satisfies `badBound n m ≤ 2⁻ᵐ`, so the
sum over `m` is below `1`.  The two regimes are `m ≤ n ^ (1/4)` (use the block-size lower bound
`√n / 2`) and `m > n ^ (1/4)` (use `m · 2 ^ rpar m`), following Alon.  Also
`rpar m ≤ 4 √(log₂ m) + 24` and `4 √(log₂ m) + 16 ≤ rpar m`.
-/

open Finset

namespace Erdos803

/-- `Nat.log 2 m` is the floor of `Real.logb 2 m`, so it is at most `Real.logb 2 m`. -/
private lemma natLog_le_logb (m : ℕ) (hm : 1 ≤ m) : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  have hfloor : ⌊Real.logb 2 m⌋₊ = Nat.log 2 m := by
    have h := Real.natFloor_logb_natCast 2 m
    norm_num at h
    exact h
  have hnn : (0 : ℝ) ≤ Real.logb 2 m :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  rw [← hfloor]
  exact Nat.floor_le hnn

/-- `Real.logb 2 m` is below `Nat.log 2 m + 1`. -/
private lemma logb_le_natLog_add_one (m : ℕ) : Real.logb 2 m ≤ (Nat.log 2 m : ℝ) + 1 := by
  have hfloor : ⌊Real.logb 2 m⌋₊ = Nat.log 2 m := by
    have h := Real.natFloor_logb_natCast 2 m
    norm_num at h
    exact h
  have h := Nat.lt_floor_add_one (Real.logb 2 m)
  rw [hfloor] at h
  exact h.le

/-- `√(log₂ m) ≤ ⌊√⌊log₂ m⌋⌋ + 1`. -/
private lemma sqrt_logb_le (m : ℕ) :
    Real.sqrt (Real.logb 2 m) ≤ (Nat.sqrt (Nat.log 2 m) : ℝ) + 1 := by
  have hnat : Nat.log 2 m + 1 ≤ (Nat.sqrt (Nat.log 2 m) + 1) * (Nat.sqrt (Nat.log 2 m) + 1) :=
    Nat.lt_succ_sqrt (Nat.log 2 m)
  have hcast : (Nat.log 2 m : ℝ) + 1 ≤ ((Nat.sqrt (Nat.log 2 m) : ℝ) + 1) ^ 2 := by
    have h := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at h
    nlinarith [h]
  have h1 : Real.logb 2 m ≤ ((Nat.sqrt (Nat.log 2 m) : ℝ) + 1) ^ 2 :=
    le_trans (logb_le_natLog_add_one m) hcast
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity)] at h2

/-- `⌊√⌊log₂ m⌋⌋ ≤ √(log₂ m)` for `m ≥ 1`. -/
private lemma natSqrt_le_sqrt_logb (m : ℕ) (hm : 1 ≤ m) :
    (Nat.sqrt (Nat.log 2 m) : ℝ) ≤ Real.sqrt (Real.logb 2 m) := by
  refine le_trans Real.nat_sqrt_le_real_sqrt ?_
  exact Real.sqrt_le_sqrt (natLog_le_logb m hm)

theorem le_rpar (m : ℕ) (hm : 1 ≤ m) : 4 * Real.sqrt (Real.logb 2 m) + 16 ≤ rpar m := by
  have h := sqrt_logb_le m
  have hlogb : (0 : ℝ) ≤ Real.logb 2 m :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  have hr : (rpar m : ℝ) = 4 * ((Nat.sqrt (Nat.log 2 m) : ℝ) + 1) + 16 := by
    unfold rpar
    push_cast
    ring
  rw [hr]
  linarith [h, hlogb]

theorem rpar_le (m : ℕ) (hm : 1 ≤ m) : (rpar m : ℝ) ≤ 4 * Real.sqrt (Real.logb 2 m) + 24 := by
  have h := natSqrt_le_sqrt_logb m hm
  have hr : (rpar m : ℝ) = 4 * ((Nat.sqrt (Nat.log 2 m) : ℝ) + 1) + 16 := by
    unfold rpar
    push_cast
    ring
  rw [hr]
  linarith

theorem sixteen_le_rpar (m : ℕ) : 16 ≤ rpar m := by
  unfold rpar
  omega

/-- `k! ≥ (k / 3) ^ k`. -/
theorem pow_div_three_le_factorial (k : ℕ) : ((k : ℝ) / 3) ^ k ≤ k.factorial := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : ((k : ℝ) / 3) ^ k ≤ ((k : ℝ) / Real.exp 1) ^ k := by
    gcongr
  have h2 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * k) := by
    have hle : Real.sqrt 1 ≤ Real.sqrt (2 * Real.pi * k) :=
      Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
    simpa using hle
  calc ((k : ℝ) / 3) ^ k ≤ ((k : ℝ) / Real.exp 1) ^ k := h1
    _ ≤ Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k :=
        le_mul_of_one_le_left (by positivity) h2
    _ ≤ (k.factorial : ℝ) := Stirling.le_factorial_stirling k

/-- `C(a, k) ≤ (3 a / k) ^ k` for `k ≥ 1`. -/
theorem choose_le_pow_three_mul_div (a k : ℕ) (hk : 1 ≤ k) :
    (a.choose k : ℝ) ≤ (3 * a / k : ℝ) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < ((k : ℝ) / 3) ^ k := by positivity
  calc (a.choose k : ℝ) ≤ (a : ℝ) ^ k / (k.factorial : ℝ) := Nat.choose_le_pow_div k a
    _ ≤ (a : ℝ) ^ k / ((k : ℝ) / 3) ^ k :=
        div_le_div_of_nonneg_left (by positivity) hpos (pow_div_three_le_factorial k)
    _ = (3 * a / k : ℝ) ^ k := by
        have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
        rw [div_pow, div_pow]
        field_simp
        ring

/-- `(m + 1) ^ 2 ≤ 4 ^ m` over the reals. -/
private lemma sq_add_one_le_four_pow (m : ℕ) : ((m : ℝ) + 1) ^ 2 ≤ 4 ^ m := by
  have h1 : m + 1 ≤ 2 ^ m := m.lt_two_pow_self
  have h2 : (m + 1) ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : ((2 : ℕ) ^ m) ^ 2 = 4 ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h3] at h2
  exact_mod_cast h2

/-- Reduction step shared by the two regimes of `badBound_le`. -/
private lemma badBound_le_of (n m : ℕ) (D : ℝ) (hm : 1 ≤ m) (hn : 0 < n) (hD0 : 0 ≤ D)
    (hpow : ((3 * (m : ℝ) / rpar m) *
        min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m) ≤ D ^ m)
    (hfin : 4 * (4 * (n : ℝ) ^ 2) * D ≤ 1 / 2) :
    badBound n m ≤ (1 / 2 : ℝ) ^ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 16 ≤ rpar m := sixteen_le_rpar m
  have hr0 : (0 : ℝ) < rpar m := by
    have h : (0 : ℕ) < rpar m := by omega
    exact_mod_cast h
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hXpos : 0 < min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) :=
    lt_min (by positivity) (by positivity)
  set X : ℝ := min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) with hXdef
  have hk : 1 ≤ m * rpar m := by
    have h : 0 < m * rpar m := Nat.mul_pos hm (by omega)
    omega
  have hchoose : (((m ^ 2).choose (m * rpar m) : ℕ) : ℝ)
      ≤ (3 * (m : ℝ) / rpar m) ^ (m * rpar m) := by
    have h := choose_le_pow_three_mul_div (m ^ 2) (m * rpar m) hk
    have he : (3 * ((m ^ 2 : ℕ) : ℝ) / ((m * rpar m : ℕ) : ℝ))
        = 3 * (m : ℝ) / (rpar m : ℝ) := by
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rwa [he] at h
  have e1 : (2 * (n : ℝ)) ^ (2 * m) = (4 * (n : ℝ) ^ 2) ^ m := by
    rw [pow_mul]
    congr 1
    ring
  have hc : (((m ^ 2).choose (m * rpar m) : ℕ) : ℝ) * X ^ (m * rpar m) ≤ D ^ m := by
    calc (((m ^ 2).choose (m * rpar m) : ℕ) : ℝ) * X ^ (m * rpar m)
        ≤ (3 * (m : ℝ) / rpar m) ^ (m * rpar m) * X ^ (m * rpar m) := by gcongr
      _ = ((3 * (m : ℝ) / rpar m) * X) ^ (m * rpar m) := (mul_pow _ _ _).symm
      _ ≤ D ^ m := hpow
  calc badBound n m
      = (((m : ℝ) + 1) ^ 2 * (2 * (n : ℝ)) ^ (2 * m)) *
          ((((m ^ 2).choose (m * rpar m) : ℕ) : ℝ) * X ^ (m * rpar m)) := by
        rw [badBound, hXdef]
        ring
    _ ≤ ((4 : ℝ) ^ m * (4 * (n : ℝ) ^ 2) ^ m) * D ^ m := by
        rw [e1]
        refine mul_le_mul ?_ hc (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (sq_add_one_le_four_pow m) (by positivity)
    _ = (4 * (4 * (n : ℝ) ^ 2) * D) ^ m := by
        rw [← mul_pow, ← mul_pow]
    _ ≤ (1 / 2 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) hfin m

/-- In the large-`m` regime `32 n ^ 2 ≤ 2 ^ (rpar m) ^ 2`. -/
private lemma thirtytwo_mul_sq_le (n m : ℕ) (h : n < m ^ 4) :
    32 * n ^ 2 ≤ 2 ^ (rpar m * rpar m) := by
  have hLs : Nat.log 2 m + 1 ≤ (Nat.sqrt (Nat.log 2 m) + 1) * (Nat.sqrt (Nat.log 2 m) + 1) :=
    Nat.lt_succ_sqrt (Nat.log 2 m)
  have h6 : 8 * Nat.log 2 m + 13 ≤ rpar m * rpar m := by
    unfold rpar
    nlinarith [hLs, Nat.zero_le (Nat.sqrt (Nat.log 2 m)), Nat.zero_le (Nat.log 2 m)]
  have hmlog : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have h1 : n ^ 2 < (m ^ 4) ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
  have h3 : (m ^ 4) ^ 2 < (2 ^ (Nat.log 2 m + 1)) ^ 8 := by
    have hrw : (m ^ 4) ^ 2 = m ^ 8 := by ring
    rw [hrw]
    exact Nat.pow_lt_pow_left hmlog (by norm_num)
  have h4 : ((2 : ℕ) ^ (Nat.log 2 m + 1)) ^ 8 = 2 ^ (8 * Nat.log 2 m + 8) := by
    rw [← pow_mul]
    congr 1
    ring
  have h5 : 32 * n ^ 2 ≤ 2 ^ (8 * Nat.log 2 m + 13) := by
    have hlt : n ^ 2 < 2 ^ (8 * Nat.log 2 m + 8) := by
      rw [← h4]
      exact lt_trans h1 h3
    calc 32 * n ^ 2 ≤ 32 * 2 ^ (8 * Nat.log 2 m + 8) := by omega
      _ = 2 ^ (8 * Nat.log 2 m + 13) := by
          rw [show 8 * Nat.log 2 m + 13 = 8 * Nat.log 2 m + 8 + 5 by ring, pow_add]
          ring
  exact h5.trans (Nat.pow_le_pow_right (by norm_num) h6)

theorem badBound_le (n m : ℕ) (hn : 2 ^ 40 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n) :
    badBound n m ≤ (1 / 2 : ℝ) ^ m := by
  have hn' : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : 16 ≤ rpar m := sixteen_le_rpar m
  have hr0 : (0 : ℝ) < rpar m := by
    have h : (0 : ℕ) < rpar m := by omega
    exact_mod_cast h
  have hr16 : (16 : ℝ) ≤ rpar m := by exact_mod_cast hr
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hsqsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hnbig : (2 : ℝ) ^ 40 ≤ (n : ℝ) := by exact_mod_cast hn
  have hmn1 : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans hm1 hmn1
  have hXpos : 0 < min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) :=
    lt_min (by positivity) (by positivity)
  rcases le_or_gt (m ^ 4) n with hcase | hcase
  · -- Small `m`: use the `2 / √n` block bound.
    refine badBound_le_of n m (1 / (2 ^ 16 * (n : ℝ) ^ 4)) hm hn' (by positivity) ?_ ?_
    · have hm4 : ((m : ℝ) ^ 2) ^ 2 ≤ (n : ℝ) := by
        have h' : ((m : ℝ) ^ 4) ≤ (n : ℝ) := by exact_mod_cast hcase
        calc ((m : ℝ) ^ 2) ^ 2 = (m : ℝ) ^ 4 := by ring
          _ ≤ (n : ℝ) := h'
      have hms : (m : ℝ) ^ 2 ≤ Real.sqrt n := by
        calc (m : ℝ) ^ 2 = Real.sqrt (((m : ℝ) ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
          _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hm4
      have hbase : (3 * (m : ℝ) / rpar m) *
          min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) ≤ (m : ℝ) / (2 * Real.sqrt n) := by
        have h1 : min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) ≤ 2 / Real.sqrt n :=
          min_le_right _ _
        have h2 : 3 * (m : ℝ) / rpar m ≤ 3 * (m : ℝ) / 16 := by gcongr
        have h3 : (3 * (m : ℝ) / rpar m) *
            min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) ≤ (3 * (m : ℝ) / 16) *
              (2 / Real.sqrt n) :=
          mul_le_mul h2 h1 hXpos.le (by positivity)
        refine h3.trans ?_
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hsq, hm0]
      have hu0 : (0 : ℝ) ≤ (m : ℝ) / (2 * Real.sqrt n) := by positivity
      have hu1 : (m : ℝ) / (2 * Real.sqrt n) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [hms, hm1, hsq]
      have hstep : ((3 * (m : ℝ) / rpar m) *
          min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m)
          ≤ ((m : ℝ) / (2 * Real.sqrt n)) ^ (m * rpar m) :=
        pow_le_pow_left₀ (by positivity) hbase _
      have hexp : 16 * m ≤ m * rpar m := by
        calc 16 * m = m * 16 := by ring
          _ ≤ m * rpar m := Nat.mul_le_mul_left m hr
      have hstep2 : ((m : ℝ) / (2 * Real.sqrt n)) ^ (m * rpar m)
          ≤ ((m : ℝ) / (2 * Real.sqrt n)) ^ (16 * m) :=
        pow_le_pow_of_le_one hu0 hu1 hexp
      have hm16 : ((m : ℝ) ^ 16) ≤ (n : ℝ) ^ 4 := by
        have hnat : (m ^ 4) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left hcase 4
        have h' : ((m : ℝ) ^ 4) ^ 4 ≤ (n : ℝ) ^ 4 := by exact_mod_cast hnat
        calc (m : ℝ) ^ 16 = ((m : ℝ) ^ 4) ^ 4 := by ring
          _ ≤ (n : ℝ) ^ 4 := h'
      have hsqrt16 : Real.sqrt n ^ 16 = (n : ℝ) ^ 8 := by
        rw [show (16 : ℕ) = 2 * 8 by norm_num, pow_mul, hsqsq]
      have hD : ((m : ℝ) / (2 * Real.sqrt n)) ^ 16 ≤ 1 / (2 ^ 16 * (n : ℝ) ^ 4) := by
        rw [div_pow, mul_pow, hsqrt16, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hm16 (le_of_lt (pow_pos hn0 4))]
      calc ((3 * (m : ℝ) / rpar m) *
            min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m)
          ≤ ((m : ℝ) / (2 * Real.sqrt n)) ^ (16 * m) := hstep.trans hstep2
        _ = (((m : ℝ) / (2 * Real.sqrt n)) ^ 16) ^ m := by rw [pow_mul]
        _ ≤ (1 / (2 ^ 16 * (n : ℝ) ^ 4)) ^ m := pow_le_pow_left₀ (by positivity) hD m
    · have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hn1]
      have hn24 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
        nlinarith [hn2, sq_nonneg ((n : ℝ) ^ 2 - 1)]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hn24, pow_pos hn0 2]
  · -- Large `m`: use the `1 / (m 2 ^ r)` block bound.
    refine badBound_le_of n m (1 / (2 : ℝ) ^ (rpar m * rpar m)) hm hn' (by positivity) ?_ ?_
    · have hbase : (3 * (m : ℝ) / rpar m) *
          min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) ≤ 1 / (2 : ℝ) ^ rpar m := by
        have h1 : min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)
            ≤ 1 / (m * 2 ^ rpar m : ℝ) := min_le_left _ _
        have h2 : (3 * (m : ℝ) / rpar m) * (1 / (m * 2 ^ rpar m : ℝ))
            = 3 / ((rpar m : ℝ) * 2 ^ rpar m) := by
          rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
          ring
        have h3 : (3 * (m : ℝ) / rpar m) *
            min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)
            ≤ (3 * (m : ℝ) / rpar m) * (1 / (m * 2 ^ rpar m : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        rw [h2] at h3
        refine h3.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hr16
          (le_of_lt (pow_pos (show (0 : ℝ) < 2 by norm_num) (rpar m))),
          pow_pos (show (0 : ℝ) < 2 by norm_num) (rpar m)]
      have hstep : ((3 * (m : ℝ) / rpar m) *
          min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m)
          ≤ (1 / (2 : ℝ) ^ rpar m) ^ (m * rpar m) :=
        pow_le_pow_left₀ (by positivity) hbase _
      refine hstep.trans_eq ?_
      rw [mul_comm m (rpar m), pow_mul, div_pow, one_pow, ← pow_mul]
    · have hkey : (32 : ℝ) * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ (rpar m * rpar m) := by
        have h := thirtytwo_mul_sq_le n m hcase
        exact_mod_cast h
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hkey]

/-- The geometric sum `∑_{m=1}^{n} 2⁻ᵐ` equals `1 - 2⁻ⁿ`. -/
private lemma sum_geom_Icc (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ m = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem sum_badBound_lt_one (n : ℕ) (hn : 2 ^ 40 ≤ n) :
    ∑ m ∈ Finset.Icc 1 n, badBound n m < 1 := by
  have h1 : ∑ m ∈ Finset.Icc 1 n, badBound n m
      ≤ ∑ m ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ m := by
    refine Finset.sum_le_sum fun m hm ↦ ?_
    rw [Finset.mem_Icc] at hm
    exact badBound_le n m hn hm.1 hm.2
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  rw [sum_geom_Icc n] at h1
  linarith

end Erdos803
