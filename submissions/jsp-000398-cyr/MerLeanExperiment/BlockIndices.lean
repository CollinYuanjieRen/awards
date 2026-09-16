import MerLeanExperiment.BlockConstruction

open Filter
open scoped Topology

namespace Erdos492Real

def blockUpperIndex (k b : ℕ) : ℕ := blockCutoff (k + 1) / b - 1

def blockLowerIndex (k : ℕ) : ℕ := blockCutoff (k + 1) / (k + 2) + 1

theorem tendsto_blockCutoff_succ :
    Tendsto (fun k => blockCutoff (k + 1)) atTop atTop := by
  rw [tendsto_atTop]
  intro n
  filter_upwards [eventually_ge_atTop n] with k hk
  exact hk.trans (Nat.le_trans (Nat.le_add_right k 2)
    (nat_succ_le_blockCutoff (k + 1)))

theorem tendsto_blockUpperIndex (b : ℕ) (hb : 0 < b) :
    Tendsto (fun k => blockUpperIndex k b) atTop atTop := by
  have hdiv : Tendsto (fun k => blockCutoff (k + 1) / b) atTop atTop :=
    (Nat.tendsto_div_const_atTop (Nat.ne_of_gt hb)).comp tendsto_blockCutoff_succ
  exact (tendsto_sub_atTop_nat 1).comp hdiv

theorem tendsto_block_index_error (b : ℕ) (hb : 0 < b) :
    Tendsto (fun k => 2 * (blockLowerIndex k : ℝ) /
      (blockUpperIndex k b : ℝ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun k : ℕ => (8 * b : ℝ) / (k + 2)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (8 * b : ℝ))).mul
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1))
    convert h using 1
    · funext k
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
      congr 2
      ring
    · norm_num
  apply squeeze_zero'
  · filter_upwards with k
    positivity
  · have hBlarge : ∀ᶠ k in atTop, 4 * b ≤ blockCutoff (k + 1) :=
      tendsto_blockCutoff_succ (eventually_ge_atTop (4 * b))
    have hTpos : ∀ᶠ k in atTop, 0 < blockUpperIndex k b :=
      (tendsto_blockUpperIndex b hb) (eventually_gt_atTop 0)
    filter_upwards [hBlarge, hTpos] with k hB hTposNat
    let B := blockCutoff (k + 1)
    let q := k + 2
    let d := B / b
    let e := B / q
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hq : 0 < q := by dsimp [q]; omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hBq : q ≤ B := by
      dsimp [q, B]
      exact nat_succ_le_blockCutoff (k + 1)
    have hdcomp : d * b + B % b = B := by
      simpa [d, mul_comm] using (Nat.div_add_mod B b)
    have hecomp : e * q + B % q = B := by
      simpa [e, mul_comm] using (Nat.div_add_mod B q)
    have hrb : B % b < b := Nat.mod_lt _ hb
    have hrq : B % q < q := Nat.mod_lt _ hq
    have hdR : (B : ℝ) / b < d + 1 := by
      have hdcompR : (d : ℝ) * b + (B % b : ℕ) = B := by exact_mod_cast hdcomp
      have hrbR : ((B % b : ℕ) : ℝ) < b := by exact_mod_cast hrb
      apply (div_lt_iff₀ hbR).2
      nlinarith
    have heR : (e : ℝ) ≤ (B : ℝ) / q := by
      have hecompR : (e : ℝ) * q + (B % q : ℕ) = B := by exact_mod_cast hecomp
      apply (le_div_iff₀ hqR).2
      have : (0 : ℝ) ≤ (B % q : ℕ) := by positivity
      nlinarith
    have hepos : 0 < e := Nat.div_pos hBq hq
    have hL : (blockLowerIndex k : ℝ) ≤ 2 * (B : ℝ) / q := by
      change ((e + 1 : ℕ) : ℝ) ≤ _
      norm_num
      apply (le_div_iff₀ hqR).2
      have hecompR : (e : ℝ) * q + (B % q : ℕ) = B := by exact_mod_cast hecomp
      have hBqR : (q : ℝ) ≤ B := by exact_mod_cast hBq
      have hrnonneg : (0 : ℝ) ≤ (B % q : ℕ) := by positivity
      nlinarith
    have hT : (B : ℝ) / (2 * b) ≤ blockUpperIndex k b := by
      change (B : ℝ) / (2 * b) ≤ ((d - 1 : ℕ) : ℝ)
      have hd4 : 4 ≤ d := by
        apply (Nat.le_div_iff_mul_le hb).2
        simpa [B, mul_comm] using hB
      rw [Nat.cast_sub (by omega)]
      have hd4R : (4 : ℝ) ≤ d := by exact_mod_cast hd4
      have heq : (B : ℝ) / (2 * b) = ((B : ℝ) / b) / 2 := by ring
      rw [heq]
      nlinarith [hdR]
    have hBR : (0 : ℝ) < B := by exact_mod_cast blockCutoff_pos (k + 1)
    have hTR : (0 : ℝ) < blockUpperIndex k b := by exact_mod_cast hTposNat
    change 2 * (blockLowerIndex k : ℝ) / (blockUpperIndex k b : ℝ) ≤
      (8 * b : ℝ) / q
    apply (div_le_iff₀ hTR).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hqR).2
    have hLmul : (blockLowerIndex k : ℝ) * q ≤ 2 * B :=
      (le_div_iff₀ hqR).1 hL
    have hTmul : (B : ℝ) ≤ 2 * b * blockUpperIndex k b := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * b)).1 hT
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    nlinarith
  · simpa using hupper

theorem eventually_blockLowerIndex_le_upperIndex (b : ℕ) (hb : 0 < b) :
    ∀ᶠ k in atTop, blockLowerIndex k ≤ blockUpperIndex k b := by
  have herr := (tendsto_block_index_error b hb)
  have hevent : ∀ᶠ k in atTop,
      2 * (blockLowerIndex k : ℝ) / (blockUpperIndex k b : ℝ) < 1 :=
    (tendsto_order.1 herr).2 1 (by norm_num)
  have hTpos : ∀ᶠ k in atTop, 0 < blockUpperIndex k b :=
    (tendsto_blockUpperIndex b hb) (eventually_gt_atTop 0)
  filter_upwards [hevent, hTpos] with k he hT
  by_contra hle
  have hLT : blockUpperIndex k b < blockLowerIndex k := Nat.lt_of_not_ge hle
  have hTR : (0 : ℝ) < blockUpperIndex k b := by exact_mod_cast hT
  have hLTR : (blockUpperIndex k b : ℝ) < blockLowerIndex k := by exact_mod_cast hLT
  have : (2 : ℝ) ≤ 2 * (blockLowerIndex k : ℝ) /
      (blockUpperIndex k b : ℝ) := by
    apply (le_div_iff₀ hTR).2
    nlinarith
  linarith

theorem block_index_window {k b m : ℕ} {α : ℝ} (hb : 2 ≤ b)
    (hbk : b ≤ k + 2) (hαlo : 1 / (b : ℝ) ≤ α) (hαhi : α ≤ b)
    (hB : b ≤ blockCutoff (k + 1))
    (hmlo : blockLowerIndex k ≤ m) (hmhi : m ≤ blockUpperIndex k b) :
    (blockCutoff k : ℝ) + 1 ≤ m * α ∧
      m * α < blockCutoff (k + 1) ∧ m ≤ blockCutoff (k + 1) := by
  have hbpos : 0 < b := by omega
  have hkpos : 0 < k + 2 := by omega
  have hlowNat : blockCutoff (k + 1) < (k + 2) * m := by
    have hdiv : blockCutoff (k + 1) / (k + 2) < m := by
      simpa [blockLowerIndex] using hmlo
    simpa [mul_comm] using (Nat.div_lt_iff_lt_mul hkpos).1 hdiv
  have huppNat : m * b < blockCutoff (k + 1) := by
    let q := blockCutoff (k + 1) / b
    have hq : 0 < q := Nat.div_pos hB hbpos
    have hmdiv : m < blockCutoff (k + 1) / b := by
      change m ≤ q - 1 at hmhi
      change m < q
      omega
    exact ((Nat.lt_div_iff_mul_lt hbpos).1 hmdiv).trans_le (Nat.sub_le _ _)
  have hmB : m ≤ blockCutoff (k + 1) := by
    exact (Nat.le_mul_of_pos_right m hbpos).trans (Nat.le_of_lt huppNat)
  have hlowR : (blockCutoff (k + 1) : ℝ) < (k + 2) * m := by
    exact_mod_cast hlowNat
  have huppR : (m : ℝ) * b < blockCutoff (k + 1) := by
    exact_mod_cast huppNat
  have hBk : (blockCutoff (k + 1) : ℝ) =
      4 * (k + 2) ^ 2 * blockCutoff k := by
    norm_num [blockCutoff_succ]
  have hbR : (b : ℝ) ≤ k + 2 := by exact_mod_cast hbk
  have hbposR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hkposR : (0 : ℝ) < k + 2 := by positivity
  constructor
  · have hmpos : (0 : ℝ) < m := by
      have : 0 < m := by
        by_contra hm
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        simp at hlowNat
      exact_mod_cast this
    have hαpos : 0 < α := lt_of_lt_of_le (one_div_pos.mpr hbposR) hαlo
    rw [hBk] at hlowR
    have hmul : 4 * (b : ℝ) * blockCutoff k < m := by
      nlinarith [show (0 : ℝ) < blockCutoff k by exact_mod_cast blockCutoff_pos k]
    have hprod : 4 * (blockCutoff k : ℝ) < (m : ℝ) / b := by
      apply (lt_div_iff₀ hbposR).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
    have hma : (m : ℝ) / b ≤ m * α := by
      rw [div_eq_mul_inv, mul_comm]
      simpa [one_div, mul_comm] using
        mul_le_mul_of_nonneg_left hαlo hmpos.le
    have hBkpos : (1 : ℝ) ≤ blockCutoff k := by
      exact_mod_cast (blockCutoff_pos k)
    nlinarith
  · constructor
    · nlinarith [mul_le_mul_of_nonneg_left hαhi (Nat.cast_nonneg m)]
    · exact hmB

end Erdos492Real
