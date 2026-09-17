import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős #381, lower bound: the Dirichlet approximation step (§3.2)

Erdős's proof of the gap theorem picks, for a highly composite `n` with largest prime factor
`p` and `q` the largest prime with exponent `≥ 2`, two positive integers `s` and `t` with

  `s ≤ p ^ A`,   `|s · δ − t| ≤ p ^ (−A)`,   `δ := log q / log p ∈ (1/2, 1)`,

and deduces `1 ≤ t ≤ p ^ A + 1`.  This file provides exactly that step, on top of Mathlib's
`Real.exists_int_int_abs_mul_sub_le`, together with the logarithmic form
`|t · log p − s · log q| ≤ p ^ (−A) · log p` that the size estimate of §3.5 consumes.

The exponent `A` is a parameter here; §3.5 pins it to `A = 1/(8L)`, which satisfies the
constraint `A < 1/(4L)` of the digest's correction to `scope.md`.
-/

namespace Erdos381Lower

open Filter

/-- **The Dirichlet step of §3.2.**  For reals `p > 1` and `q` whose logarithmic ratio
`δ = log q / log p` lies strictly between `1/2` and `1`, and for an exponent `A` with
`p ^ A > 2`, there are positive naturals `s`, `t` with `t ≤ s ≤ p ^ A` (hence
`t ≤ p ^ A + 1`) approximating `δ` to within `p ^ (−A)`, both in the fractional form
`|s·δ − t| ≤ p ^ (−A)` and in the logarithmic form
`|t·log p − s·log q| ≤ p ^ (−A) · log p`. -/
theorem exists_dirichlet_pair {p q A : ℝ} (hp : 1 < p) (hpA : 2 < p ^ A)
    (hlow : 1 / 2 < Real.log q / Real.log p) (hhigh : Real.log q / Real.log p < 1) :
    ∃ s t : ℕ, 1 ≤ s ∧ 1 ≤ t ∧ t ≤ s ∧ (s : ℝ) ≤ p ^ A ∧ (t : ℝ) ≤ p ^ A + 1 ∧
      |(s : ℝ) * (Real.log q / Real.log p) - (t : ℝ)| ≤ p ^ (-A) ∧
      |(t : ℝ) * Real.log p - (s : ℝ) * Real.log q| ≤ p ^ (-A) * Real.log p := by
  set δ : ℝ := Real.log q / Real.log p with hδ
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hpA0 : (0 : ℝ) < p ^ A := lt_trans two_pos hpA
  set N : ℕ := ⌊p ^ A⌋₊ with hNdef
  have hNfloor : (N : ℝ) ≤ p ^ A := Nat.floor_le hpA0.le
  have hNlt : p ^ A < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hpA.le)
  have hNpos : 0 < N := by omega
  obtain ⟨j, k, hk0, hkN, hjk⟩ := Real.exists_int_int_abs_mul_sub_le δ hNpos
  have hbd : (1 : ℝ) / ((N : ℝ) + 1) ≤ p ^ (-A) := by
    rw [Real.rpow_neg hp0.le, ← one_div]
    gcongr
  have hhalf : (1 : ℝ) / ((N : ℝ) + 1) < 1 / 2 := by
    refine hbd.trans_lt ?_
    rw [Real.rpow_neg hp0.le, ← one_div]
    exact one_div_lt_one_div_of_lt two_pos hpA
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hjk1 : (k : ℝ) * δ - (j : ℝ) ≤ 1 / ((N : ℝ) + 1) := (abs_le.1 hjk).2
  have hjk2 : -(1 / ((N : ℝ) + 1)) ≤ (k : ℝ) * δ - (j : ℝ) := (abs_le.1 hjk).1
  have hkδ : δ ≤ (k : ℝ) * δ := le_mul_of_one_le_left (by linarith) hk1
  have hkδ' : (k : ℝ) * δ < (k : ℝ) := by nlinarith
  have hjpos : (0 : ℤ) < j := by
    by_contra hcon
    have : (j : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 hcon
    linarith
  have hjk_le : j ≤ k := by
    have hlt : (j : ℝ) < (k : ℝ) + 1 := by linarith
    exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast hlt)
  refine ⟨k.toNat, j.toNat, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · have : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0.le
    rw [this]
    exact le_trans (by exact_mod_cast hkN) hNfloor
  · have : (j.toNat : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hjpos.le
    rw [this]
    have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk_le
    have hkR : (k : ℝ) ≤ p ^ A := le_trans (by exact_mod_cast hkN) hNfloor
    linarith
  · have h1 : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0.le
    have h2 : (j.toNat : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hjpos.le
    rw [h1, h2]
    exact hjk.trans hbd
  · have h1 : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0.le
    have h2 : (j.toNat : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hjpos.le
    have hq : Real.log q = δ * Real.log p := by
      rw [hδ]; field_simp
    have hrw : (j.toNat : ℝ) * Real.log p - (k.toNat : ℝ) * Real.log q =
        -(((k.toNat : ℝ) * δ - (j.toNat : ℝ)) * Real.log p) := by
      rw [hq]; ring
    rw [hrw, abs_neg, abs_mul, abs_of_pos hlogp]
    refine mul_le_mul_of_nonneg_right ?_ hlogp.le
    rw [h1, h2]
    exact hjk.trans hbd

end Erdos381Lower
