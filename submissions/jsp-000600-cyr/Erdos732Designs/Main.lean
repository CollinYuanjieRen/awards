import Mathlib
import Erdos732Designs.Design
import Erdos732Designs.LargeBlocks
import Erdos732Designs.Encoding

/-!
# Erdős Problem 732: the upper bound

Erdős ([Er81], see erdosproblems.com/732) stated, and Alon (remark191.pdf, §3) proved, that
the number of block-compatible sequences for `n` is at most `exp(O(√n log n))`.  Together
with Alon's lower bound (formalized in plby/lean-proofs as `Erdos732.erdos_732`) this
settles the counting question of Problem 732.

We take `T = Nat.sqrt (2 * n) + 1`, so `2 * n < T * T`, and combine the explicit bound of
`Encoding.lean` with `T ≤ 2 √n + 1`.
-/

open Finset Real

namespace Erdos732Upper

/-- **Erdős Problem 732, upper bound (Erdős; proof in Alon, remark191 §3).**
There are absolute constants `C > 0` and `N` such that for every `n ≥ N` the set of
block-compatible multisets for `n` is finite and has at most `exp (C √n log n)` elements. -/
theorem erdos_732_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      {S : Multiset ℕ | BlockCompatible n S}.Finite ∧
        (({S : Multiset ℕ | BlockCompatible n S}.ncard : ℝ) ≤
          Real.exp (C * Real.sqrt n * Real.log n)) := by
  refine ⟨56, by norm_num, 2, fun n hn => ?_⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = Nat.sqrt (2 * n) + 1 := ⟨_, rfl⟩
  have hT : 2 * n < T * T := by
    rw [hTdef]
    exact Nat.lt_succ_sqrt (2 * n)
  obtain ⟨hfin, hcard⟩ := blockCompatible_finite_and_ncard_le n T hT
  refine ⟨hfin, ?_⟩
  -- Step 1: a crude bound in `ℕ`: `explicitBound n T ≤ (n + 1) ^ (8 * T + 4)`.
  have hT2 : T ≤ (n + 1) ^ 2 := by
    have := Nat.sqrt_le_self (2 * n)
    nlinarith [hTdef]
  have hB4 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : n * n + 1 ≤ (n + 1) ^ 4 := le_trans (by nlinarith) hB4
  have h2 : T ≤ (n + 1) ^ 4 := hT2.trans hB4
  have h3 : T * (n + 1) + 1 ≤ (n + 1) ^ 4 :=
    calc T * (n + 1) + 1 ≤ (n + 1) ^ 2 * (n + 1) + 1 := by gcongr
      _ ≤ (n + 1) ^ 3 + (n + 1) ^ 3 := by
        rw [← pow_succ]; gcongr; exact Nat.one_le_pow _ _ (by omega)
      _ = 2 * (n + 1) ^ 3 := by ring
      _ ≤ (n + 1) * (n + 1) ^ 3 := by gcongr; omega
      _ = (n + 1) ^ 4 := by ring
  have hbound : explicitBound n T ≤ (n + 1) ^ (8 * T + 4) := by
    unfold explicitBound
    calc (n * n + 1) ^ T * (T * (T * (n + 1) + 1) ^ T)
        ≤ ((n + 1) ^ 4) ^ T * ((n + 1) ^ 4 * ((n + 1) ^ 4) ^ T) := by gcongr
      _ = (n + 1) ^ (8 * T + 4) := by
        rw [show 8 * T + 4 = 4 * T + (4 + 4 * T) by ring, pow_add, pow_add, pow_mul]
  -- Step 2: cast to `ℝ` and rewrite the power as an exponential.
  have hcardR : ({S : Multiset ℕ | BlockCompatible n S}.ncard : ℝ) ≤
      ((n : ℝ) + 1) ^ (8 * T + 4) := by
    exact_mod_cast hcard.trans hbound
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine hcardR.trans ?_
  rw [← Real.exp_log hpos, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  -- Step 3: compare exponents.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 hn1
  have hsqrt2 : (Nat.sqrt (2 * n) : ℝ) ≤ 2 * Real.sqrt n :=
    calc (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt ((2 * n : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt ((2 * Real.sqrt n) ^ 2) := by
        apply Real.sqrt_le_sqrt
        push_cast
        nlinarith [Real.sq_sqrt (n.cast_nonneg : (0 : ℝ) ≤ n)]
      _ = 2 * Real.sqrt n := Real.sqrt_sq (by positivity)
  have hm : ((8 * T + 4 : ℕ) : ℝ) ≤ 28 * Real.sqrt n := by
    rw [hTdef]
    push_cast
    linarith
  have hlog : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n :=
    calc Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log hpos (by nlinarith)
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hlog1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  calc ((8 * T + 4 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1)
      ≤ (28 * Real.sqrt n) * (2 * Real.log n) :=
        mul_le_mul hm hlog hlog1 (by positivity)
    _ = 56 * Real.sqrt n * Real.log n := by ring

end Erdos732Upper
