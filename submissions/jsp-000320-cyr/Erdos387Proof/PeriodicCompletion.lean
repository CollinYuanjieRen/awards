import Erdos387Proof.PeriodicStripping
import ErdosProblems.Erdos387.SquarefreeKloostermanBound

/-!
# Completion of arbitrary periodic intervals

A finite interval is split into complete periods and one residual interval.
The generic estimate is then specialized to the zero-extended inverse phase
appearing in the fixed-factor squarefree Kloosterman bound.
-/

namespace Erdos387Proof.PeriodicCompletion

open scoped BigOperators
open Erdos387Proof.PeriodicStripping

theorem intervalSum_add (A : ℤ) (L R : ℕ) (f : ℤ → ℂ) :
    intervalSum A (L + R) f =
      intervalSum A L f + intervalSum (A + L) R f := by
  simp [intervalSum, Finset.sum_range_add, Nat.cast_add, add_assoc]

theorem intervalSum_add_one_eq_of_periodic
    (A : ℤ) (q : ℕ) (f : ℤ → ℂ)
    (hperiod : Function.Periodic f (q : ℤ)) :
    intervalSum (A + 1) q f = intervalSum A q f := by
  apply sub_eq_zero.mp
  calc
    intervalSum (A + 1) q f - intervalSum A q f =
        intervalSum (A + q) 1 f - intervalSum A 1 f :=
      intervalSum_shift_sub A q 1 f
    _ = 0 := sub_eq_zero.mpr (by
      simpa [intervalSum] using hperiod A)

theorem intervalSum_full_period_eq
    (A : ℤ) (q : ℕ) (f : ℤ → ℂ)
    (hperiod : Function.Periodic f (q : ℤ)) :
    intervalSum A q f = intervalSum 0 q f := by
  induction A using Int.induction_on with
  | zero => rfl
  | succ A ih =>
      exact (intervalSum_add_one_eq_of_periodic A q f hperiod).trans ih
  | pred A ih =>
      have hstep := intervalSum_add_one_eq_of_periodic
        (-(A : ℤ) - 1) q f hperiod
      have hstep' : intervalSum (-(A : ℤ) - 1) q f =
          intervalSum (-(A : ℤ)) q f := by
        simpa using hstep.symm
      exact hstep'.trans ih

theorem intervalSum_blocks
    (A : ℤ) (q k r : ℕ) (f : ℤ → ℂ)
    (hperiod : Function.Periodic f (q : ℤ)) :
    intervalSum A (k * q + r) f =
      (k : ℂ) * intervalSum 0 q f + intervalSum (A + k * q) r f := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
      calc
        intervalSum A ((k + 1) * q + r) f =
            intervalSum A (q + (k * q + r)) f := by
              congr 1
              ring
        _ = intervalSum A q f + intervalSum (A + q) (k * q + r) f :=
          intervalSum_add A q (k * q + r) f
        _ = intervalSum 0 q f +
            ((k : ℂ) * intervalSum 0 q f +
              intervalSum ((A + q) + k * q) r f) := by
          rw [intervalSum_full_period_eq A q f hperiod,
            ih (A := A + q)]
        _ = ((k + 1 : ℕ) : ℂ) * intervalSum 0 q f +
            intervalSum (A + (k + 1) * q) r f := by
          rw [show ((A + q) + k * q : ℤ) = A + (k + 1) * q by
            ring]
          push_cast
          ring

/-- Sharp generic block estimate: complete periods cost `B`, while the final
residual interval is bounded term by term. -/
theorem norm_intervalSum_le_div_mul_add_mod
    (A : ℤ) (L q : ℕ) (f : ℤ → ℂ) (B : ℝ)
    (_hq : 0 < q) (hperiod : Function.Periodic f (q : ℤ))
    (hterm : ∀ n, ‖f n‖ ≤ 1)
    (hcomplete : ‖intervalSum 0 q f‖ ≤ B) :
    ‖intervalSum A L f‖ ≤
      ((L / q : ℕ) : ℝ) * B + (L % q : ℕ) := by
  let k := L / q
  let r := L % q
  have hL : L = k * q + r := by
    simpa [k, r, Nat.mul_comm] using (Nat.div_add_mod L q).symm
  have hmain : ‖(k : ℂ) * intervalSum 0 q f‖ ≤ (k : ℝ) * B := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hcomplete (Nat.cast_nonneg k)
  have hrem : ‖intervalSum (A + k * q) r f‖ ≤ (r : ℝ) :=
    norm_intervalSum_le _ _ f hterm
  have hblocks := intervalSum_blocks A q k r f hperiod
  rw [← hL] at hblocks
  rw [hblocks]
  exact (norm_add_le _ _).trans (add_le_add hmain hrem)

/-- If every interval of length at most one period has bound `B`, arbitrary
lengths cost at most one `B` for each complete period and one for the
remainder. -/
theorem norm_intervalSum_le_div_add_one_mul
    (A : ℤ) (L q : ℕ) (f : ℤ → ℂ) (B : ℝ)
    (hq : 0 < q) (hperiod : Function.Periodic f (q : ℤ))
    (_hB : 0 ≤ B)
    (hshort : ∀ A' m, m ≤ q → ‖intervalSum A' m f‖ ≤ B) :
    ‖intervalSum A L f‖ ≤ ((L / q + 1 : ℕ) : ℝ) * B := by
  let k := L / q
  let r := L % q
  have hL : L = k * q + r := by
    simpa [k, r, Nat.mul_comm] using (Nat.div_add_mod L q).symm
  have hmain : ‖(k : ℂ) * intervalSum 0 q f‖ ≤ (k : ℝ) * B := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hshort 0 q le_rfl)
      (Nat.cast_nonneg k)
  have hrem : ‖intervalSum (A + k * q) r f‖ ≤ B :=
    hshort _ _ (Nat.le_of_lt (Nat.mod_lt L hq))
  have hblocks := intervalSum_blocks A q k r f hperiod
  rw [← hL] at hblocks
  rw [hblocks]
  calc
    ‖(k : ℂ) * intervalSum 0 q f + intervalSum (A + k * q) r f‖ ≤
        (k : ℝ) * B + B :=
      (norm_add_le _ _).trans (add_le_add hmain hrem)
    _ = ((L / q + 1 : ℕ) : ℝ) * B := by
      dsimp [k]
      push_cast
      ring

namespace Kloosterman

open Erdos387

theorem coefficient_periodic
    (N : ℕ) [NeZero N] (b : ZMod N) :
    Function.Periodic
      (fun x : ℤ => Erdos387.Kloosterman.coefficient N b (x : ZMod N))
      (N : ℤ) := by
  intro x
  simp

theorem intervalSum_coefficient_eq_incompleteInterval
    (N : ℕ) [NeZero N] (b : ZMod N) (A : ℤ) (m : ℕ) :
    intervalSum (A + 1) m
        (fun x : ℤ => Erdos387.Kloosterman.coefficient N b (x : ZMod N)) =
      Erdos387.Kloosterman.incompleteInterval N b A m := by
  simp [intervalSum, Erdos387.Kloosterman.incompleteInterval,
    Int.Ioc_eq_finset_map, add_assoc]

noncomputable def fixedMulSquarefreeIntervalBound
    (M q : ℕ) [NeZero M] [NeZero q] (hcop : Nat.Coprime M q)
    (b : ZMod (M * q)) : ℝ :=
  (Real.log (M * q : ℕ) + 1) *
    ((4 : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) *
      Real.sqrt
        (Nat.gcd
          (((ZMod.chineseRemainder hcop b).2 *
            (Nat.gcdA M q : ZMod q)).val) q : ℝ) * M)

/-- The fixed-factor squarefree incomplete Kloosterman estimate for an
arbitrary interval length.  Each full modulus block and the final residual
block use the existing one-period completion theorem. -/
theorem norm_incompleteInterval_fixed_mul_squarefree_arbitrary
    (M q : ℕ) [NeZero M] [NeZero q]
    (hcop : Nat.Coprime M q) (hsq : Squarefree q)
    (hlarge : ∀ p ∈ q.primeFactors, 2 < p)
    (b : ZMod (M * q)) (A : ℤ) (L : ℕ) :
    ‖Erdos387.Kloosterman.incompleteInterval (M * q) b A L‖ ≤
      ((L / (M * q) + 1 : ℕ) : ℝ) *
        fixedMulSquarefreeIntervalBound M q hcop b := by
  let f : ℤ → ℂ := fun x =>
    Erdos387.Kloosterman.coefficient (M * q) b (x : ZMod (M * q))
  let B := fixedMulSquarefreeIntervalBound M q hcop b
  have hperiod : Function.Periodic f (M * q : ℤ) := by
    exact coefficient_periodic (M * q) b
  have hshort : ∀ A' m, m ≤ M * q → ‖intervalSum A' m f‖ ≤ B := by
    intro A' m hm
    rw [show intervalSum A' m f =
        Erdos387.Kloosterman.incompleteInterval (M * q) b (A' - 1) m by
      simpa [f] using
        intervalSum_coefficient_eq_incompleteInterval
          (M * q) b (A' - 1) m]
    exact Erdos387.Kloosterman.norm_incompleteInterval_fixed_mul_squarefree
      M q hcop hsq hlarge b (A' - 1) m hm
  have hB : 0 ≤ B :=
    (norm_nonneg (intervalSum 0 0 f)).trans (hshort 0 0 (Nat.zero_le _))
  rw [← intervalSum_coefficient_eq_incompleteInterval (M * q) b A L]
  exact norm_intervalSum_le_div_add_one_mul
    (A + 1) L (M * q) f B (Nat.mul_pos (NeZero.pos M) (NeZero.pos q))
      hperiod hB hshort

end Kloosterman

end Erdos387Proof.PeriodicCompletion
