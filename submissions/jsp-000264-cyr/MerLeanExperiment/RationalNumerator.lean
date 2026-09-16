import Mathlib

namespace ReciprocalSquares

/-- The sum of reciprocal denominators in a finite set. -/
def recipSumQ (S : Finset ℕ) : ℚ := ∑ d ∈ S, (1 : ℚ) / d

/-- Casting a common-denominator numerator gives the corresponding reciprocal sum. -/
theorem numerator_eq_mul_recipSum (D S : Finset ℕ) (m : ℕ)
    (hD : ∀ d ∈ D, 0 < d) (hdiv : ∀ d ∈ D, d ∣ m) (hS : S ⊆ D) :
    ((∑ d ∈ S, m / d : ℕ) : ℚ) = (m : ℚ) * recipSumQ S := by
  rw [recipSumQ, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hdS
  have hdD : d ∈ D := hS hdS
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (hD d hdD).ne'
  rw [Nat.cast_div (hdiv d hdD) hdq]
  ring

/-- The common-denominator numerator does not wrap modulo `m`, because
every subset has reciprocal mass less than one. -/
theorem modular_subset_sum_iff_exact (D S : Finset ℕ)
    (m k : ℕ) [NeZero m] (r : ℚ)
    (hD : ∀ d ∈ D, 0 < d) (hdiv : ∀ d ∈ D, d ∣ m)
    (hS : S ⊆ D) (hW : recipSumQ D < 1)
    (hr1 : r < 1) (hk : (k : ℚ) = (m : ℚ) * r) :
    ((∑ d ∈ S, ((m / d : ℕ) : ZMod m)) = (k : ZMod m)) ↔
      recipSumQ S = r := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmq : 0 < (m : ℚ) := by exact_mod_cast hm
  have hterm : ∀ d ∈ D, 0 ≤ (1 : ℚ) / d := by
    intro d hdD
    have hdq : 0 < (d : ℚ) := by exact_mod_cast hD d hdD
    positivity
  have hmass_le : recipSumQ S ≤ recipSumQ D := by
    unfold recipSumQ
    exact Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun d hdD _ ↦ hterm d hdD)
  have hmass_lt : recipSumQ S < 1 := hmass_le.trans_lt hW
  have hn_cast := numerator_eq_mul_recipSum D S m hD hdiv hS
  have hn_lt_q : ((∑ d ∈ S, m / d : ℕ) : ℚ) < (m : ℚ) := by
    rw [hn_cast]
    simpa using mul_lt_mul_of_pos_left hmass_lt hmq
  have hn_lt : (∑ d ∈ S, m / d : ℕ) < m := by exact_mod_cast hn_lt_q
  have hk_lt_q : (k : ℚ) < (m : ℚ) := by
    calc
      (k : ℚ) = (m : ℚ) * r := hk
      _ < (m : ℚ) * 1 := mul_lt_mul_of_pos_left hr1 hmq
      _ = (m : ℚ) := mul_one _
  have hk_lt : k < m := by exact_mod_cast hk_lt_q
  constructor
  · intro hmod
    have hmod_nat :
        (((∑ d ∈ S, m / d : ℕ) : ℕ) : ZMod m) = (k : ZMod m) := by
      simpa only [Nat.cast_sum] using hmod
    have hrem := (ZMod.natCast_eq_natCast_iff'
      (∑ d ∈ S, m / d : ℕ) k m).mp hmod_nat
    rw [Nat.mod_eq_of_lt hn_lt, Nat.mod_eq_of_lt hk_lt] at hrem
    have hcast : ((∑ d ∈ S, m / d : ℕ) : ℚ) = (k : ℚ) := by
      exact_mod_cast hrem
    apply mul_left_cancel₀ (ne_of_gt hmq)
    calc
      (m : ℚ) * recipSumQ S = ((∑ d ∈ S, m / d : ℕ) : ℚ) := hn_cast.symm
      _ = (k : ℚ) := hcast
      _ = (m : ℚ) * r := hk
  · intro hexact
    have hcast : ((∑ d ∈ S, m / d : ℕ) : ℚ) = (k : ℚ) := by
      calc
        ((∑ d ∈ S, m / d : ℕ) : ℚ) = (m : ℚ) * recipSumQ S := hn_cast
        _ = (m : ℚ) * r := by rw [hexact]
        _ = (k : ℚ) := hk.symm
    have hnat : (∑ d ∈ S, m / d : ℕ) = k := by exact_mod_cast hcast
    simpa only [Nat.cast_sum] using
      congrArg (fun n : ℕ ↦ (n : ZMod m)) hnat

end ReciprocalSquares
