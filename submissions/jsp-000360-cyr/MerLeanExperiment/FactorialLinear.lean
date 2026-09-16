import MerLeanExperiment.FactorialQuotient
import Mathlib.RingTheory.Coprime.Basic

namespace Erdos441

theorem factorial_linear_spec (M : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hsize : 2 * d.natAbs ≤ M) (ell : ℤ) :
    let A : ℤ := (M.factorial : ℤ) / d
    d * A = (M.factorial : ℤ) ∧ IsCoprime A (1 - A * ell) ∧
      ∀ p : ℕ, p.Prime → p ≤ M → ∀ n : ℤ,
        ¬ (p : ℤ) ∣ A * n + (1 - A * ell) := by
  dsimp only
  have hdNat : d.natAbs ∣ M.factorial :=
    Nat.dvd_factorial (Int.natAbs_pos.mpr hd) (by omega)
  have hdInt : d ∣ (M.factorial : ℤ) := by
    have hcast : (d.natAbs : ℤ) ∣ (M.factorial : ℤ) := by exact_mod_cast hdNat
    rcases le_total 0 d with hdpos | hdneg
    · simpa [Int.natAbs_of_nonneg hdpos] using hcast
    · simpa [Int.natCast_natAbs, abs_of_nonpos hdneg] using hcast
  constructor
  · exact Int.mul_ediv_cancel' hdInt
  constructor
  · exact ⟨ell, 1, by ring⟩
  · intro p hp hpM n hdiv
    have hA := factorial_int_quotient_small_prime M p d hd hsize hp hpM
    have hAn : (p : ℤ) ∣ ((M.factorial : ℤ) / d) * (n - ell) :=
      dvd_mul_of_dvd_left hA _
    have hid : ((M.factorial : ℤ) / d) * n + (1 - ((M.factorial : ℤ) / d) * ell) =
        ((M.factorial : ℤ) / d) * (n - ell) + 1 := by ring
    rw [hid] at hdiv
    have hpone : (p : ℤ) ∣ 1 := (dvd_add_right hAn).mp hdiv
    exact hp.not_dvd_one (by exact_mod_cast hpone)

end Erdos441

#print axioms Erdos441.factorial_linear_spec
