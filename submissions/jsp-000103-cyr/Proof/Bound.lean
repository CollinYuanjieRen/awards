import Proof.Ramsey

/-!
# Erdős problem #87 — the Erdős–Szekeres bound `r(m, n) ≤ C(m + n, m) − 1` and `R(n) ≤ 4ⁿ`

Reused from our own JSP-000099 package (Erdős #82), where these three results were proved
from the finiteness development of `Proof.Ramsey`.
-/

namespace Erdos87

open SimpleGraph

/-- The Erdős–Szekeres bound in the lossy `RamseyProp` form: `binom(m + n, m) - 1`
vertices already force a red `K_m` or a blue `K_n`. -/
theorem ramseyProp_choose (m n : ℕ) : RamseyProp ((m + n).choose m - 1) m n := by
  have key : ∀ k m n : ℕ, m + n ≤ k → RamseyProp ((m + n).choose m - 1) m n := by
    intro k
    induction k with
    | zero =>
      intro m n h
      have hm : m = 0 := by omega
      subst hm
      simpa using ramseyProp_zero_left n
    | succ k ih =>
      intro m n h
      obtain _ | a := m
      · simpa using ramseyProp_zero_left n
      obtain _ | b := n
      · simpa using ramseyProp_zero_right (a + 1)
      have hX : 0 < (a + b + 1).choose a := Nat.choose_pos (by omega)
      have hY : 0 < (a + b + 1).choose (a + 1) := Nat.choose_pos (by omega)
      have hpascal : (a + 1 + (b + 1)).choose (a + 1)
          = (a + b + 1).choose a + (a + b + 1).choose (a + 1) := by
        have hsum : a + 1 + (b + 1) = a + b + 1 + 1 := by omega
        rw [hsum, Nat.choose_succ_succ]
      have hAeq : a + (b + 1) = a + b + 1 := by omega
      have hBeq : a + 1 + b = a + b + 1 := by omega
      have hstep : RamseyProp
          ((a + (b + 1)).choose a - 1 + ((a + 1 + b).choose (a + 1) - 1) + 1) (a + 1) (b + 1) :=
        ramseyProp_step (by omega) (by omega) (ih a (b + 1) (by omega))
          (ih (a + 1) b (by omega))
      have hnum : (a + (b + 1)).choose a - 1 + ((a + 1 + b).choose (a + 1) - 1) + 1
          = (a + 1 + (b + 1)).choose (a + 1) - 1 := by
        rw [hAeq, hBeq, hpascal]
        omega
      rwa [hnum] at hstep
  exact key (m + n) m n le_rfl

/-- Ramsey numbers are bounded by binomial coefficients: `r(m, n) ≤ C(m + n, m) - 1`. -/
theorem ramsey_le_choose (m n : ℕ) : ramsey m n ≤ (m + n).choose m - 1 :=
  ramsey_le_of_ramseyProp (ramseyProp_choose m n)

/-- The diagonal Ramsey number is at most `4 ^ n`. -/
theorem ramsey_diag_le_four_pow (n : ℕ) : ramsey n n ≤ 4 ^ n := by
  have h1 := ramsey_le_choose n n
  have h2 : Nat.centralBinom n = (n + n).choose n := by
    rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
  have h3 := Nat.centralBinom_le_four_pow n
  omega

end Erdos87
