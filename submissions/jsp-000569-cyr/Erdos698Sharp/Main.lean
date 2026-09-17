import Mathlib

/-!
# Erdős Problem #698: the Erdős–Szekeres bound is sharp for `i = 1`, `j = p`, `n = 2p`

Erdős and Szekeres proved that for `1 ≤ i < j ≤ n/2` one has
`gcd(C(n,i), C(n,j)) ≥ C(n,i)/C(j,i) ≥ 2^i`, and Erdős asked whether the gcd must be large
(a question later settled by Bergman; not addressed here).  The problem page records: "This
inequality is sharp for `i = 1`, `j = p`, and `n = 2p`."  This file proves that sharpness
statement in the exact shape of the formal-conjectures theorem
`Erdos698.erdos_698.variants.erdos_szekeres_sharp` (tagged "research solved" with `sorry`):
for an odd prime `p`, `gcd(2p, C(2p, p)) = 2p / p = 2^1`.  Bergman's theorem, the
Erdős–Szekeres inequality itself, and the main question are not claimed.

Proof.  `gcd(2p, C(2p,p))` divides `2p`; it is even because `2 ∣ C(2p,p)` (a central binomial
coefficient), and it is not divisible by `p` because `p ∤ C(2p,p)` for `p > 2` (the exponent of
`p` in `C(2p,p)` vanishes when `2p < p²`, i.e. `p > 2`), so the gcd is `2`.  Finally
`C(2p,1)/C(p,1) = 2p/p = 2`.
-/

namespace Erdos698

open Filter

/-- For an odd prime `p`, the prime `p` does not divide the central binomial coefficient
`C(2p, p)`: the exponent of `p` in `C(2p, p)` vanishes because `2 * p < 3 * p`. -/
theorem not_dvd_centralBinom_of_prime {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    ¬ p ∣ Nat.centralBinom p := by
  have hfac : (Nat.centralBinom p).factorization p = 0 :=
    Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hp2 le_rfl (by omega)
  rcases (Nat.factorization_eq_zero_iff _ _).mp hfac with h | h | h
  · exact absurd hp h
  · exact h
  · exact absurd h (Nat.centralBinom_pos p).ne'

/-- For an odd prime `p` one has `gcd (2 * p, C(2p, p)) = 2`: the gcd is even because the central
binomial coefficient is, and it is coprime to `p` because `p ∤ C(2p, p)`. -/
theorem gcd_two_mul_centralBinom {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    Nat.gcd (2 * p) (Nat.centralBinom p) = 2 := by
  have hnotdvd : ¬ p ∣ Nat.centralBinom p := not_dvd_centralBinom_of_prime hp hp2
  refine Nat.dvd_antisymm ?_ ?_
  · have hgp : ¬ p ∣ Nat.gcd (2 * p) (Nat.centralBinom p) := fun h =>
      hnotdvd (h.trans (Nat.gcd_dvd_right _ _))
    have hcop : Nat.Coprime (Nat.gcd (2 * p) (Nat.centralBinom p)) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hgp).symm
    exact hcop.dvd_of_dvd_mul_right (Nat.gcd_dvd_left _ _)
  · exact Nat.dvd_gcd (dvd_mul_right 2 p) (Nat.two_dvd_centralBinom_of_one_le hp.pos)

/--
This inequality is sharp for $i=1$, $j=p$, and $n=2p$.
-/
theorem erdos_698.variants.erdos_szekeres_sharp (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (Nat.gcd ((2 * p).choose 1) ((2 * p).choose p) : ℝ) =
        ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) ∧
      ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) = (2 : ℝ) ^ 1 := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hgcd : Nat.gcd ((2 * p).choose 1) ((2 * p).choose p) = 2 := by
    rw [Nat.choose_one_right, ← Nat.centralBinom_eq_two_mul_choose]
    exact gcd_two_mul_centralBinom hp hp2
  have hdiv : ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) = 2 := by
    rw [Nat.choose_one_right, Nat.choose_one_right, div_eq_iff hp0]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [hgcd, hdiv]
    norm_num
  · rw [hdiv, pow_one]

end Erdos698

open Erdos698

/-- The same statement as a closed formula (no binders), used as the graded root. -/
theorem erdos_698_sharp_closed :
    ¬ ∃ p : ℕ, p.Prime ∧ 2 < p ∧
      ¬ ((Nat.gcd ((2 * p).choose 1) ((2 * p).choose p) : ℝ) =
            ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) ∧
          ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) = (2 : ℝ) ^ 1) := by
  rintro ⟨p, hp, hp2, h⟩
  exact h (erdos_698.variants.erdos_szekeres_sharp p hp hp2)
