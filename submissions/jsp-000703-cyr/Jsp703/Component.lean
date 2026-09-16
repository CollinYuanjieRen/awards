import Mathlib

/-!
# JSP-000703 / Erdős #850 — scoped component

Source (erdosproblems.com/850, hashed in `sources/erdos850-statement.txt` (`ref/` in the development workspace)): "Can there exist two
distinct integers `x` and `y` such that `x, y` have the same prime factors, `x+1, y+1` have the
same prime factors, and `x+2, y+2` also have the same prime factors?  … For just `x, y` and
`x+1, y+1` one can take `x = 2(2^r − 1)` and `y = x(x+2)`.  Erdős also asked whether there are
any other examples.  Makowski [Ma68] observed that `x = 75` and `y = 1215` is another example,
since `75 = 3·5²` and `1215 = 3⁵·5` while `76 = 2²·19` and `1216 = 2⁶·19`."

This file formalizes exactly that published partial result (the two-consecutive case):
Erdős's infinite family and Makowski's example.  The three-consecutive question itself
(the Erdős–Woods conjecture) is OPEN and is not addressed here.
-/

namespace Erdos850

/-- Two positive integers `x ≠ y` with the same prime-factor sets at `x, y` and at
`x+1, y+1`. -/
def TwoConsecutiveExample (x y : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ x ≠ y ∧ x.primeFactors = y.primeFactors ∧
    (x + 1).primeFactors = (y + 1).primeFactors

/-- Erdős's family: `x = 2(2^r − 1)`, `y = x(x+2)`. -/
def erdosX (r : ℕ) : ℕ := 2 * (2 ^ r - 1)

/-- Erdős's family: `y = x(x+2)`. -/
def erdosY (r : ℕ) : ℕ := erdosX r * (erdosX r + 2)

/-- For `r ≥ 2` the number `2 ^ r - 1` is at least `3`; this packages the `Nat`-subtraction
bookkeeping used throughout. -/
theorem exists_pred_two_pow (r : ℕ) (hr : 2 ≤ r) : ∃ m : ℕ, 3 ≤ m ∧ 2 ^ r = m + 1 := by
  have h4 : (4 : ℕ) ≤ 2 ^ r := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  exact ⟨2 ^ r - 1, by omega, by omega⟩

/-- Erdős's family for `r ≥ 2` (the case `r = 1`, i.e. `(x, y) = (2, 8)`, is added in
`erdos_family` below). -/
theorem erdos_family_of_two_le (r : ℕ) (hr : 2 ≤ r) :
    TwoConsecutiveExample (erdosX r) (erdosY r) := by
  obtain ⟨m, hm3, hm⟩ := exists_pred_two_pow r hr
  have hx : erdosX r = 2 * m := by simp only [erdosX, hm]; omega
  have hxpos : 0 < erdosX r := by omega
  have hx2 : erdosX r + 2 = 2 ^ (r + 1) := by rw [hx, pow_succ, hm]; ring
  have hxpf : (erdosX r).primeFactors = {2} ∪ m.primeFactors := by
    rw [hx, Nat.primeFactors_mul (by norm_num) (by omega), Nat.prime_two.primeFactors]
  have h2pf : (erdosX r + 2).primeFactors = {2} := by
    rw [hx2, Nat.primeFactors_pow 2 (Nat.succ_ne_zero r), Nat.prime_two.primeFactors]
  have hy : (erdosY r).primeFactors = (erdosX r).primeFactors := by
    rw [erdosY, Nat.primeFactors_mul (by omega) (by omega)]
    exact Finset.union_eq_left.mpr (by rw [h2pf, hxpf]; exact Finset.subset_union_left)
  have hy1 : (erdosY r + 1).primeFactors = (erdosX r + 1).primeFactors := by
    rw [show erdosY r + 1 = (erdosX r + 1) ^ 2 by simp only [erdosY]; ring,
      Nat.primeFactors_pow _ (by norm_num)]
  have hlt : erdosX r < erdosY r := by simp only [erdosY, hx]; nlinarith
  exact ⟨hxpos, by omega, by omega, hy.symm, hy1.symm⟩

/-- The member `r = 1` of the family: `(x, y) = (2, 8)`, with `3` and `9 = 3^2`. -/
theorem erdos_family_one : TwoConsecutiveExample (erdosX 1) (erdosY 1) := by
  have hx : erdosX 1 = 2 := by decide
  have hy : erdosY 1 = 2 ^ 3 := by decide
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rw [hx, hy, Nat.primeFactors_pow 2 (by norm_num)]
  · rw [hx, hy, show (2 : ℕ) + 1 = 3 by norm_num, show (2 : ℕ) ^ 3 + 1 = 3 ^ 2 by norm_num,
      Nat.primeFactors_pow 3 (by norm_num)]

/-- **Erdős's infinite family** (erdosproblems.com/850; Benelux MO 2011, Problem 1): for every
`r ≥ 1`, `x = 2(2^r − 1)` and `y = x(x+2)` are distinct positive integers with equal prime
supports, and so are `x + 1` and `y + 1`.  (For `r = 0` the family degenerates to `x = y = 0`.) -/
theorem erdos_family (r : ℕ) (hr : 1 ≤ r) : TwoConsecutiveExample (erdosX r) (erdosY r) := by
  rcases Nat.lt_or_ge r 2 with h | h
  · have : r = 1 := by omega
    subst this
    exact erdos_family_one
  · exact erdos_family_of_two_le r h

/-- Consequently there are infinitely many such pairs (the family is injective in `r`). -/
theorem infinite_twoConsecutive :
    Set.Infinite {p : ℕ × ℕ | TwoConsecutiveExample p.1 p.2} := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun r : ℕ ↦ ((erdosX (r + 2), erdosY (r + 2)) : ℕ × ℕ)) ?_ ?_
  · intro a b hab
    simp only [Prod.mk.injEq, erdosX] at hab
    have ha : (1 : ℕ) ≤ 2 ^ (a + 2) := Nat.one_le_two_pow
    have hb : (1 : ℕ) ≤ 2 ^ (b + 2) := Nat.one_le_two_pow
    have hpow : (2 : ℕ) ^ (a + 2) = 2 ^ (b + 2) := by omega
    have := Nat.pow_right_injective (le_refl 2) hpow
    omega
  · exact fun r ↦ erdos_family (r + 2) (by omega)

/-- **Makowski's example** (Enseign. Math. 14 (1968) 193): `75 = 3·5²`, `1215 = 3⁵·5`,
`76 = 2²·19`, `1216 = 2⁶·19`. -/
theorem makowski_example : TwoConsecutiveExample 75 1215 := by
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h19 : Nat.Prime 19 := by norm_num
  have e75 : (75 : ℕ).primeFactors = {3} ∪ {5} := by
    rw [show (75 : ℕ) = 3 * 5 ^ 2 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num), h3.primeFactors,
      Nat.primeFactors_pow 5 (by norm_num), h5.primeFactors]
  have e1215 : (1215 : ℕ).primeFactors = {3} ∪ {5} := by
    rw [show (1215 : ℕ) = 3 ^ 5 * 5 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow 3 (by norm_num), h3.primeFactors, h5.primeFactors]
  have e76 : (76 : ℕ).primeFactors = {2} ∪ {19} := by
    rw [show (76 : ℕ) = 2 ^ 2 * 19 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow 2 (by norm_num), Nat.prime_two.primeFactors, h19.primeFactors]
  have e1216 : (1216 : ℕ).primeFactors = {2} ∪ {19} := by
    rw [show (1216 : ℕ) = 2 ^ 6 * 19 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow 2 (by norm_num), Nat.prime_two.primeFactors, h19.primeFactors]
  refine ⟨by norm_num, by norm_num, by norm_num, by rw [e75, e1215], ?_⟩
  rw [show (75 : ℕ) + 1 = 76 by norm_num, show (1215 : ℕ) + 1 = 1216 by norm_num, e76, e1216]

/-- Makowski's pair is not a member of Erdős's family (so it is "another example"). -/
theorem makowski_not_in_family : ∀ r : ℕ, ¬ (erdosX r = 75 ∧ erdosY r = 1215) := by
  intro r hr
  have h := hr.1
  rw [erdosX] at h
  omega

end Erdos850
