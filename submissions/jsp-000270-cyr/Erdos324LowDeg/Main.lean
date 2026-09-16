import Mathlib

/-!
# Erdős Problem #324, the settled low-degree cases: no polynomial of degree `≤ 2`, and not `x⁴`

Erdős and Graham asked whether there is a polynomial `f ∈ ℤ[x]` such that all sums `f(a) + f(b)`
with `a < b` nonnegative integers are distinct (i.e. `{f(n)}` is a Sidon set).  The question is
OPEN (probably `x⁵` works).  The problem page records that "it is easy to check that a quadratic
`f` cannot have this property" and that "it is a classical fact that `x⁴` cannot have this
property" (Euler: `59⁴ + 158⁴ = 133⁴ + 134⁴ = 635318657`).  This file proves exactly these settled
cases, in the shape of the formal-conjectures statement `Erdos324.erdos_324`:

* no `f ∈ ℤ[X]` with `f.natDegree ≤ 2` has the property (constant, linear and quadratic `f`);
* `f = X ^ 4` does not have the property.

The general question (cubic `f`, Dubickas–Novikas 2021; degree `≥ 5`) is not addressed here.
-/

open Polynomial
open scoped Polynomial

/-- The Sidon-type property of Erdős #324, exactly as in the formal-conjectures statement:
all sums `f(a) + f(b)` with `a < b` nonnegative integers are distinct. -/
def SidonPoly (f : ℤ[X]) : Prop :=
  {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => f.eval (a : ℤ) + f.eval (b : ℤ)

/-- A polynomial of degree at most two is given on evaluations by its three lowest coefficients. -/
private lemma eval_deg_le_two {f : ℤ[X]} (hf : f.natDegree ≤ 2) (x : ℤ) :
    f.eval x = f.coeff 0 + f.coeff 1 * x + f.coeff 2 * x ^ 2 := by
  rw [Polynomial.eval_eq_sum_range' (show f.natDegree < 3 by omega) x]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The heart of the quadratic case: for a positive leading coefficient `p` and any `q`, the
quantity `p * (a ^ 2 + b ^ 2) + q * (a + b)` takes the same value on two different pairs
`d < b < a < c` of nonnegative integers.  Explicitly, with `y = 2 * p + 1`, the two pairs are
`(b, a) = (y ^ 2 + y + q ^ 2, b * y - 2 * p ^ 2 - 2 * p - 1 + q)` and `(d, c) = (b - y, a + 1)`. -/
private lemma quad_collision_pos (p q : ℤ) (hp : 0 < p) :
    ∃ a b c d : ℤ, 0 ≤ d ∧ d < b ∧ b < a ∧ a < c ∧
      p * (a ^ 2 + b ^ 2) + q * (a + b) = p * (c ^ 2 + d ^ 2) + q * (c + d) := by
  have hp1 : 1 ≤ p := hp
  have hq : 0 ≤ q ^ 2 + q := by
    rcases le_or_gt 0 q with h | h
    · nlinarith
    · have h1 : q + 1 ≤ 0 := by omega
      nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = 2 * p + 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = y ^ 2 + y + q ^ 2 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = y ^ 2 + q ^ 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = b * y - 2 * p ^ 2 - 2 * p - 1 + q := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hdb : d < b := by rw [hd, hb, hy]; linarith
  have hba : b < a := by
    have key : a - b = 8 * p ^ 3 + 10 * p ^ 2 + 2 * p - 1 + (2 * p * q ^ 2 + q) := by
      simp only [ha, hb, hy]; ring
    have h2 : 0 ≤ 2 * p * q ^ 2 + q := by
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ 2 * p - 1) (sq_nonneg q)]
    have h3 : (0:ℤ) < p ^ 3 := by positivity
    have h4 : (0:ℤ) < p ^ 2 := by positivity
    linarith
  exact ⟨a, b, a + 1, d, hd0, hdb, hba, by linarith, by simp only [ha, hb, hd, hy]; ring⟩

/-- The same collision for an arbitrary nonzero leading coefficient, by negating `p` and `q`. -/
private lemma quad_collision (p q : ℤ) (hp : p ≠ 0) :
    ∃ a b c d : ℤ, 0 ≤ d ∧ d < b ∧ b < a ∧ a < c ∧
      p * (a ^ 2 + b ^ 2) + q * (a + b) = p * (c ^ 2 + d ^ 2) + q * (c + d) := by
  rcases hp.lt_or_gt with h | h
  · obtain ⟨a, b, c, d, h1, h2, h3, h4, h5⟩ := quad_collision_pos (-p) (-q) (by linarith)
    exact ⟨a, b, c, d, h1, h2, h3, h4, by linear_combination -h5⟩
  · exact quad_collision_pos p q h

/-- Every polynomial of degree at most two has a collision: this covers constant, linear and
quadratic polynomials. -/
theorem not_sidonPoly_of_natDegree_le_two (f : ℤ[X]) (hf : f.natDegree ≤ 2) : ¬ SidonPoly f := by
  intro h
  have he : ∀ x : ℤ, f.eval x = f.coeff 0 + f.coeff 1 * x + f.coeff 2 * x ^ 2 :=
    eval_deg_le_two hf
  by_cases hp : f.coeff 2 = 0
  · by_cases hq : f.coeff 1 = 0
    -- `f` is constant on evaluations: the pairs `(0, 1)` and `(0, 2)` collide.
    · have hm1 : ((0, 1) : ℕ × ℕ) ∈ {(a, b) : ℕ × ℕ | a < b} := by
        simp only [Set.mem_ofPred_eq]; omega
      have hm2 : ((0, 2) : ℕ × ℕ) ∈ {(a, b) : ℕ × ℕ | a < b} := by
        simp only [Set.mem_ofPred_eq]; omega
      have hval : f.eval ((0 : ℕ) : ℤ) + f.eval ((1 : ℕ) : ℤ)
          = f.eval ((0 : ℕ) : ℤ) + f.eval ((2 : ℕ) : ℤ) := by
        simp only [he, hp, hq]; ring
      have := h hm1 hm2 hval
      simp only [Prod.mk.injEq] at this
      omega
    -- `f` is linear: the pairs `(0, 3)` and `(1, 2)` collide since `0 + 3 = 1 + 2`.
    · have hm1 : ((0, 3) : ℕ × ℕ) ∈ {(a, b) : ℕ × ℕ | a < b} := by
        simp only [Set.mem_ofPred_eq]; omega
      have hm2 : ((1, 2) : ℕ × ℕ) ∈ {(a, b) : ℕ × ℕ | a < b} := by
        simp only [Set.mem_ofPred_eq]; omega
      have hval : f.eval ((0 : ℕ) : ℤ) + f.eval ((3 : ℕ) : ℤ)
          = f.eval ((1 : ℕ) : ℤ) + f.eval ((2 : ℕ) : ℤ) := by
        simp only [he, hp]; push_cast; ring
      have := h hm1 hm2 hval
      simp only [Prod.mk.injEq] at this
      omega
  -- `f` is genuinely quadratic: transport the integer collision to `ℕ`.
  · obtain ⟨a, b, c, d, hd0, hdb, hba, hac, hEq⟩ := quad_collision (f.coeff 2) (f.coeff 1) hp
    have hb0 : 0 ≤ b := hd0.trans hdb.le
    have ha0 : 0 ≤ a := hb0.trans hba.le
    have hc0 : 0 ≤ c := ha0.trans hac.le
    have hca : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
    have hcb : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0
    have hcc : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc0
    have hcd : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd0
    have hm1 : ((b.toNat, a.toNat) : ℕ × ℕ) ∈ {(a, b) : ℕ × ℕ | a < b} := by
      simp only [Set.mem_ofPred_eq]; omega
    have hm2 : ((d.toNat, c.toNat) : ℕ × ℕ) ∈ {(a, b) : ℕ × ℕ | a < b} := by
      simp only [Set.mem_ofPred_eq]; omega
    have hval : f.eval ((b.toNat : ℕ) : ℤ) + f.eval ((a.toNat : ℕ) : ℤ)
        = f.eval ((d.toNat : ℕ) : ℤ) + f.eval ((c.toNat : ℕ) : ℤ) := by
      rw [he, he, he, he, hca, hcb, hcc, hcd]
      linear_combination hEq
    have := h hm1 hm2 hval
    simp only [Prod.mk.injEq] at this
    omega

/-- Euler's collision `59⁴ + 158⁴ = 133⁴ + 134⁴`, so `x⁴` does not have the property. -/
theorem not_sidonPoly_X_pow_four : ¬ SidonPoly (X ^ 4) := by
  intro h
  have hm1 : ((59, 158) : ℕ × ℕ) ∈ {(a, b) : ℕ × ℕ | a < b} := by
    simp only [Set.mem_ofPred_eq]; omega
  have hm2 : ((133, 134) : ℕ × ℕ) ∈ {(a, b) : ℕ × ℕ | a < b} := by
    simp only [Set.mem_ofPred_eq]; omega
  have hval : (X ^ 4 : ℤ[X]).eval ((59 : ℕ) : ℤ) + (X ^ 4 : ℤ[X]).eval ((158 : ℕ) : ℤ)
      = (X ^ 4 : ℤ[X]).eval ((133 : ℕ) : ℤ) + (X ^ 4 : ℤ[X]).eval ((134 : ℕ) : ℤ) := by
    simp only [eval_pow, eval_X]
    norm_num
  have := h hm1 hm2 hval
  simp only [Prod.mk.injEq] at this
  omega

/-- **Erdős Problem #324, the settled cases.**  No polynomial of degree at most two, and not
`X ^ 4`, makes all the sums `f(a) + f(b)` (`a < b` nonnegative integers) distinct.  Stated in the
exact shape of the formal-conjectures rendering (`{(a, b) : ℕ × ℕ | a < b}.InjOn
fun (a, b) => f.eval (a : ℤ) + f.eval (b : ℤ)`); the general question is open and not claimed. -/
theorem erdos_324_low_degree_and_quartic :
    ¬ ∃ f : ℤ[X], (f.natDegree ≤ 2 ∨ f = X ^ 4) ∧
      {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => f.eval (a : ℤ) + f.eval (b : ℤ) := by
  rintro ⟨f, hf | rfl, h⟩
  · exact not_sidonPoly_of_natDegree_le_two f hf h
  · exact not_sidonPoly_X_pow_four h
