import Mathlib

/-!
# Erdős Problem #143: well-separated sets of integers are primitive

Erdős asked whether a countably infinite `A ⊆ (1, ∞)` with `|kx − y| ≥ 1` for all `x ≠ y ∈ A` and
integers `k ≥ 1` must be sparse (OPEN, $500; NOT addressed here).  The problem page records:
"Note that if `A` is a set of integers then the condition implies that `A` is a primitive set
(that is, no element of `A` is divisible by any other)".  This file proves that remark in a slightly stronger form: the natural numbers lying in any
well-separated set `A` form a primitive set (so in particular this holds when `A` consists of
integers), since no element of `A` divides another
(for `x ≠ y` in `A`, `y = k x` with `k ≥ 1` would give `|kx − y| = 0 < 1`).

`WellSeparatedSet` is copied verbatim from the formal-conjectures file for the problem.
-/

namespace Erdos143

/--
Let $A \subseteq (1, \infty)$ be a countably infinite set such that for all $x\neq y\in A$ and
integers $k \geq 1$ we have $|kx - y| \geq 1$.
-/
def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ (Set.Ioi (1 : ℝ))) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |k * x - y|))

/-- A set of natural numbers is *primitive* if no element divides another. -/
def IsPrimitive (S : Set ℕ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b

/-- In a well-separated set no element is a positive integer multiple of another. -/
theorem not_mul_of_wellSeparated {A : Set ℝ} (hA : WellSeparatedSet A) {x y : ℝ} (hx : x ∈ A)
    (hy : y ∈ A) (hxy : x ≠ y) (k : ℕ) (hk : 1 ≤ k) : (k : ℝ) * x ≠ y := by
  intro h
  have hsep := hA.2.2.2 x hx y hy hxy k hk
  rw [h, sub_self, abs_zero] at hsep
  linarith

/-- **Erdős #143, the page's remark (strengthened)**: the natural numbers lying in any
well-separated set form a primitive set.  (The page states this for sets of integers; the
hypothesis that every element is an integer is not needed, see `isPrimitive_of_integer_set`.) -/
theorem isPrimitive_of_wellSeparated {A : Set ℝ} (hA : WellSeparatedSet A) :
    IsPrimitive {n : ℕ | (n : ℝ) ∈ A} := by
  -- the integrality hypothesis is not needed: membership of `(a : ℝ)`, `(b : ℝ)` already says it
  rintro a ha b hb hab ⟨k, hk⟩
  have hb1 : (1 : ℝ) < (b : ℝ) := hA.1 hb
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [hk] at hb1
      norm_num at hb1
    · exact hk0
  have hne : (a : ℝ) ≠ (b : ℝ) := by exact_mod_cast hab
  refine not_mul_of_wellSeparated hA ha hb hne k hk1 ?_
  push_cast [hk]
  ring

/-- **The page's literal form**: if a well-separated set consists of natural numbers, then the
set of those natural numbers is primitive. -/
theorem isPrimitive_of_integer_set {A : Set ℝ} (hA : WellSeparatedSet A)
    (_hint : ∀ x ∈ A, ∃ n : ℕ, x = n) : IsPrimitive {n : ℕ | (n : ℝ) ∈ A} :=
  isPrimitive_of_wellSeparated hA

end Erdos143

open Erdos143 in
/-- **Erdős #143, the page's remark, closed form**: no well-separated set contains two distinct
natural numbers one of which divides the other. -/
theorem erdos_143_primitive_closed :
    ¬ ∃ A : Set ℝ, WellSeparatedSet A ∧
      ∃ a b : ℕ, (a : ℝ) ∈ A ∧ (b : ℝ) ∈ A ∧ a ≠ b ∧ a ∣ b := by
  rintro ⟨A, hA, a, b, ha, hb, hab, hdvd⟩
  exact isPrimitive_of_wellSeparated hA a ha b hb hab hdvd
