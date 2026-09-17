import Mathlib

/-!
# Erdős Problem #830: the amicable pair `220, 284`

We say that `a, b ∈ ℕ` are an amicable pair if `σ(a) = σ(b) = a + b`.  Erdős asked whether there
are infinitely many amicable pairs and whether their counting function satisfies
`A(x) > x^{1−o(1)}` (OPEN; not addressed here, nor Erdős's and Pomerance's upper bounds).  The
problem page records the classical example: "For example `220` and `284`."  This file verifies
it, with the structure `IsAmicable` copied verbatim from formal-conjectures (the definition used
by its rendering of #830): `σ(220) = σ(284) = 504 = 220 + 284`.
-/

open scoped ArithmeticFunction.sigma

/--
We say that $a,b\in \mathbb{N}$ are an amicable pair if $\sigma(a)=\sigma(b)=a+b$.
-/
@[mk_iff]
structure IsAmicable (a b : ℕ) : Prop where
  left : σ 1 a = a + b
  right : σ 1 b = a + b
  ne : a ≠ b

/-- The divisor sums of `220` and `284` are both `504`. -/
theorem sigma_220_284 : σ 1 220 = 504 ∧ σ 1 284 = 504 :=
  ⟨by rw [ArithmeticFunction.sigma_one_apply]; rfl,
    by rw [ArithmeticFunction.sigma_one_apply]; rfl⟩

/-- **Erdős #830, the page's example**: `220` and `284` form an amicable pair. -/
theorem erdos_830_example : IsAmicable 220 284 :=
  ⟨sigma_220_284.1, sigma_220_284.2, by decide⟩

/-- Closed form: `220, 284` is an amicable pair with common divisor sum `504 = 220 + 284`. -/
theorem erdos_830_example_closed :
    IsAmicable 220 284 ∧ σ 1 220 = 504 ∧ σ 1 284 = 504 ∧ 220 + 284 = 504 :=
  ⟨erdos_830_example, sigma_220_284.1, sigma_220_284.2, rfl⟩
