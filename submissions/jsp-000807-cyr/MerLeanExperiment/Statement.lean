import Mathlib

/-!
# Frozen statements for JSP-000807 / Erdős problem 973

The original yes/no question asks whether a fixed exponential rate can make
all consecutive exterior power sums small.  `Erdos973Positive` is the literal
positive assertion, with the same indices and strict inequality as the current
Formal Conjectures statement.  The target is its negation.

`UniformExteriorLowerBound` is Luo--Yang--Zhu's stronger theorem.  Its eventual
lower bound for every positive exponent implies the target, but is kept
separate from the official statement so that the definition cannot depend on
the proof route.
-/

open Finset Filter

namespace Erdos973

/-- The affirmative assertion in Erdős problem 973. -/
def Erdos973Positive : Prop :=
  ∃ C : ℝ, 1 < C ∧
    ∀ n : ℕ, 2 ≤ n → ∃ z : ℕ → ℂ,
      z 1 = 1 ∧
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) ∧
      ∀ k ∈ Icc 2 (n + 1),
        ‖∑ i ∈ Icc 1 n, z i ^ k‖ < C ^ (-(n : ℝ))

/-- The complete official yes/no target: the affirmative assertion is false. -/
def Target : Prop := ¬ Erdos973Positive

/-- Luo--Yang--Zhu's uniform lower bound, stated on the same sequence model. -/
def UniformExteriorLowerBound : Prop :=
  ∀ lambda : ℝ, 0 < lambda →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lambda * (n : ℝ)) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

end Erdos973
