import Mathlib

/-!
# Erdős Problem #373: the trivial solutions of `n! = a₁! ⋯ a_k!` and Hickerson's four solutions

Erdős asked to show that `n! = a₁! a₂! ⋯ a_k!` with `n − 1 > a₁ ≥ a₂ ≥ ⋯ ≥ a_k ≥ 2` has only
finitely many solutions (OPEN; not addressed here, nor Luca's conditional result or the
`k = 2` bounds).  The problem page records: "The condition `a₁ < n − 1` is necessary to rule out
the trivial solutions when `n = a₂! ⋯ a_k!`", and that Hickerson conjectured that the only
non-trivial solutions are `9! = 2!3!3!7!`, `10! = 6!7!`, `10! = 3!5!7!` and `16! = 14!5!2!`.

This file proves, with the set `S` of non-trivial solutions copied verbatim from the
formal-conjectures statement `Erdos373.erdos_373` (pairs `(n, l)` with `l` the list
`[a₁, …, a_k]` in non-increasing order):

* the trivial solutions: whenever `n = a₂! ⋯ a_k!` (with `a₂ ≥ ⋯ ≥ a_k ≥ 2` and `n − 1 ≥ a₂`,
  the ordering requirement for `a₁ = n − 1`), the tuple `(n, [n − 1, a₂, …, a_k])` satisfies
  the equation, the ordering and the lower bound `a_i ≥ 2`, but is excluded from `S` because
  `a₁ = n − 1`;
* Hickerson's four solutions are elements of `S`.

Whether these four are the only elements of `S` (Hickerson's conjecture) is not claimed.
-/

open scoped Nat

namespace Erdos373

/--
Let `S` be the set of non-trivial solutions to the equation `n! = a₁! ··· aₖ!`
such that `a₁ ≥ ... ≥ aₖ` and `n-1 > a₁`.
-/
abbrev S : Set (ℕ × List ℕ) :=
  {(n, l) | n ! = (l.map Nat.factorial).prod ∧ l.Pairwise (· ≥ ·)
    ∧ l.headI < (n - 1 : ℕ) ∧ ∀ a ∈ l, 1 < a }

end Erdos373

open Erdos373

/-- **The trivial solutions**: if `n = a₂! ⋯ a_k!` with `a₂ ≥ ⋯ ≥ a_k ≥ 2` and `n − 1 ≥ a₂`, then
`(n, [n − 1, a₂, …, a_k])` satisfies `n! = (n−1)! a₂! ⋯ a_k!`, the ordering and `a_i ≥ 2`. -/
theorem erdos_373_trivial_solution (l : List ℕ) (hl0 : l ≠ []) (hl : l.Pairwise (· ≥ ·))
    (h2 : ∀ a ∈ l, 1 < a)
    (hn : l.headI + 1 ≤ (l.map Nat.factorial).prod) :
    ((l.map Nat.factorial).prod) ! = ((((l.map Nat.factorial).prod - 1) :: l).map Nat.factorial).prod ∧
      (((l.map Nat.factorial).prod - 1) :: l).Pairwise (· ≥ ·) ∧
      ∀ a ∈ ((l.map Nat.factorial).prod - 1) :: l, 1 < a := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl0
  have ha : 1 < a := h2 a (List.mem_cons_self ..)
  rw [List.headI_cons] at hn
  set n := ((a :: l').map Nat.factorial).prod with hn_def
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_cons, List.prod_cons, ← hn_def, ← Nat.mul_factorial_pred (by omega),
      Nat.mul_comm]
  · rw [List.pairwise_cons]
    refine ⟨fun b hb => ?_, hl⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · omega
    · have := (List.pairwise_cons.mp hl).1 b hb'
      omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · exact h2 x hx'

/-- The trivial solutions have `a₁ = n − 1`, so they are excluded from `S` by the condition
`a₁ < n − 1`. -/
theorem erdos_373_trivial_solution_not_mem (l : List ℕ) :
    ((l.map Nat.factorial).prod, ((l.map Nat.factorial).prod - 1) :: l) ∉ S := by
  rintro ⟨-, -, h3, -⟩
  rw [List.headI_cons] at h3
  exact lt_irrefl _ h3

/-- **Hickerson's four solutions** `9! = 2!3!3!7!`, `10! = 6!7!`, `10! = 3!5!7!`, `16! = 14!5!2!`
are non-trivial solutions, i.e. elements of `S`. -/
theorem erdos_373_hickerson_mem :
    (9, [7, 3, 3, 2]) ∈ S ∧ (10, [7, 6]) ∈ S ∧ (10, [7, 5, 3]) ∈ S ∧ (16, [14, 5, 2]) ∈ S :=
  ⟨⟨by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩⟩

/-- Closed form combining the trivial-solution remark and Hickerson's four solutions. -/
theorem erdos_373_remarks_closed :
    ((9, [7, 3, 3, 2]) ∈ S ∧ (10, [7, 6]) ∈ S ∧ (10, [7, 5, 3]) ∈ S ∧ (16, [14, 5, 2]) ∈ S) ∧
      ∀ l : List ℕ, l ≠ [] → l.Pairwise (· ≥ ·) → (∀ a ∈ l, 1 < a) →
        l.headI + 1 ≤ (l.map Nat.factorial).prod →
        (((l.map Nat.factorial).prod) ! =
            ((((l.map Nat.factorial).prod - 1) :: l).map Nat.factorial).prod ∧
          (((l.map Nat.factorial).prod - 1) :: l).Pairwise (· ≥ ·) ∧
          ∀ a ∈ ((l.map Nat.factorial).prod - 1) :: l, 1 < a) ∧
        ((l.map Nat.factorial).prod, ((l.map Nat.factorial).prod - 1) :: l) ∉ S :=
  ⟨erdos_373_hickerson_mem, fun l hl0 hl h2 hn =>
    ⟨erdos_373_trivial_solution l hl0 hl h2 hn, erdos_373_trivial_solution_not_mem l⟩⟩
