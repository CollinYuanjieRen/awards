import Mathlib

/-!
The two definition bodies below are copied from
`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` at commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`.
-/

variable {α : Type*} [AddCommMonoid α]

/-- The canonical Formal Conjectures arithmetic progression predicate with endpoints. -/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- The canonical Formal Conjectures arithmetic progression predicate. -/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d
