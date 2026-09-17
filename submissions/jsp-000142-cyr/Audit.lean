import Erdos138VdWExists

open Nat Filter Erdos138

#print axioms monoAP_guarantee_set_nonempty

/-- Erdős #138: van der Waerden's theorem in the formal-conjectures shape
`Erdos138.monoAP_guarantee_set_nonempty`. -/
example (r k : ℕ) : (monoAP_guarantee_set r k).Nonempty := monoAP_guarantee_set_nonempty r k

/-- The definitions are the formal-conjectures ones. -/
example (r k N : ℕ) : N ∈ monoAP_guarantee_set r k ↔
    ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k := Iff.rfl
example {α : Type*} [AddCommMonoid α] (s : Set α) (l : ℕ∞) :
    s.IsAPOfLength l ↔ ∃ a d : α, s.IsAPOfLengthWith l a d := Iff.rfl
example {α : Type*} [AddCommMonoid α] (s : Set α) (l : ℕ∞) (a d : α) :
    s.IsAPOfLengthWith l a d ↔ (ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}) := Iff.rfl
