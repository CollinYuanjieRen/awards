import Proof

open Erdos295

#print axioms Erdos295.card_ge_of_isUnitRepr
#print axioms Erdos295.le_kmin

example : ∀ (N : ℕ) (D : Finset ℕ), IsUnitRepr N D → (Real.exp 1 - 1) * ((N : ℝ) - 1) ≤ D.card :=
  Erdos295.card_ge_of_isUnitRepr

example : ∀ N : ℕ, (∃ D : Finset ℕ, IsUnitRepr N D) → (Real.exp 1 - 1) * ((N : ℝ) - 1) ≤ kmin N :=
  Erdos295.le_kmin

#print Erdos295.IsUnitRepr
#print Erdos295.kmin
