import Proof

open Erdos201

#print axioms Erdos201.G_le_R
#print axioms Erdos201.R_three_five
#print axioms Erdos201.G_three_five_le
#print axioms Erdos201.apFreeMax_le_iff
#print axioms Erdos201.G_le_apFreeMax

example : ∀ k N : ℕ, G k N ≤ R k N := Erdos201.G_le_R
example : R 3 5 = 4 := Erdos201.R_three_five
example : G 3 5 ≤ 3 := Erdos201.G_three_five_le
example : ∀ (k : ℕ) (T : Finset ℤ) (m : ℕ),
    apFreeMax k T ≤ m ↔ ∀ S ⊆ T, APFree k S → S.card ≤ m := Erdos201.apFreeMax_le_iff
example : ∀ (k N : ℕ) (T : Finset ℤ), T.card = N → G k N ≤ apFreeMax k T :=
  Erdos201.G_le_apFreeMax

#print Erdos201.HasAP
#print Erdos201.APFree
#print Erdos201.apFreeMax
#print Erdos201.R
#print Erdos201.G
