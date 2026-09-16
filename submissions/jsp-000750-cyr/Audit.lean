import Proof

open Erdos902

#print axioms Erdos902.two_pow_sub_one_le_of_hasProperty
#print axioms Erdos902.two_pow_sub_one_le_schutte
#print axioms Erdos902.schutte_one
#print axioms Erdos902.schutte_two

example : ∀ (N n : ℕ) (r : Fin N → Fin N → Prop), IsTournament r → HasProperty r n →
    2 ^ (n + 1) - 1 ≤ N :=
  Erdos902.two_pow_sub_one_le_of_hasProperty

example : ∀ n : ℕ, (∃ N : ℕ, ∃ r : Fin N → Fin N → Prop, IsTournament r ∧ HasProperty r n) →
    2 ^ (n + 1) - 1 ≤ schutte n :=
  Erdos902.two_pow_sub_one_le_schutte

example : schutte 1 = 3 := Erdos902.schutte_one

example : schutte 2 = 7 := Erdos902.schutte_two

#print Erdos902.IsTournament
#print Erdos902.Dominates
#print Erdos902.HasProperty
#print Erdos902.schutte
