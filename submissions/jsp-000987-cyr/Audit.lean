import Proof

open Erdos1182 SimpleGraph

#print axioms Erdos1182.not_exists_connected_triRamsey_lt
#print axioms Erdos1182.connLowerBound
#print axioms Erdos1182.le_triRamsey_of_connected
#print axioms Erdos1182.not_triRamseyProp_of_connected
#print axioms Erdos1182.triRamseyProp_ramsey
#print axioms Erdos1182.triRamsey_le_ramsey

example : ∀ n : ℕ, ¬ ∃ G : SimpleGraph (Fin n), G.Connected ∧ triRamsey G < 2 * n - 1 :=
  Erdos1182.not_exists_connected_triRamsey_lt
example : ∀ n : ℕ, ConnLowerBound n := Erdos1182.connLowerBound
example : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected → 2 * n - 1 ≤ triRamsey G :=
  Erdos1182.le_triRamsey_of_connected
example : ∀ (n N : ℕ) (G : SimpleGraph (Fin n)), G.Connected → N ≤ 2 * n - 2 →
    ¬ TriRamseyProp N G := Erdos1182.not_triRamseyProp_of_connected
example : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), TriRamseyProp (ramsey 3 n) G :=
  Erdos1182.triRamseyProp_ramsey
example : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), triRamsey G ≤ ramsey 3 n :=
  Erdos1182.triRamsey_le_ramsey

#print Erdos1182.IsGood
#print Erdos1182.RamseyProp
#print Erdos1182.ramsey
#print Erdos1182.TriRamseyProp
#print Erdos1182.triRamsey
#print Erdos1182.ConnLowerBound
