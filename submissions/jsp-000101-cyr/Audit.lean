import Proof

open Erdos85 SimpleGraph

#print axioms Erdos85.f_four
#print axioms Erdos85.f_four_le
#print axioms Erdos85.cycleGraph_four_isContained_of_two_le_minDegree
#print axioms Erdos85.perfectMatching_witness
#print axioms Erdos85.two_le_f_four

example : f 4 = 2 := Erdos85.f_four
example : f 4 ≤ 2 := Erdos85.f_four_le
example : ∀ (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj], 2 ≤ G.minDegree → cycleGraph 4 ⊑ G := by
  intro G _ h; exact Erdos85.cycleGraph_four_isContained_of_two_le_minDegree G h
example : 1 ≤ perfectMatching.minDegree ∧ ¬ cycleGraph 4 ⊑ perfectMatching :=
  Erdos85.perfectMatching_witness
example : 2 ≤ f 4 := Erdos85.two_le_f_four

#print Erdos85.f
#print Erdos85.perfectMatching
