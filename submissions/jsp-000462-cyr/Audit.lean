import Proof

open SimpleGraph Erdos572

#print axioms Erdos572.le_extremalNumber_oddCycle
#print axioms Erdos572.le_extremalNumber_oddCycle'
#print axioms Erdos572.le_extremalNumber_of_not_colorable_two
#print axioms Erdos572.extremalNumber_cycleGraph_three
#print axioms Erdos572.turanGraph_two_colorable
#print axioms Erdos572.cycleGraph_odd_free_turanGraph_two

example : ∀ n k : ℕ, n ^ 2 / 4 ≤ extremalNumber n (cycleGraph (2 * k + 3)) :=
  Erdos572.le_extremalNumber_oddCycle
example : ∀ n k : ℕ, 1 ≤ k → n ^ 2 / 4 ≤ extremalNumber n (cycleGraph (2 * k + 1)) :=
  Erdos572.le_extremalNumber_oddCycle'
example : ∀ (n : ℕ) {W : Type} (H : SimpleGraph W), ¬ H.Colorable 2 → n ^ 2 / 4 ≤ extremalNumber n H :=
  fun n _ H h => Erdos572.le_extremalNumber_of_not_colorable_two n H h
example : ∀ n : ℕ, extremalNumber n (cycleGraph 3) = n ^ 2 / 4 :=
  Erdos572.extremalNumber_cycleGraph_three
example : ∀ n : ℕ, (turanGraph n 2).Colorable 2 := Erdos572.turanGraph_two_colorable
example : ∀ n k : ℕ, (cycleGraph (2 * k + 3)).Free (turanGraph n 2) :=
  Erdos572.cycleGraph_odd_free_turanGraph_two

#print SimpleGraph.extremalNumber
#print SimpleGraph.turanGraph
#print SimpleGraph.cycleGraph
