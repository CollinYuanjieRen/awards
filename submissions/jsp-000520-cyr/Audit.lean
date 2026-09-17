import Proof

open Erdos640

#print axioms Erdos640.spanThreshold_three
#print axioms Erdos640.spansOddCycle_three_three
#print axioms Erdos640.exists_oddCycle_induce_three_le
#print axioms Erdos640.not_spansOddCycle_three_of_le_two
#print axioms Erdos640.three_le_chromaticNumber_induce_of_odd

example : spanThreshold 3 = 3 := Erdos640.spanThreshold_three
example : SpansOddCycle 3 3 := Erdos640.spansOddCycle_three_three
example : ∀ {V : Type} (G : SimpleGraph V), 3 ≤ G.chromaticNumber →
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧
      3 ≤ (G.induce {x | x ∈ c.support}).chromaticNumber :=
  fun G h => Erdos640.exists_oddCycle_induce_three_le G h
example : ∀ f : ℕ, f ≤ 2 → ¬ SpansOddCycle 3 f := Erdos640.not_spansOddCycle_three_of_le_two
example : ∀ {V : Type} (G : SimpleGraph V) {v : V} (c : G.Walk v v), Odd c.length →
    3 ≤ (G.induce {x | x ∈ c.support}).chromaticNumber :=
  fun {_V} G {_v} c hc => Erdos640.three_le_chromaticNumber_induce_of_odd G c hc

#print Erdos640.SpansOddCycle
#print Erdos640.spanThreshold
