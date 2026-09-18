import MerLeanExperiment.Main

/-! Reproducible checks of the complete theorem roots and external statement bridge. -/

example : Erdos973.Target := Erdos973.erdos973

example : Erdos973.External.FormalConjectures973Expanded :=
  Erdos973.formalConjectures973Expanded

#check Erdos973.erdos973
#check Erdos973.formalConjectures973Expanded
#check Erdos973.formalConjectures973Expanded_iff_target
#print axioms Erdos973.exterior_overconvergence_sequence
#print axioms Erdos973.not_counterexampleSequenceAt
#print axioms Erdos973.finiteUniformExteriorLowerBound
#print axioms Erdos973.uniformExteriorLowerBound
#print axioms Erdos973.erdos973
#print axioms Erdos973.formalConjectures973Expanded
