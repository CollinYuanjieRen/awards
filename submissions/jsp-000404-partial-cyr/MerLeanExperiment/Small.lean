import MerLeanExperiment.SmallThree
import MerLeanExperiment.SmallFour

namespace PlanarMinimax

/-- The two small-cardinality faces of the ordinary minimax-angle classification. -/
theorem small_cardinalities :
    minimaxAngle 3 = Real.pi / 3 ∧ minimaxAngle 4 = Real.pi / 2 :=
  ⟨minimaxAngle_three, minimaxAngle_four⟩

#print axioms small_cardinalities

end PlanarMinimax
