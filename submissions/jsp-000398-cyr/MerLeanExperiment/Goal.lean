import MerLeanExperiment.DilationLemma
import MerLeanExperiment.BlockAsymptotics

namespace Erdos492Real

/-- Schmidt's counterexample to the original real-subdivision question of
Erdős. The finite construction is proved and instantiated here; the theorem
has no additional premises. -/
theorem schmidt_counterexample : SchmidtStatement :=
  schmidt_counterexample_of_finite_subdivision finite_subdivision_lemma

end Erdos492Real
