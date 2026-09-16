import ErdosProblems.Erdos318Reused
import ErdosProblems.FormalConjecturesAP

namespace Erdos318

/-- Every infinite arithmetic progression has property `P₁`, with the official predicate. -/
theorem erdos_318.variants.infinite_AP {A : Set ℕ}
    (hA : _root_.Set.IsAPOfLength A ⊤) : P₁ A := by
  apply erdos_318.variants.infinite_AP_reused
  simpa only [_root_.Set.IsAPOfLength, _root_.Set.IsAPOfLengthWith,
    Erdos318.Set.IsAPOfLength, Erdos253.Set.IsAPOfLength,
    Erdos253.Set.IsAPOfLengthWith] using hA

end Erdos318

#print Erdos318.erdos_318.variants.infinite_AP
#print axioms Erdos318.erdos_318.variants.infinite_AP
#print Erdos318.erdos_318.parts.i
#print axioms Erdos318.erdos_318.parts.i
#print Erdos318.P₁
#print Set.HasDensity
#print Set.HasPosDensity
#print Set.IsAPOfLengthWith
#print Set.IsAPOfLength
