import MerLeanExperiment.ParityRegionDefinitions

namespace Erdos441

def parityRep (v : Bool) : ℤ := if v then 0 else 1

def ownerParity {K l : ℕ} (o : Fin K → Fin l) (r : Fin K → ℤ)
    (i : Fin K) : Fin l × Bool := (o i, decide (Even (r i)))

end Erdos441
