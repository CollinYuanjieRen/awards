import MerLeanExperiment.ShiftDefinitions
import Mathlib.Algebra.Ring.Int.Parity

namespace Erdos441

def shiftParityWeight (r s : ℤ) : ℕ :=
  if Odd r ∧ Odd s then 2 else 1

end Erdos441
