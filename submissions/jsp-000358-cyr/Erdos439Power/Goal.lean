import Erdos439Power.Statement
import Erdos439Power.FourierDecay

namespace Erdos439Power

/-- Every finite colouring contains distinct positive equally coloured
integers summing to a kth power, for every k at least two. -/
theorem full_resolution : FullStatement := by
  intro k hk r colour
  exact Erdos439.powerResolution_of_normalizedPowerFourierDecay (by omega)
    (hasNormalizedPowerFourierDecay k hk) (Fin r) colour

/-- The literal integer-domain consequence of the positive statement. -/
theorem integer_resolution : IntegerStatement := by
  intro k hk r colour
  obtain ⟨x, y, z, _hx, _hy, hxy, hc, hsum⟩ :=
    full_resolution k hk r (fun n : ℕ => colour n)
  refine ⟨x, y, z, ?_, hc, ?_⟩
  · exact_mod_cast hxy
  · exact_mod_cast hsum

/-- Explicit form of `full_resolution` with every quantifier exposed as a binder: for every
exponent `k + 2` and every colouring with `r` colours, two distinct positive equally coloured
integers sum to a `(k + 2)`-th power. -/
theorem full_resolution_explicit (k r : ℕ) (colour : ℕ → Fin r) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ colour x = colour y ∧ x + y = z ^ (k + 2) :=
  full_resolution (k + 2) (by omega) r colour

/-- Explicit form of `integer_resolution` with every quantifier exposed as a binder. -/
theorem integer_resolution_explicit (k r : ℕ) (colour : ℤ → Fin r) :
    ∃ x y z : ℤ, x ≠ y ∧ colour x = colour y ∧ x + y = z ^ (k + 2) :=
  integer_resolution (k + 2) (by omega) r colour

end Erdos439Power
