import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Erdos441

noncomputable def realIntIoc (a b : ℝ) : Finset ℤ :=
  Finset.Ioc ⌊a⌋ ⌊b⌋

end Erdos441
