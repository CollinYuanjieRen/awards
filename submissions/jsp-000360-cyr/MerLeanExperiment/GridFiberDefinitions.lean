import MerLeanExperiment.GridDefinitions

namespace Erdos441

noncomputable def gridFiber (q : ℝ) (L : ℕ) (i j : ℤ) : Finset ℤ :=
  if j = (L : ℤ) then (if i = 0 then {1} else ∅)
  else if j < (L : ℤ) then gridA q i j \ gridA q (i - 1) j else ∅

end Erdos441
