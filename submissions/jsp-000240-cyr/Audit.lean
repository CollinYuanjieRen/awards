import Erdos282Fibonacci

open Filter Real Erdos282

#print axioms Erdos282.erdos_282.variants.fibonacci
#print axioms erdos_282_fibonacci_closed

/-- Erdős #282: Fibonacci's observation, in the formal-conjectures shape. -/
example {x : ℚ} (hx : x ∈ Set.Ioo 0 1) : greedyUnitFractionRem .univ x =ᶠ[atTop] 0 :=
  Erdos282.erdos_282.variants.fibonacci hx

/-- The model is the formal-conjectures one (first step). -/
example (A : Set ℕ) (x : ℚ) : greedyUnitFractionRem A x 0 =
    (if x ≤ 0 then 0 else x - 1 / (sInf { n | n ∈ A ∧ 1 / x ≤ n } : ℕ)) := by
  simp only [greedyUnitFractionRem]
