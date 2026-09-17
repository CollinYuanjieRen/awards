import Erdos288Example

open Erdos288

#print axioms erdos_288_example

/-- Erdős #288: the page's example `1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1`. -/
example : (![((3 : ℕ+), (6 : ℕ+)), ((20 : ℕ+), (20 : ℕ+))] : Fin 2 → ℕ+ × ℕ+) ∈ integralReciprocalPairs :=
  erdos_288_example

/-- The set is the formal-conjectures set expression. -/
example : integralReciprocalPairs = { I : Fin 2 → ℕ+ × ℕ+ | ∀ j, (I j).1 ≤ (I j).2 ∧
    ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := rfl

#print axioms erdos_288_example_closed
