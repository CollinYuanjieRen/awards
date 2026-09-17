import Mathlib

/-!
# Erdős Problem #288: the example `1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1`

Erdős asked whether there are only finitely many pairs of intervals `I₁, I₂` of positive integers
with `∑_{n ∈ I₁} 1/n + ∑_{n ∈ I₂} 1/n ∈ ℕ` (OPEN; not addressed here).  The problem page records:
"For example, `1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1`."  This file verifies that example as membership
of the pair of intervals `[3, 6]`, `[20, 20]` in the set of pairs whose reciprocal sums total a
positive integer, written exactly as in the formal-conjectures statement `Erdos288.erdos_288`.
The finiteness question and its variants are not claimed.
-/

namespace Erdos288

/-- The set of pairs of intervals `[a₁, b₁]`, `[a₂, b₂]` of positive integers whose reciprocal
sums add up to a positive integer, as written in the formal-conjectures statement of #288. -/
def integralReciprocalPairs : Set (Fin 2 → ℕ+ × ℕ+) :=
  { I : Fin 2 → ℕ+ × ℕ+ |
    ∀ j, (I j).1 ≤ (I j).2 ∧
      ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n }

end Erdos288

open Erdos288

/-- **Erdős #288, the page's example**: the intervals `[3, 6]` and `[20, 20]` have reciprocal sums
totalling `1`, i.e. `1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1`. -/
theorem erdos_288_example :
    (![((3 : ℕ+), (6 : ℕ+)), ((20 : ℕ+), (20 : ℕ+))] : Fin 2 → ℕ+ × ℕ+) ∈ integralReciprocalPairs := by
  have h₁ : Finset.Icc (3 : ℕ+) 6 = {3, 4, 5, 6} := by decide
  have h₂ : Finset.Icc (20 : ℕ+) 20 = {20} := by decide
  simp only [integralReciprocalPairs, Set.mem_ofPred_eq]
  intro j
  refine ⟨?_, 1, ?_⟩
  · fin_cases j <;> decide
  · rw [Fin.sum_univ_two, Set.toFinset_Icc, Set.toFinset_Icc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h₁, h₂]
    norm_num

/-- The page's identity `1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1` in `ℚ`, spelled out. -/
theorem erdos_288_identity : (3 : ℚ)⁻¹ + 4⁻¹ + 5⁻¹ + 6⁻¹ + 20⁻¹ = 1 := by
  norm_num

/-- **Erdős #288, the page's example (closed form)**: the interval pair `([3, 6], [20, 20])` is in
the set of pairs with integral reciprocal sum, and `1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1`. -/
theorem erdos_288_example_closed :
    (![((3 : ℕ+), (6 : ℕ+)), ((20 : ℕ+), (20 : ℕ+))] : Fin 2 → ℕ+ × ℕ+) ∈ integralReciprocalPairs ∧
      (3 : ℚ)⁻¹ + 4⁻¹ + 5⁻¹ + 6⁻¹ + 20⁻¹ = 1 :=
  ⟨erdos_288_example, erdos_288_identity⟩
