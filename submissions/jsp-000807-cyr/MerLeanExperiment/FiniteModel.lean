import MerLeanExperiment.Statement
import MerLeanExperiment.AlgebraicSetup

/-!
# Finite-family model and statement adapter

The analytic proof uses a family indexed by `Fin n`.  This module isolates the
exact reindexing to the catalog's `Nat` family on `Icc 1 n`.
-/

open Finset

namespace Erdos973

/-- The paper-strength eventual lower bound in the `Fin n` model used by the
analytic proof. -/
def FiniteUniformExteriorLowerBound : Prop :=
  ∀ lambda : ℝ, 0 < lambda →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : Fin n → ℂ,
      (∀ j, 1 ≤ ‖z j‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lambda * (n : ℝ)) < ‖powerSum z k‖

private theorem sum_fin_shift_eq_Icc (n k : ℕ) (z : ℕ → ℂ) :
    (∑ j : Fin n, z (j.1 + 1) ^ k) = ∑ i ∈ Icc 1 n, z i ^ k := by
  apply Finset.sum_bij (fun j _ => j.1 + 1)
  · intro j hj
    rw [mem_Icc]
    constructor
    · omega
    · exact j.2
  · intro j₁ hj₁ j₂ hj₂ h
    apply Fin.ext
    omega
  · intro i hi
    rw [mem_Icc] at hi
    refine ⟨⟨i - 1, ?_⟩, mem_univ _, ?_⟩
    · omega
    · exact Nat.sub_add_cancel hi.1
  · intro j hj
    rfl

/-- The finite-family theorem implies the frozen `Nat`-interval statement
without changing endpoints or strictness. -/
theorem uniformExteriorLowerBound_of_finite
    (h : FiniteUniformExteriorLowerBound) : UniformExteriorLowerBound := by
  intro lambda hlambda
  obtain ⟨N, hN⟩ := h lambda hlambda
  refine ⟨N, fun n hn z hz => ?_⟩
  let zfin : Fin n → ℂ := fun j => z (j.1 + 1)
  have hzfin : ∀ j, 1 ≤ ‖zfin j‖ := by
    intro j
    apply hz (j.1 + 1)
    rw [mem_Icc]
    exact ⟨by omega, j.2⟩
  obtain ⟨k, hk, hklarge⟩ := hN n hn zfin hzfin
  refine ⟨k, hk, ?_⟩
  simpa [powerSum, zfin, sum_fin_shift_eq_Icc] using hklarge

end Erdos973
