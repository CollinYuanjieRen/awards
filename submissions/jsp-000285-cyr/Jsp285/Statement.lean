import Jsp285.Main

namespace Erdos343

/-- **Target (Szemerédi–Vu, Folkman's conjecture).**  Some absolute constant
`C` works for every multiset of positive integers whose counting function is
eventually at least `C * N`.  No monotonicity of the occurrence indexing is
assumed. -/
theorem erdos_343_eventual :
    ∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
      (∀ i, 0 < A i) →
      HasEventualLinearCountingLowerBound C A →
      IsSubcomplete A := by
  exact ⟨Jsp285.infiniteCoefficient, Jsp285.infiniteCoefficient_pos,
    Jsp285.subcomplete_of_eventual_count⟩

/-- The all-`N` face used by plby/lean-proofs follows from the eventual face. -/
theorem erdos_343_of_eventual
    (h : ∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
      (∀ i, 0 < A i) → HasEventualLinearCountingLowerBound C A → IsSubcomplete A) :
    ∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
      Monotone A → (∀ i, 0 < A i) → HasLinearCountingLowerBound C A →
      IsSubcomplete A := by
  obtain ⟨C, hC, hmain⟩ := h
  exact ⟨C, hC, fun A _ hpos hcount ↦
    hmain A hpos (Filter.Eventually.of_forall hcount)⟩

/-- The original all-`N` formulation, now closed by the proved eventual theorem. -/
theorem erdos_343_all_N :
    ∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
      Monotone A → (∀ i, 0 < A i) → HasLinearCountingLowerBound C A →
      IsSubcomplete A := by
  exact erdos_343_of_eventual erdos_343_eventual

end Erdos343
