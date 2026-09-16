import Jsp285

/-! Closed roots, expanded literal statements, and intended-object checks. -/
#print axioms Erdos343.erdos_343_eventual
#print axioms Erdos343.erdos_343_all_N
#print axioms Jsp285.finite_multiset_AP
#print axioms Jsp285.indexedSubsetSums_univ_eq

example : ∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
    (∀ i, 0 < A i) →
    (∀ᶠ N in Filter.atTop, ∃ s : Finset ℕ,
      C * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N) →
    ∃ a d : ℕ, 0 < d ∧ ∀ k, ∃ s : Finset ℕ,
      a + k * d = ∑ i ∈ s, A i :=
  Erdos343.erdos_343_eventual

example : ∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
    Monotone A → (∀ i, 0 < A i) →
    (∀ N, ∃ s : Finset ℕ, C * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N) →
    ∃ a d : ℕ, 0 < d ∧ ∀ k, ∃ s : Finset ℕ,
      a + k * d = ∑ i ∈ s, A i :=
  Erdos343.erdos_343_all_N

example (A : ℕ → ℕ) :
    Jsp285.indexedSubsetSums A Set.univ =
      {n | ∃ s : Finset ℕ, n = ∑ i ∈ s, A i} :=
  Jsp285.indexedSubsetSums_univ_eq A

-- Infinite repetition is an actual model of the original counting premise.
example (C : ℕ) : Erdos343.HasEventualLinearCountingLowerBound C (fun _ => 1) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨1, fun N hN => ?_⟩
  exact ⟨Finset.range (C * N), by simp, fun _ _ => hN⟩

-- Distinct occurrences of the same value may both be selected.
example : 2 ∈ Erdos343.SubsetSums (fun _ => 1) := by
  exact ⟨{0, 1}, by norm_num⟩
