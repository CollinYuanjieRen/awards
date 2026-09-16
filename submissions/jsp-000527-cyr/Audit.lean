import JSP527

#print axioms PohoataZakharov.erdos_651_subexponential_inv
#print axioms PohoataZakharov.erdos_651_subexponential
#print axioms PohoataZakharov.theorem_one_one
#print axioms PohoataZakharov.hasErdosSzekeresNumber_three
#print axioms PohoataZakharov.erdos_651_disproved
#print axioms PohoataZakharov.erdos_651_subexponential_all_dimensions
#print axioms PohoataZakharov.erdos_651_subexponential_inv_all_dimensions
#print axioms PohoataZakharov.erdos_651_disproved_all_dimensions
#print axioms PohoataZakharov.exists_generic_projection
#print axioms PohoataZakharov.erdosSzekeresNumber_add_three_le
#print axioms Erdos651.pohoataZakharov_forces_eventually
#print axioms Erdos651.exists_tripleGadgetFamily
#print axioms Erdos651.exists_uniformSeparatedClusters
#print axioms Erdos651.exists_generic_image
#print axioms Erdos651.PohoataZakharovEnvelopeCertificate.theoremOneOne
#print axioms Erdos651.AlternatingFreeFamily.containsConvexSubset_of_sourceEnvelope
#print axioms Erdos651.pohoata_zakharov_prop_three_one
#print axioms Erdos651.pohoata_zakharov_prop_two_one_three_edges
#print axioms Erdos651.exists_orderedStrongPositiveFractionConfiguration
#print axioms Erdos651.exists_twoSeparated_subclusters
#print axioms Erdos651.alternatingBlock_hulls_disjoint
#print axioms Erdos651.exists_alternating_free_subsets_of_monochromatic_clique
#print axioms Erdos651.hasErdosSzekeresNumber_three
#print axioms Erdos651.pohoataZakharovTheoremOneOne_imp_subexponential
#print axioms Erdos651.erdos_651_of_pohoata_zakharov
#print axioms Erdos651.not_erdos_651

open Filter in
example (k : ℕ) : ∀ᶠ n : ℕ in atTop,
    (Erdos651.erdosSzekeresNumber 3 n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) :=
  PohoataZakharov.erdos_651_subexponential_inv k

example : Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber 3) :=
  PohoataZakharov.erdos_651_subexponential

example : Erdos651.PohoataZakharovTheoremOneOne := PohoataZakharov.theorem_one_one

example (n : ℕ) : Erdos651.HasErdosSzekeresNumber 3 n := PohoataZakharov.hasErdosSzekeresNumber_three n

example : ¬ Erdos651.Erdos651Claim := PohoataZakharov.erdos_651_disproved

/-- Unfolded form of the headline: for every `ε > 0`, eventually `f₃(n) ≤ 2 ^ (ε n)`. -/
example : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    (Erdos651.erdosSzekeresNumber 3 n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) :=
  PohoataZakharov.erdos_651_subexponential

/-- Unfolded form of the disproof: no `c > 0` with `(1 + c) ^ n < f₃(n)` for all large `n`. -/
example : ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
    (1 + c) ^ n < (Erdos651.erdosSzekeresNumber 3 n : ℝ) :=
  PohoataZakharov.erdos_651_disproved

example (d : ℕ) : Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber (d + 3)) :=
  PohoataZakharov.erdos_651_subexponential_all_dimensions d

example (d : ℕ) : ¬ Erdos651.HasExponentialLowerBound (Erdos651.erdosSzekeresNumber (d + 3)) :=
  PohoataZakharov.erdos_651_disproved_all_dimensions d

/-- Every dimension `k ≥ 3`, stated with the dimension as the explicit bound `3 ≤ k`. -/
example (k : ℕ) (hk : 3 ≤ k) : Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber k) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 3 := ⟨k - 3, by omega⟩
  exact PohoataZakharov.erdos_651_subexponential_all_dimensions d
