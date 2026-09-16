import Proof.Defs

/-!
# Erdős Problem 1084: `f₁ n = n - 1`

The scoped component of Erdős Problem 1084 formalized here: in dimension one the contact number is
`f₁(n) = n - 1`.  The two-dimensional value (Harborth) and all higher dimensions are open or
outside this component and are not addressed.
-/

namespace Erdos1084

/-- Upper bound: a separated set of `n` reals has at most `n - 1` unit pairs. -/
theorem unitPairs_le_of_isSeparated (A : Finset ℝ) (hA : IsSeparated A) :
    unitPairs A ≤ A.card - 1 := by
  -- Separation is not needed: the bound holds for every finite set of reals.
  have _hsep : IsSeparated A := hA
  exact unitPairs_le A

/-- The bound is attained: there is a separated set of `n` reals with `n - 1` unit pairs. -/
theorem exists_isSeparated_unitPairs_eq (n : ℕ) :
    ∃ A : Finset ℝ, A.card = n ∧ IsSeparated A ∧ unitPairs A = n - 1 :=
  ⟨segment n, card_segment n, isSeparated_segment n, unitPairs_segment n⟩

/-- **The one-dimensional contact number.** `f₁ n = n - 1` for every `n`. -/
theorem contactOne_eq (n : ℕ) : contactOne n = n - 1 := by
  obtain ⟨A, hcard, hsep, hpairs⟩ := exists_isSeparated_unitPairs_eq n
  have hbound : ∀ m ∈ {m : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsSeparated A ∧ unitPairs A = m},
      m ≤ n - 1 := by
    rintro m ⟨B, hB, hBsep, rfl⟩
    simpa [hB] using unitPairs_le_of_isSeparated B hBsep
  have hmem : n - 1 ∈ {m : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsSeparated A ∧ unitPairs A = m} :=
    ⟨A, hcard, hsep, hpairs⟩
  unfold contactOne
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound)
    (le_csSup ⟨n - 1, fun m hm => hbound m hm⟩ hmem)

end Erdos1084
