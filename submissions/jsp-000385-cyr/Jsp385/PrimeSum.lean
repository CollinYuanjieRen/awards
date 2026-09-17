import Mathlib

namespace Erdos473

set_option linter.deprecated false in
/-- A permutation of `{1,…,n}` all of whose adjacent sums are prime. -/
def HasPrimeSumPerm (n : ℕ) : Prop :=
  ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ l.Chain' (fun a b => Nat.Prime (a + b))

theorem hasPrimeSumPerm_two : HasPrimeSumPerm 2 :=
  ⟨[1, 2], by decide, by show List.IsChain _ _; decide⟩

theorem hasPrimeSumPerm_three : HasPrimeSumPerm 3 :=
  ⟨[1, 2, 3], by decide, by show List.IsChain _ _; decide⟩

theorem hasPrimeSumPerm_four : HasPrimeSumPerm 4 :=
  ⟨[1, 2, 3, 4], by decide, by show List.IsChain _ _; decide⟩

theorem hasPrimeSumPerm_five : HasPrimeSumPerm 5 :=
  ⟨[1, 4, 3, 2, 5], by decide, by show List.IsChain _ _; decide⟩

theorem hasPrimeSumPerm_six : HasPrimeSumPerm 6 :=
  ⟨[1, 4, 3, 2, 5, 6], by decide, by show List.IsChain _ _; decide⟩

theorem hasPrimeSumPerm_seven : HasPrimeSumPerm 7 :=
  ⟨[1, 2, 3, 4, 7, 6, 5], by decide, by show List.IsChain _ _; decide⟩

theorem hasPrimeSumPerm_eight : HasPrimeSumPerm 8 :=
  ⟨[1, 2, 3, 4, 7, 6, 5, 8], by decide, by show List.IsChain _ _; decide⟩

theorem hasPrimeSumPerm_nine : HasPrimeSumPerm 9 :=
  ⟨[1, 2, 3, 4, 7, 6, 5, 8, 9], by decide, by show List.IsChain _ _; decide⟩

theorem hasPrimeSumPerm_ten : HasPrimeSumPerm 10 :=
  ⟨[1, 2, 3, 4, 7, 6, 5, 8, 9, 10], by decide, by show List.IsChain _ _; decide⟩

/-- the finite Segal version holds for every `2 ≤ n ≤ 10`. -/
theorem hasPrimeSumPerm_of_le_ten {n : ℕ} (h2 : 2 ≤ n) (h10 : n ≤ 10) : HasPrimeSumPerm n := by
  interval_cases n
  · exact hasPrimeSumPerm_two
  · exact hasPrimeSumPerm_three
  · exact hasPrimeSumPerm_four
  · exact hasPrimeSumPerm_five
  · exact hasPrimeSumPerm_six
  · exact hasPrimeSumPerm_seven
  · exact hasPrimeSumPerm_eight
  · exact hasPrimeSumPerm_nine
  · exact hasPrimeSumPerm_ten

end Erdos473

#print axioms Erdos473.hasPrimeSumPerm_ten
#print axioms Erdos473.hasPrimeSumPerm_of_le_ten
