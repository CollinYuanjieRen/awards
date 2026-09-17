import Mathlib

/-! Comparator-style challenge module (Mathlib-only; targets with `sorry`, not imported by the build)
for JSP-000385 / Erdős #473, the finite prime-sum permutations for 2 ≤ n ≤ 10. -/

namespace Challenge473

/-- A permutation of `{1,…,n}` all of whose adjacent sums are prime. -/
def HasPrimeSumPerm (n : ℕ) : Prop :=
  ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ l.Chain' (fun a b => Nat.Prime (a + b))

theorem hasPrimeSumPerm_ten : HasPrimeSumPerm 10 := by
  sorry

theorem hasPrimeSumPerm_of_le_ten {n : ℕ} (h2 : 2 ≤ n) (h10 : n ≤ 10) : HasPrimeSumPerm n := by
  sorry

end Challenge473
