import Mathlib

/-! Comparator-style challenge module (Mathlib-only definitions, targets with `sorry`; not
imported by the build) for JSP-000232 / Erdős #271, the `A(1)` component (Odlyzko–Stanley). -/

namespace Challenge271

/-- `S` contains a three-term arithmetic progression `a < b < c`, `a + c = 2 b`. -/
def HasThreeAP (S : Set ℕ) : Prop :=
  ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c ∧ a + c = 2 * b

/-- `IsStanleySeq n a`: `a` is the Stanley sequence `A(n)`: `a 0 = 0`, `a 1 = n`, and `a (k+2)` is the
least integer `> a (k+1)` such that `{a 0, …, a (k+2)}` has no three-term arithmetic progression. -/
structure IsStanleySeq (n : ℕ) (a : ℕ → ℕ) : Prop where
  zero : a 0 = 0
  one : a 1 = n
  greedy : ∀ k, IsLeast {m : ℕ | a (k + 1) < m ∧ ¬ HasThreeAP (insert m (a '' Set.Iic (k + 1)))} (a (k + 2))

theorem exists_stanleySeq (n : ℕ) : ∃ a, IsStanleySeq n a := by
  sorry

theorem stanleySeq_one_eq {a : ℕ → ℕ} (ha : IsStanleySeq 1 a) (k : ℕ) :
    a k = Nat.ofDigits 3 (Nat.digits 2 k) := by
  sorry

theorem range_stanleySeq_one {a : ℕ → ℕ} (ha : IsStanleySeq 1 a) :
    Set.range a = {m : ℕ | 2 ∉ Nat.digits 3 m} := by
  sorry

end Challenge271
