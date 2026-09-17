import Mathlib

/-! Comparator-style challenge module (Mathlib-only definitions; targets with `sorry`, not imported by
the build) for JSP-000749 / Erdős #901: the lower bound 2^{n−1} ≤ m(n) and the value m(2) = 3. -/

namespace Challenge901

/-- Every edge of `E` has exactly `n` vertices. -/
def IsUniform {V : Type*} (n : ℕ) (E : Finset (Finset V)) : Prop := ∀ e ∈ E, e.card = n

/-- Property B: some `2`-colouring makes every edge bichromatic. -/
def TwoColorable {V : Type*} (E : Finset (Finset V)) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ E, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- `m(n)`: least number of edges of an `n`-uniform `3`-chromatic (no Property B) hypergraph. -/
noncomputable def m (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ (N : ℕ) (E : Finset (Finset (Fin N))), IsUniform n E ∧ ¬ TwoColorable E ∧ E.card = k}

/-- Erdős's lower bound `2^{n−1} ≤ m(n)`. -/
theorem two_pow_le_m (n : ℕ) : 2 ^ (n - 1) ≤ m n := by
  sorry

/-- The value `m(2) = 3`. -/
theorem m_two : m 2 = 3 := by
  sorry

end Challenge901
