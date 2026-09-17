/-
Comparator-style challenge module for JSP-000850 / Erdős Problem #1020 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos1020Challenge

/-- Every edge of `H` has exactly `r` vertices. -/
def IsUniform {n : ℕ} (r : ℕ) (H : Finset (Finset (Fin n))) : Prop := ∀ e ∈ H, e.card = r

/-- `H` contains `k` pairwise disjoint edges. -/
def HasMatching {n : ℕ} (k : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  ∃ M ⊆ H, M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id

open Classical in
/-- `f(n; r, k)`: the maximal number of edges of an `r`-uniform hypergraph on `n` vertices with no
`k` independent edges. -/
noncomputable def f (n r k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter
    (fun H => IsUniform r H ∧ ¬ HasMatching k H)).sup Finset.card

theorem not_exists_lt_and_ne (n r k : ℕ) : ¬ (n < r * k ∧ f n r k ≠ n.choose r) := by
  sorry

theorem f_eq_choose_of_lt (n r k : ℕ) (h : n < r * k) : f n r k = n.choose r := by
  sorry

theorem not_hasMatching_of_lt (n r k : ℕ) (H : Finset (Finset (Fin n))) (hH : IsUniform r H)
    (h : n < r * k) : ¬ HasMatching k H := by
  sorry

theorem f_le_choose (n r k : ℕ) : f n r k ≤ n.choose r := by
  sorry

theorem card_le_f (n r k : ℕ) (H : Finset (Finset (Fin n))) (hH : IsUniform r H)
    (hM : ¬ HasMatching k H) : H.card ≤ f n r k := by
  sorry

end Erdos1020Challenge
