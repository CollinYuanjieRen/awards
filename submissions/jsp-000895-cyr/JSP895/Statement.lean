import JSP895.Assembly
import JSP895.External.Erdos1076

/-!
# JSP-000895 / Erdős Problem 1076 — the auditable statement surface

Two readings of Problem 1076 ("Let `k ≥ 5` and let `𝓕_k` be the family of all 3-uniform
hypergraphs with `k` vertices and `k − 2` edges. Is `ex₃(n, 𝓕_k) ~ n²/6`?") occur in the
literature:

* **Locally sparse reading (the one proved, and marked PROVED on erdosproblems.com via
  Bohman–Warnke 2019 and Glock–Kühn–Lo–Osthus 2020):** forbid every `j`-vertex,
  `(j − 2)`-edge configuration for all `4 ≤ j ≤ k` simultaneously. Then the extremal number
  is `(1/6 + o(1)) n²` for every `k ≥ 4`.  This is `Erdos1076Sparse.erdos_1076_locally_sparse`
  below (new; lower bound via the third-party formalization `Erdos207.erdos_207` of the
  Kwan–Sah–Sawhney–Simkin high-girth Steiner triple systems).
* **Literal per-`k` reading:** forbid only the `k`-vertex, `(k − 2)`-edge configurations.
  This is false for `k = 5` (Glock 2019: the constant is `1/5`); the third-party
  formalization `Erdos1076.not_erdos_1076` (plby/lean-proofs) disproves it and is
  re-exported here for completeness.  It is not claimed as this submission's work.
-/

namespace Erdos1076Sparse

open Filter Topology

/-- The intended (locally sparse) statement: for every `k ≥ 4`, with `exLe k n` the largest
number of triples on `n` vertices such that no `j − 2` triples span at most `j` vertices for all
`4 ≤ j ≤ k`, we have `3 · exLe k n ≤ C(n,2)`, `C(n−3,2) ≤ 3 · exLe k n` for large `n`, and
`exLe k n / n² → 1/6`. -/
theorem statement_locally_sparse (k : ℕ) (hk : 4 ≤ k) :
    (∀ n : ℕ, 3 * exLe k n ≤ n.choose 2) ∧
      (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * exLe k n) ∧
      Tendsto (fun n : ℕ => (exLe k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6)) :=
  erdos_1076_locally_sparse_of_le k hk

/-- Premise-free form of the same statement, indexing the configuration size as `k + 4`. -/
theorem statement_locally_sparse' (k : ℕ) :
    (∀ n : ℕ, 3 * exLe (k + 4) n ≤ n.choose 2) ∧
      (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * exLe (k + 4) n) ∧
      Tendsto (fun n : ℕ => (exLe (k + 4) n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6)) :=
  erdos_1076_locally_sparse k

/-- `ex₃(n, 𝓕_{≤k}) ~ n² / 6` in Mathlib's asymptotic-equivalence notation. -/
theorem statement_isEquivalent (k : ℕ) (hk : 4 ≤ k) :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (exLe k n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ 2 / 6) :=
  exLe_isEquivalent k hk

/-- The literal per-`k` reading is false (third-party: plby/lean-proofs `Erdos1076`,
mathematics by Glock).  Re-exported only to document the two readings side by side. -/
theorem statement_literal_reading_false :
    ¬ (∀ k : ℕ, 5 ≤ k →
        Tendsto (fun n : ℕ => (Erdos1076.extremalNumber k n : ℝ) / (n : ℝ) ^ 2)
          atTop (𝓝 (1 / 6 : ℝ))) :=
  Erdos1076.not_erdos_1076

end Erdos1076Sparse
