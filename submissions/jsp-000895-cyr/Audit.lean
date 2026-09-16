import JSP895.Statement

#print axioms Erdos1076Sparse.three_mul_exLe_le_choose
#print axioms Erdos1076Sparse.choose_le_three_mul_exLe
#print axioms Erdos1076Sparse.erdos_1076_locally_sparse_of_le
#print axioms Erdos1076Sparse.erdos_1076_locally_sparse
#print axioms Erdos1076Sparse.exLe_isEquivalent
#print axioms Erdos1076Sparse.statement_locally_sparse
#print axioms Erdos1076Sparse.statement_locally_sparse'
#print axioms Erdos1076Sparse.statement_isEquivalent
#print axioms Erdos1076Sparse.statement_literal_reading_false
#print axioms Erdos207.erdos_207
#print axioms Erdos1076.not_erdos_1076

open Filter Topology in
example (k : ℕ) (hk : 4 ≤ k) :
    (∀ n : ℕ, 3 * Erdos1076Sparse.exLe k n ≤ n.choose 2) ∧
    (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * Erdos1076Sparse.exLe k n) ∧
    Tendsto (fun n : ℕ => (Erdos1076Sparse.exLe k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6)) :=
  Erdos1076Sparse.erdos_1076_locally_sparse_of_le k hk

open Filter Topology in
example (k : ℕ) :
    (∀ n : ℕ, 3 * Erdos1076Sparse.exLe (k + 4) n ≤ n.choose 2) ∧
    (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * Erdos1076Sparse.exLe (k + 4) n) ∧
    Tendsto (fun n : ℕ => (Erdos1076Sparse.exLe (k + 4) n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6)) :=
  Erdos1076Sparse.erdos_1076_locally_sparse k
