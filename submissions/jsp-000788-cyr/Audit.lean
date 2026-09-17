import Erdos948Colouring

#print axioms Erdos948.erdos_948
#print axioms Erdos948.erdos_948_nat
#print axioms Erdos948.erdos_948_closed
#print axioms Erdos948.exists_finiteSum_greedy
#print axioms Erdos948.exists_block
#print axioms Erdos948.greedy_sum_blocks
#print axioms Erdos948.greedy_add
#print axioms Erdos948.greedy_eq

/-- Erdős Problem 948, finite-colour form: for every `f : ℕ → ℕ` and every `k ≥ 1` there is a
`k`-colouring of `ℕ` such that every strictly increasing sequence `a` with `a n < f n` for
infinitely many `n` has nonempty finite subset sums of every colour. -/
example (f : ℕ → ℕ) (k : ℕ) (hk : 0 < k) :
    ∃ c : ℕ → Fin k, ∀ a : ℕ → ℕ, StrictMono a → Erdos948.SmallInfinitelyOften f a →
      ∀ j : Fin k, ∃ m ∈ Erdos948.FiniteSums a, c m = j :=
  Erdos948.erdos_948 f k hk

/-- The countable-colour strengthening: one colouring `ℕ → ℕ` works for every colour `j : ℕ`. -/
example (f : ℕ → ℕ) :
    ∃ c : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → Erdos948.SmallInfinitelyOften f a →
      ∀ j : ℕ, ∃ m ∈ Erdos948.FiniteSums a, c m = j :=
  Erdos948.erdos_948_nat f

/-- The question as asked (Erdős–Galvin), answered negatively: there are no `f` and `k ≥ 1` such
that every `k`-colouring admits a sparse sequence whose finite subset sums miss a colour. -/
example :
    ¬ ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧ ∀ c : ℕ → Fin k, ∃ a : ℕ → ℕ, StrictMono a ∧
      Erdos948.SmallInfinitelyOften f a ∧ ∃ j : Fin k, ∀ m ∈ Erdos948.FiniteSums a, c m ≠ j :=
  Erdos948.erdos_948_closed

/-- The definitions unfold as intended. -/
example (a : ℕ → ℕ) (m : ℕ) :
    m ∈ Erdos948.FiniteSums a ↔ ∃ S : Finset ℕ, S.Nonempty ∧ m = ∑ i ∈ S, a i := Iff.rfl
example (f a : ℕ → ℕ) :
    Erdos948.SmallInfinitelyOften f a ↔ ∀ N, ∃ n, N ≤ n ∧ a n < f n := Iff.rfl
