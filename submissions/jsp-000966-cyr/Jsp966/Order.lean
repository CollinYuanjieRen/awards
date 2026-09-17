import Mathlib

namespace Erdos1161

open Equiv Nat

/-- `f n k` = number of elements of `S_n` (permutations of `Fin n`) of order `k`. -/
noncomputable def f (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun g : Perm (Fin n) => orderOf g = k)).card

/-- The `n`-cycles number exactly `(n-1)!`, and all have order `n`; hence `(n-1)! ≤ f n n`,
so the maximal order-count is at least `(n-1)!`. -/
theorem factorial_le_f (n : ℕ) (hn : 2 ≤ n) : (n - 1)! ≤ f n n := by
  unfold f
  -- The set of `n`-cycles has cardinality `(n-1)!`.
  have hcard :
      (Finset.univ.filter (fun g : Perm (Fin n) => g.cycleType = {n})).card = (n - 1)! := by
    have h := Perm.card_of_cycleType_singleton (α := Fin n) hn (by simp)
    simpa [Fintype.card_fin, Nat.choose_self] using h
  rw [← hcard]
  apply Finset.card_le_card
  intro g hg
  rw [Finset.mem_filter] at hg ⊢
  refine ⟨hg.1, ?_⟩
  -- Every `n`-cycle has order `n`, since `orderOf g = g.cycleType.lcm = ({n}).lcm = n`.
  have hlcm : orderOf g = g.cycleType.lcm := (Perm.lcm_cycleType g).symm
  rw [hlcm, hg.2, Multiset.lcm_singleton]
  simp

/-- consequently the maximum over `k` of `f n k` is at least `(n-1)!`. -/
theorem factorial_le_max (n : ℕ) (hn : 2 ≤ n) : ∃ k, (n - 1)! ≤ f n k :=
  ⟨n, factorial_le_f n hn⟩

#print axioms factorial_le_f
#print axioms factorial_le_max

end Erdos1161
