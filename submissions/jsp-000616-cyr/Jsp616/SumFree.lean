import Mathlib

/-!
# Erdős #748 (JSP-000616) — the trivial Cameron–Erdős lower bound

We define the sum-free counting function `f n` and prove the trivial lower bound
`f n ≥ 2 ^ (n - n / 2) ≥ 2 ^ (n / 2)`, obtained by counting all subsets of the
upper interval `(n/2, n] = {n/2+1, …, n}`, each of which is sum-free.
-/

namespace Erdos748

-- `SumFree` is a `∀`-proposition and not decidable by default; the classical
-- instance lets `f`'s `Finset.filter` elaborate (keeping `Classical.choice`).
attribute [local instance] Classical.propDecidable

/-- `A` is sum-free: it contains no solution of `a = b + c` (a,b,c ∈ A, not
necessarily distinct). -/
def SumFree (A : Finset ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b + c

/-- the Cameron–Erdős counting function: the number of sum-free subsets of
`{1, …, n}`. -/
noncomputable def f (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => SumFree A)).card

/-- every subset of the upper interval `(n/2, n]` is sum-free -/
theorem sumFree_of_subset_upper {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc (n / 2 + 1) n) : SumFree A := by
  intro a ha b hb c hc
  have ha' := Finset.mem_Icc.mp (hA ha)
  have hb' := Finset.mem_Icc.mp (hA hb)
  have hc' := Finset.mem_Icc.mp (hA hc)
  -- `a ≤ n` while `b + c ≥ 2*(n/2 + 1) > n`, using `n/2 + n/2 ≤ n`.
  have hhalf : n / 2 + n / 2 ≤ n := by omega
  omega

/-- the trivial Cameron–Erdős lower bound: at least `2^{⌈n/2⌉}` sum-free subsets -/
theorem f_ge (n : ℕ) : 2 ^ (n - n / 2) ≤ f n := by
  -- The powerset of the upper interval injects into the counted set.
  have hsub : (Finset.Icc (n / 2 + 1) n).powerset ⊆
      (Finset.Icc 1 n).powerset.filter (fun A => SumFree A) := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, sumFree_of_subset_upper hA⟩
    exact hA.trans (Finset.Icc_subset_Icc_left (by omega))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_powerset, Nat.card_Icc] at hcard
  -- `n + 1 - (n/2 + 1) = n - n/2`.
  have : n + 1 - (n / 2 + 1) = n - n / 2 := by omega
  rw [this] at hcard
  exact hcard

/-- weaker `2^{n/2}` form, matching the page verbatim -/
theorem f_ge_two_pow_half (n : ℕ) : 2 ^ (n / 2) ≤ f n :=
  le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (f_ge n)

#print axioms sumFree_of_subset_upper
#print axioms f_ge
#print axioms f_ge_two_pow_half

end Erdos748
