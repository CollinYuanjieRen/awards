import Proof.Counting
import Proof.Extremal

/-!
# Erdős Problem 1011: `f₃(n) = ⌊(n - 1)² / 4⌋ + 2` (Erdős–Gallai)

The scoped component of Erdős Problem 1011 formalized here: for `n ≥ 5`, the least number of
edges forcing a triangle in a graph on `n` vertices of chromatic number at least `3` is
`⌊(n - 1)² / 4⌋ + 2`.  The values `f_r(n)` for `r ≥ 4` are not addressed.
-/

open Finset SimpleGraph

namespace Erdos1011

/-- **Erdős–Gallai, upper bound.** Every triangle-free graph on `n` vertices that is not
`2`-colourable has at most `⌊(n - 1)² / 4⌋ + 1` edges. -/
theorem edges_le_of_cliqueFree_of_not_colorable (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) (hb : ¬ G.Colorable 2) : G.edgeSet.ncard ≤ (n - 1) ^ 2 / 4 + 1 := by
  have : DecidableRel G.Adj := Classical.decRel _
  rw [edgeSet_ncard_eq]
  simpa using card_edgeFinset_le hG hb

/-- **Erdős–Gallai, extremal graph.** For `n ≥ 5` there is a triangle-free graph on `n` vertices
that is not `2`-colourable with exactly `⌊(n - 1)² / 4⌋ + 1` edges. -/
theorem exists_extremal (n : ℕ) (hn : 5 ≤ n) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ ¬ G.Colorable 2 ∧
      G.edgeSet.ncard = (n - 1) ^ 2 / 4 + 1 := by
  refine ⟨extremal n, extremal_cliqueFree n hn, extremal_not_colorable n hn, ?_⟩
  rw [edgeSet_ncard_eq, extremal_card_edgeFinset n hn]

/-- **Erdős–Gallai.** `f₃(n) = ⌊(n - 1)² / 4⌋ + 2` for every `n ≥ 5`. -/
theorem f3_eq (n : ℕ) (hn : 5 ≤ n) : f3 n = (n - 1) ^ 2 / 4 + 2 := by
  set N : ℕ := (n - 1) ^ 2 / 4 with hN
  have hmem : N + 2 ∈ {m : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.Colorable 2 →
      m ≤ G.edgeSet.ncard → ¬ G.CliqueFree 3} := by
    intro G hb hcard hcf
    have h := edges_le_of_cliqueFree_of_not_colorable n G hcf hb
    rw [← hN] at h
    omega
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have hmem' : ∀ G : SimpleGraph (Fin n), ¬ G.Colorable 2 → f3 n ≤ G.edgeSet.ncard →
      ¬ G.CliqueFree 3 := Nat.sInf_mem ⟨N + 2, hmem⟩
  by_contra hlt
  have hlt' : f3 n < N + 2 := Nat.not_le.mp hlt
  obtain ⟨G, hcf, hb, hcard⟩ := exists_extremal n hn
  exact hmem' G hb (by rw [hcard, ← hN]; omega) hcf

end Erdos1011
