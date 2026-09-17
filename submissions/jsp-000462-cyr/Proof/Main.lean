import Proof.Witness

/-!
# The elementary odd-cycle Turán bound of Erdős problem #572

Erdős problem #572 asks to show that `ex(n; C_{2k}) ≫ n^{1+1/k}` for `k ≥ 3`.  Along the way the
problem page records the contrasting elementary fact about *odd* cycles: "It is easy to see that
`ex(n; C_{2k+1}) = ⌊n²/4⌋` for any `k ≥ 1` (and `n > 2k+1`) (since no bipartite graph contains an
odd cycle)."  This module formalises exactly what that parenthetical justifies.

The argument is the one from `Proof.Witness`.  The balanced complete bipartite graph
`K_{⌊n/2⌋,⌈n/2⌉}`, which is Mathlib's `SimpleGraph.turanGraph n 2` on `Fin n`, is 2-colourable and
therefore contains no odd cycle — indeed no graph `H` that fails to be 2-colourable.  Since the
extremal number `SimpleGraph.extremalNumber n H` is the supremum of the edge counts of `H`-free
graphs on `Fin n`, the edge count of that witness is a lower bound for it, and Mathlib's
`SimpleGraph.turanNumber_two` evaluates that edge count as `n ^ 2 / 4 = ⌊n²/4⌋`:

* `Erdos572.le_extremalNumber_of_not_colorable_two`: `⌊n²/4⌋ ≤ ex(n; H)` for every non-2-colourable
  (i.e. non-bipartite) `H`;
* `Erdos572.le_extremalNumber_oddCycle`: the case `H = C_{2k+3}`, which ranges over all odd cycles
  of length at least `3` as `k` ranges over `ℕ`;
* `Erdos572.le_extremalNumber_oddCycle'`: the same statement in the page's own indexing `C_{2k+1}`
  with `k ≥ 1`.

For the smallest odd cycle the matching upper bound is elementary and already in Mathlib: `C_3` is
the complete graph on three vertices, so being `C_3`-free means being triangle-free, and Mantel's
theorem — Mathlib's `SimpleGraph.CliqueFree.card_edgeFinset_le` with `r = 2`, together with
`SimpleGraph.turanNumber_two` — bounds every triangle-free graph on `n` vertices by `⌊n²/4⌋` edges.
Combining the two bounds gives the exact value `Erdos572.extremalNumber_cycleGraph_three`:
`ex(n; C_3) = ⌊n²/4⌋`, valid for every `n`.

Not claimed here: the open conjecture of Erdős problem #572 (`ex(n; C_{2k}) ≫ n^{1+1/k}` for
`k ≥ 3`), the Erdős–Klein, Bondy–Simonovits, Benson and Lazebnik–Ustimenko–Woldar results, and the
upper bound `ex(n; C_{2k+1}) ≤ ⌊n²/4⌋` for `k ≥ 2`, which needs `n` large relative to `k` and is
not elementary.  The page's parenthetical ("since no bipartite graph contains an odd cycle")
justifies exactly the lower bound proved here, and nothing more: it supplies the bipartite witness,
not the upper bound.
-/

namespace Erdos572

open Finset SimpleGraph

/-- **The general lower bound.** If `H` is not 2-colourable — that is, if `H` is not bipartite —
then every `n` admits an `H`-free graph on `Fin n` with `⌊n²/4⌋` edges, namely the balanced
complete bipartite graph `turanGraph n 2`; hence `⌊n²/4⌋ ≤ ex(n; H)`. -/
theorem le_extremalNumber_of_not_colorable_two (n : ℕ) {W : Type*} (H : SimpleGraph W)
    (h : ¬ H.Colorable 2) : n ^ 2 / 4 ≤ extremalNumber n H := by
  have hle : #(turanGraph n 2).edgeFinset ≤ extremalNumber (Fintype.card (Fin n)) H :=
    card_edgeFinset_le_extremalNumber (free_of_not_colorable_two H h n)
  rw [Fintype.card_fin] at hle
  rwa [← turanNumber_two]

/-- **The odd-cycle lower bound** (the audited root).  For every `n` and every `k`, the odd cycle
`C_{2k+3}` satisfies `⌊n²/4⌋ ≤ ex(n; C_{2k+3})`.  As `k` ranges over `ℕ`, `2 * k + 3` ranges over
all odd numbers at least `3`, so this covers every odd cycle. -/
theorem le_extremalNumber_oddCycle (n k : ℕ) :
    n ^ 2 / 4 ≤ extremalNumber n (cycleGraph (2 * k + 3)) :=
  le_extremalNumber_of_not_colorable_two n _ (not_colorable_two_cycleGraph_odd k)

/-- The odd-cycle lower bound in the indexing used on the problem page: for `k ≥ 1`,
`⌊n²/4⌋ ≤ ex(n; C_{2k+1})`. -/
theorem le_extremalNumber_oddCycle' (n k : ℕ) (hk : 1 ≤ k) :
    n ^ 2 / 4 ≤ extremalNumber n (cycleGraph (2 * k + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
  rw [h]
  exact le_extremalNumber_oddCycle n j

/-- **The exact value for the triangle** (`k = 1`): `ex(n; C_3) = ⌊n²/4⌋` for every `n`.  The lower
bound is the bipartite witness above; the upper bound is Mantel's theorem, since `C_3` is the
complete graph on three vertices and so `C_3`-free means triangle-free. -/
theorem extremalNumber_cycleGraph_three (n : ℕ) : extremalNumber n (cycleGraph 3) = n ^ 2 / 4 := by
  refine le_antisymm ?_ ?_
  · have key : extremalNumber (Fintype.card (Fin n)) (cycleGraph 3) ≤ n ^ 2 / 4 := by
      refine (extremalNumber_le_iff (V := Fin n) (cycleGraph 3) (n ^ 2 / 4)).2 ?_
      intro G _ hfree
      have hcf : G.CliqueFree 3 := by
        rw [show (3 : ℕ) = Fintype.card (Fin 3) by simp, cliqueFree_card_iff_free_top]
        rwa [← cycleGraph_three_eq_top]
      have := hcf.card_edgeFinset_le (r := 2)
      rwa [Fintype.card_fin, turanNumber_two] at this
    rwa [Fintype.card_fin] at key
  · simpa using le_extremalNumber_oddCycle n 0

end Erdos572
