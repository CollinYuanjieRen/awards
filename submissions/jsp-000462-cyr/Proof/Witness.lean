import Mathlib

/-!
# The bipartite witness for the odd-cycle Turán lower bound

Erdős problem #572 remarks in passing that `ex(n; C_{2k+1}) = ⌊n²/4⌋`, justifying it with the
parenthetical "since no bipartite graph contains an odd cycle".  This module formalises the
witness half of that parenthetical.

The witness is Mathlib's Turán graph `SimpleGraph.turanGraph n 2` on `Fin n`, whose adjacency is
`↑v % 2 ≠ ↑w % 2`; it is the balanced complete bipartite graph `K_{⌊n/2⌋,⌈n/2⌉}`.  Two facts are
proved here:

* `Erdos572.turanGraph_two_colorable`: colouring a vertex `v` by its residue `↑v % 2` is a proper
  2-colouring of `turanGraph n 2`, since adjacent vertices have different residues by definition.
* `Erdos572.cycleGraph_odd_free_turanGraph_two`: consequently `turanGraph n 2` contains no copy of
  an odd cycle `C_{2k+3}`.  The odd cycle has chromatic number `3`, so it is not 2-colourable, and
  a copy of a graph inside a 2-colourable host graph would pull the host's 2-colouring back to a
  2-colouring of that graph.

The intermediate steps `Erdos572.not_colorable_two_cycleGraph_odd` (odd cycles are not
2-colourable) and `Erdos572.free_of_not_colorable_two` (a graph that is not 2-colourable is not
contained in `turanGraph n 2`) are recorded separately, the latter for an arbitrary non-bipartite
graph `H`, which is what the general lower bound in `Proof.Main` needs.

The edge count of the witness is supplied by Mathlib's `SimpleGraph.turanNumber_two` and is used
in `Proof.Main`.
-/

namespace Erdos572

open SimpleGraph

/-- The Turán graph `turanGraph n 2` is 2-colourable: colour each vertex `v : Fin n` by the
residue `↑v % 2 : Fin 2`.  Adjacency in `turanGraph n 2` is *defined* to be `↑v % 2 ≠ ↑w % 2`,
so adjacent vertices receive different colours. -/
theorem turanGraph_two_colorable (n : ℕ) : (turanGraph n 2).Colorable 2 := by
  refine ⟨Coloring.mk (fun v : Fin n => (⟨(v : ℕ) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2)) ?_⟩
  intro v w hvw
  rw [turanGraph_adj] at hvw
  simpa [Fin.ext_iff] using hvw

/-- An odd cycle `C_{2k+3}` is not 2-colourable: its chromatic number is `3`, whereas a
2-colouring would force the chromatic number to be at most `2`. -/
theorem not_colorable_two_cycleGraph_odd (k : ℕ) : ¬ (cycleGraph (2 * k + 3)).Colorable 2 := by
  intro hc
  have h : (cycleGraph (2 * k + 3)).chromaticNumber ≤ 2 := chromaticNumber_le_iff_colorable.2 hc
  rw [chromaticNumber_cycleGraph_of_odd _ (by omega) ⟨k + 1, by ring⟩] at h
  exact absurd h (by norm_num)

/-- A graph `H` that is not 2-colourable is not contained in the 2-colourable graph
`turanGraph n 2`: a copy of `H` inside a 2-colourable graph pulls the 2-colouring back to `H`. -/
theorem free_of_not_colorable_two {W : Type*} (H : SimpleGraph W) (h : ¬ H.Colorable 2) (n : ℕ) :
    H.Free (turanGraph n 2) :=
  free_of_colorable h (turanGraph_two_colorable n)

/-- The Turán graph `turanGraph n 2` contains no odd cycle `C_{2k+3}`.  This is the formal content
of the problem page's "no bipartite graph contains an odd cycle". -/
theorem cycleGraph_odd_free_turanGraph_two (n k : ℕ) :
    (cycleGraph (2 * k + 3)).Free (turanGraph n 2) :=
  free_of_not_colorable_two _ (not_colorable_two_cycleGraph_odd k) n

end Erdos572
