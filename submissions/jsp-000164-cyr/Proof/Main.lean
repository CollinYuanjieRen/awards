import Proof.Defs

/-!
# The trivial bound `τ(G) ≤ 3ν(G)` (Erdős problem #167, Tuza's conjecture)

Erdős problem #167 asks Tuza's question: if a graph `G` contains at most `k` edge-disjoint
triangles, can `G` be made triangle-free by removing at most `2k` edges?  The problem page calls
the bound `3k` trivial: "It is trivial that `G` can be made triangle-free after removing at most
`3k` edges."  This package proves exactly that trivial bound, via a maximal edge-disjoint triangle
packing: take a packing `F` of maximum size and delete the union of the edge sets of its members;
this is at most `3|F| ≤ 3ν(G)` edges, and any triangle surviving the deletion could be added to
`F`, contradicting maximality.

Not claimed here: Tuza's conjecture `τ(G) ≤ 2ν(G)` of Erdős problem #167, the `K_4`/`K_5`
sharpness examples, Haxell's `(3 − 3/23 + o(1))k` bound, and the Kahn–Park result for random
graphs.
-/

namespace Erdos167

open Finset

/-- The heart of the argument: the union of the edge sets of a maximum-size packing is a cover.
If a triangle `s` survived the deletion, all three of its edges would avoid the deleted set, so
`s` would be edge-disjoint from every member of `F` and not itself a member, and `insert s F`
would be a strictly larger packing. -/
theorem exists_cover_of_maximal_packing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V)) (hF : IsPacking G F)
    (hmax : ∀ F', IsPacking G F' → F'.card ≤ F.card) :
    IsCover G (F.biUnion edgesOf) := by
  classical
  show (G.deleteEdges ((F.biUnion edgesOf : Finset (Sym2 V)) : Set (Sym2 V))).CliqueFree 3
  intro s hs
  obtain ⟨hclique, hcard⟩ := hs
  -- Each edge of `s` is an edge of `G` that survived the deletion, so it avoids the deleted set.
  have hedge : ∀ e ∈ edgesOf s, e ∉ F.biUnion edgesOf := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      rw [mem_edgesOf] at he
      obtain ⟨hmem, hdiag⟩ := he
      have ha : a ∈ s := hmem a (Sym2.mem_iff.2 (Or.inl rfl))
      have hb : b ∈ s := hmem b (Sym2.mem_iff.2 (Or.inr rfl))
      have hab : a ≠ b := fun h => hdiag (Sym2.mk_isDiag_iff.2 h)
      have hadj := hclique (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hab
      rw [SimpleGraph.deleteEdges_adj] at hadj
      exact fun hc => hadj.2 (Finset.mem_coe.2 hc)
  -- `s` is a triangle of `G` itself.
  have hstri : s ∈ triangles G :=
    mem_triangles.2 ⟨hcard, hclique.mono (SimpleGraph.deleteEdges_le _)⟩
  -- `s` spans at least one edge, so it cannot already be a member of `F`.
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ s, ∃ y ∈ s, x ≠ y := Finset.one_lt_card.1 (by omega)
  have hmemxy : s(x, y) ∈ edgesOf s := by
    refine mem_edgesOf.2 ⟨?_, fun h => hxy (Sym2.mk_isDiag_iff.1 h)⟩
    intro z hz
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · exact hx
    · exact hy
  have hsF : s ∉ F := fun hsF =>
    hedge _ hmemxy (Finset.mem_biUnion.2 ⟨s, hsF, hmemxy⟩)
  -- Hence `insert s F` is a strictly larger packing, contradicting maximality.
  have hins : IsPacking G (insert s F) := by
    refine ⟨Finset.insert_subset hstri hF.1, ?_⟩
    rw [Finset.coe_insert]
    refine hF.2.insert ?_
    intro T hT _
    rw [Finset.disjoint_left]
    intro e he hcon
    exact hedge e he (Finset.mem_biUnion.2 ⟨T, Finset.mem_coe.1 hT, hcon⟩)
  have hle := hmax _ hins
  rw [Finset.card_insert_of_notMem hsF] at hle
  omega

/-- T2: the trivial bound `τ(G) ≤ 3ν(G)` for an arbitrary finite vertex type. -/
theorem coverNumber_le_three_mul_packingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : coverNumber G ≤ 3 * packingNumber G := by
  classical
  obtain ⟨F, hF, hcard⟩ := exists_packing_card_eq G
  have hmax : ∀ F', IsPacking G F' → F'.card ≤ F.card := by
    intro F' hF'
    rw [hcard]
    exact card_le_packingNumber G F' hF'
  have hcov : IsCover G (F.biUnion edgesOf) := exists_cover_of_maximal_packing G F hF hmax
  have hsize : (F.biUnion edgesOf).card ≤ F.card * 3 :=
    Finset.card_biUnion_le_card_mul _ _ _ fun T hT =>
      card_edgesOf_le T (mem_triangles.1 (hF.1 hT)).1
  calc coverNumber G ≤ (F.biUnion edgesOf).card := coverNumber_le_card G _ hcov
    _ ≤ F.card * 3 := hsize
    _ = 3 * packingNumber G := by rw [hcard, Nat.mul_comm]

/-- T3: the problem page's sentence in `k`-form: if `G` has at most `k` edge-disjoint triangles
then deleting at most `3k` edges makes `G` triangle-free. -/
theorem exists_cover_of_packingNumber_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) (hk : packingNumber G ≤ k) : ∃ D : Finset (Sym2 V), D.card ≤ 3 * k ∧ (G.deleteEdges (D : Set (Sym2 V))).CliqueFree 3 := by
  obtain ⟨D, hD, hDcard⟩ := exists_isCover_card_eq G
  refine ⟨D, ?_, hD⟩
  rw [hDcard]
  exact le_trans (coverNumber_le_three_mul_packingNumber G) (Nat.mul_le_mul_left 3 hk)

/-- T1: the audited root, in negation form over `Fin n`: no graph on `n` vertices has
`τ(G) > 3ν(G)`. -/
theorem not_exists_coverNumber_gt (n : ℕ) : ¬ ∃ G : SimpleGraph (Fin n), 3 * packingNumber G < coverNumber G := by
  rintro ⟨G, h⟩
  exact absurd (coverNumber_le_three_mul_packingNumber G) (not_le.2 h)

end Erdos167
