import Proof.Ramsey

/-!
# Erdős problem #1182 — the triangle-versus-graph Ramsey number `R(K_3, G)`

A red/blue colouring of the complete graph on `Fin N` is encoded, as in our Ramsey
toolbox, by a `SimpleGraph (Fin N)` `R`: the *red* edges are the edges of `R`, the
*blue* edges are the edges of the complement `Rᶜ`.

This file defines `TriRamseyProp N G` ("every red/blue colouring of `K_N` contains a
red triangle or a blue copy of `G`"), the Ramsey number `triRamsey G = R(K_3, G)` as
the least such `N`, and the statement `ConnLowerBound n` of the page's trivial bound.

It also builds the witness colouring used to refute `TriRamseyProp N G` for small `N`:
`redBipartite N m` is the complete bipartite red graph between `{i | i.val < m}` and
its complement inside `Fin N`. It has no red triangle, and its blue graph is the
disjoint union of two cliques, so a blue copy of a connected graph lands inside a
single part.
-/

namespace Erdos1182

open SimpleGraph

/-- `TriRamseyProp N G` says that every red/blue colouring of the complete graph on `N`
vertices (red = the edges of `R`, blue = the edges of `Rᶜ`) contains a red triangle or a
blue copy of `G`. -/
def TriRamseyProp (N : ℕ) {W : Type*} (G : SimpleGraph W) : Prop :=
  ∀ R : SimpleGraph (Fin N), ¬ R.CliqueFree 3 ∨ G ⊑ Rᶜ

/-- The Ramsey number `R(K_3, G)`: the least `N` such that every red/blue colouring of
`K_N` contains a red triangle or a blue copy of `G`. -/
noncomputable def triRamsey {W : Type*} (G : SimpleGraph W) : ℕ := sInf {N : ℕ | TriRamseyProp N G}

/-- `ConnLowerBound n` is the page's trivial bound for graphs on `n` vertices:
`R(K_3, G) ≥ 2n − 1` for every connected graph `G` on `n` vertices. -/
def ConnLowerBound (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.Connected → 2 * n - 1 ≤ triRamsey G

/-- The witness colouring of `K_N`: the red graph is the complete bipartite graph between
the first `m` vertices and the remaining ones. -/
def redBipartite (N m : ℕ) : SimpleGraph (Fin N) where
  Adj i j := (i.val < m) ≠ (j.val < m)
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

/-- Two vertices are red-adjacent in `redBipartite N m` exactly when they lie on opposite
sides of the split. -/
@[simp] theorem redBipartite_adj {N m : ℕ} {i j : Fin N} :
    (redBipartite N m).Adj i j ↔ ((i.val < m) ≠ (j.val < m)) := Iff.rfl

/-- Two distinct vertices are blue-adjacent (adjacent in the complement of
`redBipartite N m`) exactly when they lie on the same side of the split. -/
theorem redBipartite_compl_adj {N m : ℕ} {i j : Fin N} :
    (redBipartite N m)ᶜ.Adj i j ↔ i ≠ j ∧ ((i.val < m) ↔ (j.val < m)) := by
  simp only [SimpleGraph.compl_adj, redBipartite_adj, ne_eq, not_not, iff_iff_eq]

/-- The witness colouring has no red triangle: of any three vertices, two lie on the same
side of the split and hence are not red-adjacent. -/
theorem redBipartite_cliqueFree (N m : ℕ) : (redBipartite N m).CliqueFree 3 := by
  intro t ht
  have hcard : (Finset.univ : Finset Bool).card < t.card := by
    rw [ht.card_eq]; decide
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun i : Fin N => decide (i.val < m)) (fun a _ => Finset.mem_univ _)
  have hadj : (redBipartite N m).Adj x y := ht.isClique hx hy hxy
  exact redBipartite_adj.mp hadj (propext (decide_eq_decide.mp hfxy))

/-- Along a walk, a homomorphism into the blue graph of the witness colouring stays on one
side of the split. -/
theorem side_of_walk {N m : ℕ} {W : Type*} {G : SimpleGraph W}
    (f : G →g (redBipartite N m)ᶜ) {u v : W} (p : G.Walk u v) :
    ((f u).val < m ↔ (f v).val < m) := by
  induction p with
  | nil => exact Iff.rfl
  | cons h _ ih => exact (redBipartite_compl_adj.mp (f.map_adj h)).2.trans ih

end Erdos1182
