import Mathlib

/-!
# Erdős Problem 1078: transversal cliques in balanced multipartite graphs

Bollobás, Erdős and Szemerédi conjectured that an `r`-partite graph with `n` vertices in each
part and minimum degree at least `(r − 3/2) n` contains a `K_r`. Haxell (2001) proved it, as a
consequence of her theorem that a graph of maximum degree `Δ` whose vertex classes all have at
least `2Δ` vertices has an independent transversal.

This file sets up independent transversals, the non-domination hypothesis of Haxell's theorem
(the form in which it is proved: no union of `|B|` classes is dominated by `2(|B| − 1)` vertices),
and the constellation states of the augmenting procedure with their lexicographic measure.
-/

namespace Erdos1078

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → ι)

/-- A partial independent transversal: an independent set meeting every class at most once. -/
def IsPIT (M : Finset V) : Prop :=
  (∀ v ∈ M, ∀ w ∈ M, ¬ G.Adj v w) ∧ Set.InjOn part (M : Set V)

/-- An independent transversal: a partial one meeting every class. -/
def IsIT (M : Finset V) : Prop := IsPIT G part M ∧ ∀ i : ι, ∃ v ∈ M, part v = i

/-- Haxell's non-domination hypothesis: for every nonempty set `B` of classes, no set of at most
`2(|B| − 1)` vertices from those classes dominates the union of the classes in `B`. -/
def NonDom : Prop :=
  ∀ B : Finset ι, B.Nonempty → ∀ D : Finset V, (∀ u ∈ D, part u ∈ B) →
    D.card ≤ 2 * (B.card - 1) → ∃ w, part w ∈ B ∧ ∀ u ∈ D, ¬ G.Adj u w

/-- The leaves of a centre `x`: its neighbours in `M`. -/
def leaves (M : Finset V) (x : V) : Finset V := M.filter (fun y => G.Adj x y)

/-- The vertex set of the constellation with centres `xs` and leaves in `M`. -/
def Tset (M : Finset V) (xs : List V) : Finset V :=
  xs.toFinset ∪ xs.toFinset.biUnion (leaves G M)

/-- The classes reached by the constellation: the root class `a` and the classes of all leaves. -/
def classes (M : Finset V) (a : ι) (xs : List V) : Finset ι :=
  insert a ((xs.toFinset.biUnion (leaves G M)).image part)

/-- A valid state of the augmenting procedure for the root class `a`: `M` is a partial
independent transversal missing `a`; each centre lies in a class already reached by the earlier
centres and is not adjacent to any earlier centre or leaf; every centre except possibly the last
has at least one leaf. -/
structure Valid (a : ι) (M : Finset V) (xs : List V) : Prop where
  pit : IsPIT G part M
  miss : ∀ v ∈ M, part v ≠ a
  chain : ∀ j (hj : j < xs.length),
    part xs[j] ∈ classes G part M a (xs.take j) ∧ ∀ u ∈ Tset G M (xs.take j), ¬ G.Adj u xs[j]
  nonempty : ∀ j (hj : j + 1 < xs.length), (leaves G M (xs[j]'(by omega))).Nonempty

variable (ι) in
/-- The signature of a state, read lexicographically: the leaf counts of the centres, padded by
the number of classes (which exceeds every leaf count). -/
def vec (M : Finset V) (xs : List V) : Lex (Fin (Fintype.card ι + 1) → ℕ) :=
  toLex (fun j => if h : (j : ℕ) < xs.length then (leaves G M xs[j]).card else Fintype.card ι)

end Erdos1078
