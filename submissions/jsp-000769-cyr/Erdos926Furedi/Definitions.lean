import Mathlib

/-!
# Erdős Problem 926: the graph `H_k` and the objects of the counting argument

For `k ≥ 4` let `H_k` be the graph on the vertices `x`, `y₁, …, y_k`, `z_p` (one for each pair
`p = {i, j}`), where `x` is adjacent to every `y_i` and `z_p` is adjacent to `y_i` and `y_j`.
Erdős asked whether `ex(n; H_k) ≪_k n^{3/2}`; Füredi (1991) proved `ex(n; H_k) ≪ (kn)^{3/2}`.

This file defines `H_k` and the auxiliary notions used in the proof: the codegree of two vertices,
the "rich graph" at a vertex `x` (pairs of neighbours of `x` with many common neighbours), and the
number of ordered "poor" pairs of neighbours of `x`.
-/

namespace Erdos926

open SimpleGraph Finset

/-- Unordered pairs `{i, j}` of `Fin k`, as ordered pairs with `i < j`. -/
abbrev PairIdx (k : ℕ) : Type := {p : Fin k × Fin k // p.1 < p.2}

/-- The vertices of `H_k`: the centre `none`, the branch vertices `some (Sum.inl i)` and the pair
vertices `some (Sum.inr p)`. -/
abbrev HVertex (k : ℕ) : Type := Option (Fin k ⊕ PairIdx k)

/-- Adjacency in `H_k`: the centre is joined to every branch vertex, and the pair vertex of
`{i, j}` is joined to the branch vertices `i` and `j`. -/
def HAdj (k : ℕ) : HVertex k → HVertex k → Prop
  | none, some (Sum.inl _) => True
  | some (Sum.inl _), none => True
  | some (Sum.inl i), some (Sum.inr p) => p.1.1 = i ∨ p.1.2 = i
  | some (Sum.inr p), some (Sum.inl i) => p.1.1 = i ∨ p.1.2 = i
  | _, _ => False

theorem hAdj_symm (k : ℕ) : ∀ a b : HVertex k, HAdj k a b → HAdj k b a := by
  rintro (_ | ⟨i | p⟩) (_ | ⟨j | q⟩) h <;> simp_all [HAdj]

theorem hAdj_irrefl (k : ℕ) : ∀ a : HVertex k, ¬ HAdj k a a := by
  rintro (_ | ⟨i | p⟩) h <;> simp_all [HAdj]

/-- The graph `H_k`. -/
def Hk (k : ℕ) : SimpleGraph (HVertex k) where
  Adj := HAdj k
  symm := ⟨fun a b h => hAdj_symm k a b h⟩
  loopless := ⟨fun a h => hAdj_irrefl k a h⟩

instance (k : ℕ) : DecidableRel (Hk k).Adj := by
  intro a b
  rcases a with _ | ⟨i | p⟩ <;> rcases b with _ | ⟨j | q⟩ <;> simp only [Hk, HAdj] <;>
    infer_instance

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Codegree: the number of common neighbours of `u` and `v`. -/
def codeg (u v : V) : ℕ := (G.neighborFinset u ∩ G.neighborFinset v).card

/-- The rich graph at `x` with threshold `T`: two distinct neighbours of `x` are adjacent when they
have at least `T` common neighbours. -/
def richGraph (T : ℕ) (x : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.Adj x u ∧ G.Adj x v ∧ T ≤ codeg G u v
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.2.1, h.2.1, by simpa [codeg, Finset.inter_comm] using h.2.2.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

instance (T : ℕ) (x : V) : DecidableRel (richGraph G T x).Adj := by
  intro u v
  unfold richGraph
  infer_instance

/-- The number of ordered pairs of distinct neighbours of `x` with fewer than `T` common
neighbours. -/
def poorOrd (T : ℕ) (x : V) : ℕ :=
  ((G.neighborFinset x).offDiag.filter (fun uv => codeg G uv.1 uv.2 < T)).card

/-- The threshold used in the proof. -/
def threshold (k : ℕ) : ℕ := Fintype.card (PairIdx k) + k + 1

end Graph

end Erdos926
