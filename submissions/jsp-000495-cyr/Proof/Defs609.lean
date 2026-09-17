import Proof.OddCycle

/-!
# Erdős Problem 609: definitions and elementary odd-cycle facts

Erdős asked for the growth of `f(n)`, the least `m` such that every colouring of the edges of
`K_{2^n+1}` with `n` colours admits a monochromatic odd cycle of length at most `m`.  This file
sets up the colour classes of an edge colouring, the predicates "contains an odd cycle" and
"contains an odd cycle of length at most `m`", the definition of `f(n)` as an infimum, and the two
elementary facts relating odd cycles to `2`-colourings: a graph with a proper `Bool`-colouring has
no odd cycle, and a graph that is not `2`-colourable has one.
-/

open SimpleGraph

namespace Erdos609

/-- The colour class `i` of an edge colouring `c` of the complete graph on `V`: `u ~ v` iff
`u ≠ v` and the edge `{u, v}` has colour `i`. -/
def colourClass {V : Type*} {n : ℕ} (c : Sym2 V → Fin n) (i : Fin n) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => c s(u, v) = i)

/-- `G` contains an odd cycle. -/
def HasOddCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ Odd p.length

/-- `G` contains an odd cycle of length at most `m`. -/
def HasOddCycleLe {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ Odd p.length ∧ p.length ≤ m

/-- `f(n)`: the least `m` such that every `n`-colouring of the edges of `K_{2^n+1}` has a
monochromatic odd cycle of length at most `m`. -/
noncomputable def oddCycleThreshold (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ c : Sym2 (Fin (2 ^ n + 1)) → Fin n, ∃ i, HasOddCycleLe (colourClass c i) m}

/-- Adjacency in a colour class: `u` and `v` are joined in class `i` iff they are distinct and the
edge `s(u, v)` has colour `i`. -/
theorem colourClass_adj {V : Type*} {n : ℕ} {c : Sym2 V → Fin n} {i : Fin n} {u v : V} :
    (colourClass c i).Adj u v ↔ u ≠ v ∧ c s(u, v) = i := by
  rw [colourClass, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, by rwa [Sym2.eq_swap]⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

/-- If `f : V → Bool` is a proper colouring of `G`, then a walk of `G` joins two vertices of the
same colour exactly when its length is even. -/
theorem walk_length_even_of_coloring {V : Type*} {G : SimpleGraph V} {f : V → Bool}
    (hf : ∀ u v, G.Adj u v → f u ≠ f v) {u v : V} (p : G.Walk u v) :
    (f u = f v) ↔ Even p.length := by
  induction p with
  | nil => simp
  | cons hab t ih =>
    rename_i a b w
    have hab' : f a ≠ f b := hf a b hab
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    cases ha : f a <;> cases hb : f b <;> cases hw : f w <;> simp_all

/-- A graph with a proper `Bool`-colouring has no odd cycle. -/
theorem not_hasOddCycle_of_coloring {V : Type*} {G : SimpleGraph V} (f : V → Bool)
    (hf : ∀ u v, G.Adj u v → f u ≠ f v) : ¬ HasOddCycle G := by
  rintro ⟨v, p, -, hodd⟩
  have heven : Even p.length := (walk_length_even_of_coloring hf p).mp rfl
  rw [Nat.even_iff] at heven
  rw [Nat.odd_iff] at hodd
  omega

/-- A graph that is not `2`-colourable contains an odd cycle. -/
theorem hasOddCycle_of_not_colorable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (h : ¬ G.Colorable 2) : HasOddCycle G :=
  exists_odd_cycle G h

/-- A cycle in a finite graph has length at most the number of vertices. -/
theorem cycle_length_le_card {V : Type*} [Fintype V] {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) : p.length ≤ Fintype.card V := by
  have hnd : p.support.tail.Nodup := hp.support_nodup
  have hlen : p.support.tail.length = p.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support, Nat.add_sub_cancel]
  have := hnd.length_le_card
  omega

end Erdos609
