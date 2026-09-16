import Mathlib

/-!
# Erdős Problem 803: definitions

A subgraph `H` of a graph `G` is `D`-balanced when every vertex degree inside `H` is at most `D`
times every other vertex degree inside `H` (equivalently, maximum degree ≤ `D` · minimum degree).
Erdős and Simonovits asked whether there are absolute constants `ε > 0` and `D` such that every
graph on `n` vertices with at least `n log₂ n` edges (for `n` large in terms of `m`) contains a
`D`-balanced subgraph on `m` vertices with at least `ε m log₂ m` edges.  Alon (2008) answered
this negatively.  We record the question in its uniform form (a balanced subgraph on at least `m₀`
vertices) and in its literal form (exactly `m` vertices); the literal form implies the uniform one.
-/

open SimpleGraph

namespace Erdos803

variable {V : Type*}

/-- The degree of `v` inside the subgraph `H` (number of `H`-neighbours). -/
noncomputable def sdeg {G : SimpleGraph V} (H : G.Subgraph) (v : V) : ℕ :=
  (H.neighborSet v).ncard

/-- `H` is `D`-balanced: every degree inside `H` is at most `D` times every other degree. -/
def Balanced {G : SimpleGraph V} (D : ℝ) (H : G.Subgraph) : Prop :=
  ∀ v ∈ H.verts, ∀ w ∈ H.verts, (sdeg H v : ℝ) ≤ D * sdeg H w

theorem Balanced.mono {G : SimpleGraph V} {D D' : ℝ} (h : D ≤ D') {H : G.Subgraph}
    (hH : Balanced D H) : Balanced D' H := by
  intro v hv w hw
  exact (hH v hv w hw).trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))

/-- A balanced subgraph containing a vertex of degree `0` has no edges. -/
theorem Balanced.edgeSet_eq_empty_of_sdeg_eq_zero [Finite V] {G : SimpleGraph V} {D : ℝ}
    {H : G.Subgraph} (hH : Balanced D H) {v : V} (hv : v ∈ H.verts) (h0 : sdeg H v = 0) :
    H.edgeSet = ∅ := by
  have hzero : ∀ w ∈ H.verts, H.neighborSet w = ∅ := by
    intro w hw
    have h1 : (sdeg H w : ℝ) ≤ D * (sdeg H v : ℝ) := hH w hw v hv
    rw [h0, Nat.cast_zero, mul_zero] at h1
    have h2 : sdeg H w = 0 := Nat.le_zero.mp (by exact_mod_cast h1)
    exact (Set.ncard_eq_zero (Set.toFinite _)).mp h2
  rw [Set.eq_empty_iff_forall_notMem]
  intro e
  induction e using Sym2.ind with
  | _ x y =>
    rw [Subgraph.mem_edgeSet]
    intro he
    have hy : y ∈ H.neighborSet x := he
    rw [hzero x (H.edge_vert he)] at hy
    exact hy

/-- Inside a subgraph with finitely many neighbours, `sdeg` agrees with `Subgraph.degree`. -/
private theorem sdeg_eq_degree {G : SimpleGraph V} (H : G.Subgraph) (v : V)
    [Fintype (H.neighborSet v)] : sdeg H v = H.degree v :=
  (Set.ncard_eq_toFinset_card' _).trans (Set.toFinset_card _)

/-- Handshake identity inside a subgraph of a graph on a finite vertex type. -/
theorem sum_sdeg [Fintype V] [DecidableEq V] {G : SimpleGraph V} (H : G.Subgraph) :
    ∑ v ∈ H.verts.toFinite.toFinset, sdeg H v = 2 * H.edgeSet.ncard := by
  classical
  have hfv : Fintype H.verts := Fintype.ofFinite _
  have hdec : DecidableRel H.coe.Adj := Classical.decRel _
  have key := H.coe.sum_degrees_eq_twice_card_edges
  simp only [Subgraph.coe_degree, ← sdeg_eq_degree, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at key
  have himg : H.coe.edgeSet.ncard = H.edgeSet.ncard := by
    rw [← H.image_coe_edgeSet_coe,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  rw [Finset.sum_subtype (F := hfv) _ (fun x => H.verts.toFinite.mem_toFinset) (sdeg H), key,
    himg]

/-- Every degree inside `H` is at most the number of vertices of `H`. -/
theorem sdeg_le_ncard_verts [Finite V] {G : SimpleGraph V} (H : G.Subgraph) (v : V) :
    sdeg H v ≤ H.verts.ncard :=
  Set.ncard_le_ncard (H.neighborSet_subset_verts v) (Set.toFinite _)

/-- The uniform form of the Erdős–Simonovits question with constants `ε`, `D`: for every `m₀`,
all sufficiently large graphs with `n log₂ n` edges contain a `D`-balanced subgraph on at least
`m₀` vertices with at least `ε m log₂ m` edges. -/
def ErdosSimonovitsUniform (ε D : ℝ) : Prop :=
  ∀ m₀ : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    (n : ℝ) * Real.logb 2 n ≤ G.edgeSet.ncard →
      ∃ H : G.Subgraph, m₀ ≤ H.verts.ncard ∧ Balanced D H ∧
        ε * H.verts.ncard * Real.logb 2 H.verts.ncard ≤ H.edgeSet.ncard

/-- The literal form: a `D`-balanced subgraph on exactly `m` vertices. -/
def ErdosSimonovitsLiteral (ε D : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    (n : ℝ) * Real.logb 2 n ≤ G.edgeSet.ncard →
      ∃ H : G.Subgraph, H.verts.ncard = m ∧ Balanced D H ∧
        ε * m * Real.logb 2 m ≤ H.edgeSet.ncard

theorem ErdosSimonovitsLiteral.uniform {ε D : ℝ} (h : ErdosSimonovitsLiteral ε D) :
    ErdosSimonovitsUniform ε D := by
  intro m₀
  obtain ⟨n₀, hn₀⟩ := h (max m₀ 1) (le_max_right _ _)
  refine ⟨n₀, fun n hn G hG => ?_⟩
  obtain ⟨H, hcard, hbal, hedge⟩ := hn₀ n hn G hG
  refine ⟨H, ?_, hbal, ?_⟩
  · rw [hcard]
    exact le_max_left _ _
  · rw [hcard]
    exact hedge

end Erdos803
