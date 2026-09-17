import Mathlib

/-!
# JSP-000671 / Erdős #814 — size-uncapped `k`-core existence

We formalize the clean existence direction: a graph on `n` vertices with more than
`(k - 1) · n` edges contains a nonempty induced subgraph of minimum degree `≥ k`.

The proof is the standard degeneracy / vertex-removal argument.  We generalize to an
arbitrary vertex set `W` together with the (ordered-pair) induced edge count `e G W`, and
argue by strong induction on `W`: either every vertex of `W` has `≥ k` neighbours inside
`W` (take `S = W`), or some vertex has `< k` neighbours inside `W` and we recurse on
`W.erase v`, using the identity `e G W = e G (W.erase v) + 2 * d` where `d` is the number
of neighbours of `v` inside `W`.
-/

namespace Erdos814

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S` induces a subgraph of minimum degree `≥ k` (every vertex of `S` has `≥ k`
neighbours in `S`). -/
def InducedMinDegGe (G : SimpleGraph V) (k : ℕ) (S : Finset V) : Prop :=
  ∀ v ∈ S, k ≤ (S.filter (fun w => G.Adj v w)).card

/-- The number of *ordered* adjacent pairs with both endpoints in `W`; equal to twice the
number of edges of `G` inside `W`.  Written as a sum of in-`W` degrees. -/
noncomputable def e (G : SimpleGraph V) (W : Finset V) : ℕ :=
  ∑ a ∈ W, (W.filter (fun b => G.Adj a b)).card

omit [Fintype V] in
/-- Removing a vertex `v ∈ W` decreases the ordered edge count by twice the number of
neighbours of `v` inside `W`. -/
lemma e_erase (G : SimpleGraph V) (W : Finset V) (v : V) (hv : v ∈ W) :
    e G W = e G (W.erase v) + 2 * (W.filter (fun w => G.Adj v w)).card := by
  have key : e G W = (W.filter (fun w => G.Adj v w)).card
      + ∑ a ∈ W.erase v, (W.filter (fun w => G.Adj a w)).card :=
    (Finset.add_sum_erase W (fun a => (W.filter (fun w => G.Adj a w)).card) hv).symm
  have hstep : ∀ a ∈ W.erase v, (W.filter (fun w => G.Adj a w)).card
      = ((W.erase v).filter (fun w => G.Adj a w)).card + (if G.Adj a v then 1 else 0) := by
    intro a _
    rw [Finset.filter_erase]
    split_ifs with hav
    · have hmem : v ∈ W.filter (fun w => G.Adj a w) := Finset.mem_filter.2 ⟨hv, hav⟩
      rw [Finset.card_erase_of_mem hmem, Nat.sub_add_cancel (Finset.card_pos.2 ⟨v, hmem⟩)]
    · have hnm : v ∉ W.filter (fun w => G.Adj a w) := fun hm => hav (Finset.mem_filter.1 hm).2
      rw [Finset.erase_eq_of_notMem hnm, Nat.add_zero]
  have hS1 : ∑ a ∈ W.erase v, ((W.erase v).filter (fun w => G.Adj a w)).card
      = e G (W.erase v) := rfl
  have hset : (W.erase v).filter (fun a => G.Adj a v) = W.filter (fun w => G.Adj v w) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, haW⟩, hav⟩
      exact ⟨haW, (G.adj_comm a v).mp hav⟩
    · rintro ⟨haW, hva⟩
      refine ⟨⟨?_, haW⟩, (G.adj_comm v a).mp hva⟩
      rintro rfl
      exact G.irrefl hva
  have hS2 : ∑ a ∈ W.erase v, (if G.Adj a v then 1 else 0)
      = (W.filter (fun w => G.Adj v w)).card := by
    rw [Finset.sum_boole, Nat.cast_id, hset]
  have hsum : ∑ a ∈ W.erase v, (W.filter (fun w => G.Adj a w)).card
      = e G (W.erase v) + (W.filter (fun w => G.Adj v w)).card := by
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hS1, hS2]
  rw [key, hsum]
  ring

/-- Core induction: any vertex set `W` with `2 * (k - 1) * |W| < e G W` contains a nonempty
induced subgraph of minimum degree `≥ k`. -/
lemma core_aux (G : SimpleGraph V) (k : ℕ) :
    ∀ W : Finset V, 2 * (k - 1) * W.card < e G W →
      ∃ S : Finset V, S ⊆ W ∧ S.Nonempty ∧ InducedMinDegGe G k S := by
  intro W
  induction W using Finset.strongInductionOn with
  | _ W IH =>
    intro hW
    by_cases hmin : ∀ v ∈ W, k ≤ (W.filter (fun w => G.Adj v w)).card
    · refine ⟨W, subset_rfl, ?_, hmin⟩
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp [e] at hW
    · simp only [not_forall, not_le] at hmin
      obtain ⟨v, hv, hdv⟩ := hmin
      have hsub : W.erase v ⊂ W := Finset.erase_ssubset hv
      have hcard : W.card = (W.erase v).card + 1 := by
        rw [Finset.card_erase_of_mem hv]
        have : 0 < W.card := Finset.card_pos.2 ⟨v, hv⟩
        omega
      have hident : e G W = e G (W.erase v) + 2 * (W.filter (fun w => G.Adj v w)).card :=
        e_erase G W v hv
      have hrec : 2 * (k - 1) * (W.erase v).card < e G (W.erase v) := by
        have hd : (W.filter (fun w => G.Adj v w)).card ≤ k - 1 := by omega
        have hexp : 2 * (k - 1) * W.card
            = 2 * (k - 1) * (W.erase v).card + 2 * (k - 1) := by
          rw [hcard]; ring
        omega
      obtain ⟨S, hSsub, hSne, hSmin⟩ := IH (W.erase v) hsub hrec
      exact ⟨S, hSsub.trans (Finset.erase_subset v W), hSne, hSmin⟩

omit [DecidableEq V] in
/-- Over the whole vertex set, `e G` equals twice the number of edges. -/
lemma e_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    e G Finset.univ = 2 * G.edgeFinset.card := by
  have h1 : ∀ a : V, (Finset.univ.filter (fun b => G.Adj a b)).card = G.degree a := by
    intro a
    have hs : (Finset.univ.filter (fun b => G.Adj a b)) = G.neighborFinset a := by
      ext b; simp [SimpleGraph.mem_neighborFinset]
    rw [hs, SimpleGraph.card_neighborFinset_eq_degree]
  have h2 : e G Finset.univ = ∑ a : V, G.degree a := by
    unfold e
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.filter_congr_decidable]
    exact h1 a
  rw [h2, SimpleGraph.sum_degrees_eq_twice_card_edges]

/-- A graph with more than `(k - 1)·n` edges contains a nonempty induced subgraph of
minimum degree `≥ k`. -/
theorem exists_core (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : (k - 1) * Fintype.card V < G.edgeFinset.card) :
    ∃ S : Finset V, S.Nonempty ∧ InducedMinDegGe G k S := by
  have huniv : 2 * (k - 1) * (Finset.univ : Finset V).card < e G Finset.univ := by
    rw [e_univ G, Finset.card_univ]
    have hmul : 2 * (k - 1) * Fintype.card V = 2 * ((k - 1) * Fintype.card V) := by ring
    omega
  obtain ⟨S, _, hSne, hSmin⟩ := core_aux G k Finset.univ huniv
  exact ⟨S, hSne, hSmin⟩

#print axioms Erdos814.exists_core

end Erdos814
