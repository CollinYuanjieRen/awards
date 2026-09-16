import Proof.ShortestOddCycle
import Proof.OddCycle

/-!
# Erdős Problem 1011: the Erdős–Gallai upper bound

Split the edges of `G` by how many endpoints lie on the vertex set `S` of a shortest odd cycle `c`
(length `m`): edges inside `S` number `m` (chordless), edges between `S` and its complement number at
most `2 (n - m)` (each outside vertex sends at most two), and edges inside the complement number at
most `⌊(n - m)² / 4⌋` (Mantel).  With `bound_arith` this gives `e(G) ≤ ⌊(n - 1)² / 4⌋ + 1`.
-/

open Finset SimpleGraph

namespace Erdos1011

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Edges of `G` with both endpoints outside `S` are at most `⌊(n - |S|)² / 4⌋` when `G` is
triangle-free. -/
theorem card_edges_outside_le (hG : G.CliqueFree 3) (S : Finset V) :
    (G.edgeFinset.filter fun e => ∀ x ∈ e, x ∉ S).card ≤ (Fintype.card V - S.card) ^ 2 / 4 := by
  have : DecidableRel (G.comap (Subtype.val : {x : V // x ∉ S} → V)).Adj := fun a b =>
    inferInstanceAs (Decidable (G.Adj a.val b.val))
  have hfree : (G.comap (Subtype.val : {x : V // x ∉ S} → V)).CliqueFree 3 :=
    hG.comap ⟨⟨⟨Subtype.val, fun h => h⟩, Subtype.val_injective⟩⟩
  have hcard : Fintype.card {x : V // x ∉ S} = Fintype.card V - S.card := by
    rw [← Finset.card_compl, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp))
  have hsurj : Set.SurjOn (Sym2.map (Subtype.val : {x : V // x ∉ S} → V))
      ↑(G.comap (Subtype.val : {x : V // x ∉ S} → V)).edgeFinset
      ↑(G.edgeFinset.filter fun e => ∀ x ∈ e, x ∉ S) := by
    rintro e he
    simp only [Finset.mem_coe, Finset.mem_filter, mem_edgeFinset] at he
    obtain ⟨he₁, he₂⟩ := he
    induction e using Sym2.ind with
    | _ a b =>
      have ha : a ∉ S := he₂ a (by simp)
      have hb : b ∉ S := he₂ b (by simp)
      rw [mem_edgeSet] at he₁
      exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa [comap_adj] using he₁, rfl⟩
  calc (G.edgeFinset.filter fun e => ∀ x ∈ e, x ∉ S).card
      ≤ #(G.comap (Subtype.val : {x : V // x ∉ S} → V)).edgeFinset :=
        Finset.card_le_card_of_surjOn _ hsurj
    _ ≤ Fintype.card {x : V // x ∉ S} ^ 2 / 4 := mantel _ hfree
    _ = (Fintype.card V - S.card) ^ 2 / 4 := by rw [hcard]

/-- Edges of `G` with exactly one endpoint in `S` are counted by the neighbours in `S` of the
outside vertices. -/
theorem card_edges_between_eq (S : Finset V) :
    (G.edgeFinset.filter fun e => ∃ x ∈ e, x ∈ S ∧ ∃ y ∈ e, y ∉ S).card =
      ∑ x ∈ univ.filter (· ∉ S), (G.neighborFinset x ∩ S).card := by
  have hinj : ∀ x : V, Function.Injective fun y : V => s(x, y) := by
    intro x y₁ y₂ h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h₁, h₂⟩
    · exact h
    · rw [h₂, ← h₁]
  have hdisj : ((univ.filter (· ∉ S) : Finset V) : Set V).PairwiseDisjoint
      fun x => (G.neighborFinset x ∩ S).image fun y => s(x, y) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image, Finset.mem_inter]
    rintro e ⟨u, ⟨-, huS⟩, rfl⟩ ⟨w, ⟨-, -⟩, hw⟩
    rw [Sym2.eq_iff] at hw
    rcases hw with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact hxy h₁.symm
    · exact hy (h₁ ▸ huS)
  have step : ∑ x ∈ univ.filter (· ∉ S), (G.neighborFinset x ∩ S).card
      = ∑ x ∈ univ.filter (· ∉ S), ((G.neighborFinset x ∩ S).image fun y => s(x, y)).card :=
    Finset.sum_congr rfl fun x _ => (Finset.card_image_of_injective _ (hinj x)).symm
  rw [step, ← Finset.card_biUnion hdisj]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, Sym2.mem_iff, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_inter, mem_neighborFinset, Finset.mem_univ, true_and,
      Sym2.eq_iff]
    constructor
    · rintro ⟨hab, x, hx, hxS, y, hy, hyS⟩
      rcases hx with rfl | rfl
      · rcases hy with rfl | rfl
        · exact absurd hxS hyS
        · exact ⟨y, hyS, x, ⟨hab.symm, hxS⟩, Or.inr ⟨rfl, rfl⟩⟩
      · rcases hy with rfl | rfl
        · exact ⟨y, hyS, x, ⟨hab, hxS⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact absurd hxS hyS
    · rintro ⟨i, hiS, y, ⟨hiy, hyS⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨hiy, y, Or.inr rfl, hyS, i, Or.inl rfl, hiS⟩
      · exact ⟨hiy.symm, y, Or.inl rfl, hyS, i, Or.inr rfl, hiS⟩

/-- The edge set splits into the three classes. -/
theorem card_edgeFinset_eq_add (S : Finset V) :
    #G.edgeFinset = (G.edgeFinset.filter fun e => ∀ x ∈ e, x ∈ S).card +
      (G.edgeFinset.filter fun e => ∃ x ∈ e, x ∈ S ∧ ∃ y ∈ e, y ∉ S).card +
      (G.edgeFinset.filter fun e => ∀ x ∈ e, x ∉ S).card := by
  simp only [Finset.card_filter]
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]

/-- The bound in terms of a shortest odd cycle of length `m`. -/
theorem card_edgeFinset_le_of_isShortestOddCycle (hG : G.CliqueFree 3) {v : V} {c : G.Walk v v}
    (hc : IsShortestOddCycle c) :
    #G.edgeFinset ≤ c.length + 2 * (Fintype.card V - c.length) +
      (Fintype.card V - c.length) ^ 2 / 4 := by
  have hvs : (vset c).card = c.length := card_vset_eq_length hc.1
  have hin : (G.edgeFinset.filter fun e => ∀ x ∈ e, x ∈ vset c).card = c.length :=
    card_edges_within hG hc
  have hout : (G.edgeFinset.filter fun e => ∀ x ∈ e, x ∉ vset c).card
      ≤ (Fintype.card V - c.length) ^ 2 / 4 := by
    have h := card_edges_outside_le hG (vset c)
    rwa [hvs] at h
  have hbet : (G.edgeFinset.filter fun e => ∃ x ∈ e, x ∈ vset c ∧ ∃ y ∈ e, y ∉ vset c).card
      ≤ 2 * (Fintype.card V - c.length) := by
    rw [card_edges_between_eq (vset c)]
    have hle : ∀ x ∈ univ.filter (· ∉ vset c), (G.neighborFinset x ∩ vset c).card ≤ 2 := by
      intro x hx
      exact card_neighbors_le_two hG hc (by simpa using hx)
    calc ∑ x ∈ univ.filter (· ∉ vset c), (G.neighborFinset x ∩ vset c).card
        ≤ ∑ _x ∈ univ.filter (· ∉ vset c), 2 := Finset.sum_le_sum hle
      _ = #(univ.filter (· ∉ vset c) : Finset V) * 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ = 2 * (Fintype.card V - c.length) := by
          rw [show (univ.filter (· ∉ vset c) : Finset V) = (vset c)ᶜ by ext x; simp,
            Finset.card_compl, hvs, Nat.mul_comm]
  rw [card_edgeFinset_eq_add (vset c), hin]
  exact Nat.add_le_add (Nat.add_le_add_left hbet _) hout

/-- **Erdős–Gallai, upper bound.** A triangle-free graph that is not `2`-colourable has at most
`⌊(n - 1)² / 4⌋ + 1` edges. -/
theorem card_edgeFinset_le (hG : G.CliqueFree 3) (hb : ¬ G.Colorable 2) :
    #G.edgeFinset ≤ (Fintype.card V - 1) ^ 2 / 4 + 1 := by
  obtain ⟨v, c, hc⟩ := exists_isShortestOddCycle (exists_odd_cycle G hb)
  have hlen : 5 ≤ c.length := five_le_length hG hc.1 hc.2.1
  have hle : c.length ≤ Fintype.card V := by
    rw [← card_vset_eq_length hc.1]
    exact Finset.card_le_univ _
  exact (card_edgeFinset_le_of_isShortestOddCycle hG hc).trans (bound_arith hc.2.1 hlen hle)

end Erdos1011
