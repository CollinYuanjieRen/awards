import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
Small finite Ramsey bounds used by the cochromatic-number development.
The predicates below expose both the finite cardinality and the pairwise graph
condition, rather than storing a certificate or a precomputed answer.
-/

namespace CochromaticTwenty

open Finset

variable {V : Type*} {G : SimpleGraph V}

/-- A clique with exactly `n` vertices. -/
def HasCliqueOfSize (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ s : Finset V, s.card = n ∧ G.IsClique s

/-- An independent set with exactly `n` vertices. -/
def HasIndependentOfSize (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ s : Finset V, s.card = n ∧ G.IsIndepSet s

@[simp]
theorem hasCliqueOfSize_compl_iff {n : ℕ} :
    HasCliqueOfSize Gᶜ n ↔ HasIndependentOfSize G n := by
  simp [HasCliqueOfSize, HasIndependentOfSize, SimpleGraph.isClique_compl]

@[simp]
theorem hasIndependentOfSize_compl_iff {n : ℕ} :
    HasIndependentOfSize Gᶜ n ↔ HasCliqueOfSize G n := by
  simp [HasCliqueOfSize, HasIndependentOfSize, SimpleGraph.isIndepSet_compl]

private theorem isClique_map_induce {S : Set V} (s : Finset S)
    (hs : (G.induce S).IsClique s) :
    G.IsClique (s.map (Function.Embedding.subtype _)) := by
  intro a ha b hb hab
  change a ∈ s.map (Function.Embedding.subtype _) at ha
  change b ∈ s.map (Function.Embedding.subtype _) at hb
  rw [Finset.mem_map] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  exact hs ha' hb' (ne_of_apply_ne _ hab)

private theorem isIndependent_map_induce {S : Set V} (s : Finset S)
    (hs : (G.induce S).IsIndepSet s) :
    G.IsIndepSet (s.map (Function.Embedding.subtype _)) := by
  intro a ha b hb hab
  change a ∈ s.map (Function.Embedding.subtype _) at ha
  change b ∈ s.map (Function.Embedding.subtype _) at hb
  rw [Finset.mem_map] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  exact hs ha' hb' (ne_of_apply_ne _ hab)

private theorem HasCliqueOfSize.of_induce {S : Set V} {n : ℕ} :
    HasCliqueOfSize (G.induce S) n → HasCliqueOfSize G n := by
  rintro ⟨s, hs_card, hs⟩
  let e : S ↪ V := Function.Embedding.subtype _
  refine ⟨s.map e, by simp [hs_card], ?_⟩
  simpa only [e] using isClique_map_induce s hs

private theorem HasIndependentOfSize.of_induce {S : Set V} {n : ℕ} :
    HasIndependentOfSize (G.induce S) n → HasIndependentOfSize G n := by
  rintro ⟨s, hs_card, hs⟩
  let e : S ↪ V := Function.Embedding.subtype _
  refine ⟨s.map e, by simp [hs_card], ?_⟩
  simpa only [e] using isIndependent_map_induce s hs

private theorem neighbor_three {v : V} [Fintype V] [DecidableRel G.Adj]
    (hdeg : 3 ≤ G.degree v) :
    HasCliqueOfSize G 3 ∨ HasIndependentOfSize G 3 := by
  classical
  obtain ⟨s, hs, hs_card⟩ := Finset.exists_subset_card_eq hdeg
  by_cases hedge : ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ G.Adj a b
  · obtain ⟨a, ha, b, hb, hab, hab_adj⟩ := hedge
    have hva : G.Adj v a := by simpa using hs ha
    have hvb : G.Adj v b := by simpa using hs hb
    have hc : G.IsNClique 3 {v, a, b} :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨hva, hvb, hab_adj⟩
    exact Or.inl ⟨{v, a, b}, hc.card_eq, hc.isClique⟩
  · refine Or.inr ⟨s, hs_card, ?_⟩
    intro a ha b hb hab hadj
    exact hedge ⟨a, ha, b, hb, hab, hadj⟩

/-- The finite Ramsey bound `R(3,3) ≤ 6`, for every finite vertex type with
at least six elements. -/
theorem ramsey_three_three [Fintype V] (G : SimpleGraph V)
    (hcard : 6 ≤ Fintype.card V) :
    HasCliqueOfSize G 3 ∨ HasIndependentOfSize G 3 := by
  classical
  let hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice hV
  by_cases hdeg : 3 ≤ G.degree v
  · exact neighbor_three hdeg
  · have hdeg_compl : 3 ≤ Gᶜ.degree v := by
      rw [SimpleGraph.degree_compl]
      omega
    rcases neighbor_three (G := Gᶜ) hdeg_compl with hc | hi
    · exact Or.inr (hasCliqueOfSize_compl_iff.mp hc)
    · exact Or.inl (hasIndependentOfSize_compl_iff.mp hi)

private theorem degree_le_three_of_no_small_sets [Fintype V] [DecidableRel G.Adj]
    (htriangle : G.CliqueFree 3) (hno_independent : ¬ HasIndependentOfSize G 4)
    (v : V) : G.degree v ≤ 3 := by
  classical
  by_contra hdeg
  obtain ⟨s, hs, hs_card⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ G.degree v)
  apply hno_independent
  refine ⟨s, hs_card, ?_⟩
  apply (G.isIndepSet_neighborSet_of_triangleFree htriangle v).mono
  intro w hw
  simpa using hs hw

private theorem degree_ge_three_of_no_small_sets [Fintype V] [DecidableRel G.Adj]
    (hcard : Fintype.card V = 9)
    (hno_clique : ¬ HasCliqueOfSize G 3)
    (hno_independent : ¬ HasIndependentOfSize G 4)
    (v : V) : 3 ≤ G.degree v := by
  classical
  by_contra hdeg
  have hdeg_compl : 6 ≤ Gᶜ.degree v := by
    rw [SimpleGraph.degree_compl, hcard]
    omega
  obtain ⟨s, hs, hs_card⟩ := Finset.exists_subset_card_eq hdeg_compl
  let S : Set V := (s : Set V)
  have hS_card : 6 ≤ Fintype.card S := by
    simp [S, hs_card]
  rcases ramsey_three_three (G.induce S) hS_card with hc | hi
  · exact hno_clique hc.of_induce
  · obtain ⟨t, ht_card, ht⟩ := hi
    let e : S ↪ V := Function.Embedding.subtype _
    let u : Finset V := t.map e
    have hu_card : u.card = 3 := by simp [u, ht_card]
    have hu_independent : G.IsIndepSet (u : Set V) := by
      simpa only [u, e] using isIndependent_map_induce t ht
    have hu_compl : ∀ w ∈ u, Gᶜ.Adj v w := by
      intro w hw
      change w ∈ t.map e at hw
      rw [Finset.mem_map] at hw
      obtain ⟨x, _, rfl⟩ := hw
      simpa [e] using hs x.property
    have hv_not_mem : v ∉ u := by
      intro hv
      exact (Gᶜ).irrefl (hu_compl v hv)
    have hfour : G.IsNIndepSet 4 (insert v u) := by
      rw [← SimpleGraph.isNClique_compl]
      have hthree : Gᶜ.IsNClique 3 u := by
        rw [SimpleGraph.isNClique_iff]
        exact ⟨by simpa using hu_independent, hu_card⟩
      simpa using hthree.insert (fun w hw ↦ hu_compl w hw)
    exact hno_independent ⟨insert v u, hfour.card_eq, hfour.isIndepSet⟩

/-- The finite Ramsey bound `R(3,4) ≤ 9`. -/
theorem ramsey_three_four [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V = 9) :
    HasCliqueOfSize G 3 ∨ HasIndependentOfSize G 4 := by
  classical
  by_cases hclique : HasCliqueOfSize G 3
  · exact Or.inl hclique
  by_cases hindependent : HasIndependentOfSize G 4
  · exact Or.inr hindependent
  have htriangle : G.CliqueFree 3 := by
    intro s hs
    exact hclique ⟨s, hs.card_eq, hs.isClique⟩
  have hdegree : ∀ v : V, G.degree v = 3 := by
    intro v
    exact Nat.le_antisymm
      (degree_le_three_of_no_small_sets htriangle hindependent v)
      (degree_ge_three_of_no_small_sets hcard hclique hindependent v)
  have heven := G.even_card_odd_degree_vertices
  have hall : (Finset.univ.filter fun v : V ↦ Odd (G.degree v)) = Finset.univ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hdegree v]
    norm_num [Odd]
  rw [hall, Finset.card_univ, hcard] at heven
  norm_num [Even] at heven

private theorem neighbor_nine {v : V} [Fintype V] [DecidableRel G.Adj]
    (hdeg : 9 ≤ G.degree v) :
    HasCliqueOfSize G 4 ∨ HasIndependentOfSize G 4 := by
  classical
  obtain ⟨s, hs, hs_card⟩ := Finset.exists_subset_card_eq hdeg
  let S : Set V := (s : Set V)
  have hS_card : Fintype.card S = 9 := by simp [S, hs_card]
  rcases ramsey_three_four (G.induce S) hS_card with hc | hi
  · obtain ⟨t, ht_card, ht⟩ := hc
    let e : S ↪ V := Function.Embedding.subtype _
    let u : Finset V := t.map e
    have hu_clique : G.IsNClique 3 u := by
      rw [SimpleGraph.isNClique_iff]
      refine ⟨?_, by simp [u, ht_card]⟩
      simpa only [u, e] using isClique_map_induce t ht
    have hu_neighbor : ∀ w ∈ u, G.Adj v w := by
      intro w hw
      change w ∈ t.map e at hw
      rw [Finset.mem_map] at hw
      obtain ⟨x, _, rfl⟩ := hw
      simpa [e] using hs x.property
    have hfour := hu_clique.insert (fun w hw ↦ hu_neighbor w hw)
    exact Or.inl ⟨insert v u, hfour.card_eq, hfour.isClique⟩
  · exact Or.inr hi.of_induce

/-- The finite Ramsey bound `R(4,4) ≤ 18`, for every finite vertex type with
at least eighteen elements. -/
theorem ramsey_four_four [Fintype V] (G : SimpleGraph V)
    (hcard : 18 ≤ Fintype.card V) :
    HasCliqueOfSize G 4 ∨ HasIndependentOfSize G 4 := by
  classical
  let hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice hV
  by_cases hdeg : 9 ≤ G.degree v
  · exact neighbor_nine hdeg
  · have hdeg_compl : 9 ≤ Gᶜ.degree v := by
      rw [SimpleGraph.degree_compl]
      omega
    rcases neighbor_nine (G := Gᶜ) hdeg_compl with hc | hi
    · exact Or.inr (hasCliqueOfSize_compl_iff.mp hc)
    · exact Or.inl (hasIndependentOfSize_compl_iff.mp hi)

/-- Every graph on `Fin 6` has a homogeneous set of size three. -/
theorem fin6_has_homogeneous_three (G : SimpleGraph (Fin 6)) :
    HasCliqueOfSize G 3 ∨ HasIndependentOfSize G 3 :=
  ramsey_three_three G (by simp)

/-- Every graph on `Fin 9` has a triangle or an independent set of size four. -/
theorem fin9_has_clique_three_or_independent_four (G : SimpleGraph (Fin 9)) :
    HasCliqueOfSize G 3 ∨ HasIndependentOfSize G 4 :=
  ramsey_three_four G (by simp)

/-- Every graph on `Fin 18` has a homogeneous set of size four. -/
theorem fin18_has_homogeneous_four (G : SimpleGraph (Fin 18)) :
    HasCliqueOfSize G 4 ∨ HasIndependentOfSize G 4 :=
  ramsey_four_four G (by simp)

end CochromaticTwenty

#print axioms CochromaticTwenty.fin6_has_homogeneous_three
#print axioms CochromaticTwenty.fin9_has_clique_three_or_independent_four
#print axioms CochromaticTwenty.fin18_has_homogeneous_four
