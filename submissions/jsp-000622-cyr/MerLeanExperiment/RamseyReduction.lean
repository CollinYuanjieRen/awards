import MerLeanExperiment.SmallCatalog

noncomputable section

/-!
Structural consequences of forbidding homogeneous four-sets.  These lemmas
reduce the neighborhoods used by the later catalog argument to `R(3,4)`-free
graphs on at most eight vertices.
-/

namespace CochromaticTwenty

open Finset

variable {V : Type*} {G : SimpleGraph V}

local instance {W : Type*} (H : SimpleGraph W) : DecidableRel H.Adj :=
  Classical.decRel _

/-- A graph has no clique of size four and no independent set of size four. -/
def NoHomogeneousFour (G : SimpleGraph V) : Prop :=
  ¬ HasCliqueOfSize G 4 ∧ ¬ HasIndependentOfSize G 4

@[simp]
theorem noHomogeneousFour_compl_iff :
    NoHomogeneousFour Gᶜ ↔ NoHomogeneousFour G := by
  simp [NoHomogeneousFour, and_comm]

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

private theorem hasIndependentOfSize_of_induce {S : Set V} {n : ℕ} :
    HasIndependentOfSize (G.induce S) n → HasIndependentOfSize G n := by
  rintro ⟨s, hcard, hs⟩
  refine ⟨s.map (Function.Embedding.subtype _), by simpa using hcard, ?_⟩
  exact isIndependent_map_induce s hs

/-- The graph induced by the neighbors of a vertex is `R(3,4)`-free. -/
theorem neighbor_induce_r34Free (hG : NoHomogeneousFour G) (v : V) :
    R34Free (G.induce (G.neighborSet v)) := by
  classical
  constructor
  · rintro ⟨s, hscard, hs⟩
    let e : G.neighborSet v ↪ V := Function.Embedding.subtype _
    let t : Finset V := s.map e
    have htcard : t.card = 3 := by simp [t, hscard]
    have htclique : G.IsClique t := by
      simpa only [t, e] using isClique_map_induce s hs
    have hvadj : ∀ w ∈ t, G.Adj v w := by
      intro w hw
      rw [Finset.mem_map] at hw
      obtain ⟨w, _, rfl⟩ := hw
      exact w.property
    have hthree : G.IsNClique 3 t := by
      rw [SimpleGraph.isNClique_iff]
      exact ⟨htclique, htcard⟩
    have hfour := hthree.insert hvadj
    exact hG.1 ⟨insert v t, hfour.card_eq, hfour.isClique⟩
  · exact fun h ↦ hG.2 (hasIndependentOfSize_of_induce h)

/-- On the nonneighbors of a vertex, the complement of the induced graph is
`R(3,4)`-free. -/
theorem nonneighbor_induce_compl_r34Free (hG : NoHomogeneousFour G) (v : V) :
    R34Free ((G.induce ((Gᶜ).neighborSet v))ᶜ) := by
  have hfree := neighbor_induce_r34Free
    (G := Gᶜ) (noHomogeneousFour_compl_iff.mpr hG) v
  have heq : (Gᶜ).induce ((Gᶜ).neighborSet v) =
      (G.induce ((Gᶜ).neighborSet v))ᶜ := by
    ext u w
    simp
    intro _
    constructor
    · intro hval huw
      exact hval (congrArg Subtype.val huw)
    · intro huw hval
      exact huw (Subtype.ext hval)
  rwa [heq] at hfree

/-- The finite Ramsey bound `R(3,4) ≤ 9` forces every `R(3,4)`-free
finite graph to have at most eight vertices. -/
theorem r34Free_card_le_eight [Fintype V] (hG : R34Free G) :
    Fintype.card V ≤ 8 := by
  classical
  by_contra hcard
  have hnine : 9 ≤ Fintype.card V := by omega
  have huniv : 9 ≤ (Finset.univ : Finset V).card := by simpa using hnine
  obtain ⟨s, _, hscard⟩ := Finset.exists_subset_card_eq huniv
  let S : Set V := (s : Set V)
  have hSCard : Fintype.card S = 9 := by simp [S, hscard]
  have hfree : R34Free (G.induce S) :=
    r34Free_comap G (Function.Embedding.subtype _) hG
  rcases ramsey_three_four (G.induce S) hSCard with hc | hi
  · exact hfree.1 hc
  · exact hfree.2 hi

/-- Every neighborhood in a graph with no homogeneous four-set has at most
eight vertices. -/
theorem neighbor_card_le_eight [Fintype V]
    (hG : NoHomogeneousFour G) (v : V) : G.degree v ≤ 8 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact r34Free_card_le_eight (neighbor_induce_r34Free hG v)

/-- Every nonneighborhood (excluding the center vertex) in a graph with no
homogeneous four-set has at most eight vertices. -/
theorem nonneighbor_card_le_eight [Fintype V]
    (hG : NoHomogeneousFour G) (v : V) : (Gᶜ).degree v ≤ 8 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact r34Free_card_le_eight (nonneighbor_induce_compl_r34Free hG v)

/-- Relabel an `R(3,4)`-free finite graph on `n` vertices as an actual graph
on `Fin n`. -/
theorem R34Free.overFin {n : ℕ} [Fintype V] (hG : R34Free G)
    (hcard : Fintype.card V = n) : R34Free (G.overFin hcard) :=
  r34Free_iso (G.overFinIso hcard) hG

/-- On sixteen vertices every degree is seven or eight. -/
theorem degree_seven_or_eight_of_card_sixteen [Fintype V]
    (hcard : Fintype.card V = 16) (hG : NoHomogeneousFour G) (v : V) :
    G.degree v = 7 ∨ G.degree v = 8 := by
  have hupper := neighbor_card_le_eight hG v
  have hcomp := nonneighbor_card_le_eight hG v
  rw [SimpleGraph.degree_compl, hcard] at hcomp
  omega

/-- A sixteen-vertex graph with no homogeneous four-set can be complemented,
if necessary, so that a selected vertex has degree seven. -/
theorem choose_degree_seven_of_card_sixteen [Fintype V]
    (hcard : Fintype.card V = 16) (hG : NoHomogeneousFour G) :
    ∃ H : SimpleGraph V,
      (H = G ∨ H = Gᶜ) ∧ NoHomogeneousFour H ∧
        ∃ v : V, H.degree v = 7 := by
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice hV
  rcases degree_seven_or_eight_of_card_sixteen hcard hG v with hv | hv
  · exact ⟨G, Or.inl rfl, hG, v, hv⟩
  · refine ⟨Gᶜ, Or.inr rfl, noHomogeneousFour_compl_iff.mpr hG, v, ?_⟩
    rw [SimpleGraph.degree_compl, hcard, hv]

/-- On twelve vertices every degree lies between three and eight. -/
theorem degree_between_three_and_eight_of_card_twelve [Fintype V]
    (hcard : Fintype.card V = 12) (hG : NoHomogeneousFour G) (v : V) :
    3 ≤ G.degree v ∧ G.degree v ≤ 8 := by
  have hupper := neighbor_card_le_eight hG v
  have hcomp := nonneighbor_card_le_eight hG v
  rw [SimpleGraph.degree_compl, hcard] at hcomp
  omega

/-- A twelve-vertex graph with no homogeneous four-set can be complemented,
if necessary, so that a selected vertex has degree three, four, or five. -/
theorem choose_degree_three_four_or_five_of_card_twelve [Fintype V]
    (hcard : Fintype.card V = 12) (hG : NoHomogeneousFour G) :
    ∃ H : SimpleGraph V,
      (H = G ∨ H = Gᶜ) ∧ NoHomogeneousFour H ∧
        ∃ v : V, H.degree v = 3 ∨ H.degree v = 4 ∨ H.degree v = 5 := by
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice hV
  have hv := degree_between_three_and_eight_of_card_twelve hcard hG v
  by_cases hsmall : G.degree v ≤ 5
  · refine ⟨G, Or.inl rfl, hG, v, ?_⟩
    omega
  · refine ⟨Gᶜ, Or.inr rfl, noHomogeneousFour_compl_iff.mpr hG, v, ?_⟩
    have hcomp := degree_between_three_and_eight_of_card_twelve
      (G := Gᶜ) hcard (noHomogeneousFour_compl_iff.mpr hG) v
    rw [SimpleGraph.degree_compl, hcard] at hcomp ⊢
    omega

end CochromaticTwenty

#print axioms CochromaticTwenty.neighbor_induce_r34Free
#print axioms CochromaticTwenty.nonneighbor_induce_compl_r34Free
#print axioms CochromaticTwenty.r34Free_card_le_eight
#print axioms CochromaticTwenty.choose_degree_seven_of_card_sixteen
#print axioms CochromaticTwenty.choose_degree_three_four_or_five_of_card_twelve
