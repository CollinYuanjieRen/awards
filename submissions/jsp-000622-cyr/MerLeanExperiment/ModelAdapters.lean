import MerLeanExperiment.Target
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Embedding

/-!
Transport lemmas connecting the labelled `Fin 20` target to ordinary finite
simple graphs.  These statements do not prove either extremal bound.
-/

namespace CochromaticTwenty

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Homogeneity is inherited by subsets. -/
theorem homogeneous_mono {s t : Set V} (hst : t ⊆ s) :
    Homogeneous G s → Homogeneous G t := by
  rintro (hs | hs)
  · exact Or.inl (hs.mono hst)
  · exact Or.inr (hs.mono hst)

/-- A graph isomorphism sends a homogeneous set to a homogeneous set. -/
theorem homogeneous_image (e : G ≃g H) {s : Set V} (hs : Homogeneous G s) :
    Homogeneous H (e '' s) := by
  rcases hs with hs | hs
  · refine Or.inl (Set.Pairwise.image ?_)
    intro u hu v hv huv
    exact e.map_adj_iff.mpr (hs hu hv huv)
  · refine Or.inr (Set.Pairwise.image ?_)
    intro u hu v hv huv hadj
    exact hs hu hv huv (e.map_adj_iff.mp hadj)

/-- Homogeneity is invariant under graph isomorphism. -/
theorem homogeneous_image_iff (e : G ≃g H) (s : Set V) :
    Homogeneous H (e '' s) ↔ Homogeneous G s := by
  constructor
  · intro hs
    have h := homogeneous_image e.symm hs
    simpa only [Set.image_image, Function.comp_apply, e.symm_apply_apply,
      Set.image_id'] using h
  · exact homogeneous_image e

/-- Pull a cocoloring forward along a graph isomorphism. -/
theorem HasCocoloring.map_iso {k : ℕ} (e : G ≃g H) :
    HasCocoloring G k → HasCocoloring H k := by
  rintro ⟨color, hcolor⟩
  refine ⟨fun w ↦ color (e.symm w), ?_⟩
  intro i
  have hi := homogeneous_image e (hcolor i)
  convert hi using 1
  ext w
  constructor
  · intro hw
    exact ⟨e.symm w, hw, e.apply_symm_apply w⟩
  · rintro ⟨v, hv, rfl⟩
    change color (e.symm (e v)) = i
    rw [e.symm_apply_apply]
    exact hv

/-- Existence of a cocoloring is invariant under graph isomorphism. -/
theorem hasCocoloring_iso_iff {k : ℕ} (e : G ≃g H) :
    HasCocoloring G k ↔ HasCocoloring H k :=
  ⟨HasCocoloring.map_iso e, HasCocoloring.map_iso e.symm⟩

/-- Enlarging the palette preserves a cocoloring. -/
theorem HasCocoloring.mono {k l : ℕ} (hkl : k ≤ l) :
    HasCocoloring G k → HasCocoloring G l := by
  rintro ⟨color, hcolor⟩
  refine ⟨fun v ↦ Fin.castLE hkl (color v), ?_⟩
  intro i
  by_cases hi : ∃ j : Fin k, Fin.castLE hkl j = i
  · obtain ⟨j, rfl⟩ := hi
    exact homogeneous_mono
      (fun _ hv ↦ Fin.castLE_injective hkl hv) (hcolor j)
  · have hempty : {v | Fin.castLE hkl (color v) = i} = (∅ : Set V) := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hv
      exact hi ⟨color v, hv⟩
    rw [hempty]
    exact Or.inl (Set.pairwise_empty G.Adj)

/-- Relabel a graph on a finite type of cardinality twenty as a graph on `Fin 20`. -/
noncomputable def toFin20 [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V = 20) : SimpleGraph (Fin 20) :=
  G.comap (Fintype.equivFinOfCardEq hcard).symm

/-- The canonical relabeling map from a twenty-element finite type to `Fin 20`. -/
noncomputable def toFin20Iso [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V = 20) : G ≃g toFin20 G hcard :=
  (SimpleGraph.Iso.comap (Fintype.equivFinOfCardEq hcard).symm G).symm

/-- The `toFin20` relabeling preserves and reflects cocolorability. -/
theorem hasCocoloring_toFin20_iff [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V = 20) (k : ℕ) :
    HasCocoloring (toFin20 G hcard) k ↔ HasCocoloring G k :=
  (hasCocoloring_iso_iff (toFin20Iso G hcard)).symm

/-- The labelled universal upper bound applies to every finite twenty-vertex graph. -/
theorem upperBound_on_card_twenty (hupper : UpperBound) [Fintype V]
    (hcard : Fintype.card V = 20) (G : SimpleGraph V) : HasCocoloring G 6 :=
  (hasCocoloring_toFin20_iff G hcard 6).mp (hupper (toFin20 G hcard))

/-- A labelled lower-bound witness transports to every twenty-element vertex type. -/
theorem lowerBound_on_card_twenty (hlower : LowerBound) [Fintype V]
    (hcard : Fintype.card V = 20) :
    ∃ G : SimpleGraph V, ¬ HasCocoloring G 5 := by
  obtain ⟨H, hH⟩ := hlower
  let e : V ≃ Fin 20 := Fintype.equivFinOfCardEq hcard
  refine ⟨H.comap e, ?_⟩
  intro hcolor
  exact hH ((hasCocoloring_iso_iff (SimpleGraph.Iso.comap e H)).mp hcolor)

/-- The labelled upper bound is equivalent to its formulation on any
twenty-element finite vertex type. -/
theorem upperBound_iff_on_card_twenty [Fintype V]
    (hcard : Fintype.card V = 20) :
    UpperBound ↔ ∀ G : SimpleGraph V, HasCocoloring G 6 := by
  constructor
  · intro hupper
    exact upperBound_on_card_twenty hupper hcard
  · intro hupper H
    let e : V ≃ Fin 20 := Fintype.equivFinOfCardEq hcard
    exact (hasCocoloring_iso_iff (SimpleGraph.Iso.comap e H)).mp
      (hupper (H.comap e))

/-- The labelled lower bound is equivalent to its formulation on any
twenty-element finite vertex type. -/
theorem lowerBound_iff_on_card_twenty [Fintype V]
    (hcard : Fintype.card V = 20) :
    LowerBound ↔ ∃ G : SimpleGraph V, ¬ HasCocoloring G 5 := by
  constructor
  · intro hlower
    exact lowerBound_on_card_twenty hlower hcard
  · rintro ⟨G, hG⟩
    refine ⟨toFin20 G hcard, ?_⟩
    intro hcolor
    exact hG ((hasCocoloring_toFin20_iff G hcard 5).mp hcolor)

/-- The frozen target has its ordinary meaning on every finite type of cardinality twenty. -/
theorem target_on_card_twenty (htarget : Target) [Fintype V]
    (hcard : Fintype.card V = 20) :
    (∀ G : SimpleGraph V, HasCocoloring G 6) ∧
      (∃ G : SimpleGraph V, ¬ HasCocoloring G 5) :=
  ⟨upperBound_on_card_twenty htarget.1 hcard,
    lowerBound_on_card_twenty htarget.2 hcard⟩

/-- The frozen labelled target is equivalent to the same two bounds on any
finite vertex type of cardinality twenty. -/
theorem target_iff_on_card_twenty [Fintype V]
    (hcard : Fintype.card V = 20) :
    Target ↔
      ((∀ G : SimpleGraph V, HasCocoloring G 6) ∧
        (∃ G : SimpleGraph V, ¬ HasCocoloring G 5)) := by
  rw [Target, upperBound_iff_on_card_twenty hcard,
    lowerBound_iff_on_card_twenty hcard]

end CochromaticTwenty

#print axioms CochromaticTwenty.homogeneous_image_iff
#print axioms CochromaticTwenty.hasCocoloring_iso_iff
#print axioms CochromaticTwenty.HasCocoloring.mono
#print axioms CochromaticTwenty.target_iff_on_card_twenty
