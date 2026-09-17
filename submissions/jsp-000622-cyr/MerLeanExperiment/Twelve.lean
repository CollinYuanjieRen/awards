import MerLeanExperiment.LowerBound
import MerLeanExperiment.TwelveColoring
import MerLeanExperiment.ModelAdapters

/-!
The twelve-vertex value asked for on the problem page: `z(12) = 4`.

The upper bound `z(12) ≤ 4` is `fin12_hasCocoloring_four`.  The lower bound
uses the Paley graph of order seventeen restricted to its first twelve
vertices: it has no homogeneous four-set, so three homogeneous classes cover
at most nine of the twelve vertices.
-/

namespace CochromaticTwenty

/-- The natural embedding of the first twelve vertices into `Fin 17`. -/
def firstTwelve : Fin 12 ↪ Fin 17 :=
  Fin.castLEEmb (by omega)

/-- The Paley graph of order seventeen induced on its first twelve vertices. -/
def paley17OnTwelve : SimpleGraph (Fin 12) :=
  paley17.comap firstTwelve

theorem paley17OnTwelve_adj (a b : Fin 12) :
    paley17OnTwelve.Adj a b ↔ paley17.Adj (firstTwelve a) (firstTwelve b) :=
  Iff.rfl

/-- Three colors cannot cocolor the twelve-vertex Paley subgraph. -/
theorem paley17OnTwelve_not_hasCocoloring_three :
    ¬ HasCocoloring paley17OnTwelve 3 := by
  rintro ⟨color, hcolor⟩
  obtain ⟨i, hi⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card color (n := 3) (by norm_num)
  let fiber : Finset (Fin 12) := {v | color v = i}
  have hfour : 4 ≤ fiber.card := by
    have : 3 < fiber.card := by simpa [fiber] using hi
    omega
  obtain ⟨s, hs, hs_card⟩ := Finset.exists_subset_card_eq hfour
  apply paley17_no_homogeneous_four (s.map firstTwelve) (by simp [hs_card])
  have hmem : ∀ a ∈ s, color a = i := fun a ha => by simpa [fiber] using hs ha
  rcases hcolor i with hclique | hindependent
  · left
    intro a ha b hb hab
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact (paley17OnTwelve_adj a b).mp
      (hclique (hmem a ha) (hmem b hb) (fun h => hab (by rw [h])))
  · right
    intro a ha b hb hab hadj
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact hindependent (hmem a ha) (hmem b hb) (fun h => hab (by rw [h]))
      ((paley17OnTwelve_adj a b).mpr hadj)

/-- Every twelve-vertex simple graph admits at most four homogeneous classes. -/
def UpperBoundTwelve : Prop := ∀ G : SimpleGraph (Fin 12), HasCocoloring G 4

/-- Some twelve-vertex simple graph admits no coloring with three such classes. -/
def LowerBoundTwelve : Prop := ∃ G : SimpleGraph (Fin 12), ¬ HasCocoloring G 3

/-- The maximum cochromatic number among twelve-vertex graphs is exactly four. -/
def TargetTwelve : Prop := UpperBoundTwelve ∧ LowerBoundTwelve

theorem paley17OnTwelve_lowerBound : LowerBoundTwelve :=
  ⟨paley17OnTwelve, paley17OnTwelve_not_hasCocoloring_three⟩

end CochromaticTwenty

open CochromaticTwenty in
/-- The maximum cochromatic number of an ordinary twelve-vertex graph is four:
`z(12) = 4`, the value the problem page asks for in particular. -/
theorem cochromatic_twelve : CochromaticTwenty.TargetTwelve :=
  ⟨fin12_hasCocoloring_four, paley17OnTwelve_lowerBound⟩

open CochromaticTwenty in
/-- `z(12) = 4` on every twelve-element vertex type. -/
theorem cochromatic_twelve_on_finite_type {V : Type*} [Fintype V]
    (hcard : Fintype.card V = 12) :
    (∀ G : SimpleGraph V, HasCocoloring G 4) ∧
      (∃ G : SimpleGraph V, ¬ HasCocoloring G 3) := by
  have e : V ≃ Fin 12 := Fintype.equivFinOfCardEq hcard
  refine ⟨fun G => ?_, ?_⟩
  · have h := cochromatic_twelve.1 (G.map e.toEmbedding)
    exact (hasCocoloring_iso_iff (SimpleGraph.Iso.map e G)).mpr h
  · obtain ⟨G, hG⟩ := cochromatic_twelve.2
    refine ⟨G.comap e.toEmbedding, fun h => hG ?_⟩
    exact (hasCocoloring_iso_iff (SimpleGraph.Iso.comap e G)).mp h

#print axioms cochromatic_twelve
#print axioms cochromatic_twelve_on_finite_type
