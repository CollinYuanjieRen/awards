import MerLeanExperiment.ModelAdapters
import MerLeanExperiment.SmallRamsey

/-!
Assembly lemmas for cocolorings.  They turn homogeneous covers and colorings
of complementary induced subgraphs into actual color functions.
-/

namespace CochromaticTwenty

variable {V : Type*} {G : SimpleGraph V}

/-- A cover by `k` homogeneous sets yields a `k`-cocoloring.  The sets in the
cover may overlap: choosing one containing set for each vertex only shrinks
the resulting color classes. -/
theorem hasCocoloring_of_homogeneous_cover {k : ℕ}
    (parts : Fin k → Set V)
    (hcover : ∀ v, ∃ i, v ∈ parts i)
    (hhomogeneous : ∀ i, Homogeneous G (parts i)) :
    HasCocoloring G k := by
  classical
  choose color hcolor using hcover
  refine ⟨color, fun i ↦ homogeneous_mono ?_ (hhomogeneous i)⟩
  intro v hv
  rw [← hv]
  exact hcolor v

/-- Restricting a homogeneous set to an induced subgraph preserves
homogeneity. -/
theorem homogeneous_induce_preimage {s t : Set V}
    (ht : Homogeneous G t) :
    Homogeneous (G.induce s) {v : s | (v : V) ∈ t} := by
  rcases ht with ht | ht
  · refine Or.inl ?_
    intro u hu v hv huv
    exact ht hu hv (Subtype.coe_ne_coe.mpr huv)
  · refine Or.inr ?_
    intro u hu v hv huv
    exact ht hu hv (Subtype.coe_ne_coe.mpr huv)

/-- A homogeneous set in an induced subgraph is homogeneous after its
vertices are included back into the ambient graph. -/
theorem homogeneous_image_subtype {s : Set V} {t : Set s}
    (ht : Homogeneous (G.induce s) t) :
    Homogeneous G (Subtype.val '' t) := by
  rcases ht with ht | ht
  · refine Or.inl (Set.Pairwise.image ?_)
    intro u hu v hv huv
    exact ht hu hv huv
  · refine Or.inr (Set.Pairwise.image ?_)
    intro u hu v hv huv
    exact ht hu hv huv

/-- Cocolorings of a set and its complement combine by adjoining their
palettes. -/
theorem HasCocoloring.induce_add {s : Set V} {k l : ℕ}
    (hleft : HasCocoloring (G.induce s) k)
    (hright : HasCocoloring (G.induce (sᶜ)) l) :
    HasCocoloring G (k + l) := by
  classical
  obtain ⟨leftColor, hleftColor⟩ := hleft
  obtain ⟨rightColor, hrightColor⟩ := hright
  let leftParts : Fin k → Set V := fun i ↦
    Subtype.val '' {v : s | leftColor v = i}
  let rightParts : Fin l → Set V := fun i ↦
    Subtype.val '' {v : ↥(sᶜ) | rightColor v = i}
  let parts : Fin (k + l) → Set V := Fin.append leftParts rightParts
  apply hasCocoloring_of_homogeneous_cover parts
  · intro v
    by_cases hv : v ∈ s
    · refine ⟨Fin.castAdd l (leftColor ⟨v, hv⟩), ?_⟩
      rw [show parts (Fin.castAdd l (leftColor ⟨v, hv⟩)) =
        leftParts (leftColor ⟨v, hv⟩) by simp [parts]]
      exact ⟨⟨v, hv⟩, rfl, rfl⟩
    · have hvc : v ∈ sᶜ := by simpa using hv
      refine ⟨Fin.natAdd k (rightColor ⟨v, hvc⟩), ?_⟩
      rw [show parts (Fin.natAdd k (rightColor ⟨v, hvc⟩)) =
        rightParts (rightColor ⟨v, hvc⟩) by simp [parts]]
      exact ⟨⟨v, hvc⟩, rfl, rfl⟩
  · refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [show parts (Fin.castAdd l i) = leftParts i by simp [parts]]
      exact homogeneous_image_subtype (hleftColor i)
    · rw [show parts (Fin.natAdd k i) = rightParts i by simp [parts]]
      exact homogeneous_image_subtype (hrightColor i)

/-- A homogeneous set consumes one color in the induced graph on that set. -/
theorem hasCocoloring_one_of_homogeneous {s : Set V}
    (hs : Homogeneous G s) : HasCocoloring (G.induce s) 1 := by
  refine ⟨fun _ ↦ 0, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa using (homogeneous_induce_preimage (G := G) (s := s) hs)

/-- A universal cocoloring theorem on `Fin n` applies to every finite vertex
type of cardinality `n`. -/
theorem hasCocoloring_of_forall_fin {n k : ℕ} [Fintype V]
    (hcard : Fintype.card V = n)
    (hfin : ∀ H : SimpleGraph (Fin n), HasCocoloring H k)
    (G : SimpleGraph V) : HasCocoloring G k :=
  (hasCocoloring_iso_iff (G.overFinIso hcard)).mpr (hfin (G.overFin hcard))

/-- Two homogeneous sets cover their union with two colors. -/
theorem hasCocoloring_induce_union_two {s t : Set V}
    (hs : Homogeneous G s) (ht : Homogeneous G t) :
    HasCocoloring (G.induce (s ∪ t)) 2 := by
  let parts : Fin 2 → Set {v : V // v ∈ s ∪ t} := fun i ↦
    if i = 0 then {v | (v : V) ∈ s} else {v | (v : V) ∈ t}
  apply hasCocoloring_of_homogeneous_cover parts
  · intro v
    rcases v.property with hv | hv
    · exact ⟨0, by simp [parts, hv]⟩
    · exact ⟨1, by simp [parts, hv]⟩
  · intro i
    fin_cases i
    · simpa [parts] using
        (homogeneous_induce_preimage (G := G) (s := s ∪ t) hs)
    · simpa [parts] using
        (homogeneous_induce_preimage (G := G) (s := s ∪ t) ht)

/-- Removing one homogeneous four-set from twelve vertices reduces a
four-coloring to the universal three-color theorem on eight vertices. -/
theorem hasCocoloring_four_of_homogeneous_four [Fintype V]
    (hcard : Fintype.card V = 12)
    (hfin8 : ∀ H : SimpleGraph (Fin 8), HasCocoloring H 3)
    {s : Finset V} (hscard : s.card = 4)
    (hs : Homogeneous G (s : Set V)) : HasCocoloring G 4 := by
  classical
  let S : Set V := (s : Set V)
  have hScard : Fintype.card S = 4 := by simp [S, hscard]
  have hcomplement : Fintype.card ↥(Sᶜ) = 8 := by
    rw [Fintype.card_compl_set, hScard, hcard]
  have hleft : HasCocoloring (G.induce S) 1 := by
    exact hasCocoloring_one_of_homogeneous hs
  have hright : HasCocoloring (G.induce (Sᶜ)) 3 :=
    hasCocoloring_of_forall_fin hcomplement hfin8 (G.induce (Sᶜ))
  simpa using hleft.induce_add hright

/-- Existential form of `hasCocoloring_four_of_homogeneous_four`. -/
theorem hasCocoloring_four_of_exists_homogeneous_four [Fintype V]
    (hcard : Fintype.card V = 12)
    (hfin8 : ∀ H : SimpleGraph (Fin 8), HasCocoloring H 3)
    (hset : ∃ s : Finset V, s.card = 4 ∧ Homogeneous G (s : Set V)) :
    HasCocoloring G 4 := by
  obtain ⟨s, hscard, hs⟩ := hset
  exact hasCocoloring_four_of_homogeneous_four hcard hfin8 hscard hs

/-- Removing two disjoint homogeneous four-sets from twenty vertices reduces
a six-coloring to the universal four-color theorem on twelve vertices. -/
theorem hasCocoloring_six_of_two_disjoint_homogeneous_four [Fintype V]
    (hcard : Fintype.card V = 20)
    (hfin12 : ∀ H : SimpleGraph (Fin 12), HasCocoloring H 4)
    {s t : Finset V} (hdisjoint : Disjoint s t)
    (hscard : s.card = 4) (htcard : t.card = 4)
    (hs : Homogeneous G (s : Set V))
    (ht : Homogeneous G (t : Set V)) : HasCocoloring G 6 := by
  classical
  let U : Set V := (s : Set V) ∪ (t : Set V)
  have hstcard : (s ∪ t).card = 8 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hscard, htcard]
  have hUcard : Fintype.card U = 8 := by
    simp [U, hstcard]
  have hcomplement : Fintype.card ↥(Uᶜ) = 12 := by
    rw [Fintype.card_compl_set, hUcard, hcard]
  have hleft : HasCocoloring (G.induce U) 2 := by
    simpa [U] using hasCocoloring_induce_union_two hs ht
  have hright : HasCocoloring (G.induce (Uᶜ)) 4 :=
    hasCocoloring_of_forall_fin hcomplement hfin12 (G.induce (Uᶜ))
  simpa using hleft.induce_add hright

/-- Existential form of
`hasCocoloring_six_of_two_disjoint_homogeneous_four`. -/
theorem hasCocoloring_six_of_exists_two_disjoint_homogeneous_four [Fintype V]
    (hcard : Fintype.card V = 20)
    (hfin12 : ∀ H : SimpleGraph (Fin 12), HasCocoloring H 4)
    (hsets : ∃ s t : Finset V,
      Disjoint s t ∧ s.card = 4 ∧ t.card = 4 ∧
        Homogeneous G (s : Set V) ∧ Homogeneous G (t : Set V)) :
    HasCocoloring G 6 := by
  obtain ⟨s, t, hdisjoint, hscard, htcard, hs, ht⟩ := hsets
  exact hasCocoloring_six_of_two_disjoint_homogeneous_four
    hcard hfin12 hdisjoint hscard htcard hs ht

end CochromaticTwenty

#print axioms CochromaticTwenty.hasCocoloring_of_homogeneous_cover
#print axioms CochromaticTwenty.HasCocoloring.induce_add
#print axioms CochromaticTwenty.hasCocoloring_four_of_exists_homogeneous_four
#print axioms CochromaticTwenty.hasCocoloring_six_of_exists_two_disjoint_homogeneous_four
