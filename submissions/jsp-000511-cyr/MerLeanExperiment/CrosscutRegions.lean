import MerLeanExperiment.Vendor.Schoenflies.CrosscutCells

open Set
namespace Schoenflies

/-- Elementary region selection for a crosscut. -/
theorem region_eq_right_of_disjoint
    {C W V S R : Set Plane}
    (hWV : IsRegionPair C W V)
    (hR : IsRegionOf C R)
    (hne : S.Nonempty) (hSW : S ⊆ W)
    (hRS : Disjoint R S) : R = V := by
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hR with hR | hR
    · subst R
      obtain ⟨x, hxS⟩ := hne
      exact False.elim (Set.disjoint_left.mp hRS (hSW hxS) hxS)
    · exact hR
  · rcases hR with hR | hR
    · exact hR
    · subst R
      obtain ⟨x, hxS⟩ := hne
      exact False.elim (Set.disjoint_left.mp hRS (hSW hxS) hxS)

/-- Elementary region selection for a crosscut. -/
theorem oppositeRegion_disjoint_crosscut_curve
    {J A P Ω Ω' : Set Plane} {p q : Plane}
    (hΩ : IsRegionPair J Ω Ω')
    (hAJ : A ⊆ J)
    (hends : ({p, q} : Set Plane) ⊆ J)
    (hPsub : P \ {p, q} ⊆ Ω) :
    Disjoint Ω' (A ∪ P) := by
  rw [Set.disjoint_left]
  intro x hxΩ' hx
  rcases hx with hxA | hxP
  · exact (hΩ.right.subset_compl hxΩ') (hAJ hxA)
  · by_cases hxend : x ∈ ({p, q} : Set Plane)
    · exact (hΩ.right.subset_compl hxΩ') (hends hxend)
    · exact Set.disjoint_left.mp hΩ.disjoint (hPsub ⟨hxP, hxend⟩) hxΩ'

end Schoenflies
