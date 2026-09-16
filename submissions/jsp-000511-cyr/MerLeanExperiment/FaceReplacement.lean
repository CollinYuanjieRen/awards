import MerLeanExperiment.FaceSystemBasics
import MerLeanExperiment.FinsetReplacement

open scoped Graph Classical
open Set Schoenflies

namespace Graph

/-- Replace one old face by two actual new faces while preserving the complete enumeration.
Every geometric input is supplied by the crosscut and unaffected-face lemmas at the ear step. -/
theorem FaceSystem.exists_replacement
    {β : Type*} {B H : Graph Plane β} {drawing : β → ℝ → Plane}
    (M : FaceSystem B drawing) (q q₁ q₂ : Set Plane × List β) (hq : q ∈ M.boundaries)
    (hv₁ : IsBoundaryList H drawing q₁.1 q₁.2)
    (hv₂ : IsBoundaryList H drawing q₂.1 q₂.2) (hne : q₁.1 ≠ q₂.1)
    (hsub₁ : q₁.1 ⊆ q.1) (hsub₂ : q₂.1 ⊆ q.1)
    (hsurvive : ∀ r ∈ M.boundaries, r ≠ q → IsBoundaryList H drawing r.1 r.2)
    (hext : exterior H drawing ⊆ exterior B drawing)
    (hcover : ∀ z ∈ exterior H drawing, z ∈ q.1 → z ∈ q₁.1 ∨ z ∈ q₂.1) :
    ∃ M' : FaceSystem H drawing,
      M'.boundaries = insert q₁ (insert q₂ (M.boundaries.erase q)) ∧
      M'.faceCount = M.faceCount + 1 ∧
      M'.boundaryLength + q.2.length =
        M.boundaryLength + q₁.2.length + q₂.2.length := by
  let old := M.boundaries.erase q
  have hfresh₁ : q₁ ∉ old := by
    intro hmem
    have hr := (Finset.mem_erase.mp hmem).2
    have hrq := (Finset.mem_erase.mp hmem).1
    obtain ⟨z, hz⟩ := hv₁.nonempty
    exact Set.disjoint_left.1 (M.disjoint_regions hq hr hrq.symm) (hsub₁ hz) hz
  have hfresh₂ : q₂ ∉ old := by
    intro hmem
    have hr := (Finset.mem_erase.mp hmem).2
    have hrq := (Finset.mem_erase.mp hmem).1
    obtain ⟨z, hz⟩ := hv₂.nonempty
    exact Set.disjoint_left.1 (M.disjoint_regions hq hr hrq.symm) (hsub₂ hz) hz
  have hq₁q₂ : q₁ ≠ q₂ := fun h ↦ hne (congrArg Prod.fst h)
  have hregion₁ : ∀ r ∈ old, q₁.1 ≠ r.1 := by
    intro r hr her
    have hrM := (Finset.mem_erase.mp hr).2
    have hrq := (Finset.mem_erase.mp hr).1
    obtain ⟨z, hz⟩ := hv₁.nonempty
    exact Set.disjoint_left.1 (M.disjoint_regions hq hrM hrq.symm)
      (hsub₁ hz) (her ▸ hz)
  have hregion₂ : ∀ r ∈ old, q₂.1 ≠ r.1 := by
    intro r hr her
    have hrM := (Finset.mem_erase.mp hr).2
    have hrq := (Finset.mem_erase.mp hr).1
    obtain ⟨z, hz⟩ := hv₂.nonempty
    exact Set.disjoint_left.1 (M.disjoint_regions hq hrM hrq.symm)
      (hsub₂ hz) (her ▸ hz)
  let newBoundaries := insert q₁ (insert q₂ old)
  let M' : FaceSystem H drawing :=
    { boundaries := newBoundaries
      valid := by
        intro r hr
        simp only [newBoundaries, Finset.mem_insert] at hr
        rcases hr with rfl | rfl | hr
        · exact hv₁
        · exact hv₂
        · exact hsurvive r (Finset.mem_erase.mp hr).2 (Finset.mem_erase.mp hr).1
      unique := by
        intro r hr s hs hrs
        simp only [newBoundaries, Finset.coe_insert, Set.mem_insert_iff] at hr hs
        rcases hr with rfl | rfl | hr
        · rcases hs with rfl | rfl | hs
          · rfl
          · exact False.elim (hne hrs)
          · exact False.elim (hregion₁ s hs hrs)
        · rcases hs with rfl | rfl | hs
          · exact False.elim (hne hrs.symm)
          · rfl
          · exact False.elim (hregion₂ s hs hrs)
        · rcases hs with rfl | rfl | hs
          · exact False.elim (hregion₁ r hr hrs.symm)
          · exact False.elim (hregion₂ r hr hrs.symm)
          · exact M.unique (Finset.mem_erase.mp hr).2
              (Finset.mem_erase.mp hs).2 hrs
      exhaustive := by
        intro z hz
        obtain ⟨r, hr, hrface⟩ := M.exhaustive z (hext hz)
        have hzr : z ∈ r.1 := by
          rw [hrface]
          exact mem_face (hext hz)
        by_cases hrq : r = q
        · subst r
          rcases hcover z hz hzr with hz₁ | hz₂
          · exact ⟨q₁, by simp [newBoundaries], (hv₁.face_eq hz₁).symm⟩
          · exact ⟨q₂, by simp [newBoundaries], (hv₂.face_eq hz₂).symm⟩
        · have hrOld : r ∈ old := Finset.mem_erase.mpr ⟨hrq, hr⟩
          exact ⟨r, by simp [newBoundaries, hrOld],
            ((hsurvive r hr hrq).face_eq hzr).symm⟩ }
  refine ⟨M', rfl, ?_, ?_⟩
  · exact Finset.card_replace_one_by_two M.boundaries hq hfresh₁ hfresh₂ hq₁q₂
  · exact Finset.sum_replace_one_by_two M.boundaries (fun r ↦ r.2.length)
      hq hfresh₁ hfresh₂ hq₁q₂

end Graph
