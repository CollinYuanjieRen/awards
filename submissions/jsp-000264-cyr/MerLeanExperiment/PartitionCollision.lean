import MerLeanExperiment.FiniteCollision

namespace ReciprocalSquares

open Classical

/-- A second representation of the mass of one color gives the two nonempty
monochromatic subsets required by the original partition problem. -/
theorem partition_collision_of_distinct_representation
    (Z S : Finset ℕ) (X : Set ℕ)
    (hZ : ∀ n ∈ Z, 1 < n ∧ IsSquare n)
    (hS : S ⊆ Z)
    (hne : S ≠ Z.filter (fun n => n ∉ X))
    (hsum : (∑ n ∈ S, (1 : ℚ) / n) =
      ∑ n ∈ Z.filter (fun n => n ∉ X), (1 : ℚ) / n) :
    ∃ A B : Finset ℕ, A.Nonempty ∧ B.Nonempty ∧
      (∀ n ∈ A, 1 < n ∧ IsSquare n ∧ n ∈ X) ∧
      (∀ n ∈ B, 1 < n ∧ IsSquare n ∧ n ∉ X) ∧
      (∑ n ∈ A, (1 : ℚ) / n) = ∑ n ∈ B, (1 : ℚ) / n := by
  classical
  let Y := Z.filter (fun n => n ∉ X)
  have hY : Y ⊆ Z := Finset.filter_subset _ _
  have hw : ∀ n ∈ Z, 0 < (1 : ℚ) / n := by
    intro n hn
    have hnlarge := (hZ n hn).1
    have hnpos : 0 < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
    exact div_pos (by norm_num) hnpos
  obtain ⟨hA, hB, heq⟩ :=
    nonempty_sdiffs_of_sum_eq Z S Y (fun n => (1 : ℚ) / n) hw hS hY hne hsum
  refine ⟨S \ Y, Y \ S, hA, hB, ?_, ?_, heq⟩
  · intro n hn
    obtain ⟨hnS, hnY⟩ := Finset.mem_sdiff.mp hn
    have hnZ := hS hnS
    refine ⟨(hZ n hnZ).1, (hZ n hnZ).2, ?_⟩
    by_contra hnX
    exact hnY (Finset.mem_filter.mpr ⟨hnZ, hnX⟩)
  · intro n hn
    have hnY := (Finset.mem_sdiff.mp hn).1
    have hfilter := Finset.mem_filter.mp hnY
    exact ⟨(hZ n hfilter.1).1, (hZ n hfilter.1).2, hfilter.2⟩

end ReciprocalSquares
