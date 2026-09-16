import MerLeanExperiment.PartitionCollision
import MerLeanExperiment.RationalNumerator

namespace ReciprocalSquares

open Classical

/-- Adjoining a fixed disjoint prefix preserves distinct representations. -/
theorem distinct_unions_of_disjoint (S U V : Finset ℕ)
    (hSU : Disjoint S U) (hSV : Disjoint S V) (hUV : U ≠ V) :
    S ∪ U ≠ S ∪ V := by
  intro heq
  apply hUV
  ext n
  constructor
  · intro hn
    have hnS : n ∉ S := fun h => Finset.disjoint_left.mp hSU h hn
    have hnunion : n ∈ S ∪ V := heq ▸ Finset.mem_union_right S hn
    exact (Finset.mem_union.mp hnunion).resolve_left hnS
  · intro hn
    have hnS : n ∉ S := fun h => Finset.disjoint_left.mp hSV h hn
    have hnunion : n ∈ S ∪ U := heq.symm ▸ Finset.mem_union_right S hn
    exact (Finset.mem_union.mp hnunion).resolve_left hnS

/-- Two residual representations complete the original finite color collision. -/
theorem partition_collision_of_two_residual_representations
    (Z S U V : Finset ℕ) (X : Set ℕ) (r : ℚ)
    (hZ : ∀ n ∈ Z, 1 < n ∧ IsSquare n)
    (hS : S ⊆ Z) (hU : U ⊆ Z) (hV : V ⊆ Z)
    (hSU : Disjoint S U) (hSV : Disjoint S V) (hUV : U ≠ V)
    (hUr : recipSumQ U = r) (hVr : recipSumQ V = r)
    (hres : r = (∑ n ∈ Z.filter (fun n => n ∉ X), (1 : ℚ) / n) - recipSumQ S) :
    ∃ A B : Finset ℕ, A.Nonempty ∧ B.Nonempty ∧
      (∀ n ∈ A, 1 < n ∧ IsSquare n ∧ n ∈ X) ∧
      (∀ n ∈ B, 1 < n ∧ IsSquare n ∧ n ∉ X) ∧
      (∑ n ∈ A, (1 : ℚ) / n) = ∑ n ∈ B, (1 : ℚ) / n := by
  classical
  have hsumU : recipSumQ (S ∪ U) =
      ∑ n ∈ Z.filter (fun n => n ∉ X), (1 : ℚ) / n := by
    unfold recipSumQ
    rw [Finset.sum_union hSU]
    change recipSumQ S + recipSumQ U = _
    rw [hUr, hres]
    ring
  have hsumV : recipSumQ (S ∪ V) =
      ∑ n ∈ Z.filter (fun n => n ∉ X), (1 : ℚ) / n := by
    unfold recipSumQ
    rw [Finset.sum_union hSV]
    change recipSumQ S + recipSumQ V = _
    rw [hVr, hres]
    ring
  by_cases hne : S ∪ U ≠ Z.filter (fun n => n ∉ X)
  · exact partition_collision_of_distinct_representation Z (S ∪ U) X hZ
      (Finset.union_subset hS hU) hne hsumU
  · have heq : S ∪ U = Z.filter (fun n => n ∉ X) := not_ne_iff.mp hne
    have hneV : S ∪ V ≠ Z.filter (fun n => n ∉ X) := by
      intro hVeq
      exact distinct_unions_of_disjoint S U V hSU hSV hUV (heq.trans hVeq.symm)
    exact partition_collision_of_distinct_representation Z (S ∪ V) X hZ
      (Finset.union_subset hS hV) hneV hsumV

end ReciprocalSquares
