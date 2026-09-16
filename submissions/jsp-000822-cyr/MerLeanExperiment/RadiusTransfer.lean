import MerLeanExperiment.DiskModel

/-!
# Transferring disk discrepancy between nearby radii and centres

This file isolates the monotonicity argument that transfers discrepancy
estimates on an inner and an outer disk to an intermediate disk.
-/

namespace DiskDiscrepancy

noncomputable section

theorem pointCount_le_of_closedBall_subset
    {S : Set Plane} (hS : Admissible S) {x y : Plane} {r s : ℝ}
    (hsub : Metric.closedBall x r ⊆ Metric.closedBall y s) :
    pointCount S x r ≤ pointCount S y s := by
  apply Set.ncard_le_ncard _ (hS.2 y s)
  intro p hp
  exact ⟨hp.1, hsub hp.2⟩

/-- Discrepancy on nested inner and outer disks controls the discrepancy on
an intermediate disk by the larger of the two area shells. -/
theorem discrepancy_le_of_inner_outer
    {A : Set Plane} (hA : Admissible A)
    {x y : Plane} {s r t D : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t)
    (hinnerSub : Metric.closedBall y s ⊆ Metric.closedBall x r)
    (houterSub : Metric.closedBall x r ⊆ Metric.closedBall y t)
    (hinner : discrepancy A y s ≤ D)
    (houter : discrepancy A y t ≤ D) :
    discrepancy A x r ≤ D + Real.pi * max (r ^ 2 - s ^ 2) (t ^ 2 - r ^ 2) := by
  have hcountLowerNat : pointCount A y s ≤ pointCount A x r :=
    pointCount_le_of_closedBall_subset hA hinnerSub
  have hcountUpperNat : pointCount A x r ≤ pointCount A y t :=
    pointCount_le_of_closedBall_subset hA houterSub
  have hcountLower : (pointCount A y s : ℝ) ≤ pointCount A x r := by
    exact_mod_cast hcountLowerNat
  have hcountUpper : (pointCount A x r : ℝ) ≤ pointCount A y t := by
    exact_mod_cast hcountUpperNat
  change |(pointCount A y s : ℝ) - Real.pi * s ^ 2| ≤ D at hinner
  change |(pointCount A y t : ℝ) - Real.pi * t ^ 2| ≤ D at houter
  rcases abs_le.mp hinner with ⟨hinnerLower, hinnerUpper⟩
  rcases abs_le.mp houter with ⟨houterLower, houterUpper⟩
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hinnerShellNonneg : 0 ≤ r ^ 2 - s ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsr) (add_nonneg hs hr)]
  have ht : 0 ≤ t := le_trans hr hrt
  have houterShellNonneg : 0 ≤ t ^ 2 - r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrt) (add_nonneg hr ht)]
  have hinnerMax : r ^ 2 - s ^ 2 ≤ max (r ^ 2 - s ^ 2) (t ^ 2 - r ^ 2) :=
    le_max_left _ _
  have houterMax : t ^ 2 - r ^ 2 ≤ max (r ^ 2 - s ^ 2) (t ^ 2 - r ^ 2) :=
    le_max_right _ _
  change |(pointCount A x r : ℝ) - Real.pi * r ^ 2| ≤
    D + Real.pi * max (r ^ 2 - s ^ 2) (t ^ 2 - r ^ 2)
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Nearby-centre inclusions and radius gaps of at most `η` give the usual
symmetric shell estimate, including the case `r < η`. -/
theorem discrepancy_le_of_nearby_radii
    {A : Set Plane} (hA : Admissible A)
    {x y : Plane} {s r t δ η D : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hη : 0 ≤ η)
    (hxy : dist x y ≤ δ) (hsδ : s + δ ≤ r) (hrδ : r + δ ≤ t)
    (htη : t ≤ r + η) (hηs : r - η ≤ s)
    (hinner : discrepancy A y s ≤ D)
    (houter : discrepancy A y t ≤ D) :
    discrepancy A x r ≤ D + Real.pi * (2 * r * η + η ^ 2) := by
  have hδ : 0 ≤ δ := le_trans (dist_nonneg : 0 ≤ dist x y) hxy
  have hsr : s ≤ r := by linarith
  have hrt : r ≤ t := by linarith
  have hinnerSub : Metric.closedBall y s ⊆ Metric.closedBall x r := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ = dist z y + dist x y := by rw [dist_comm y x]
      _ ≤ s + δ := add_le_add hz hxy
      _ ≤ r := hsδ
  have houterSub : Metric.closedBall x r ⊆ Metric.closedBall y t := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc
      dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
      _ ≤ r + δ := add_le_add hz hxy
      _ ≤ t := hrδ
  have htransfer := discrepancy_le_of_inner_outer hA hr hs hsr hrt hinnerSub houterSub
    hinner houter
  have houterShell : t ^ 2 - r ^ 2 ≤ 2 * r * η + η ^ 2 := by
    nlinarith [sq_nonneg (t - r - η), sq_nonneg t]
  have hinnerShell : r ^ 2 - s ^ 2 ≤ 2 * r * η + η ^ 2 := by
    by_cases hηr : η ≤ r
    · nlinarith [sq_nonneg (s - (r - η))]
    · nlinarith [sq_nonneg s]
  have hmax : max (r ^ 2 - s ^ 2) (t ^ 2 - r ^ 2) ≤
      2 * r * η + η ^ 2 :=
    max_le hinnerShell houterShell
  nlinarith [Real.pi_pos.le]

end

end DiskDiscrepancy

#print axioms DiskDiscrepancy.discrepancy_le_of_inner_outer
#print axioms DiskDiscrepancy.discrepancy_le_of_nearby_radii
