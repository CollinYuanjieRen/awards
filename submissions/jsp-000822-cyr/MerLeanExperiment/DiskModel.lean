import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Bounded

namespace DiskDiscrepancy

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Points of a given set that lie in a closed Euclidean disk. -/
def diskPoints (S : Set Plane) (center : Plane) (radius : ℝ) : Set Plane :=
  {p | p ∈ S ∧ dist p center ≤ radius}

/-- Finiteness of actual disk intersections, with no separation or density assumption. -/
def LocallyFinitePoints (S : Set Plane) : Prop :=
  ∀ center : Plane, ∀ radius : ℝ, (diskPoints S center radius).Finite

def Admissible (S : Set Plane) : Prop := S.Infinite ∧ LocallyFinitePoints S

noncomputable def pointCount (S : Set Plane) (center : Plane) (radius : ℝ) : ℕ :=
  (diskPoints S center radius).ncard

noncomputable def discrepancy (S : Set Plane) (center : Plane) (radius : ℝ) : ℝ :=
  |(pointCount S center radius : ℝ) - Real.pi * radius ^ 2|

theorem diskPoints_eq_inter_closedBall (S : Set Plane) (center : Plane) (radius : ℝ) :
    diskPoints S center radius = S ∩ Metric.closedBall center radius := rfl

/-- Disk finiteness agrees with the compact-set convention in Beck's counting problem. -/
theorem locallyFinitePoints_iff_compact (S : Set Plane) :
    LocallyFinitePoints S ↔ ∀ K : Set Plane, IsCompact K → (S ∩ K).Finite := by
  constructor
  · intro h K hK
    obtain ⟨r, hKr⟩ := hK.isBounded.subset_closedBall (0 : Plane)
    exact (h 0 r).subset fun p hp ↦ ⟨hp.1, hKr hp.2⟩
  · intro h center radius
    exact h (Metric.closedBall center radius) (isCompact_closedBall center radius)

theorem discrepancy_nonneg (S : Set Plane) (center : Plane) (radius : ℝ) :
    0 ≤ discrepancy S center radius := abs_nonneg _

end DiskDiscrepancy
