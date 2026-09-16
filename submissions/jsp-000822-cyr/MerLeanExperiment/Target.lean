import MerLeanExperiment.DiskModel

/-!
The Beck disk specialization: absolute discrepancy over every positive radius
up to a prescribed outer scale. The upper point set may depend on that scale.
These are obligations, not proved assertions. The signed formula in the 1964
paper and the stronger modern fixed-radius/global-witness summary are distinct.
-/

namespace DiskDiscrepancy

def RunningLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
    ∀ R : ℝ, R₀ ≤ R → ∀ S : Set Plane, Admissible S →
      ∃ center : Plane, ∃ r : ℝ,
        0 < r ∧ r ≤ R ∧ c * Real.sqrt R ≤ discrepancy S center r

def RunningUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
    ∀ R : ℝ, R₀ ≤ R → ∃ S : Set Plane, Admissible S ∧
      ∀ center : Plane, ∀ r : ℝ, 0 < r → r ≤ R →
        discrepancy S center r ≤ C * Real.sqrt (R * Real.log R)

def UniformDiskBound (S : Set Plane) (B : ℝ) : Prop :=
  ∀ center : Plane, ∀ r : ℝ, 0 ≤ r →
    (diskPoints S center r).Finite ∧ discrepancy S center r ≤ B

def NoUniformDiskBound : Prop := ∀ S : Set Plane, ¬ ∃ B : ℝ, UniformDiskBound S B

def CompleteTarget : Prop := RunningLowerBound ∧ RunningUpperBound ∧ NoUniformDiskBound

end DiskDiscrepancy
