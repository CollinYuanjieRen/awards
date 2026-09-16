import Erdos387Proof.MediumComplementMass
import Erdos387Proof.MediumComplementBounds

/-! Preserve the two periodic-completion contributions when summing over
actual complementary vectors. The long-interval term uses reciprocal mass. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumOscillatoryMass

open Erdos387 MediumComplementGrouping MediumComplementMass MediumComplementBounds
open scoped BigOperators

def minComplement (B X large : ℕ) : ℕ := (X / 2) / (B * large) + 1

def maxComplement (X medium : ℕ) : ℕ := X / (medium + 1)

theorem representative_bounds {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    (hB : 0 < B) (c : {a // a ∈ vectors S X z medium large i}) :
    minComplement B X large ≤ (representative c).val.otherValue i ∧
      (representative c).val.otherValue i ≤ maxComplement X medium := by
  refine ⟨lower_complement_lt hB (representative_mem c), ?_⟩
  have h := vector_product_le_div c.property
  rw [← vector_representative c, prod_vector_eq_otherValue] at h
  exact h

/-- The term proportional to interval length must be summed using the
reciprocal mass; replacing it by a worst-case bound would lose the saving. -/
theorem sum_longInterval_le {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k) (hB : 0 < B) :
    (∑ c ∈ (vectors S X z medium large i).attach,
      (X : ℝ) / ((representative c).val.otherValue i *
        Real.sqrt ((representative c).val.otherValue i))) ≤
      ((X : ℝ) / Real.sqrt (minComplement B X large)) *
        roughReciprocalMass z X ^ (S.k - 1) := by
  classical
  have hmin : (0 : ℝ) < minComplement B X large := by
    exact_mod_cast (Nat.succ_pos ((X / 2) / (B * large)))
  have hroot := Real.sqrt_pos.mpr hmin
  calc
    _ ≤ ∑ c ∈ (vectors S X z medium large i).attach,
        ((X : ℝ) / Real.sqrt (minComplement B X large)) *
          (1 / ((representative c).val.otherValue i : ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      have hD : (0 : ℝ) < (representative c).val.otherValue i := by
        exact_mod_cast (representative c).val.otherValue_pos i
      calc
        _ ≤ (X : ℝ) / ((representative c).val.otherValue i *
            Real.sqrt (minComplement B X large)) := by
          apply div_le_div_of_nonneg_left (by positivity) (mul_pos hD hroot)
          exact mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (by exact_mod_cast (representative_bounds hB c).1)) hD.le
        _ = _ := by ring
    _ = ((X : ℝ) / Real.sqrt (minComplement B X large)) *
        ∑ c ∈ (vectors S X z medium large i).attach,
          (1 / ((representative c).val.otherValue i : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_reciprocal_representatives_le i) (by positivity)

/-- The incomplete last period instead uses the actual complementary
cardinality and its upper product bound. -/
theorem sum_lastPeriod_le {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k) (hB : 0 < B) :
    (∑ c ∈ (vectors S X z medium large i).attach,
      Real.sqrt ((representative c).val.otherValue i)) ≤
      Real.sqrt (maxComplement X medium) * maxComplement X medium *
        (1 + Real.log (maxComplement X medium)) ^ (S.k - 1) := by
  classical
  calc
    _ ≤ ∑ _c ∈ (vectors S X z medium large i).attach,
        Real.sqrt (maxComplement X medium) := by
      apply Finset.sum_le_sum
      intro c hc
      exact Real.sqrt_le_sqrt (by exact_mod_cast (representative_bounds hB c).2)
    _ = Real.sqrt (maxComplement X medium) * (vectors S X z medium large i).card := by
      simp [mul_comm]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (card_vectors_le (X := X) (z := z)
        (medium := medium) (large := large) i) (Real.sqrt_nonneg (maxComplement X medium))
      simpa only [maxComplement, mul_assoc] using h

noncomputable def envelope {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (X z medium large : ℕ) : ℝ :=
  ((X : ℝ) / Real.sqrt (minComplement B X large)) * roughReciprocalMass z X ^ (S.k - 1) +
    Real.sqrt (maxComplement X medium) * maxComplement X medium *
      (1 + Real.log (maxComplement X medium)) ^ (S.k - 1)

theorem sum_completion_shape_le {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k) (hB : 0 < B) :
    (∑ c ∈ (vectors S X z medium large i).attach,
      ((X : ℝ) / ((representative c).val.otherValue i *
        Real.sqrt ((representative c).val.otherValue i)) +
          Real.sqrt ((representative c).val.otherValue i))) ≤
      envelope S X z medium large := by
  rw [Finset.sum_add_distrib]
  exact add_le_add (sum_longInterval_le i hB) (sum_lastPeriod_le i hB)

end Erdos387Proof.MediumOscillatoryMass
