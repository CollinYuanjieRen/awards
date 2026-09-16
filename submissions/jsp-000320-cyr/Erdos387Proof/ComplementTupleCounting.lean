import Mathlib
import ErdosProblems.Erdos387.RoughReciprocal

/-!
# Positive complementary tuple counting

All enlargements in this file concern nonnegative reciprocal weights.
The index type is arbitrary and finite, so it can be the complement of one
coordinate without including an unused coordinate in the exponent.
-/

namespace Erdos387Proof.ComplementTupleCounting

open Erdos387
open scoped BigOperators

/-- Factorization of a full Cartesian reciprocal sum. -/
theorem sum_piFinset_reciprocal_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finset ℕ) :
    (∑ f ∈ Fintype.piFinset (fun _ : ι => R),
      (1 : ℝ) / (∏ i, f i : ℕ)) =
      (∑ d ∈ R, (1 : ℝ) / d) ^ Fintype.card ι := by
  classical
  calc
    _ = ∑ f ∈ Fintype.piFinset (fun _ : ι => R),
        ∏ i, ((1 : ℝ) / f i) := by
      apply Finset.sum_congr rfl
      intro f hf
      push_cast
      simp only [one_div, Finset.prod_inv_distrib]
    _ = _ := by
      exact (Finset.sum_prod_piFinset R
        (fun (_ : ι) (d : ℕ) => (1 : ℝ) / d)).trans (by simp)

/-- Any finite tuple family with coordinates in `R` is bounded by the
Cartesian reciprocal mass; the pointwise weights are nonnegative. -/
theorem sum_reciprocal_prod_le_mass_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → ℕ)) (R : Finset ℕ)
    (hA : ∀ f ∈ A, ∀ i, f i ∈ R) :
    (∑ f ∈ A, (1 : ℝ) / (∏ i, f i : ℕ)) ≤
      (∑ d ∈ R, (1 : ℝ) / d) ^ Fintype.card ι := by
  classical
  rw [← sum_piFinset_reciprocal_prod R]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f hf
    exact Fintype.mem_piFinset.mpr (hA f hf)
  · intro f _ _
    positivity

/-- A positive coordinate cannot exceed the positive total product. -/
theorem coordinate_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (hf : ∀ i, 0 < f i) (i : ι) :
    f i ≤ ∏ j, f j := by
  classical
  exact Nat.le_of_dvd (Finset.prod_pos (fun j _ => hf j))
    (Finset.dvd_prod_of_mem f (Finset.mem_univ i))

/-- Finite positive tuples bounded by their product, with a safe logarithmic
exponent equal to the number of coordinates. No pairwise-coprimality or
roughness condition is needed for this upper bound. -/
theorem card_le_mul_one_add_log_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → ℕ)) (T : ℕ)
    (hpos : ∀ f ∈ A, ∀ i, 0 < f i)
    (hprod : ∀ f ∈ A, (∏ i, f i) ≤ T) :
    (A.card : ℝ) ≤ (T : ℝ) * (1 + Real.log T) ^ Fintype.card ι := by
  classical
  have hbox : ∀ f ∈ A, ∀ i, f i ∈ Finset.Icc 1 T := by
    intro f hf i
    exact Finset.mem_Icc.mpr
      ⟨hpos f hf i, (coordinate_le_prod f (hpos f hf) i).trans (hprod f hf)⟩
  have hmass := sum_reciprocal_prod_le_mass_pow A (Finset.Icc 1 T) hbox
  have hsum : (∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / d) = harmonic T := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div]
  rw [hsum] at hmass
  have hper : ∀ f ∈ A, (1 : ℝ) ≤ (T : ℝ) / (∏ i, f i : ℕ) := by
    intro f hf
    have hp : (0 : ℝ) < (∏ i, f i : ℕ) := by
      exact_mod_cast Finset.prod_pos (fun i _ => hpos f hf i)
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using (show ((∏ i, f i : ℕ) : ℝ) ≤ T by
      exact_mod_cast hprod f hf)
  calc
    (A.card : ℝ) = ∑ f ∈ A, (1 : ℝ) := by simp
    _ ≤ ∑ f ∈ A, (T : ℝ) / (∏ i, f i : ℕ) := Finset.sum_le_sum hper
    _ = (T : ℝ) * ∑ f ∈ A, (1 : ℝ) / (∏ i, f i : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      ring
    _ ≤ (T : ℝ) * (harmonic T : ℝ) ^ Fintype.card ι :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh : 0 ≤ (harmonic T : ℝ) := by
        rw [← hsum]
        exact Finset.sum_nonneg (fun d _ => by positivity)
      exact pow_le_pow_left₀ hh (harmonic_le_one_add_log T) _

/-- Explicit independent domain of all positive tuples of product at most T. -/
noncomputable def positiveTuplesUpTo (ι : Type*) [Fintype ι] [DecidableEq ι] (T : ℕ) :
    Finset (ι → ℕ) :=
  (Fintype.piFinset (fun _ : ι => Finset.Icc 1 T)).filter
    (fun f => (∏ i, f i) ≤ T)

theorem card_positiveTuplesUpTo_le (ι : Type*) [Fintype ι] [DecidableEq ι] (T : ℕ) :
    ((positiveTuplesUpTo ι T).card : ℝ) ≤
      (T : ℝ) * (1 + Real.log T) ^ Fintype.card ι := by
  apply card_le_mul_one_add_log_pow
  · intro f hf i
    simp only [positiveTuplesUpTo, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_Icc] at hf
    exact (hf.1 i).1
  · intro f hf
    exact (Finset.mem_filter.mp hf).2

/-- Rough complementary tuples contribute at most the corresponding power
of the exact one-dimensional rough reciprocal mass. -/
theorem sum_rough_reciprocal_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → ℕ)) (z X : ℕ)
    (hA : ∀ f ∈ A, ∀ i, 0 < f i ∧ f i ≤ X ∧ IsZRough z (f i)) :
    (∑ f ∈ A, (1 : ℝ) / (∏ i, f i : ℕ)) ≤
      (roughReciprocalMass z X) ^ Fintype.card ι := by
  exact sum_reciprocal_prod_le_mass_pow A (roughPositiveUpTo z X)
    (fun f hf i => mem_roughPositiveUpTo_iff.mpr (hA f hf i))

/-- Cardinality interface on precisely the coordinates other than `i`. -/
theorem card_complement_tuples_le {k : ℕ} (i : Fin k)
    (A : Finset ({j : Fin k // j ≠ i} → ℕ)) (T : ℕ)
    (hpos : ∀ f ∈ A, ∀ j, 0 < f j)
    (hprod : ∀ f ∈ A, (∏ j, f j) ≤ T) :
    (A.card : ℝ) ≤ (T : ℝ) * (1 + Real.log T) ^ (k - 1) := by
  simpa only [Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Fintype.card_fin] using card_le_mul_one_add_log_pow A T hpos hprod

/-- Rough reciprocal mass on exactly the `k-1` complementary coordinates. -/
theorem sum_complement_rough_reciprocal_prod_le {k : ℕ} (i : Fin k)
    (A : Finset ({j : Fin k // j ≠ i} → ℕ)) (z X : ℕ)
    (hA : ∀ f ∈ A, ∀ j, 0 < f j ∧ f j ≤ X ∧ IsZRough z (f j)) :
    (∑ f ∈ A, (1 : ℝ) / (∏ j, f j : ℕ)) ≤
      (roughReciprocalMass z X) ^ (k - 1) := by
  simpa only [Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Fintype.card_fin] using sum_rough_reciprocal_prod_le A z X hA

end Erdos387Proof.ComplementTupleCounting
