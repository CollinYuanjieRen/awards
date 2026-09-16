import Mathlib
import ErdosProblems.Erdos387.BrunMainTerm

/-!
# Finite relative Brun truncation bounds

The powers-of-two tail estimate is reused from the pinned Brun main-term
module. Here it is compared to the actual Euler product, without an assumed
sieve estimate. Even truncation is bounded below by that product by an exact
finite subset recurrence.
-/

namespace Erdos387Proof.BrunTruncation

open Erdos387
open scoped BigOperators

/-- Exact insertion recurrence, with the signed top-degree layer explicit. -/
theorem brunSubsetSum_insert {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (x : ι → ℝ) (L : ℕ) {a : ι} (ha : a ∉ P) :
    brunSubsetSum (insert a P) x L =
      (1 - x a) * brunSubsetSum P x L +
        x a * ∑ T ∈ P.powerset,
          if T.card = L then (-1 : ℝ) ^ L * subsetMonomial x T else 0 := by
  unfold brunSubsetSum
  rw [Finset.sum_powerset_insert ha]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have haT : a ∉ T := fun hat => ha ((Finset.mem_powerset.mp hT) hat)
  simp only [Finset.card_insert_of_notMem haT, subsetMonomial, Finset.prod_insert haT]
  by_cases hlt : T.card < L
  · have hle : T.card ≤ L := hlt.le
    have hs : T.card + 1 ≤ L := hlt
    have he : T.card ≠ L := ne_of_lt hlt
    simp only [if_pos hle, if_pos hs, if_neg he, pow_succ]
    ring
  · by_cases he : T.card = L
    · simp only [he, le_refl, if_true, Nat.not_succ_le_self, if_false]
      ring
    · have hle : ¬ T.card ≤ L := by omega
      have hs : ¬ T.card + 1 ≤ L := by omega
      simp only [if_neg hle, if_neg hs, if_neg he, mul_zero, zero_add]

/-- Finite Bonferroni inequality for real local densities in `[0,1]`. -/
theorem finiteEulerProduct_le_brunSubsetSum_of_even
    {ι : Type*} (P : Finset ι) (x : ι → ℝ) {L : ℕ} (hL : Even L)
    (hx : ∀ p ∈ P, 0 ≤ x p ∧ x p ≤ 1) :
    finiteEulerProduct P x ≤ brunSubsetSum P x L := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [finiteEulerProduct, brunSubsetSum, subsetMonomial]
  | @insert a P ha ih =>
    have hxa := hx a (Finset.mem_insert_self _ _)
    have hxP : ∀ p ∈ P, 0 ≤ x p ∧ x p ≤ 1 :=
      fun p hp => hx p (Finset.mem_insert_of_mem hp)
    have htop : 0 ≤ ∑ T ∈ P.powerset,
        if T.card = L then (-1 : ℝ) ^ L * subsetMonomial x T else 0 := by
      apply Finset.sum_nonneg
      intro T hT
      rw [hL.neg_one_pow]
      split
      · simp only [one_mul]
        exact subsetMonomial_nonneg (fun p hp =>
          (hxP p ((Finset.mem_powerset.mp hT) hp)).1)
      · exact le_rfl
    rw [brunSubsetSum_insert P x L ha]
    change (∏ p ∈ insert a P, (1 - x p)) ≤ _
    rw [Finset.prod_insert ha]
    change (1 - x a) * finiteEulerProduct P x ≤ _
    exact (mul_le_mul_of_nonneg_left (ih hxP) (by linarith)).trans
      (le_add_of_nonneg_right (mul_nonneg hxa.1 htop))

/-- Euler factors stay positive in the half interval. -/
theorem finiteEulerProduct_pos {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ p ∈ P, x p ≤ 1 / 2) : 0 < finiteEulerProduct P x := by
  apply Finset.prod_pos
  intro p hp
  have := hx p hp
  linarith

/-- One local exponential-moment factor, relative to the Euler factor. -/
theorem one_add_two_mul_le_euler_mul_exp {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    1 + 2 * x ≤ (1 - x) * Real.exp (4 * x) := by
  have hd : 0 < 1 - x := by linarith
  have hn : 0 < 1 + 2 * x := by linarith
  have hlogn := Real.log_le_sub_one_of_pos hn
  have hlogd := Real.one_sub_inv_le_log_of_pos hd
  have hinv : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    apply (sub_le_iff_le_add).mpr
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 2 * x by linarith)]
  have hlog : Real.log ((1 + 2 * x) / (1 - x)) ≤ 4 * x := by
    rw [Real.log_div hn.ne' hd.ne']
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (div_pos hn hd)] at hexp
  have := (div_le_iff₀ hd).mp hexp
  simpa only [mul_comm] using this

/-- The moment product is controlled relative to the actual Euler product. -/
theorem prod_one_add_two_mul_le_euler_mul_exp
    {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ p ∈ P, 0 ≤ x p ∧ x p ≤ 1 / 2) :
    (∏ p ∈ P, (1 + 2 * x p)) ≤
      finiteEulerProduct P x * Real.exp (4 * ∑ p ∈ P, x p) := by
  calc
    _ ≤ ∏ p ∈ P, ((1 - x p) * Real.exp (4 * x p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have := (hx p hp).1
        positivity
      · intro p hp
        exact one_add_two_mul_le_euler_mul_exp (hx p hp).1 (hx p hp).2
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
      rfl

/-- Relative unsigned tail estimate, valid for either truncation parity. -/
theorem brunSubsetTail_le_relative_exp
    {ι : Type*} (P : Finset ι) (x : ι → ℝ) (L : ℕ)
    (hx : ∀ p ∈ P, 0 ≤ x p ∧ x p ≤ 1 / 2) :
    brunSubsetTail P x L ≤ finiteEulerProduct P x *
      ((2 : ℝ) ^ (L + 1))⁻¹ * Real.exp (4 * ∑ p ∈ P, x p) := by
  have htail := pow_two_mul_brunSubsetTail_le P x L (fun p hp => (hx p hp).1)
  have hmoment := prod_one_add_two_mul_le_euler_mul_exp P x hx
  have hpow : 0 < (2 : ℝ) ^ (L + 1) := by positivity
  apply (mul_le_mul_iff_of_pos_left hpow).mp
  calc
    _ ≤ finiteEulerProduct P x * Real.exp (4 * ∑ p ∈ P, x p) :=
      htail.trans hmoment
    _ = _ := by field_simp

/-- The same relative estimate for the absolute error of the signed sum. -/
theorem abs_brunSubsetSum_sub_euler_le_relative_exp
    {ι : Type*} (P : Finset ι) (x : ι → ℝ) (L : ℕ)
    (hx : ∀ p ∈ P, 0 ≤ x p ∧ x p ≤ 1 / 2) :
    |brunSubsetSum P x L - finiteEulerProduct P x| ≤
      finiteEulerProduct P x * ((2 : ℝ) ^ (L + 1))⁻¹ *
        Real.exp (4 * ∑ p ∈ P, x p) :=
  (abs_brunSubsetSum_sub_finiteEulerProduct_le P x L
    (fun p hp => (hx p hp).1)).trans (brunSubsetTail_le_relative_exp P x L hx)

/-- The even Brun main term lies between the Euler product and a relative
explicit upper bound. The constant is slightly stronger than `2^(-L)`. -/
theorem brunSubsetSum_bounds_of_even
    {ι : Type*} (P : Finset ι) (x : ι → ℝ) {L : ℕ} (hL : Even L)
    (hx : ∀ p ∈ P, 0 ≤ x p ∧ x p ≤ 1 / 2) :
    0 < finiteEulerProduct P x ∧
      finiteEulerProduct P x ≤ brunSubsetSum P x L ∧
      brunSubsetSum P x L ≤ finiteEulerProduct P x *
        (1 + ((2 : ℝ) ^ (L + 1))⁻¹ * Real.exp (4 * ∑ p ∈ P, x p)) := by
  refine ⟨finiteEulerProduct_pos P x (fun p hp => (hx p hp).2), ?_, ?_⟩
  · apply finiteEulerProduct_le_brunSubsetSum_of_even P x hL
    intro p hp
    exact ⟨(hx p hp).1, (hx p hp).2.trans (by norm_num)⟩
  · have h := (abs_le.mp (abs_brunSubsetSum_sub_euler_le_relative_exp P x L hx)).2
    nlinarith

end Erdos387Proof.BrunTruncation
