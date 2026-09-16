import Mathlib
import JSP518.External.Erdos88.Probability

/-!
# The vertex-dependent product Bernoulli measure

The probability model in `JSP518.External.Erdos88.Probability` keeps a single scalar
parameter `p : ℝ` for every coordinate.  The Jenssen--Keevash--Lichev--Yepremyan argument on
distinct degrees in induced subgraphs instead needs an independent Bernoulli coordinate for every
vertex, with its own parameter `p v`.

This file develops that model in exactly the same explicit-finite-sum style: `weight` is a product
of `ite`s over the vertex type, `expectation` is a finite sum over `Finset (Finset V)`, and no
measure theory is involved.  The structural lemma `expectation_prod_coord` — an immediate
consequence of the (already vertex-dependent) identity
`Erdos88.Probability.sum_prod_ite_mem` — encodes independence of the coordinates and generates the
normalisation, the coordinate expectations, and the variance of a linear form.

The Markov and Chebyshev bounds are ports of the scalar versions.
-/

open scoped BigOperators

universe u

namespace JKLY
namespace PB

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The vertex-dependent Bernoulli product weight of a subset `W` of the vertex type. -/
noncomputable def weight (p : V → ℝ) (W : Finset V) : ℝ :=
  ∏ v : V, if v ∈ W then p v else 1 - p v

/-- Expectation in the vertex-dependent product Bernoulli model. -/
noncomputable def expectation (p : V → ℝ) (f : Finset V → ℝ) : ℝ :=
  ∑ W : Finset V, weight p W * f W

/-- Variance in the vertex-dependent product Bernoulli model. -/
noncomputable def variance (p : V → ℝ) (f : Finset V → ℝ) : ℝ :=
  expectation p fun W ↦ (f W - expectation p f) ^ 2

/-- Probability of a predicate in the vertex-dependent product Bernoulli model. -/
noncomputable def eventProbability (p : V → ℝ) (P : Finset V → Prop)
    [DecidablePred P] : ℝ :=
  expectation p fun W ↦ if P W then 1 else 0

/-- The parameter vector takes all its values in the unit interval. -/
def InUnit (p : V → ℝ) : Prop := ∀ v : V, 0 ≤ p v ∧ p v ≤ 1

/-- Each product Bernoulli weight is nonnegative for a parameter vector in `[0,1]`. -/
lemma weight_nonneg {p : V → ℝ} (hp : InUnit p) (W : Finset V) : 0 ≤ weight p W := by
  classical
  refine Finset.prod_nonneg fun v _ ↦ ?_
  by_cases hv : v ∈ W
  · simpa [hv] using (hp v).1
  · simpa [hv] using sub_nonneg.mpr (hp v).2

/-- The product Bernoulli weights sum to one. -/
lemma sum_weight (p : V → ℝ) : ∑ W : Finset V, weight p W = 1 := by
  classical
  rw [Erdos88.Probability.sum_univ_eq_sum_powerset]
  simpa [weight] using
    Erdos88.Probability.sum_prod_ite_mem (Finset.univ : Finset V) p fun v ↦ 1 - p v

/-- Independence of the coordinates: the expectation of a product of coordinate functions over a
finset `T` is the product of the coordinate expectations. -/
lemma expectation_prod_coord (p : V → ℝ) (T : Finset V) (g : V → Bool → ℝ) :
    expectation p (fun W ↦ ∏ v ∈ T, g v (decide (v ∈ W))) =
      ∏ v ∈ T, (p v * g v true + (1 - p v) * g v false) := by
  classical
  set a : V → ℝ := fun v ↦ if v ∈ T then p v * g v true else p v with ha
  set b : V → ℝ := fun v ↦ if v ∈ T then (1 - p v) * g v false else 1 - p v with hb
  have hterm : ∀ W : Finset V,
      weight p W * (∏ v ∈ T, g v (decide (v ∈ W))) =
        ∏ v : V, if v ∈ W then a v else b v := by
    intro W
    have h1 : (∏ v ∈ T, g v (decide (v ∈ W))) =
        ∏ v : V, if v ∈ T then g v (decide (v ∈ W)) else 1 := by
      rw [Finset.prod_ite_mem, Finset.univ_inter]
    rw [weight, h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    by_cases hvT : v ∈ T <;> by_cases hvW : v ∈ W <;> simp [ha, hb, hvT, hvW]
  have hsum : ∀ v : V, a v + b v =
      if v ∈ T then p v * g v true + (1 - p v) * g v false else 1 := by
    intro v
    by_cases hvT : v ∈ T <;> simp [ha, hb, hvT]
  calc expectation p (fun W ↦ ∏ v ∈ T, g v (decide (v ∈ W)))
      = ∑ W ∈ (Finset.univ : Finset V).powerset, ∏ v : V, if v ∈ W then a v else b v := by
        rw [expectation, Erdos88.Probability.sum_univ_eq_sum_powerset]
        exact Finset.sum_congr rfl fun W _ ↦ hterm W
    _ = ∏ v : V, (a v + b v) :=
        Erdos88.Probability.sum_prod_ite_mem (Finset.univ : Finset V) a b
    _ = ∏ v ∈ T, (p v * g v true + (1 - p v) * g v false) := by
        simp_rw [hsum]
        rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- The expectation of a constant is that constant. -/
@[simp] lemma expectation_const (p : V → ℝ) (c : ℝ) :
    expectation p (fun _ ↦ c) = c := by
  classical
  simp [expectation, ← Finset.sum_mul, sum_weight]

/-- Expectation is additive. -/
lemma expectation_add (p : V → ℝ) (f g : Finset V → ℝ) :
    expectation p (fun W ↦ f W + g W) = expectation p f + expectation p g := by
  classical
  simp [expectation, mul_add, Finset.sum_add_distrib]

/-- Expectation commutes with differences. -/
lemma expectation_sub (p : V → ℝ) (f g : Finset V → ℝ) :
    expectation p (fun W ↦ f W - g W) = expectation p f - expectation p g := by
  classical
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

/-- Expectation commutes with scalar multiples. -/
lemma expectation_smul (p : V → ℝ) (c : ℝ) (f : Finset V → ℝ) :
    expectation p (fun W ↦ c * f W) = c * expectation p f := by
  classical
  unfold expectation
  calc
    (∑ W : Finset V, weight p W * (c * f W)) =
        ∑ W : Finset V, c * (weight p W * f W) :=
      Finset.sum_congr rfl fun W _ ↦ by ring
    _ = c * ∑ W : Finset V, weight p W * f W := by rw [Finset.mul_sum]

/-- Expectation commutes with finite sums of functions. -/
lemma expectation_sum {I : Type*} (p : V → ℝ) (s : Finset I) (f : I → Finset V → ℝ) :
    expectation p (fun W ↦ ∑ i ∈ s, f i W) = ∑ i ∈ s, expectation p (f i) := by
  classical
  unfold expectation
  calc
    (∑ W : Finset V, weight p W * ∑ i ∈ s, f i W) =
        ∑ W : Finset V, ∑ i ∈ s, weight p W * f i W :=
      Finset.sum_congr rfl fun W _ ↦ by rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ W : Finset V, weight p W * f i W := Finset.sum_comm

/-- Expectation is monotone for a parameter vector in `[0,1]`. -/
lemma expectation_mono {p : V → ℝ} (hp : InUnit p) {f g : Finset V → ℝ}
    (hfg : ∀ W : Finset V, f W ≤ g W) : expectation p f ≤ expectation p g := by
  classical
  unfold expectation
  exact Finset.sum_le_sum fun W _ ↦
    mul_le_mul_of_nonneg_left (hfg W) (weight_nonneg hp W)

/-- The expectation of the `0`--`1` coordinate at `v` is `p v`. -/
lemma expectation_bit (p : V → ℝ) (v : V) :
    expectation p (fun W ↦ if v ∈ W then (1 : ℝ) else 0) = p v := by
  classical
  simpa using expectation_prod_coord p {v} fun _ b ↦ if b then (1 : ℝ) else 0

/-- Distinct coordinates are independent: the expectation of the product of two distinct
coordinate indicators is the product of the two parameters. -/
lemma expectation_bit_mul_of_ne (p : V → ℝ) {v v' : V} (hvv' : v ≠ v') :
    expectation p
        (fun W ↦ (if v ∈ W then (1 : ℝ) else 0) * (if v' ∈ W then (1 : ℝ) else 0)) =
      p v * p v' := by
  classical
  simpa [Finset.prod_pair hvv'] using
    expectation_prod_coord p {v, v'} fun _ b ↦ if b then (1 : ℝ) else 0

/-- The expectation of a linear form in the coordinate indicators. -/
lemma expectation_linear (p : V → ℝ) (a : V → ℝ) :
    expectation p (fun W ↦ ∑ v : V, a v * (if v ∈ W then (1 : ℝ) else 0)) =
      ∑ v : V, a v * p v := by
  classical
  rw [expectation_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [expectation_smul, expectation_bit]

/-- Variance is the second moment minus the square of the first moment. -/
lemma variance_eq_expectation_sq_sub (p : V → ℝ) (f : Finset V → ℝ) :
    variance p f = expectation p (fun W ↦ f W ^ 2) - (expectation p f) ^ 2 := by
  classical
  unfold variance
  have hfun : (fun W : Finset V ↦ (f W - expectation p f) ^ 2) =
      fun W ↦ f W ^ 2 - (2 * expectation p f) * f W + (expectation p f) ^ 2 := by
    funext W
    ring
  rw [hfun, expectation_add, expectation_sub, expectation_smul, expectation_const]
  ring

/-- The variance of a linear form in the coordinate indicators, using independence of distinct
coordinates. -/
lemma variance_linear {p : V → ℝ} (_hp : InUnit p) (a : V → ℝ) :
    variance p (fun W ↦ ∑ v : V, a v * (if v ∈ W then (1 : ℝ) else 0)) =
      ∑ v : V, a v ^ 2 * (p v * (1 - p v)) := by
  classical
  have hpair : ∀ v w : V,
      expectation p
          (fun W ↦ (if v ∈ W then (1 : ℝ) else 0) * (if w ∈ W then (1 : ℝ) else 0)) =
        if v = w then p v else p v * p w := by
    intro v w
    split_ifs with hvw
    · subst hvw
      have hfun : (fun W : Finset V ↦
          (if v ∈ W then (1 : ℝ) else 0) * (if v ∈ W then (1 : ℝ) else 0)) =
          fun W ↦ if v ∈ W then (1 : ℝ) else 0 := by
        funext W
        by_cases hv : v ∈ W <;> simp [hv]
      rw [hfun, expectation_bit]
    · exact expectation_bit_mul_of_ne p hvw
  have hsq : expectation p
      (fun W ↦ (∑ v : V, a v * (if v ∈ W then (1 : ℝ) else 0)) ^ 2) =
      ∑ v : V, ∑ w : V, a v * a w * (if v = w then p v else p v * p w) := by
    have hfun : (fun W : Finset V ↦ (∑ v : V, a v * (if v ∈ W then (1 : ℝ) else 0)) ^ 2) =
        fun W ↦ ∑ v : V, ∑ w : V, a v * a w *
          ((if v ∈ W then (1 : ℝ) else 0) * (if w ∈ W then (1 : ℝ) else 0)) := by
      funext W
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun w _ ↦ by ring
    rw [hfun, expectation_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [expectation_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [expectation_smul, hpair v w]
  rw [variance_eq_expectation_sq_sub, hsq, expectation_linear, sq, Finset.sum_mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ w : V,
      a v * a w * (if v = w then p v else p v * p w) - a v * p v * (a w * p w) =
        if v = w then a v ^ 2 * (p v * (1 - p v)) else 0 := by
    intro w
    split_ifs with hvw
    · subst hvw
      ring
    · ring
  rw [Finset.sum_congr rfl fun w _ ↦ hterm w]
  simp

/-- Markov's inequality in the vertex-dependent product Bernoulli model. -/
lemma markov_bound {p : V → ℝ} (hp : InUnit p) {a : ℝ} (ha : 0 < a)
    (Y : Finset V → ℝ) (hY : ∀ W : Finset V, 0 ≤ Y W) :
    eventProbability p (fun W ↦ a ≤ Y W) ≤ expectation p Y / a := by
  classical
  unfold eventProbability expectation
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm]
  calc
    a * ∑ W : Finset V, weight p W * (if a ≤ Y W then (1 : ℝ) else 0) =
        ∑ W : Finset V, a * (weight p W * (if a ≤ Y W then (1 : ℝ) else 0)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ W : Finset V, weight p W * Y W := by
      refine Finset.sum_le_sum fun W _ ↦ ?_
      have hw := weight_nonneg hp W
      by_cases h : a ≤ Y W
      · have hite : (if a ≤ Y W then (1 : ℝ) else 0) = 1 := by simp [h]
        rw [hite, mul_one]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left h hw
      · have hite : (if a ≤ Y W then (1 : ℝ) else 0) = 0 := by simp [h]
        rw [hite, mul_zero, mul_zero]
        exact mul_nonneg hw (hY W)

/-- Chebyshev's inequality, in the squared-deviation form. -/
lemma chebyshev_sq_bound {p : V → ℝ} (hp : InUnit p) {t : ℝ} (ht : 0 < t)
    (f : Finset V → ℝ) :
    eventProbability p (fun W ↦ t ^ 2 ≤ (f W - expectation p f) ^ 2) ≤
      variance p f / t ^ 2 := by
  classical
  exact markov_bound hp (by positivity) (fun W ↦ (f W - expectation p f) ^ 2)
    fun W ↦ sq_nonneg _

/-- Event probabilities are nonnegative. -/
lemma eventProbability_nonneg {p : V → ℝ} (hp : InUnit p) (P : Finset V → Prop)
    [DecidablePred P] : 0 ≤ eventProbability p P := by
  classical
  unfold eventProbability expectation
  refine Finset.sum_nonneg fun W _ ↦ ?_
  exact mul_nonneg (weight_nonneg hp W) (by positivity)

/-- Event probabilities are monotone in the event. -/
lemma eventProbability_mono {p : V → ℝ} (hp : InUnit p) {P Q : Finset V → Prop}
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ W : Finset V, P W → Q W) :
    eventProbability p P ≤ eventProbability p Q := by
  classical
  unfold eventProbability
  refine expectation_mono hp fun W ↦ ?_
  by_cases hP : P W
  · have h1 : (if P W then (1 : ℝ) else 0) = 1 := by simp [hP]
    have h2 : (if Q W then (1 : ℝ) else 0) = 1 := by simp [hPQ W hP]
    rw [h1, h2]
  · have h1 : (if P W then (1 : ℝ) else 0) = 0 := by simp [hP]
    rw [h1]
    positivity

/-- Event probabilities are at most one. -/
lemma eventProbability_le_one {p : V → ℝ} (hp : InUnit p) (P : Finset V → Prop)
    [DecidablePred P] : eventProbability p P ≤ 1 := by
  classical
  unfold eventProbability
  calc expectation p (fun W ↦ if P W then (1 : ℝ) else 0)
      ≤ expectation p (fun _ ↦ (1 : ℝ)) := by
        refine expectation_mono hp fun W ↦ ?_
        by_cases hP : P W <;> simp [hP]
    _ = 1 := expectation_const p 1

/-- The probability of the complement of an event. -/
lemma eventProbability_compl (p : V → ℝ) (P : Finset V → Prop) [DecidablePred P] :
    eventProbability p (fun W ↦ ¬ P W) = 1 - eventProbability p P := by
  classical
  have hfun : (fun W : Finset V ↦ if ¬ P W then (1 : ℝ) else 0) =
      fun W ↦ (1 : ℝ) - (if P W then (1 : ℝ) else 0) := by
    funext W
    by_cases hP : P W <;> simp [hP]
  unfold eventProbability
  rw [hfun, expectation_sub, expectation_const]

/-- The expectation of a finite sum of indicators is the sum of the event probabilities. -/
lemma expectation_indicator_sum {I : Type*} (p : V → ℝ) (s : Finset I)
    (P : I → Finset V → Prop) [∀ i, DecidablePred (P i)] :
    expectation p (fun W ↦ ∑ i ∈ s, if P i W then (1 : ℝ) else 0) =
      ∑ i ∈ s, eventProbability p (P i) :=
  expectation_sum p s fun i W ↦ if P i W then (1 : ℝ) else 0

/-- An event of positive probability is nonempty. -/
lemma exists_of_eventProbability_pos {p : V → ℝ} (_hp : InUnit p) {P : Finset V → Prop}
    [DecidablePred P] (h : 0 < eventProbability p P) : ∃ W : Finset V, P W := by
  classical
  by_contra hcon
  rw [not_exists] at hcon
  have hzero : eventProbability p P = 0 := by
    unfold eventProbability
    have hfun : (fun W : Finset V ↦ if P W then (1 : ℝ) else 0) = fun _ ↦ (0 : ℝ) := by
      funext W
      simp [hcon W]
    rw [hfun, expectation_const]
  rw [hzero] at h
  exact lt_irrefl 0 h

/-- Two events whose complements have probability at most and less than one half meet. -/
lemma exists_of_two_events {p : V → ℝ} {P Q : Finset V → Prop}
    [DecidablePred P] [DecidablePred Q] (hp : InUnit p)
    (hP : eventProbability p (fun W ↦ ¬ P W) ≤ 1 / 2)
    (hQ : eventProbability p (fun W ↦ ¬ Q W) < 1 / 2) :
    ∃ W : Finset V, P W ∧ Q W := by
  classical
  have hsub : eventProbability p (fun W ↦ ¬ (P W ∧ Q W)) ≤
      eventProbability p (fun W ↦ ¬ P W) + eventProbability p (fun W ↦ ¬ Q W) := by
    have hadd := expectation_add p (fun W ↦ if ¬ P W then (1 : ℝ) else 0)
      fun W ↦ if ¬ Q W then (1 : ℝ) else 0
    unfold eventProbability
    rw [← hadd]
    refine expectation_mono hp fun W ↦ ?_
    by_cases hPW : P W <;> by_cases hQW : Q W <;> norm_num [hPW, hQW]
  have hc := eventProbability_compl p fun W ↦ P W ∧ Q W
  refine exists_of_eventProbability_pos hp (P := fun W ↦ P W ∧ Q W) ?_
  linarith

end PB
end JKLY
