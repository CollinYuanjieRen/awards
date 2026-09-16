/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
import JSP518.JKLY.ProductBernoulli
import JSP518.JKLY.Counting

/-!
# The continuous relaxation (JKLY Lemma 4)

Fix a graph `G`, a set `U` of vertices and a disjoint reservoir `W₀`, and sample a random
subset of `W₀` with independent vertex probabilities `p v ∈ [0.1, 0.9]`.  If the expected
degrees `expDeg G U W₀ p` are pairwise `1`-separated on a subset `U' ⊆ U` and all pairs of
`U'` are `δ`-diverse inside `W₀`, then some `W ⊆ W₀` makes the graph induced on `U ∪ W`
have at least `|U'| / (4 + 160 C / √δ)` distinct degrees; here `C` is the constant of the
anticoncentration bound `AnticBound`, which is taken as a hypothesis.

Two events are combined: Chebyshev's inequality keeps at least half of `U'` within `√|W₀|`
of its expected degree, and Markov's inequality plus the anticoncentration bound keeps the
number of colliding close pairs below `20 C |U'| / √δ`.  A restricted Cauchy--Schwarz
(`card_sq_le_numDistinctDegrees_mul`) replaces the Turán step of the original argument.

Since the product Bernoulli measure of `JSP518.JKLY.ProductBernoulli` samples
subsets of the whole vertex type, the random induced set is `U ∪ (W ∩ W₀)` throughout, and
the returned set is `W ∩ W₀`.  The marginalisation lemma `eventProbability_congr_of_agree`
lets the anticoncentration hypothesis — which needs `p v ∈ [0.1, 0.9]` at *every* vertex —
be applied to a parameter vector that vanishes off `W₀`.
-/

open scoped BigOperators symmDiff

namespace JKLY

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The subsets of the vertex type meeting a ground set `S` in a prescribed `T ⊆ S` are
exactly the unions of `T` with a subset of the complement of `S`. -/
lemma filter_inter_eq_image {S T : Finset V} (hTS : T ⊆ S) :
    ((Finset.univ : Finset (Finset V)).filter fun W ↦ W ∩ S = T) =
      (Sᶜ.powerset).image fun R ↦ T ∪ R := by
  ext W
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_powerset]
  constructor
  · intro hW
    refine ⟨W \ S, ?_, ?_⟩
    · intro z hz
      rw [Finset.mem_sdiff] at hz
      simpa using hz.2
    · rw [← hW]
      ext z
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      by_cases hz : z ∈ S <;> simp [hz]
  · rintro ⟨R, hR, rfl⟩
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hz | hz, hzS⟩
      · exact hz
      · exact absurd hzS (by simpa using hR hz)
    · intro hz
      exact ⟨Or.inl hz, hTS hz⟩

/-- The total product Bernoulli weight of the subsets meeting a ground set `S` in a
prescribed `T ⊆ S` is the product of the marginal weights over `S`. -/
lemma sum_weight_fiber (p : V → ℝ) {S T : Finset V} (hTS : T ⊆ S) :
    (∑ W ∈ (Finset.univ : Finset (Finset V)).filter fun W ↦ W ∩ S = T, PB.weight p W) =
      ∏ v ∈ S, (if v ∈ T then p v else 1 - p v) := by
  classical
  have hinj : ∀ R₁ ∈ Sᶜ.powerset, ∀ R₂ ∈ Sᶜ.powerset,
      T ∪ R₁ = T ∪ R₂ → R₁ = R₂ := by
    intro R₁ h₁ R₂ h₂ h
    rw [Finset.mem_powerset] at h₁ h₂
    have key : ∀ R : Finset V, R ⊆ Sᶜ → (T ∪ R) \ S = R := by
      intro R hR
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hz | hz, hzS⟩
        · exact absurd (hTS hz) hzS
        · exact hz
      · intro hz
        exact ⟨Or.inr hz, by simpa using hR hz⟩
    rw [← key R₁ h₁, ← key R₂ h₂, h]
  have hsplit : ∀ R ∈ Sᶜ.powerset, PB.weight p (T ∪ R) =
      (∏ v ∈ S, (if v ∈ T then p v else 1 - p v)) *
        ∏ v ∈ Sᶜ, (if v ∈ R then p v else 1 - p v) := by
    intro R hR
    rw [Finset.mem_powerset] at hR
    rw [PB.weight, ← Finset.prod_mul_prod_compl S]
    congr 1
    · refine Finset.prod_congr rfl fun v hv ↦ ?_
      have hvR : v ∉ R := fun h ↦ (by simpa using hR h : v ∉ S) hv
      by_cases hvT : v ∈ T <;> simp [hvT, hvR]
    · refine Finset.prod_congr rfl fun v hv ↦ ?_
      have hvS : v ∉ S := by simpa using hv
      have hvT : v ∉ T := fun h ↦ hvS (hTS h)
      by_cases hvR : v ∈ R <;> simp [hvT, hvR]
  rw [filter_inter_eq_image hTS, Finset.sum_image hinj,
    Finset.sum_congr rfl hsplit, ← Finset.mul_sum,
    Erdos88.Probability.sum_prod_ite_mem Sᶜ p fun v ↦ 1 - p v]
  simp

/-- Marginalisation: the expectation of a function depending only on the trace on a ground
set `S` is a weighted sum over the subsets of `S`. -/
lemma expectation_eq_sum_powerset (p : V → ℝ) (S : Finset V) (f : Finset V → ℝ)
    (hf : ∀ W : Finset V, f W = f (W ∩ S)) :
    PB.expectation p f =
      ∑ T ∈ S.powerset, (∏ v ∈ S, (if v ∈ T then p v else 1 - p v)) * f T := by
  classical
  have hmaps : ∀ W ∈ (Finset.univ : Finset (Finset V)), W ∩ S ∈ S.powerset := fun W _ ↦
    Finset.mem_powerset.mpr Finset.inter_subset_right
  rw [PB.expectation, ← Finset.sum_fiberwise_of_maps_to hmaps fun W ↦ PB.weight p W * f W]
  refine Finset.sum_congr rfl fun T hT ↦ ?_
  have hTS : T ⊆ S := Finset.mem_powerset.mp hT
  have hterm : ∀ W ∈ (Finset.univ : Finset (Finset V)).filter fun W ↦ W ∩ S = T,
      PB.weight p W * f W = PB.weight p W * f T := by
    intro W hW
    rw [Finset.mem_filter] at hW
    rw [hf W, hW.2]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_weight_fiber p hTS]

/-- Two parameter vectors agreeing on a ground set `S` give the same expectation to every
function depending only on the trace on `S`. -/
lemma expectation_congr_of_agree {p q : V → ℝ} {S : Finset V} (hpq : ∀ v ∈ S, p v = q v)
    (f : Finset V → ℝ) (hf : ∀ W : Finset V, f W = f (W ∩ S)) :
    PB.expectation p f = PB.expectation q f := by
  rw [expectation_eq_sum_powerset p S f hf, expectation_eq_sum_powerset q S f hf]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  congr 1
  exact Finset.prod_congr rfl fun v hv ↦ by rw [hpq v hv]

/-- Two parameter vectors agreeing on a ground set `S` give the same probability to every
event depending only on the trace on `S`. -/
lemma eventProbability_congr_of_agree {p q : V → ℝ} {S : Finset V} (hpq : ∀ v ∈ S, p v = q v)
    (P : Finset V → Prop) [DecidablePred P] (hP : ∀ W : Finset V, P W ↔ P (W ∩ S)) :
    PB.eventProbability p P = PB.eventProbability q P := by
  unfold PB.eventProbability
  refine expectation_congr_of_agree hpq _ fun W ↦ ?_
  by_cases h : P W
  · have h' : P (W ∩ S) := (hP W).mp h
    simp [h, h']
  · have h' : ¬ P (W ∩ S) := fun hc ↦ h ((hP W).mpr hc)
    simp [h, h']

/-- Expected degree of `u` into `U ∪ W` when `W ⊆ W₀` is sampled with probabilities `p`. -/
noncomputable def expDeg (G : SimpleGraph V) (U W₀ : Finset V) (p : V → ℝ) (u : V) : ℝ :=
  ((Erdos88.neighborsIn G u U).card : ℝ) + ∑ v ∈ W₀, (if G.Adj u v then p v else 0)

/-- The anticoncentration input (JKLY Proposition 5, `±1` coefficients), taken as a
hypothesis. -/
def AnticBound (C : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (p : V → ℝ)
    (_hp : ∀ v, 0.1 ≤ p v ∧ p v ≤ 0.9) (P Q : Finset V) (_hPQ : Disjoint P Q)
    (_hq : 1 ≤ (P ∪ Q).card) (t : ℤ),
    PB.eventProbability p (fun W ↦ ((W ∩ P).card : ℤ) - ((W ∩ Q).card : ℤ) = t) ≤
      C / Real.sqrt ((P ∪ Q).card)

/-- Adding a constant does not change the variance. -/
lemma variance_const_add (p : V → ℝ) (c : ℝ) (f : Finset V → ℝ) :
    PB.variance p (fun W ↦ c + f W) = PB.variance p f := by
  have hE : PB.expectation p (fun W ↦ c + f W) = c + PB.expectation p f := by
    rw [PB.expectation_add, PB.expectation_const]
  have hfun : (fun W : Finset V ↦ (c + f W - PB.expectation p fun W ↦ c + f W) ^ 2) =
      fun W ↦ (f W - PB.expectation p f) ^ 2 := by
    funext W
    rw [hE]
    ring_nf
  simp only [PB.variance, hfun]

/-- The degree of `u` into `U ∪ (W ∩ W₀)` splits into the constant contribution of `U` and a
linear form in the coordinate indicators. -/
lemma degreeInto_eq_add_linear {G : SimpleGraph V} {U W₀ : Finset V} (hUW : Disjoint U W₀)
    (u : V) (W : Finset V) :
    ((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ) =
      ((Erdos88.neighborsIn G u U).card : ℝ) +
        ∑ v : V, (if v ∈ W₀ ∧ G.Adj u v then (1 : ℝ) else 0) * (if v ∈ W then 1 else 0) := by
  classical
  have hunion : Erdos88.neighborsIn G u (U ∪ (W ∩ W₀)) =
      Erdos88.neighborsIn G u U ∪ Erdos88.neighborsIn G u (W ∩ W₀) := by
    ext z
    simp only [Erdos88.mem_neighborsIn, Finset.mem_union, Finset.mem_inter]
    tauto
  have hdisj : Disjoint (Erdos88.neighborsIn G u U) (Erdos88.neighborsIn G u (W ∩ W₀)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [Erdos88.mem_neighborsIn] at hz hz'
    exact Finset.disjoint_left.mp hUW hz.1 (Finset.mem_inter.mp hz'.1).2
  have hsum : (∑ v : V, (if v ∈ W₀ ∧ G.Adj u v then (1 : ℝ) else 0) *
      (if v ∈ W then 1 else 0)) = ((Erdos88.neighborsIn G u (W ∩ W₀)).card : ℝ) := by
    have hterm : ∀ v : V, (if v ∈ W₀ ∧ G.Adj u v then (1 : ℝ) else 0) *
        (if v ∈ W then 1 else 0) =
        if v ∈ Erdos88.neighborsIn G u (W ∩ W₀) then (1 : ℝ) else 0 := by
      intro v
      by_cases hvW₀ : v ∈ W₀ <;> by_cases hvW : v ∈ W <;> by_cases hadj : G.Adj u v <;>
        simp [Erdos88.mem_neighborsIn, hvW₀, hvW, hadj]
    rw [Finset.sum_congr rfl fun v _ ↦ hterm v, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Erdos637.degreeInto, hunion, Finset.card_union_of_disjoint hdisj, hsum]
  push_cast
  ring

/-- The expectation of the degree of `u` into the random set `U ∪ (W ∩ W₀)`. -/
lemma expectation_degreeInto {G : SimpleGraph V} {U W₀ : Finset V} (hUW : Disjoint U W₀)
    (p : V → ℝ) (u : V) :
    PB.expectation p (fun W ↦ ((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ)) =
      expDeg G U W₀ p u := by
  classical
  have hfun : (fun W : Finset V ↦ ((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ)) =
      fun W ↦ ((Erdos88.neighborsIn G u U).card : ℝ) +
        ∑ v : V, (if v ∈ W₀ ∧ G.Adj u v then (1 : ℝ) else 0) * (if v ∈ W then 1 else 0) := by
    funext W
    exact degreeInto_eq_add_linear hUW u W
  have hcoef : (∑ v : V, (if v ∈ W₀ ∧ G.Adj u v then (1 : ℝ) else 0) * p v) =
      ∑ v ∈ W₀, (if G.Adj u v then p v else 0) := by
    rw [← Finset.sum_subset (Finset.subset_univ W₀)]
    · refine Finset.sum_congr rfl fun v hv ↦ ?_
      by_cases hadj : G.Adj u v <;> simp [hv, hadj]
    · intro v _ hv
      simp [hv]
  rw [hfun, PB.expectation_add, PB.expectation_const, PB.expectation_linear, hcoef, expDeg]

omit [Fintype V] in
/-- A parameter vector in `[0.1, 0.9]` on `W₀` and vanishing off `W₀` is a `[0,1]`-vector. -/
lemma inUnit_of_mem {W₀ : Finset V} {p : V → ℝ} (hp : ∀ v ∈ W₀, 0.1 ≤ p v ∧ p v ≤ 0.9)
    (hp0 : ∀ v ∉ W₀, p v = 0) : PB.InUnit p := by
  intro v
  by_cases hv : v ∈ W₀
  · exact ⟨by linarith [(hp v hv).1], by linarith [(hp v hv).2]⟩
  · rw [hp0 v hv]
    norm_num

/-- The variance of the degree of `u` into the random set `U ∪ (W ∩ W₀)` is at most
`|W₀| / 4`. -/
lemma variance_degreeInto_le {G : SimpleGraph V} {U W₀ : Finset V} (hUW : Disjoint U W₀)
    {p : V → ℝ} (hp : ∀ v ∈ W₀, 0.1 ≤ p v ∧ p v ≤ 0.9) (hp0 : ∀ v ∉ W₀, p v = 0) (u : V) :
    PB.variance p (fun W ↦ ((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ)) ≤
      (W₀.card : ℝ) / 4 := by
  classical
  have hpU : PB.InUnit p := inUnit_of_mem hp hp0
  have hfun : (fun W : Finset V ↦ ((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ)) =
      fun W ↦ ((Erdos88.neighborsIn G u U).card : ℝ) +
        ∑ v : V, (if v ∈ W₀ ∧ G.Adj u v then (1 : ℝ) else 0) * (if v ∈ W then 1 else 0) := by
    funext W
    exact degreeInto_eq_add_linear hUW u W
  have hzero : ∀ v ∈ (Finset.univ : Finset V), v ∉ W₀ →
      (if v ∈ W₀ ∧ G.Adj u v then (1 : ℝ) else 0) ^ 2 * (p v * (1 - p v)) = 0 := by
    intro v _ hv
    simp [hv]
  rw [hfun, variance_const_add, PB.variance_linear hpU,
    ← Finset.sum_subset (Finset.subset_univ W₀) hzero]
  calc (∑ v ∈ W₀, (if v ∈ W₀ ∧ G.Adj u v then (1 : ℝ) else 0) ^ 2 * (p v * (1 - p v)))
      ≤ ∑ _v ∈ W₀, (1 : ℝ) / 4 := by
        refine Finset.sum_le_sum fun v hv ↦ ?_
        have h1 := (hp v hv).1
        have h2 := (hp v hv).2
        set c : ℝ := if v ∈ W₀ ∧ G.Adj u v then (1 : ℝ) else 0 with hc
        have hc1 : c ^ 2 ≤ 1 := by
          rw [hc]
          split_ifs <;> norm_num
        have hX0 : 0 ≤ p v * (1 - p v) := by nlinarith
        calc c ^ 2 * (p v * (1 - p v)) ≤ 1 * (p v * (1 - p v)) :=
              mul_le_mul_of_nonneg_right hc1 hX0
          _ ≤ (1 : ℝ) / 4 := by
              rw [one_mul]
              nlinarith [sq_nonneg (p v - 1 / 2)]
    _ = (W₀.card : ℝ) / 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- Chebyshev's inequality: the degree of `u` into the random set deviates from its
expectation by more than `√|W₀|` with probability at most `1/4`. -/
lemma prob_deviate_le {G : SimpleGraph V} {U W₀ : Finset V} (hUW : Disjoint U W₀)
    {p : V → ℝ} (hp : ∀ v ∈ W₀, 0.1 ≤ p v ∧ p v ≤ 0.9) (hp0 : ∀ v ∉ W₀, p v = 0)
    (hN : 1 ≤ W₀.card) (u : V) :
    PB.eventProbability p (fun W ↦ ¬ |((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ) -
        expDeg G U W₀ p u| ≤ Real.sqrt W₀.card) ≤ 1 / 4 := by
  classical
  have hpU : PB.InUnit p := inUnit_of_mem hp hp0
  have hNR : (1 : ℝ) ≤ (W₀.card : ℝ) := by exact_mod_cast hN
  have ht : 0 < Real.sqrt W₀.card := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt W₀.card ^ 2 = (W₀.card : ℝ) := Real.sq_sqrt (by linarith)
  set f : Finset V → ℝ := fun W ↦ ((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ) with hf
  have hE : PB.expectation p f = expDeg G U W₀ p u := expectation_degreeInto hUW p u
  have hmono : PB.eventProbability p
      (fun W ↦ ¬ |f W - expDeg G U W₀ p u| ≤ Real.sqrt W₀.card) ≤
      PB.eventProbability p
        (fun W ↦ Real.sqrt W₀.card ^ 2 ≤ (f W - PB.expectation p f) ^ 2) := by
    refine PB.eventProbability_mono hpU fun W hW ↦ ?_
    rw [hE]
    have hlt : Real.sqrt W₀.card ≤ |f W - expDeg G U W₀ p u| := le_of_lt (not_le.mp hW)
    calc Real.sqrt W₀.card ^ 2 ≤ |f W - expDeg G U W₀ p u| ^ 2 :=
          pow_le_pow_left₀ ht.le hlt 2
      _ = (f W - expDeg G U W₀ p u) ^ 2 := sq_abs _
  refine hmono.trans ((PB.chebyshev_sq_bound hpU ht f).trans ?_)
  rw [hsq]
  have hvar : PB.variance p f ≤ (W₀.card : ℝ) / 4 := variance_degreeInto_le hUW hp hp0 u
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- The degree of `u` into `U ∪ (W ∩ W₀)`, as a constant plus a count inside `W`. -/
lemma degreeInto_eq_card_inter {G : SimpleGraph V} {U W₀ : Finset V} (hUW : Disjoint U W₀)
    (u : V) (W : Finset V) :
    Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) =
      (Erdos88.neighborsIn G u U).card + (W ∩ Erdos88.neighborsIn G u W₀).card := by
  classical
  have hunion : Erdos88.neighborsIn G u (U ∪ (W ∩ W₀)) =
      Erdos88.neighborsIn G u U ∪ (W ∩ Erdos88.neighborsIn G u W₀) := by
    ext z
    simp only [Erdos88.mem_neighborsIn, Finset.mem_union, Finset.mem_inter]
    tauto
  have hdisj : Disjoint (Erdos88.neighborsIn G u U) (W ∩ Erdos88.neighborsIn G u W₀) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [Erdos88.mem_neighborsIn] at hz
    rw [Finset.mem_inter, Erdos88.mem_neighborsIn] at hz'
    exact Finset.disjoint_left.mp hUW hz.1 hz'.2.1
  rw [Erdos637.degreeInto, hunion, Finset.card_union_of_disjoint hdisj]

omit [Fintype V] in
/-- Splitting a count inside `W` along a second set. -/
lemma card_inter_sdiff_add_card_inter_inter (W A B : Finset V) :
    (W ∩ (A \ B)).card + (W ∩ (A ∩ B)).card = (W ∩ A).card := by
  classical
  have h1 : W ∩ (A \ B) = (W ∩ A) \ B := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have h2 : W ∩ (A ∩ B) = (W ∩ A) ∩ B := by
    ext z
    simp only [Finset.mem_inter]
    tauto
  rw [h1, h2, Finset.card_sdiff_add_card_inter]

/-- The anticoncentration bound, applied to a `1`-separated pair: the two random degrees
agree with probability at most `C / √(δ |W₀|)`. -/
lemma prob_degree_collision_le {C : ℝ} (hC : 0 < C) (hantic : AnticBound.{u} C) {δ : ℝ}
    (hδ0 : 0 < δ) {G : SimpleGraph V} {U W₀ : Finset V} (hUW : Disjoint U W₀)
    {p : V → ℝ} (hp : ∀ v ∈ W₀, 0.1 ≤ p v ∧ p v ≤ 0.9) (hp0 : ∀ v ∉ W₀, p v = 0)
    (hN : 1 ≤ W₀.card) {u u' : V}
    (hdiv : δ * W₀.card ≤ (((Erdos637.neighborhoodDiff G u u') ∩ W₀).card : ℝ)) :
    PB.eventProbability p (fun W ↦ Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) =
        Erdos637.degreeInto G u' (U ∪ (W ∩ W₀))) ≤ C / Real.sqrt (δ * W₀.card) := by
  classical
  have hpU : PB.InUnit p := inUnit_of_mem hp hp0
  have hNR : (1 : ℝ) ≤ (W₀.card : ℝ) := by exact_mod_cast hN
  set A : Finset V := Erdos88.neighborsIn G u W₀ with hA
  set B : Finset V := Erdos88.neighborsIn G u' W₀ with hB
  set P : Finset V := A \ B with hP
  set Q : Finset V := B \ A with hQ
  set t : ℤ := ((Erdos88.neighborsIn G u' U).card : ℤ) -
    ((Erdos88.neighborsIn G u U).card : ℤ) with hT
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [hP, Finset.mem_sdiff] at hz
    rw [hQ, Finset.mem_sdiff] at hz'
    exact hz'.2 hz.1
  have hunion : P ∪ Q = (Erdos637.neighborhoodDiff G u u') ∩ W₀ := by
    ext z
    simp only [hP, hQ, hA, hB, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Erdos637.neighborhoodDiff, Finset.mem_symmDiff, Erdos88.mem_neighborsIn,
      Finset.mem_univ, true_and]
    tauto
  have hsqrtpos : 0 < Real.sqrt (δ * W₀.card) :=
    Real.sqrt_pos.mpr (by positivity)
  have hcardR : δ * (W₀.card : ℝ) ≤ (((P ∪ Q).card : ℕ) : ℝ) := by rw [hunion]; exact hdiv
  have hq : 1 ≤ (P ∪ Q).card := by
    by_contra hcon
    have : ((P ∪ Q).card : ℝ) = 0 := by
      have : (P ∪ Q).card = 0 := by omega
      rw [this]
      norm_num
    rw [this] at hcardR
    nlinarith
  set p' : V → ℝ := fun v ↦ if v ∈ W₀ then p v else 1 / 2 with hp'
  have hp'mem : ∀ v, 0.1 ≤ p' v ∧ p' v ≤ 0.9 := by
    intro v
    rw [hp']
    by_cases hv : v ∈ W₀
    · simpa [hv] using hp v hv
    · norm_num [hv]
  have hagree : ∀ v ∈ W₀, p v = p' v := by
    intro v hv
    simp [hp', hv]
  have hPW₀ : P ⊆ W₀ := by
    intro z hz
    rw [hP, Finset.mem_sdiff, hA, Erdos88.mem_neighborsIn] at hz
    exact hz.1.1
  have hQW₀ : Q ⊆ W₀ := by
    intro z hz
    rw [hQ, Finset.mem_sdiff, hB, Erdos88.mem_neighborsIn] at hz
    exact hz.1.1
  have hdepends : ∀ W : Finset V,
      (((W ∩ P).card : ℤ) - ((W ∩ Q).card : ℤ) = t) ↔
        ((((W ∩ W₀) ∩ P).card : ℤ) - (((W ∩ W₀) ∩ Q).card : ℤ) = t) := by
    intro W
    have h1 : (W ∩ W₀) ∩ P = W ∩ P := by
      ext z
      simp only [Finset.mem_inter]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hPW₀ h.2⟩, h.2⟩⟩
    have h2 : (W ∩ W₀) ∩ Q = W ∩ Q := by
      ext z
      simp only [Finset.mem_inter]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hQW₀ h.2⟩, h.2⟩⟩
    rw [h1, h2]
  calc PB.eventProbability p (fun W ↦ Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) =
          Erdos637.degreeInto G u' (U ∪ (W ∩ W₀)))
      ≤ PB.eventProbability p
          (fun W ↦ ((W ∩ P).card : ℤ) - ((W ∩ Q).card : ℤ) = t) := by
        refine PB.eventProbability_mono hpU fun W hW ↦ ?_
        rw [degreeInto_eq_card_inter hUW u W, degreeInto_eq_card_inter hUW u' W,
          ← hA, ← hB] at hW
        have h1 : (W ∩ P).card + (W ∩ (A ∩ B)).card = (W ∩ A).card :=
          card_inter_sdiff_add_card_inter_inter W A B
        have h2 : (W ∩ Q).card + (W ∩ (A ∩ B)).card = (W ∩ B).card := by
          have h := card_inter_sdiff_add_card_inter_inter W B A
          rwa [Finset.inter_comm B A] at h
        omega
    _ = PB.eventProbability p'
          (fun W ↦ ((W ∩ P).card : ℤ) - ((W ∩ Q).card : ℤ) = t) :=
        eventProbability_congr_of_agree hagree _ hdepends
    _ ≤ C / Real.sqrt ((P ∪ Q).card) := hantic p' hp'mem P Q hPQ hq t
    _ ≤ C / Real.sqrt (δ * W₀.card) := by
        gcongr

/-- Markov's inequality for a count of events: if each event in a finite family has
probability at most `c`, then the count of the ones that occur exceeds `a` with probability
at most `s.card * c / a`. -/
lemma prob_count_ge_le {p : V → ℝ} (hpU : PB.InUnit p) {ι : Type*} (s : Finset ι)
    (R : ι → Finset V → Prop) [∀ i, DecidablePred (R i)] {c a : ℝ} (ha : 0 < a)
    (hR : ∀ i ∈ s, PB.eventProbability p (R i) ≤ c) :
    PB.eventProbability p (fun W ↦ a ≤ ((s.filter fun i ↦ R i W).card : ℝ)) ≤
      s.card * c / a := by
  classical
  have hY : ∀ W : Finset V, ((s.filter fun i ↦ R i W).card : ℝ) =
      ∑ i ∈ s, (if R i W then (1 : ℝ) else 0) := fun W ↦ (Finset.sum_boole _ _).symm
  have hnn : ∀ W : Finset V, 0 ≤ ∑ i ∈ s, (if R i W then (1 : ℝ) else 0) := fun W ↦
    Finset.sum_nonneg fun i _ ↦ by positivity
  have hexp : PB.expectation p (fun W ↦ ∑ i ∈ s, (if R i W then (1 : ℝ) else 0)) =
      ∑ i ∈ s, PB.eventProbability p (R i) := PB.expectation_indicator_sum p s R
  have hle : (∑ i ∈ s, PB.eventProbability p (R i)) ≤ s.card * c := by
    calc (∑ i ∈ s, PB.eventProbability p (R i)) ≤ ∑ _i ∈ s, c := Finset.sum_le_sum hR
      _ = s.card * c := by rw [Finset.sum_const, nsmul_eq_mul]
  calc PB.eventProbability p (fun W ↦ a ≤ ((s.filter fun i ↦ R i W).card : ℝ))
      ≤ PB.eventProbability p
          (fun W ↦ a ≤ ∑ i ∈ s, (if R i W then (1 : ℝ) else 0)) :=
        PB.eventProbability_mono hpU fun W hW ↦ by rw [← hY W]; exact hW
    _ ≤ PB.expectation p (fun W ↦ ∑ i ∈ s, (if R i W then (1 : ℝ) else 0)) / a :=
        PB.markov_bound hpU ha _ hnn
    _ ≤ s.card * c / a := by
        rw [hexp]
        gcongr

/-- **JKLY Lemma 4**, the continuous relaxation, with explicit constants.  If the expected
degrees on `U'` are `1`-separated and the pairs of `U'` are `δ`-diverse inside `W₀`, then
some `W ⊆ W₀` makes `U ∪ W` have at least `|U'| / (4 + 160 C / √δ)` distinct degrees. -/
theorem lemma4 {C : ℝ} (hC : 0 < C) (hantic : AnticBound.{u} C)
    {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1)
    (G : SimpleGraph V) (U W₀ U' : Finset V)
    (hUW : Disjoint U W₀) (hU' : U' ⊆ U) (hN : 1 ≤ W₀.card)
    (p : V → ℝ) (hp : ∀ v ∈ W₀, 0.1 ≤ p v ∧ p v ≤ 0.9) (hp0 : ∀ v ∉ W₀, p v = 0)
    (hsep : ∀ u ∈ U', ∀ u' ∈ U', u ≠ u' → 1 ≤ |expDeg G U W₀ p u - expDeg G U W₀ p u'|)
    (hdiv : ∀ u ∈ U', ∀ u' ∈ U', u ≠ u' →
      δ * W₀.card ≤ (((Erdos637.neighborhoodDiff G u u') ∩ W₀).card : ℝ)) :
    ∃ W ⊆ W₀, (1 / (4 + 160 * C / Real.sqrt δ)) * U'.card ≤
      Erdos637.numDistinctDegrees G (U ∪ W) := by
  classical
  have hpU : PB.InUnit p := inUnit_of_mem hp hp0
  have hsqδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have hNR : (1 : ℝ) ≤ (W₀.card : ℝ) := by exact_mod_cast hN
  have hsN : 1 ≤ Real.sqrt W₀.card := by
    simpa using Real.sqrt_le_sqrt hNR
  rcases Nat.eq_zero_or_pos U'.card with hm0 | hmpos
  · refine ⟨∅, Finset.empty_subset _, ?_⟩
    rw [hm0]
    simp
  have hmR : (1 : ℝ) ≤ (U'.card : ℝ) := by exact_mod_cast hmpos
  set A : ℝ := 20 * C / Real.sqrt δ with hAdef
  have hA0 : 0 < A := by rw [hAdef]; positivity
  -- the event that at least half of `U'` has a concentrated degree
  have hE1 : PB.eventProbability p (fun W ↦ ¬ ((U'.card : ℝ) / 2 ≤
      ((U'.filter fun u ↦ |((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ) -
        expDeg G U W₀ p u| ≤ Real.sqrt W₀.card).card : ℝ))) ≤ 1 / 2 := by
    have hbad := prob_count_ge_le (p := p) hpU U'
      (fun u W ↦ ¬ |((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ) -
        expDeg G U W₀ p u| ≤ Real.sqrt W₀.card)
      (c := 1 / 4) (a := (U'.card : ℝ) / 2) (by linarith)
      (fun u _ ↦ prob_deviate_le hUW hp hp0 hN u)
    have hval : (U'.card : ℝ) * (1 / 4) / ((U'.card : ℝ) / 2) = 1 / 2 := by
      have : (U'.card : ℝ) ≠ 0 := by linarith
      field_simp
      norm_num
    refine le_trans (PB.eventProbability_mono hpU ?_) (hbad.trans hval.le)
    intro W hW
    have hsplit := Finset.card_filter_add_card_filter_not (s := U')
      (fun u ↦ |((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ) -
        expDeg G U W₀ p u| ≤ Real.sqrt W₀.card)
    have hsplitR : ((U'.filter fun u ↦ |((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ) -
          expDeg G U W₀ p u| ≤ Real.sqrt W₀.card).card : ℝ) +
        ((U'.filter fun u ↦ ¬ |((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ) -
          expDeg G U W₀ p u| ≤ Real.sqrt W₀.card).card : ℝ) = (U'.card : ℝ) := by
      exact_mod_cast hsplit
    have := not_le.mp hW
    linarith
  -- the close pairs
  have hclose : ((((U' ×ˢ U').filter fun q ↦ q.1 ≠ q.2 ∧
      |expDeg G U W₀ p q.1 - expDeg G U W₀ p q.2| ≤ 2 * Real.sqrt W₀.card).card : ℝ)) ≤
      5 * U'.card * Real.sqrt W₀.card := by
    have h := card_close_pairs_le (S := U') (expDeg G U W₀ p) hsep
      (r := 2 * Real.sqrt W₀.card) (by positivity)
    have hmul : (U'.card : ℝ) * (2 * (2 * Real.sqrt W₀.card) + 1) ≤
        5 * U'.card * Real.sqrt W₀.card := by nlinarith
    exact h.trans hmul
  -- the event that few close pairs collide
  have hE2 : PB.eventProbability p (fun W ↦ ¬ ((((((U' ×ˢ U').filter fun q ↦ q.1 ≠ q.2 ∧
      |expDeg G U W₀ p q.1 - expDeg G U W₀ p q.2| ≤ 2 * Real.sqrt W₀.card).filter
        fun q ↦ Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) =
          Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀))).card : ℝ)) < A * U'.card)) < 1 / 2 := by
    have hcoll : ∀ q ∈ (U' ×ˢ U').filter (fun q ↦ q.1 ≠ q.2 ∧
        |expDeg G U W₀ p q.1 - expDeg G U W₀ p q.2| ≤ 2 * Real.sqrt W₀.card),
        PB.eventProbability p (fun W ↦ Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) =
          Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀))) ≤
          C / Real.sqrt (δ * W₀.card) := by
      intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      exact prob_degree_collision_le hC hantic hδ0 hUW hp hp0 hN
        (hdiv q.1 hq.1.1 q.2 hq.1.2 hq.2.1)
    have hmk := prob_count_ge_le (p := p) hpU
      ((U' ×ˢ U').filter fun q ↦ q.1 ≠ q.2 ∧
        |expDeg G U W₀ p q.1 - expDeg G U W₀ p q.2| ≤ 2 * Real.sqrt W₀.card)
      (fun q W ↦ Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) =
        Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀)))
      (c := C / Real.sqrt (δ * W₀.card)) (a := A * U'.card) (by positivity) hcoll
    have hsqrtmul : Real.sqrt (δ * W₀.card) = Real.sqrt δ * Real.sqrt W₀.card :=
      Real.sqrt_mul hδ0.le _
    have hsNne : Real.sqrt W₀.card ≠ 0 := by linarith
    have hδne : Real.sqrt δ ≠ 0 := ne_of_gt hsqδ
    have hCne : C ≠ 0 := ne_of_gt hC
    have hmne : (U'.card : ℝ) ≠ 0 := by linarith
    have hnum : ((((U' ×ˢ U').filter fun q ↦ q.1 ≠ q.2 ∧
        |expDeg G U W₀ p q.1 - expDeg G U W₀ p q.2| ≤
          2 * Real.sqrt W₀.card).card : ℝ)) * (C / Real.sqrt (δ * W₀.card)) ≤
        5 * C * U'.card / Real.sqrt δ := by
      rw [hsqrtmul]
      have hc0 : 0 ≤ C / (Real.sqrt δ * Real.sqrt W₀.card) := by positivity
      calc ((((U' ×ˢ U').filter fun q ↦ q.1 ≠ q.2 ∧
            |expDeg G U W₀ p q.1 - expDeg G U W₀ p q.2| ≤
              2 * Real.sqrt W₀.card).card : ℝ)) *
              (C / (Real.sqrt δ * Real.sqrt W₀.card))
          ≤ (5 * U'.card * Real.sqrt W₀.card) *
              (C / (Real.sqrt δ * Real.sqrt W₀.card)) := by
            exact mul_le_mul_of_nonneg_right hclose hc0
        _ = 5 * C * U'.card / Real.sqrt δ := by field_simp
    have hquot : 5 * C * (U'.card : ℝ) / Real.sqrt δ / (A * U'.card) = 1 / 4 := by
      rw [hAdef]
      field_simp
      norm_num
    have hfinal : (((U' ×ˢ U').filter fun q ↦ q.1 ≠ q.2 ∧
        |expDeg G U W₀ p q.1 - expDeg G U W₀ p q.2| ≤
          2 * Real.sqrt W₀.card).card : ℝ) * (C / Real.sqrt (δ * W₀.card)) /
        (A * U'.card) ≤ 1 / 4 := by
      rw [← hquot]
      gcongr
    refine lt_of_le_of_lt (le_trans (PB.eventProbability_mono hpU ?_)
      (hmk.trans hfinal)) (by norm_num)
    intro W hW
    exact not_lt.mp hW
  obtain ⟨W, hW1, hW2⟩ := PB.exists_of_two_events hpU hE1 hE2
  refine ⟨W ∩ W₀, Finset.inter_subset_right, ?_⟩
  set S : Finset V := U'.filter fun u ↦
    |((Erdos637.degreeInto G u (U ∪ (W ∩ W₀)) : ℕ) : ℝ) - expDeg G U W₀ p u| ≤
      Real.sqrt W₀.card with hSdef
  have hSU' : S ⊆ U' := Finset.filter_subset _ _
  have hSH : S ⊆ U ∪ (W ∩ W₀) := fun x hx ↦ Finset.mem_union_left _ (hU' (hSU' hx))
  have hcs := card_sq_le_numDistinctDegrees_mul (G := G) (S := S) (W := U ∪ (W ∩ W₀)) hSH
  have hD0 : (0 : ℝ) ≤ (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) :=
    Nat.cast_nonneg _
  have hsub : (S ×ˢ S).filter (fun q ↦ Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) =
      Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀))) ⊆
      ((S ×ˢ S).filter fun q ↦ q.1 = q.2) ∪
        (((U' ×ˢ U').filter fun q ↦ q.1 ≠ q.2 ∧
          |expDeg G U W₀ p q.1 - expDeg G U W₀ p q.2| ≤ 2 * Real.sqrt W₀.card).filter
            fun q ↦ Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) =
              Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀))) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2⟩, heq⟩ := hq
    by_cases hne : q.1 = q.2
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hne⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, heq⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hSU' h1, hSU' h2⟩, hne, ?_⟩
      have ha1 := abs_le.mp (Finset.mem_filter.mp h1).2
      have ha2 := abs_le.mp (Finset.mem_filter.mp h2).2
      have hd : ((Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) : ℕ) : ℝ) =
          ((Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀)) : ℕ) : ℝ) := by rw [heq]
      rw [abs_le]
      constructor <;> [linarith [ha1.1, ha2.2]; linarith [ha1.2, ha2.1]]
  have hdiag : ((S ×ˢ S).filter fun q ↦ q.1 = q.2).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun q ↦ q.1) ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
      exact hq.1.1
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
      have h2 : a.2 = b.2 := by rw [← ha.2, ← hb.2]; exact hab
      exact Prod.ext hab h2
  have hpairs : (((S ×ˢ S).filter fun q ↦ Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) =
      Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀))).card : ℝ) ≤
      (U'.card : ℝ) + A * U'.card := by
    have hc1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc1R : (((S ×ˢ S).filter fun q ↦ Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) =
        Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀))).card : ℝ) ≤
        (((S ×ˢ S).filter fun q ↦ q.1 = q.2).card : ℝ) +
          ((((U' ×ˢ U').filter fun q ↦ q.1 ≠ q.2 ∧
            |expDeg G U W₀ p q.1 - expDeg G U W₀ p q.2| ≤
              2 * Real.sqrt W₀.card).filter
              fun q ↦ Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) =
                Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀))).card : ℝ) := by
      exact_mod_cast hc1
    have hdiagR : (((S ×ˢ S).filter fun q ↦ q.1 = q.2).card : ℝ) ≤ (U'.card : ℝ) := by
      have : ((S ×ˢ S).filter fun q ↦ q.1 = q.2).card ≤ U'.card :=
        hdiag.trans (Finset.card_le_card hSU')
      exact_mod_cast this
    linarith
  have hScard : (U'.card : ℝ) / 2 ≤ (S.card : ℝ) := hW1
  have hmpos' : (0 : ℝ) < (U'.card : ℝ) := by linarith
  have key : ((U'.card : ℝ) / 2) ^ 2 ≤
      (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) *
        ((U'.card : ℝ) + A * U'.card) := by
    calc ((U'.card : ℝ) / 2) ^ 2 ≤ (S.card : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by linarith) hScard 2
      _ ≤ (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) *
            (((S ×ˢ S).filter fun q ↦ Erdos637.degreeInto G q.1 (U ∪ (W ∩ W₀)) =
              Erdos637.degreeInto G q.2 (U ∪ (W ∩ W₀))).card : ℝ) := hcs
      _ ≤ (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) *
            ((U'.card : ℝ) + A * U'.card) := mul_le_mul_of_nonneg_left hpairs hD0
  have hstep : ((U'.card : ℝ) / 4) * U'.card ≤
      ((Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) * (1 + A)) * U'.card := by
    have e1 : ((U'.card : ℝ) / 4) * U'.card = ((U'.card : ℝ) / 2) ^ 2 := by ring
    have e2 : ((Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) * (1 + A)) * U'.card =
        (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) *
          ((U'.card : ℝ) + A * U'.card) := by ring
    rw [e1, e2]
    exact key
  have hstep2 : (U'.card : ℝ) / 4 ≤
      (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) * (1 + A) :=
    le_of_mul_le_mul_right hstep hmpos'
  have hden : 0 < 4 + 160 * C / Real.sqrt δ := by positivity
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hden]
  have hAeq : 160 * C / Real.sqrt δ = 8 * A := by rw [hAdef]; ring
  have he2 : (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) * (1 + A) =
      (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) +
        (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) * A := by ring
  have he3 : (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) * (4 + 8 * A) =
      4 * (Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) +
        8 * ((Erdos637.numDistinctDegrees G (U ∪ (W ∩ W₀)) : ℝ) * A) := by ring
  rw [hAeq, he3]
  rw [he2] at hstep2
  linarith [mul_nonneg hD0 hA0.le]

end JKLY
