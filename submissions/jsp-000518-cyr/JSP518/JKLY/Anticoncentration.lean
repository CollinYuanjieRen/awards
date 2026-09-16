/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
import JSP518.JKLY.ProductBernoulli
import JSP518.JKLY.Counting

/-!
# Anticoncentration for the vertex-dependent product Bernoulli measure

This file proves Proposition 5 of Jenssen--Keevash--Lichev--Yepremyan, specialised to `±1`
coefficients: if `p v ∈ [0.1, 0.9]` for every vertex `v` and `P`, `Q` are disjoint finsets with
`q := |P ∪ Q| ≥ 1`, then for every `t : ℤ`

`P( |W ∩ P| - |W ∩ Q| = t ) ≤ anticConst / √q`.

The route is the splitting argument of the paper.  Every `p v ∈ [0.1, 0.9]` can be written as
`p v = w v / 2 + (1 - w v) * z v` with `w v ∈ [0.2, 1]` and `z v ∈ {0, 1}` (`exists_split`).
Sampling `W` from the product measure with parameters `p` is therefore the same as first sampling
a set `S` from the product measure with parameters `w` and then choosing `W ∩ S` uniformly among
the subsets of `S`, the coordinates outside `S` being frozen to `z` (`expectation_eq_mixture`).

Conditionally on `S`, the event becomes a `±1` Erdős--Littlewood--Offord event on the ground set
`S`, so `card_filter_shift_le` bounds its conditional probability by `K / √|(P ∪ Q) ∩ S|`.
Chebyshev's inequality applied to `|(P ∪ Q) ∩ S|` (whose mean is at least `0.2 q` and whose
variance is at most `q / 4`) shows that `|(P ∪ Q) ∩ S| > q / 10` except with probability `25 / q`.
-/

open scoped BigOperators

namespace JKLY

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The splitting of a parameter in `[0.1, 0.9]` -/

omit [Fintype V] [DecidableEq V] in
/-- Every parameter in `[0.1, 0.9]` is a mixture of a fair coin and a constant bit, with mixture
weight at least `0.2` on the fair coin. -/
lemma exists_split (p : V → ℝ) (hp : ∀ v : V, 0.1 ≤ p v ∧ p v ≤ 0.9) :
    ∃ (w : V → ℝ) (z : V → Bool), (∀ v : V, 0.2 ≤ w v ∧ w v ≤ 1) ∧
      ∀ v : V, p v = w v / 2 + (1 - w v) * (if z v then 1 else 0) := by
  refine ⟨fun v ↦ if p v ≤ 1 / 2 then 2 * p v else 2 * (1 - p v),
    fun v ↦ decide (1 / 2 < p v), ?_, ?_⟩
  · intro v
    obtain ⟨h1, h2⟩ := hp v
    dsimp only
    rcases le_or_gt (p v) (1 / 2) with hv | hv
    · rw [ite_eq_left hv]
      constructor <;> norm_num <;> linarith
    · rw [ite_eq_right (not_le.mpr hv)]
      constructor <;> norm_num <;> linarith
  · intro v
    obtain ⟨h1, h2⟩ := hp v
    dsimp only
    rcases le_or_gt (p v) (1 / 2) with hv | hv
    · have hz : ¬ (1 / 2 < p v) := not_lt.mpr hv
      rw [ite_eq_left hv, ite_eq_right (by simpa using hz)]
      ring
    · rw [ite_eq_right (not_le.mpr hv), ite_eq_left (by simpa using hv)]
      ring

/-! ## The mixture decomposition of the product measure -/

/-- A product of `0`--`1` factors detecting agreement with `Z` off `S`. -/
lemma prod_ite_agree (W Z S : Finset V) :
    (∏ v : V, if v ∈ S then (1 : ℝ) else if (v ∈ W ↔ v ∈ Z) then 1 else 0) =
      if W \ S = Z \ S then 1 else 0 := by
  by_cases h : W \ S = Z \ S
  · rw [ite_eq_left h]
    refine Finset.prod_eq_one fun v _ ↦ ?_
    by_cases hv : v ∈ S
    · simp [hv]
    · have hiff : v ∈ W ↔ v ∈ Z := by
        constructor
        · intro hw
          have hmem : v ∈ W \ S := Finset.mem_sdiff.mpr ⟨hw, hv⟩
          rw [h] at hmem
          exact (Finset.mem_sdiff.mp hmem).1
        · intro hz
          have hmem : v ∈ Z \ S := Finset.mem_sdiff.mpr ⟨hz, hv⟩
          rw [← h] at hmem
          exact (Finset.mem_sdiff.mp hmem).1
      simp [hv, hiff]
  · rw [ite_eq_right h]
    have hex : ∃ v : V, v ∉ S ∧ ¬ (v ∈ W ↔ v ∈ Z) := by
      by_contra hcon
      push Not at hcon
      refine h ?_
      ext x
      simp only [Finset.mem_sdiff]
      constructor
      · exact fun hx ↦ ⟨(hcon x hx.2).mp hx.1, hx.2⟩
      · exact fun hx ↦ ⟨(hcon x hx.2).mpr hx.1, hx.2⟩
    obtain ⟨v, hvS, hviff⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hvS, hviff])

/-- The weight of `W` under `p` splits as a sum over the "fair coin" coordinate set `S`. -/
lemma weight_eq_sum_mixture (p w : V → ℝ) (z : V → Bool)
    (hsplit : ∀ v : V, p v = w v / 2 + (1 - w v) * (if z v then 1 else 0))
    (W : Finset V) :
    PB.weight p W =
      ∑ S : Finset V, PB.weight w S * (1 / 2 : ℝ) ^ S.card *
        (if W \ S = (Finset.univ.filter fun v ↦ z v) \ S then 1 else 0) := by
  classical
  set Z : Finset V := Finset.univ.filter fun v ↦ z v with hZ
  set a : V → ℝ := fun v ↦ w v / 2 with ha
  set b : V → ℝ := fun v ↦ (1 - w v) * (if (v ∈ W ↔ v ∈ Z) then 1 else 0) with hb
  have hhalf : ∀ S : Finset V,
      (∏ v : V, if v ∈ S then (1 / 2 : ℝ) else 1) = (1 / 2 : ℝ) ^ S.card := by
    intro S
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  have hterm : ∀ S : Finset V,
      PB.weight w S * (1 / 2 : ℝ) ^ S.card * (if W \ S = Z \ S then 1 else 0) =
        ∏ v : V, if v ∈ S then a v else b v := by
    intro S
    rw [← hhalf S, ← prod_ite_agree W Z S, PB.weight, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    by_cases hv : v ∈ S <;> (simp [ha, hb, hv]; try ring)
  have hab : ∀ v : V, a v + b v = if v ∈ W then p v else 1 - p v := by
    intro v
    have hzmem : (v ∈ Z) ↔ z v = true := by simp [hZ]
    have hsp := hsplit v
    have hiff : (if (v ∈ W ↔ v ∈ Z) then (1 : ℝ) else 0) =
        if v ∈ W then (if z v then (1 : ℝ) else 0) else 1 - (if z v then (1 : ℝ) else 0) := by
      by_cases hvW : v ∈ W <;> by_cases hvz : z v = true <;> simp [hvW, hvz, hzmem]
    simp only [ha, hb, hiff]
    by_cases hvW : v ∈ W <;> (simp only [hvW, ite_true, ite_false]; rw [hsp]; try ring)
  calc PB.weight p W = ∏ v : V, (a v + b v) := by
        rw [PB.weight]
        exact Finset.prod_congr rfl fun v _ ↦ (hab v).symm
    _ = ∑ S ∈ (Finset.univ : Finset V).powerset, ∏ v : V, if v ∈ S then a v else b v :=
        (Erdos88.Probability.sum_prod_ite_mem (Finset.univ : Finset V) a b).symm
    _ = ∑ S : Finset V, PB.weight w S * (1 / 2 : ℝ) ^ S.card *
          (if W \ S = Z \ S then 1 else 0) := by
        rw [← Erdos88.Probability.sum_univ_eq_sum_powerset]
        exact Finset.sum_congr rfl fun S _ ↦ (hterm S).symm

/-- Reindexing the subsets of a ground set `S` as the sets agreeing with `Z` off `S`. -/
lemma sum_powerset_eq_sum_filter (Z S : Finset V) (f : Finset V → ℝ) :
    ∑ T ∈ S.powerset, f (T ∪ (Z \ S)) =
      ∑ W : Finset V, if W \ S = Z \ S then f W else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun T ↦ T ∪ (Z \ S)) (fun W ↦ W ∩ S) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powerset] at hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxS⟩
      · exact absurd (hT hx) hxS
      · exact hx
    · exact fun hx ↦ ⟨Or.inr hx, hx.2⟩
  · exact fun W _ ↦ Finset.mem_powerset.mpr Finset.inter_subset_right
  · intro T hT
    rw [Finset.mem_powerset] at hT
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hx | hx, hxS⟩
      · exact hx
      · exact absurd hxS hx.2
    · exact fun hx ↦ ⟨Or.inl hx, hT hx⟩
  · intro W hW
    have hWS : W \ S = Z \ S := (Finset.mem_filter.mp hW).2
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · have hx' : x ∈ W \ S := by rw [hWS]; exact hx
        exact (Finset.mem_sdiff.mp hx').1
    · intro hx
      by_cases hxS : x ∈ S
      · exact Or.inl ⟨hx, hxS⟩
      · refine Or.inr ?_
        have hx' : x ∈ W \ S := Finset.mem_sdiff.mpr ⟨hx, hxS⟩
        rwa [hWS] at hx'
  · exact fun T _ ↦ rfl

/-- **Mixture decomposition.**  Sampling from the product measure with parameters `p` is the
same as first sampling the set `S` of "fair coin" coordinates from the product measure with
parameters `w`, and then choosing the trace on `S` uniformly, the coordinates off `S` being
frozen to `Z`. -/
lemma expectation_eq_mixture (p w : V → ℝ) (z : V → Bool)
    (hsplit : ∀ v : V, p v = w v / 2 + (1 - w v) * (if z v then 1 else 0))
    (f : Finset V → ℝ) :
    PB.expectation p f =
      ∑ S : Finset V, PB.weight w S *
        ((1 / 2 : ℝ) ^ S.card *
          ∑ T ∈ S.powerset, f (T ∪ ((Finset.univ.filter fun v ↦ z v) \ S))) := by
  classical
  set Z : Finset V := Finset.univ.filter fun v ↦ z v with hZ
  have hinner : ∀ S : Finset V, (∑ T ∈ S.powerset, f (T ∪ (Z \ S))) =
      ∑ W : Finset V, (if W \ S = Z \ S then (1 : ℝ) else 0) * f W := by
    intro S
    rw [sum_powerset_eq_sum_filter Z S f]
    exact Finset.sum_congr rfl fun W _ ↦ by by_cases h : W \ S = Z \ S <;> simp [h]
  calc PB.expectation p f = ∑ W : Finset V, PB.weight p W * f W := rfl
    _ = ∑ W : Finset V, ∑ S : Finset V, PB.weight w S * (1 / 2 : ℝ) ^ S.card *
          (if W \ S = Z \ S then (1 : ℝ) else 0) * f W := by
        refine Finset.sum_congr rfl fun W _ ↦ ?_
        rw [weight_eq_sum_mixture p w z hsplit W, Finset.sum_mul]
    _ = ∑ S : Finset V, ∑ W : Finset V, PB.weight w S * (1 / 2 : ℝ) ^ S.card *
          (if W \ S = Z \ S then (1 : ℝ) else 0) * f W := Finset.sum_comm
    _ = ∑ S : Finset V, PB.weight w S *
          ((1 / 2 : ℝ) ^ S.card * ∑ T ∈ S.powerset, f (T ∪ (Z \ S))) := by
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        rw [hinner S, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun W _ ↦ by ring

/-! ## The conditional Erdős--Littlewood--Offord bound -/

omit [Fintype V] in
/-- Conditionally on the "fair coin" set `S` and on the frozen part `R` (disjoint from `S`),
the signed-count event is a `±1` Erdős--Littlewood--Offord event on the ground set `S`. -/
lemma card_filter_union_le (P Q S R : Finset V) (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (t : ℤ) :
    ((S.powerset).filter fun T ↦
        (((T ∪ R) ∩ P).card : ℤ) - (((T ∪ R) ∩ Q).card : ℤ) = t).card ≤
      Nat.choose ((P ∪ Q) ∩ S).card (((P ∪ Q) ∩ S).card / 2) *
        2 ^ (S.card - ((P ∪ Q) ∩ S).card) := by
  classical
  have hcard : ∀ T ∈ S.powerset, ∀ A : Finset V,
      ((T ∪ R) ∩ A).card = (T ∩ (A ∩ S)).card + (R ∩ A).card := by
    intro T hT A
    rw [Finset.mem_powerset] at hT
    have h1 : (T ∪ R) ∩ A = (T ∩ (A ∩ S)) ∪ (R ∩ A) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hA⟩
        · exact Or.inl ⟨hx, hA, hT hx⟩
        · exact Or.inr ⟨hx, hA⟩
      · rintro (⟨hx, hA, _⟩ | ⟨hx, hA⟩)
        · exact ⟨Or.inl hx, hA⟩
        · exact ⟨Or.inr hx, hA⟩
    have h2 : Disjoint (T ∩ (A ∩ S)) (R ∩ A) := by
      refine Finset.disjoint_left.mpr fun x hx hx' ↦ ?_
      exact Finset.disjoint_left.mp hRS (Finset.mem_inter.mp hx').1
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).2
    rw [h1, Finset.card_union_of_disjoint h2]
  have hfe : ((S.powerset).filter fun T ↦
        (((T ∪ R) ∩ P).card : ℤ) - (((T ∪ R) ∩ Q).card : ℤ) = t) =
      ((S.powerset).filter fun T ↦ ((T ∩ (P ∩ S)).card : ℤ) - ((T ∩ (Q ∩ S)).card : ℤ) =
        t - ((R ∩ P).card : ℤ) + ((R ∩ Q).card : ℤ)) := by
    refine Finset.filter_congr fun T hT ↦ ?_
    rw [hcard T hT P, hcard T hT Q]
    constructor <;> intro h <;> push_cast at h ⊢ <;> omega
  rw [hfe]
  have hunion : (P ∩ S) ∪ (Q ∩ S) = (P ∪ Q) ∩ S :=
    (Finset.union_inter_distrib_right P Q S).symm
  have hmain := card_filter_shift_le (P := P ∩ S) (Q := Q ∩ S) (S := S)
    (hPQ.mono Finset.inter_subset_left Finset.inter_subset_left)
    Finset.inter_subset_right Finset.inter_subset_right
    (t - ((R ∩ P).card : ℤ) + ((R ∩ Q).card : ℤ))
  rwa [hunion] at hmain

/-! ## The anticoncentration constant -/

/-- A constant `K` with `C(q, ⌊q/2⌋) ≤ K · 2 ^ q / √q` for every `q ≥ 1`. -/
noncomputable def centralBinomConst : ℝ :=
  Erdos637.exists_positive_central_binom_bound.choose

/-- The central binomial constant is positive. -/
lemma centralBinomConst_pos : 0 < centralBinomConst :=
  Erdos637.exists_positive_central_binom_bound.choose_spec.1

/-- The defining estimate of the central binomial constant. -/
lemma centralBinomConst_spec : ∀ q ≥ 1,
    (Nat.choose q (q / 2) : ℝ) ≤ centralBinomConst * ((2 : ℝ) ^ q / Real.sqrt q) :=
  Erdos637.exists_positive_central_binom_bound.choose_spec.2

omit [Fintype V] in
/-- The conditional probability that the signed count hits `t`, given the "fair coin" set `S`
and the frozen part `R`. -/
lemma inner_bound (P Q S R : Finset V) (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (hm : 1 ≤ ((P ∪ Q) ∩ S).card) (t : ℤ) :
    (1 / 2 : ℝ) ^ S.card *
        (((S.powerset).filter fun T ↦
          (((T ∪ R) ∩ P).card : ℤ) - (((T ∪ R) ∩ Q).card : ℤ) = t).card : ℝ) ≤
      centralBinomConst / Real.sqrt (((P ∪ Q) ∩ S).card) := by
  classical
  set m : ℕ := ((P ∪ Q) ∩ S).card with hmdef
  have hmS : m ≤ S.card := Finset.card_le_card Finset.inter_subset_right
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hpow : (2 : ℝ) ^ (S.card - m) * 2 ^ m = 2 ^ S.card := by
    rw [← pow_add, Nat.sub_add_cancel hmS]
  have hcast : (((S.powerset).filter fun T ↦
      (((T ∪ R) ∩ P).card : ℤ) - (((T ∪ R) ∩ Q).card : ℤ) = t).card : ℝ) ≤
      (Nat.choose m (m / 2) : ℝ) * (2 : ℝ) ^ (S.card - m) := by
    exact_mod_cast card_filter_union_le P Q S R hPQ hRS t
  have hkey : (1 / 2 : ℝ) ^ S.card * (2 : ℝ) ^ (S.card - m) = 1 / 2 ^ m := by
    have h2n : ((2 : ℝ) ^ S.card) ≠ 0 := by positivity
    have h2m' : ((2 : ℝ) ^ m) ≠ 0 := by positivity
    rw [div_pow, one_pow]
    field_simp
    linear_combination hpow
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  calc (1 / 2 : ℝ) ^ S.card * (((S.powerset).filter fun T ↦
          (((T ∪ R) ∩ P).card : ℤ) - (((T ∪ R) ∩ Q).card : ℤ) = t).card : ℝ)
      ≤ (1 / 2 : ℝ) ^ S.card * ((Nat.choose m (m / 2) : ℝ) * (2 : ℝ) ^ (S.card - m)) :=
        mul_le_mul_of_nonneg_left hcast (by positivity)
    _ = (Nat.choose m (m / 2) : ℝ) / 2 ^ m := by
        rw [show (1 / 2 : ℝ) ^ S.card * ((Nat.choose m (m / 2) : ℝ) * (2 : ℝ) ^ (S.card - m))
          = ((1 / 2 : ℝ) ^ S.card * (2 : ℝ) ^ (S.card - m)) * (Nat.choose m (m / 2) : ℝ) from
          by ring, hkey]
        ring
    _ ≤ (centralBinomConst * ((2 : ℝ) ^ m / Real.sqrt (m : ℝ))) / 2 ^ m := by
        gcongr
        exact centralBinomConst_spec m hm
    _ = centralBinomConst / Real.sqrt (m : ℝ) := by
        field_simp

omit [Fintype V] in
/-- The product of the indicators of `D` and `S` is the indicator of `D ∩ S`. -/
lemma ite_mul_ite_mem_inter (D S : Finset V) (v : V) :
    (if v ∈ D then (1 : ℝ) else 0) * (if v ∈ S then (1 : ℝ) else 0) =
      if v ∈ D ∩ S then (1 : ℝ) else 0 := by
  by_cases h1 : v ∈ D <;> by_cases h2 : v ∈ S <;> simp [h1, h2, Finset.mem_inter]

omit [Fintype V] in
/-- Multiplying a scalar by the indicator of `D`. -/
lemma ite_one_mul (D : Finset V) (v : V) (c : ℝ) :
    (if v ∈ D then (1 : ℝ) else 0) * c = if v ∈ D then c else 0 := by
  by_cases h : v ∈ D <;> simp [h]

omit [Fintype V] in
/-- Multiplying a scalar by the square of the indicator of `D`. -/
lemma ite_one_sq_mul (D : Finset V) (v : V) (c : ℝ) :
    (if v ∈ D then (1 : ℝ) else 0) ^ 2 * c = if v ∈ D then c else 0 := by
  by_cases h : v ∈ D <;> simp [h]

omit [Fintype V] [DecidableEq V] in
/-- The conditional probability on a ground set is at most one. -/
lemma inner_le_one (S : Finset V) (r : Finset V → Prop) [DecidablePred r] :
    (1 / 2 : ℝ) ^ S.card * (((S.powerset).filter r).card : ℝ) ≤ 1 := by
  have h := Finset.card_filter_le S.powerset r
  rw [Finset.card_powerset] at h
  have hR : (((S.powerset).filter r).card : ℝ) ≤ (2 : ℝ) ^ S.card := by exact_mod_cast h
  calc (1 / 2 : ℝ) ^ S.card * (((S.powerset).filter r).card : ℝ)
      ≤ (1 / 2 : ℝ) ^ S.card * (2 : ℝ) ^ S.card :=
        mul_le_mul_of_nonneg_left hR (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

/-- The anticoncentration constant of Proposition 5. -/
noncomputable def anticConst : ℝ := Real.sqrt 10 * centralBinomConst + 25

/-- The anticoncentration constant is positive. -/
lemma anticConst_pos : 0 < anticConst := by
  have h := mul_nonneg (Real.sqrt_nonneg 10) centralBinomConst_pos.le
  unfold anticConst
  linarith

/-- **Proposition 5** for `±1` coefficients, with the explicit constant `anticConst`. -/
theorem antic_bound (p : V → ℝ) (hp : ∀ v : V, 0.1 ≤ p v ∧ p v ≤ 0.9)
    (P Q : Finset V) (hPQ : Disjoint P Q) (hq : 1 ≤ (P ∪ Q).card) (t : ℤ) :
    PB.eventProbability p (fun W ↦ ((W ∩ P).card : ℤ) - ((W ∩ Q).card : ℤ) = t) ≤
      anticConst / Real.sqrt ((P ∪ Q).card) := by
  classical
  obtain ⟨w, z, hw, hsplit⟩ := exists_split p hp
  have hwU : PB.InUnit w := fun v ↦ ⟨by linarith [(hw v).1], (hw v).2⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset V, Z = Finset.univ.filter fun v ↦ z v := ⟨_, rfl⟩
  set q : ℝ := ((P ∪ Q).card : ℝ) with hqdef
  have hq1 : (1 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
  have h1s : (1 : ℝ) ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq1
  have hsqle : Real.sqrt q ≤ q := by
    nlinarith [Real.mul_self_sqrt hqpos.le, h1s, Real.sqrt_nonneg q]
  set A : V → ℝ := fun v ↦ if v ∈ P ∪ Q then (1 : ℝ) else 0 with hAdef
  set X : Finset V → ℝ := fun S ↦ ∑ v : V, A v * (if v ∈ S then (1 : ℝ) else 0) with hXdef
  have hXcard : ∀ S : Finset V, X S = (((P ∪ Q) ∩ S).card : ℝ) := by
    intro S
    have hterm : ∀ v : V, A v * (if v ∈ S then (1 : ℝ) else 0) =
        if v ∈ (P ∪ Q) ∩ S then (1 : ℝ) else 0 := fun v ↦ ite_mul_ite_mem_inter (P ∪ Q) S v
    show (∑ v : V, A v * (if v ∈ S then (1 : ℝ) else 0)) = _
    simp only [hterm]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hEX : PB.expectation w X = ∑ v : V, A v * w v := PB.expectation_linear w A
  have hEXge : 0.2 * q ≤ PB.expectation w X := by
    rw [hEX]
    have hterm : ∀ v : V, A v * w v = if v ∈ P ∪ Q then w v else 0 :=
      fun v ↦ ite_one_mul (P ∪ Q) v (w v)
    simp only [hterm]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    calc 0.2 * q = ∑ _v ∈ P ∪ Q, (0.2 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, hqdef]; ring
      _ ≤ ∑ v ∈ P ∪ Q, w v := Finset.sum_le_sum fun v _ ↦ (hw v).1
  have hVX : PB.variance w X = ∑ v : V, A v ^ 2 * (w v * (1 - w v)) :=
    PB.variance_linear hwU A
  have hVXle : PB.variance w X ≤ q / 4 := by
    rw [hVX]
    have hterm : ∀ v : V, A v ^ 2 * (w v * (1 - w v)) =
        if v ∈ P ∪ Q then w v * (1 - w v) else 0 :=
      fun v ↦ ite_one_sq_mul (P ∪ Q) v (w v * (1 - w v))
    simp only [hterm]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    calc (∑ v ∈ P ∪ Q, w v * (1 - w v)) ≤ ∑ _v ∈ P ∪ Q, (1 / 4 : ℝ) :=
          Finset.sum_le_sum fun v _ ↦ by nlinarith [sq_nonneg (w v - 1 / 2)]
      _ = q / 4 := by rw [Finset.sum_const, nsmul_eq_mul, hqdef]; ring
  have ht0 : (0 : ℝ) < 0.1 * q := by linarith
  have hcheb := PB.chebyshev_sq_bound hwU ht0 X
  have hbad : PB.eventProbability w (fun S ↦ ¬ (0.1 * q < X S)) ≤ 25 / q := by
    have hmono : PB.eventProbability w (fun S ↦ ¬ (0.1 * q < X S)) ≤
        PB.eventProbability w
          (fun S ↦ (0.1 * q) ^ 2 ≤ (X S - PB.expectation w X) ^ 2) := by
      refine PB.eventProbability_mono hwU fun S hS ↦ ?_
      have hS' : X S ≤ 0.1 * q := not_lt.mp hS
      have hprod : (0 : ℝ) ≤
          (-(X S - PB.expectation w X) - 0.1 * q) *
            (-(X S - PB.expectation w X) + 0.1 * q) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hprod]
    have hdiv : PB.variance w X / (0.1 * q) ^ 2 ≤ 25 / q := by
      rw [div_le_div_iff₀ (pow_pos ht0 2) hqpos]
      nlinarith [hVXle, hqpos]
    exact hmono.trans (hcheb.trans hdiv)
  set g : Finset V → ℝ := fun S ↦ (1 / 2 : ℝ) ^ S.card *
    (((S.powerset).filter fun T ↦
      (((T ∪ (Z \ S)) ∩ P).card : ℤ) - (((T ∪ (Z \ S)) ∩ Q).card : ℤ) = t).card : ℝ)
    with hgdef
  have hstart : PB.eventProbability p
      (fun W ↦ ((W ∩ P).card : ℤ) - ((W ∩ Q).card : ℤ) = t) = PB.expectation w g := by
    unfold PB.eventProbability
    rw [expectation_eq_mixture p w z hsplit, ← hZ]
    unfold PB.expectation
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [hgdef]
    simp
  have hgbound : ∀ S : Finset V, g S ≤
      Real.sqrt 10 * centralBinomConst / Real.sqrt q +
        (if ¬ (0.1 * q < X S) then (1 : ℝ) else 0) := by
    intro S
    by_cases hS : 0.1 * q < X S
    · rw [ite_eq_right (not_not_intro hS), add_zero]
      have hmR : (0 : ℝ) < (((P ∪ Q) ∩ S).card : ℝ) := by rw [← hXcard S]; linarith
      have hm : 1 ≤ ((P ∪ Q) ∩ S).card := by exact_mod_cast hmR
      have hin := inner_bound P Q S (Z \ S) hPQ Finset.sdiff_disjoint hm t
      have h10m : q ≤ 10 * (((P ∪ Q) ∩ S).card : ℝ) := by rw [← hXcard S]; linarith
      have hsqrt10 : Real.sqrt q ≤
          Real.sqrt 10 * Real.sqrt ((((P ∪ Q) ∩ S).card : ℝ)) := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
        exact Real.sqrt_le_sqrt h10m
      have hsm : 0 < Real.sqrt ((((P ∪ Q) ∩ S).card : ℝ)) := Real.sqrt_pos.mpr hmR
      have hfin : centralBinomConst / Real.sqrt ((((P ∪ Q) ∩ S).card : ℝ)) ≤
          Real.sqrt 10 * centralBinomConst / Real.sqrt q := by
        rw [div_le_div_iff₀ hsm hsq]
        nlinarith [mul_le_mul_of_nonneg_left hsqrt10 centralBinomConst_pos.le]
      exact (le_trans (by rw [hgdef]; exact hin) hfin)
    · rw [ite_eq_left hS]
      have h1 : g S ≤ 1 := by rw [hgdef]; exact inner_le_one S _
      have h2 : (0 : ℝ) ≤ Real.sqrt 10 * centralBinomConst / Real.sqrt q :=
        div_nonneg (mul_nonneg (Real.sqrt_nonneg 10) centralBinomConst_pos.le)
          (Real.sqrt_nonneg q)
      linarith
  calc PB.eventProbability p (fun W ↦ ((W ∩ P).card : ℤ) - ((W ∩ Q).card : ℤ) = t)
      = PB.expectation w g := hstart
    _ ≤ PB.expectation w (fun S ↦ Real.sqrt 10 * centralBinomConst / Real.sqrt q +
          (if ¬ (0.1 * q < X S) then (1 : ℝ) else 0)) := PB.expectation_mono hwU hgbound
    _ = PB.expectation w (fun _ ↦ Real.sqrt 10 * centralBinomConst / Real.sqrt q) +
          PB.expectation w (fun S ↦ if ¬ (0.1 * q < X S) then (1 : ℝ) else 0) :=
        PB.expectation_add w _ _
    _ = Real.sqrt 10 * centralBinomConst / Real.sqrt q +
          PB.eventProbability w (fun S ↦ ¬ (0.1 * q < X S)) := by
        rw [PB.expectation_const]
        rfl
    _ ≤ Real.sqrt 10 * centralBinomConst / Real.sqrt q + 25 / q := by linarith
    _ ≤ anticConst / Real.sqrt q := by
        have h25 : 25 / q ≤ 25 / Real.sqrt q :=
          div_le_div_of_nonneg_left (by norm_num) hsq hsqle
        have hsplit2 : anticConst / Real.sqrt q =
            Real.sqrt 10 * centralBinomConst / Real.sqrt q + 25 / Real.sqrt q := by
          unfold anticConst
          rw [add_div]
        rw [hsplit2]
        linarith

/-- **Proposition 5** (±1 coefficients, vertex-dependent `p ∈ [0.1, 0.9]`). -/
theorem exists_antic_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (p : V → ℝ)
        (_hp : ∀ v, 0.1 ≤ p v ∧ p v ≤ 0.9) (P Q : Finset V) (_hPQ : Disjoint P Q)
        (_hq : 1 ≤ (P ∪ Q).card) (t : ℤ),
        PB.eventProbability p
            (fun W ↦ ((W ∩ P).card : ℤ) - ((W ∩ Q).card : ℤ) = t) ≤
          C / Real.sqrt ((P ∪ Q).card) := by
  refine ⟨anticConst, anticConst_pos, ?_⟩
  intro V _ _ p hp P Q hPQ hq t
  exact antic_bound p hp P Q hPQ hq t

end JKLY
