import Jsp539.Defs

/-!
# JSP-000539 / Erdős #664 — the random sample space

The construction behind the negative answer to Erdős #664 (Alon, Remark 1.9.1) samples a random
subset of every line of an affine plane.  This file develops the counting machinery over abstract
finite index types `L` (later: the lines) and `X` (later: the coordinate `ZMod p`):

* `Ω L X M = L → X → Fin M` is the (uniform, counting) sample space: for every line `ℓ` and every
  coordinate `x` an independent value in `Fin M`; the coordinate is *kept* iff the value is nonzero
  (so with "probability" `1 - 1/M`).
* `sum_prod_eq_prod_sum`, `sum_prod_eq_prod_sum'`: independence, i.e. the factorisation of a sum of
  products over the sample space into a product of sums (`Fintype.prod_sum`).
* `card_tail_le`: the θ-trick tail bound — few coordinates of a set `S ⊆ L × X` are kept only for a
  `2 ^ #S * M ^ K / M ^ #S`-fraction of the sample space.
* `card_hitsAll_le`, `card_hitsAll_le'`: the block bound — the probability that a given transversal
  candidate meets every line's kept set is `∏ ℓ (1 - M ^ (-#(T ℓ)))`.

All counts are kept as natural numbers cast into `ℝ`.

Note on `M`: the "kept" predicate is `ω ℓ x ≠ 0`, so the number `M` of values carries a `NeZero M`
instance (needed for `(0 : Fin M)`); the redundant hypotheses `1 ≤ M` are kept in the statements of
the two main bounds.  Downstream the parameter is `M ≥ 5`, so this is no restriction.
-/

open Finset

namespace Erdos664

variable {L X : Type*} [Fintype L] [Fintype X] [DecidableEq L] [DecidableEq X] (M : ℕ)

/-- Sample space: for every line `ℓ` and coordinate `x` an independent uniform value in `Fin M`;
the coordinate is "kept" iff the value is nonzero (probability `1 - 1/M`). -/
abbrev Ω (L X : Type*) (M : ℕ) := L → X → Fin M

theorem card_Ω : Fintype.card (Ω L X M) = M ^ (Fintype.card L * Fintype.card X) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-! ### An auxiliary product lemma -/

/-- A product of an indicator-style factor `a` is a power of `a`. -/
theorem prod_ite_one_eq_pow {ι R : Type*} [CommMonoid R] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (a : R) : ∏ i ∈ s, (if p i then a else 1) = a ^ #(s.filter p) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-! ### Independence: factorisation of sums of products -/

/-- Independence of the lines: a sum over the sample space of a product over the lines factors as a
product over the lines of sums over single-line samples. -/
theorem sum_prod_eq_prod_sum (w : L → (X → Fin M) → ℝ) :
    ∑ ω : Ω L X M, ∏ ℓ, w ℓ (ω ℓ) = ∏ ℓ, ∑ g : X → Fin M, w ℓ g :=
  (Fintype.prod_sum w).symm

/-- Independence of the coordinates of a single line. -/
theorem sum_prod_eq_prod_sum' (v : X → Fin M → ℝ) :
    ∑ g : X → Fin M, ∏ x, v x (g x) = ∏ x, ∑ u : Fin M, v x u :=
  (Fintype.prod_sum v).symm

/-! ### The tail bound -/

variable [NeZero M]

/-- **Tail bound** (θ-trick with `θ = 1/M`).  The number of samples keeping at most `K` of the
coordinates in `S` is at most a `2 ^ #S * M ^ K / M ^ #S` fraction of the sample space. -/
theorem card_tail_le (hM : 1 ≤ M) (S : Finset (L × X)) (K : ℕ) :
    (#(univ.filter fun ω : Ω L X M => #(S.filter fun c => ω c.1 c.2 ≠ 0) ≤ K) : ℝ)
      ≤ (Fintype.card (Ω L X M) : ℝ) * 2 ^ #S * (M : ℝ) ^ K / (M : ℝ) ^ #S := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  -- the θ-trick weights
  set w : L → X → Fin M → ℝ := fun ℓ x u => if (ℓ, x) ∈ S ∧ u ≠ 0 then 1 / M else 1 with hw
  have hwnonneg : ∀ ℓ x u, 0 ≤ w ℓ x u := by
    intro ℓ x u
    rw [hw]
    dsimp only
    split_ifs <;> positivity
  -- the product of the weights along a sample is `θ ^ (number of kept coordinates of S)`
  have key : ∀ ω : Ω L X M, ∏ ℓ, ∏ x, w ℓ x (ω ℓ x)
      = (1 / (M : ℝ)) ^ #(S.filter fun c => ω c.1 c.2 ≠ 0) := by
    intro ω
    have hfil : (univ.filter fun c : L × X => c ∈ S ∧ ω c.1 c.2 ≠ 0)
        = S.filter fun c => ω c.1 c.2 ≠ 0 := by
      ext c; simp
    calc ∏ ℓ, ∏ x, w ℓ x (ω ℓ x)
        = ∏ c : L × X, (if c ∈ S ∧ ω c.1 c.2 ≠ 0 then 1 / (M : ℝ) else 1) := by
          rw [← Fintype.prod_prod_type']
      _ = (1 / (M : ℝ)) ^ #(univ.filter fun c : L × X => c ∈ S ∧ ω c.1 c.2 ≠ 0) :=
          prod_ite_one_eq_pow _ _ _
      _ = (1 / (M : ℝ)) ^ #(S.filter fun c => ω c.1 c.2 ≠ 0) := by rw [hfil]
  -- the indicator of the tail event is dominated by `M ^ K` times the weights
  have ind : ∀ ω : Ω L X M,
      (if #(S.filter fun c => ω c.1 c.2 ≠ 0) ≤ K then (1 : ℝ) else 0)
        ≤ (M : ℝ) ^ K * ∏ ℓ, ∏ x, w ℓ x (ω ℓ x) := by
    intro ω
    rw [key ω]
    split_ifs with h
    · have h1 : (M : ℝ) ^ #(S.filter fun c => ω c.1 c.2 ≠ 0) ≤ (M : ℝ) ^ K :=
        pow_le_pow_right₀ hM1 h
      rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      simpa using h1
    · positivity
  -- one factor of the inner sum
  have hcard1 : #(univ.filter fun u : Fin M => u ≠ 0) = M - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have inner_le : ∀ (ℓ : L) (x : X), ∑ u : Fin M, w ℓ x u ≤ if (ℓ, x) ∈ S then 2 else (M : ℝ) := by
    intro ℓ x
    by_cases hc : (ℓ, x) ∈ S
    · rw [hw]
      simp only [hc, true_and, ite_true]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard1]
      have hcard2 : #(univ.filter fun u : Fin M => ¬ u ≠ 0) = 1 := by
        simp only [ne_eq, not_not]
        rw [Finset.filter_eq' univ (0 : Fin M)]
        simp
      rw [hcard2, nsmul_eq_mul, nsmul_eq_mul]
      have h2 : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast Nat.sub_le M 1
      have h3 : ((M - 1 : ℕ) : ℝ) * (1 / (M : ℝ)) ≤ 1 := by
        rw [mul_one_div, div_le_one hM0]; exact h2
      linarith
    · rw [hw]
      simp [hc]
  -- put everything together
  have hSN : #S ≤ Fintype.card (L × X) := (Finset.card_le_univ S).trans_eq Finset.card_univ
  have hcompl : (univ.filter fun c : L × X => ¬ c ∈ S) = Sᶜ := by ext c; simp
  have hpow : (M : ℝ) ^ (Fintype.card (L × X) - #S)
      = (M : ℝ) ^ Fintype.card (L × X) / (M : ℝ) ^ #S := by
    rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel hSN]
  calc (#(univ.filter fun ω : Ω L X M => #(S.filter fun c => ω c.1 c.2 ≠ 0) ≤ K) : ℝ)
      = ∑ ω : Ω L X M, (if #(S.filter fun c => ω c.1 c.2 ≠ 0) ≤ K then (1 : ℝ) else 0) :=
        (Finset.sum_boole _ _).symm
    _ ≤ ∑ ω : Ω L X M, (M : ℝ) ^ K * ∏ ℓ, ∏ x, w ℓ x (ω ℓ x) :=
        Finset.sum_le_sum fun ω _ => ind ω
    _ = (M : ℝ) ^ K * ∑ ω : Ω L X M, ∏ ℓ, ∏ x, w ℓ x (ω ℓ x) := by rw [← Finset.mul_sum]
    _ = (M : ℝ) ^ K * ∏ ℓ, ∑ g : X → Fin M, ∏ x, w ℓ x (g x) := by
        rw [sum_prod_eq_prod_sum M fun ℓ g => ∏ x, w ℓ x (g x)]
    _ = (M : ℝ) ^ K * ∏ c : L × X, ∑ u : Fin M, w c.1 c.2 u := by
        rw [Fintype.prod_prod_type' fun ℓ x => ∑ u : Fin M, w ℓ x u]
        exact congrArg _ (Finset.prod_congr rfl fun ℓ _ => sum_prod_eq_prod_sum' M (w ℓ))
    _ ≤ (M : ℝ) ^ K * ∏ c : L × X, (if c ∈ S then 2 else (M : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod ?_ ?_) (by positivity)
        · exact fun c _ => Finset.sum_nonneg fun u _ => hwnonneg _ _ _
        · exact fun c _ => inner_le c.1 c.2
    _ = (M : ℝ) ^ K * (2 ^ #S * (M : ℝ) ^ (Fintype.card (L × X) - #S)) := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_univ_mem,
          hcompl, Finset.card_compl]
    _ = (Fintype.card (Ω L X M) : ℝ) * 2 ^ #S * (M : ℝ) ^ K / (M : ℝ) ^ #S := by
        rw [hpow, card_Ω, Fintype.card_prod]
        push_cast
        ring

/-! ### The block bound -/

/-- Counting the samples of a single line that vanish on a given set of coordinates. -/
theorem card_all_zero (T : Finset X) :
    #(univ.filter fun g : X → Fin M => ∀ x ∈ T, g x = 0) = M ^ (Fintype.card X - #T) := by
  calc #(univ.filter fun g : X → Fin M => ∀ x ∈ T, g x = 0)
      = ∑ g : X → Fin M, (if ∀ x ∈ T, g x = 0 then 1 else 0) := Finset.card_filter _ _
    _ = ∑ g : X → Fin M, ∏ x : X, (if x ∈ T → g x = 0 then 1 else 0) :=
        Finset.sum_congr rfl fun g _ => (Fintype.prod_boole).symm
    _ = ∏ x : X, ∑ u : Fin M, (if x ∈ T → u = 0 then 1 else 0) :=
        (Fintype.prod_sum fun x u => if x ∈ T → u = 0 then 1 else 0).symm
    _ = ∏ x : X, (if x ∈ T then 1 else M) := by
        refine Finset.prod_congr rfl fun x _ => ?_
        by_cases hx : x ∈ T <;> simp [hx]
    _ = M ^ (Fintype.card X - #T) := by
        have hcompl : (univ.filter fun x : X => ¬ x ∈ T) = Tᶜ := by ext x; simp
        rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
          hcompl, Finset.card_compl]

/-- The probability that a single line's sample is nonzero somewhere on `T`. -/
theorem sum_exists_ne_zero (T : Finset X) :
    ∑ g : X → Fin M, (if ∃ x ∈ T, g x ≠ 0 then (1 : ℝ) else 0)
      = (M : ℝ) ^ Fintype.card X - (M : ℝ) ^ (Fintype.card X - #T) := by
  have hneg : (univ.filter fun g : X → Fin M => ¬ ∃ x ∈ T, g x ≠ 0)
      = univ.filter fun g : X → Fin M => ∀ x ∈ T, g x = 0 := by
    ext g; simp
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (X → Fin M))) (p := fun g => ∃ x ∈ T, g x ≠ 0)
  rw [hneg, card_all_zero, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hsum
  rw [Finset.sum_boole]
  have : ((#(univ.filter fun g : X → Fin M => ∃ x ∈ T, g x ≠ 0) : ℕ) : ℝ)
      + ((M ^ (Fintype.card X - #T) : ℕ) : ℝ) = ((M ^ Fintype.card X : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsum
  push_cast at this
  linarith

/-- **Block bound.**  The number of samples whose kept sets are all met by a fixed candidate
transversal (encoded by `T ℓ`, the coordinates of the candidate on the line `ℓ`). -/
theorem card_hitsAll_le (_hM : 1 ≤ M) (T : L → Finset X) :
    (#(univ.filter fun ω : Ω L X M => ∀ ℓ, ∃ x ∈ T ℓ, ω ℓ x ≠ 0) : ℝ)
      ≤ ∏ ℓ, ((M : ℝ) ^ Fintype.card X - (M : ℝ) ^ (Fintype.card X - #(T ℓ))) := by
  refine le_of_eq ?_
  calc (#(univ.filter fun ω : Ω L X M => ∀ ℓ, ∃ x ∈ T ℓ, ω ℓ x ≠ 0) : ℝ)
      = ∑ ω : Ω L X M, (if ∀ ℓ, ∃ x ∈ T ℓ, ω ℓ x ≠ 0 then (1 : ℝ) else 0) :=
        (Finset.sum_boole _ _).symm
    _ = ∑ ω : Ω L X M, ∏ ℓ, (if ∃ x ∈ T ℓ, ω ℓ x ≠ 0 then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun ω _ => (Fintype.prod_boole).symm
    _ = ∏ ℓ, ∑ g : X → Fin M, (if ∃ x ∈ T ℓ, g x ≠ 0 then (1 : ℝ) else 0) :=
        sum_prod_eq_prod_sum M fun ℓ g => if ∃ x ∈ T ℓ, g x ≠ 0 then (1 : ℝ) else 0
    _ = ∏ ℓ, ((M : ℝ) ^ Fintype.card X - (M : ℝ) ^ (Fintype.card X - #(T ℓ))) :=
        Finset.prod_congr rfl fun ℓ _ => sum_exists_ne_zero M (T ℓ)

/-- **Block bound, corollary form.**  If the candidate transversal is light (at most `t`
coordinates) on every line of `Light`, the samples all of whose kept sets are met form at most a
`(1 - M ^ (-t)) ^ #Light` fraction of the sample space. -/
theorem card_hitsAll_le' (hM : 1 ≤ M) (T : L → Finset X) (t : ℕ) (Light : Finset L)
    (hL : ∀ ℓ ∈ Light, #(T ℓ) ≤ t) :
    (#(univ.filter fun ω : Ω L X M => ∀ ℓ, ∃ x ∈ T ℓ, ω ℓ x ≠ 0) : ℝ)
      ≤ (Fintype.card (Ω L X M) : ℝ) * (1 - (1 / (M : ℝ)) ^ t) ^ #Light := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  have hcX : ∀ ℓ, #(T ℓ) ≤ Fintype.card X := fun ℓ =>
    (Finset.card_le_univ _).trans_eq Finset.card_univ
  have hnonneg : ∀ ℓ : L,
      (0 : ℝ) ≤ (M : ℝ) ^ Fintype.card X - (M : ℝ) ^ (Fintype.card X - #(T ℓ)) := by
    intro ℓ
    have := pow_le_pow_right₀ (a := (M : ℝ)) hM1 (Nat.sub_le (Fintype.card X) #(T ℓ))
    linarith
  have key : ∀ ℓ : L, (M : ℝ) ^ Fintype.card X - (M : ℝ) ^ (Fintype.card X - #(T ℓ))
      ≤ (M : ℝ) ^ Fintype.card X * (if ℓ ∈ Light then 1 - (1 / (M : ℝ)) ^ t else 1) := by
    intro ℓ
    by_cases h : ℓ ∈ Light
    · simp only [h, ite_true]
      rw [mul_sub, mul_one]
      have e1 : (M : ℝ) ^ (Fintype.card X - #(T ℓ)) * (M : ℝ) ^ #(T ℓ)
          = (M : ℝ) ^ Fintype.card X := by
        rw [← pow_add, Nat.sub_add_cancel (hcX ℓ)]
      have e2 : (M : ℝ) ^ #(T ℓ) ≤ (M : ℝ) ^ t := pow_le_pow_right₀ hM1 (hL ℓ h)
      have e3 : (M : ℝ) ^ Fintype.card X * (1 / (M : ℝ)) ^ t
          ≤ (M : ℝ) ^ (Fintype.card X - #(T ℓ)) := by
        rw [← e1, one_div, inv_pow, mul_assoc]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        exact e2
      linarith
    · simp only [h, ite_false, mul_one]
      have : (0 : ℝ) ≤ (M : ℝ) ^ (Fintype.card X - #(T ℓ)) := by positivity
      linarith
  refine (card_hitsAll_le M hM T).trans ?_
  calc ∏ ℓ, ((M : ℝ) ^ Fintype.card X - (M : ℝ) ^ (Fintype.card X - #(T ℓ)))
      ≤ ∏ ℓ, ((M : ℝ) ^ Fintype.card X * (if ℓ ∈ Light then 1 - (1 / (M : ℝ)) ^ t else 1)) :=
        Finset.prod_le_prod (fun ℓ _ => hnonneg ℓ) (fun ℓ _ => key ℓ)
    _ = ((M : ℝ) ^ Fintype.card X) ^ Fintype.card L * (1 - (1 / (M : ℝ)) ^ t) ^ #Light := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, prod_ite_one_eq_pow,
          Finset.filter_univ_mem, Finset.card_univ]
    _ = (Fintype.card (Ω L X M) : ℝ) * (1 - (1 / (M : ℝ)) ^ t) ^ #Light := by
        rw [card_Ω]
        push_cast
        rw [← pow_mul, Nat.mul_comm]

end Erdos664
