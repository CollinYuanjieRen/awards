import CameronErdos.CE.Basic
import CameronErdos.CE.GFunction

/-!
# `Thm_CE_IntervalCount`: `T(n) = O(2^{n/2})`

This file assembles the two halves of the Cameron–Erdős argument as recorded in Green's
note *An argument of Cameron and Erdős* (`ref/green-ce-notes.pdf`):

* the exact count `intervalSumFreeCount_eq'` of `CameronErdos/CE/Basic.lean`,
  `T(n) = Σ_{S ⊆ B} 2^{|U ∖ (S+S)|}` with `B = ceBlock n` and `U = ceUpper n`, and
* the bound `gCE_bound` of `CameronErdos/CE/GFunction.lean`, `g(k) ≤ 50 − 50 ρ^k ≤ 50`.

Writing `m = topThird n` and `b = ceBlockLen n = n + 1 − 2m = |B|`, the translation
`S ↦ S − m` identifies `B` with `range b` and carries `(S + S) ∩ U` onto
`(S' + S') ∩ range b` — the crucial point being `n + 1 ≤ 3m` (`three_mul_topThird_ge`),
which is exactly what makes the shifted copy of `U` contain `range b`.  Hence

  `T(n) = 2^{|U|} · ceBlockSum b`,  `ceBlockSum b = Σ_{S ⊆ range b} 2^{−|(S+S) ∩ range b|}`,

and `ceBlockSum (2k) = 2^k g(k) ≤ 50 · 2^k`, while `ceBlockSum (b+1) ≤ 2 · ceBlockSum b`
handles the odd case, giving `ceBlockSum b ≤ 100 · 2^{⌊b/2⌋}` for **every** `b` (small `n`
included — no case split on `n` is needed).  Since `2|U| + b ≤ n + 1` this yields

  `T(n) ≤ 100 · 2^{|U| + ⌊b/2⌋}`,  `T(n)^2 ≤ 20000 · 2^n`,  `T(n) ≤ 200 · 2^{n/2}`.
-/

namespace CameronErdos

open Finset
open scoped Pointwise

/-! ## The shifted block -/

/-- `b = |B|`, the length of the initial block `B = Icc m (n - m)`. -/
def ceBlockLen (n : ℕ) : ℕ := n + 1 - 2 * topThird n

private lemma addRight_inj (m : ℕ) : Function.Injective (· + m) := by
  intro a b h
  simp only at h
  omega

/-- Translating a set by `m` translates its sumset by `2m`. -/
private lemma image_add_image (S : Finset ℕ) (m : ℕ) :
    (S.image (· + m)) + (S.image (· + m)) = (S + S).image (· + 2 * m) := by
  ext a
  simp only [Finset.mem_add, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨x', hx', rfl⟩, y, ⟨y', hy', rfl⟩, rfl⟩
    exact ⟨x' + y', ⟨x', hx', y', hy', rfl⟩, by ring⟩
  · rintro ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨x + m, ⟨x, hx, rfl⟩, y + m, ⟨y, hy, rfl⟩, by ring⟩

/-- The initial block is the translate by `m` of `range b`. -/
lemma ceBlock_eq_image (n : ℕ) :
    ceBlock n = (Finset.range (ceBlockLen n)).image (· + topThird n) := by
  have h1 := three_mul_topThird_ge n
  have h2 := topThird_pos n
  ext a
  simp only [mem_ceBlock, Finset.mem_image, Finset.mem_range, ceBlockLen]
  constructor
  · rintro ⟨ha1, ha2⟩
    exact ⟨a - topThird n, by omega, by omega⟩
  · rintro ⟨x, hx, rfl⟩
    omega

/-- **The bookkeeping of Green's note.**  For `S ⊆ ℕ` put `T = S + m`.  Then
`(T + T) ∩ U` is the translate by `2m` of `(S + S) ∩ range b`: the upper end because
`|U| + b = ` the right endpoint `n`, and the lower end because `n + 1 ≤ 3m`. -/
lemma inter_ceUpper_image (n : ℕ) (S : Finset ℕ) :
    ceUpper n ∩ ((S.image (· + topThird n)) + (S.image (· + topThird n)))
      = ((S + S) ∩ Finset.range (ceBlockLen n)).image (· + 2 * topThird n) := by
  have h1 := three_mul_topThird_ge n
  have h2 := topThird_pos n
  rw [image_add_image]
  ext a
  simp only [Finset.mem_inter, Finset.mem_image, mem_ceUpper, Finset.mem_range, ceBlockLen]
  constructor
  · rintro ⟨⟨hu1, hu2⟩, z, hz, rfl⟩
    exact ⟨z, ⟨hz, by omega⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hzr⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, z, hz, rfl⟩

/-- Reindexing a sum over the powerset of a translate. -/
private lemma sum_powerset_image_add (b m : ℕ) (F : Finset ℕ → ℝ) :
    ∑ S ∈ ((Finset.range b).image (· + m)).powerset, F S
      = ∑ S ∈ (Finset.range b).powerset, F (S.image (· + m)) := by
  rw [Finset.powerset_image, Finset.sum_image]
  intro x _ y _ h
  exact Finset.image_injective (addRight_inj m) h

/-! ## The normalised block sum -/

/-- `ceBlockSum b = Σ_{S ⊆ [0, b-1]} 2^{-|(S+S) ∩ [0, b-1]|}`; for `b = 2k` this is
`2^k g(k)`. -/
noncomputable def ceBlockSum (b : ℕ) : ℝ :=
  ∑ S ∈ (Finset.range b).powerset, (1/2 : ℝ) ^ ((S + S) ∩ Finset.range b).card

lemma ceBlockSum_two_mul (k : ℕ) : ceBlockSum (2 * k) = 2 ^ k * gCE k := by
  have h : ∑ S ∈ (Finset.range (2 * k)).powerset, wCE k S = ceBlockSum (2 * k) := rfl
  rw [gCE, h, ← mul_assoc, ← mul_pow]
  norm_num

lemma gCE_zero : gCE 0 = 1 := by
  simp [gCE, wCE]

lemma gCE_le_fifty (k : ℕ) : gCE k ≤ 50 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [gCE_zero]; norm_num
  · have h := gCE_bound hk
    have hp : (0:ℝ) ≤ (18769/20000 : ℝ) ^ k := by positivity
    linarith

/-- Adding one point to the ground set at most doubles the block sum: this is how the
odd case (`n` even) is reduced to the even case in Green's note. -/
lemma ceBlockSum_succ_le (b : ℕ) : ceBlockSum (b + 1) ≤ 2 * ceBlockSum b := by
  have hns : b ∉ Finset.range b := Finset.notMem_range_self
  rw [ceBlockSum, Finset.range_add_one, Finset.sum_powerset_insert hns, ceBlockSum, two_mul]
  refine add_le_add (Finset.sum_le_sum fun S _ => ?_) (Finset.sum_le_sum fun S _ => ?_)
  · refine pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.card_le_card ?_)
    exact Finset.inter_subset_inter (le_refl _) (Finset.subset_insert _ _)
  · refine pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.card_le_card ?_)
    exact Finset.inter_subset_inter
      (Finset.add_subset_add (Finset.subset_insert _ _) (Finset.subset_insert _ _))
      (Finset.subset_insert _ _)

/-- `ceBlockSum b ≤ 100 · 2^{⌊b/2⌋}` for every `b`, both parities and `b ≤ 1` included. -/
lemma ceBlockSum_le (b : ℕ) : ceBlockSum b ≤ 100 * 2 ^ (b / 2) := by
  rcases Nat.even_or_odd b with he | ho
  · obtain ⟨k, rfl⟩ := he
    have hd : (k + k) / 2 = k := by omega
    have hk : k + k = 2 * k := by ring
    rw [hd, hk, ceBlockSum_two_mul]
    have h1 := gCE_le_fifty k
    have h2 : (0:ℝ) < 2 ^ k := by positivity
    nlinarith
  · obtain ⟨k, rfl⟩ := ho
    have hd : (2 * k + 1) / 2 = k := by omega
    rw [hd]
    have h1 := ceBlockSum_succ_le (2 * k)
    rw [ceBlockSum_two_mul] at h1
    have h2 := gCE_le_fifty k
    have h3 : (0:ℝ) < 2 ^ k := by positivity
    nlinarith

/-! ## The interval count -/

/-- **Green's identity.**  `T(n) = 2^{|U|} · ceBlockSum b`. -/
theorem intervalSumFreeCount_eq_mul (n : ℕ) :
    (intervalSumFreeCount n : ℝ)
      = 2 ^ (ceUpper n).card * ceBlockSum (ceBlockLen n) := by
  rw [intervalSumFreeCount_eq']
  push_cast
  rw [ceBlock_eq_image n,
    sum_powerset_image_add (ceBlockLen n) (topThird n)
      (fun S => (2:ℝ) ^ (ceUpper n \ (S + S)).card),
    ceBlockSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  set T := S.image (· + topThird n) with hT
  have hcard : (ceUpper n ∩ (T + T)).card
      = ((S + S) ∩ Finset.range (ceBlockLen n)).card := by
    rw [hT, inter_ceUpper_image n S, Finset.card_image_of_injective _ (addRight_inj _)]
  have hsum : (ceUpper n ∩ (T + T)).card + (ceUpper n \ (T + T)).card = (ceUpper n).card :=
    Finset.card_inter_add_card_sdiff _ _
  rw [← hcard, ← hsum, pow_add, one_div, inv_pow]
  have hne : ((2:ℝ) ^ (ceUpper n ∩ (T + T)).card) ≠ 0 := by positivity
  field_simp

/-- `2 |U| + b ≤ n + 1`. -/
lemma two_mul_exponent_le (n : ℕ) :
    2 * ((ceUpper n).card + ceBlockLen n / 2) ≤ n + 1 := by
  have h1 := three_mul_topThird_ge n
  have h2 := topThird_le n
  have h3 : (ceUpper n).card = n + 1 - (n - topThird n + 1) := by
    simp [ceUpper, Nat.card_Icc]
  rw [h3, ceBlockLen]
  omega

/-- The explicit form of `Thm_CE_IntervalCount`: `T(n) ≤ 100 · 2^{|U| + ⌊b/2⌋}`. -/
theorem intervalSumFreeCount_le_pow (n : ℕ) :
    intervalSumFreeCount n ≤ 100 * 2 ^ ((ceUpper n).card + ceBlockLen n / 2) := by
  have key : (intervalSumFreeCount n : ℝ)
      ≤ 100 * 2 ^ ((ceUpper n).card + ceBlockLen n / 2) := by
    rw [intervalSumFreeCount_eq_mul n, pow_add]
    have hpos : (0:ℝ) ≤ 2 ^ (ceUpper n).card := by positivity
    calc (2:ℝ) ^ (ceUpper n).card * ceBlockSum (ceBlockLen n)
        ≤ 2 ^ (ceUpper n).card * (100 * 2 ^ (ceBlockLen n / 2)) :=
          mul_le_mul_of_nonneg_left (ceBlockSum_le _) hpos
      _ = 100 * (2 ^ (ceUpper n).card * 2 ^ (ceBlockLen n / 2)) := by ring
  exact_mod_cast key

/-- **`Thm_CE_IntervalCount`, squared ℕ form.**  `T(n)^2 ≤ 20000 · 2^n`. -/
theorem intervalSumFreeCount_sq_le_explicit (n : ℕ) :
    intervalSumFreeCount n ^ 2 ≤ 20000 * 2 ^ n := by
  have h := intervalSumFreeCount_le_pow n
  have he := two_mul_exponent_le n
  set e := (ceUpper n).card + ceBlockLen n / 2 with hedef
  calc intervalSumFreeCount n ^ 2 ≤ (100 * 2 ^ e) ^ 2 := Nat.pow_le_pow_left h 2
    _ = 10000 * 2 ^ (e * 2) := by rw [mul_pow, ← pow_mul]; norm_num
    _ ≤ 10000 * 2 ^ (n + 1) := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 20000 * 2 ^ n := by rw [pow_succ]; ring

/-- **`Thm_CE_IntervalCount`.**  `T(n) = O(2^{n/2})`, with the explicit constant `200`. -/
theorem intervalSumFreeCount_le_explicit (n : ℕ) :
    (intervalSumFreeCount n : ℝ) ≤ 200 * 2 ^ ((n : ℝ) / 2) := by
  have h := intervalSumFreeCount_le_pow n
  have he := two_mul_exponent_le n
  set e := (ceUpper n).card + ceBlockLen n / 2 with hedef
  have h1 : (intervalSumFreeCount n : ℝ) ≤ 100 * 2 ^ e := by exact_mod_cast h
  have hexp : ((e : ℕ) : ℝ) ≤ (n : ℝ) / 2 + 1 / 2 := by
    have h2 : (2 * e : ℕ) ≤ n + 1 := by omega
    have h3 : ((2 * e : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.mpr h2
    push_cast at h3
    linarith
  have h2 : (2:ℝ) ^ e ≤ 2 ^ ((n : ℝ) / 2) * 2 := by
    have hhalf : (2:ℝ) ^ ((1:ℝ)/2) ≤ 2 := by
      calc (2:ℝ) ^ ((1:ℝ)/2) ≤ (2:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hpos : (0:ℝ) ≤ (2:ℝ) ^ ((n : ℝ) / 2) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    calc (2:ℝ) ^ e = (2:ℝ) ^ ((e : ℕ) : ℝ) := (Real.rpow_natCast 2 e).symm
      _ ≤ (2:ℝ) ^ ((n : ℝ) / 2 + 1 / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = (2:ℝ) ^ ((n : ℝ) / 2) * (2:ℝ) ^ ((1:ℝ)/2) := Real.rpow_add (by norm_num) _ _
      _ ≤ (2:ℝ) ^ ((n : ℝ) / 2) * 2 := mul_le_mul_of_nonneg_left hhalf hpos
  calc (intervalSumFreeCount n : ℝ) ≤ 100 * 2 ^ e := h1
    _ ≤ 100 * ((2:ℝ) ^ ((n : ℝ) / 2) * 2) := by linarith
    _ = 200 * 2 ^ ((n : ℝ) / 2) := by ring

/-- **`Thm_CE_IntervalCount`, existential real form.** -/
theorem intervalSumFreeCount_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (intervalSumFreeCount n : ℝ) ≤ C * 2 ^ ((n : ℝ) / 2) :=
  ⟨200, by norm_num, intervalSumFreeCount_le_explicit⟩

/-- **`Thm_CE_IntervalCount`, existential squared ℕ form.** -/
theorem intervalSumFreeCount_sq_le :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, intervalSumFreeCount n ^ 2 ≤ C * 2 ^ n :=
  ⟨20000, by norm_num, intervalSumFreeCount_sq_le_explicit⟩

/-! ## Axiom audit -/

#print axioms ceBlock_eq_image
#print axioms inter_ceUpper_image
#print axioms ceBlockSum_two_mul
#print axioms gCE_zero
#print axioms gCE_le_fifty
#print axioms ceBlockSum_succ_le
#print axioms ceBlockSum_le
#print axioms intervalSumFreeCount_eq_mul
#print axioms two_mul_exponent_le
#print axioms intervalSumFreeCount_le_pow
#print axioms intervalSumFreeCount_sq_le_explicit
#print axioms intervalSumFreeCount_le_explicit
#print axioms intervalSumFreeCount_le
#print axioms intervalSumFreeCount_sq_le

end CameronErdos
