import Mathlib

/-!
# JSP-000799 / Erdős #960 — the index sets

Pure finite combinatorics on `ℕ` modulo `M = 7m`: the index set `Idx m s = I₀ m ∪ T m s`
of size `6m + s`, its "ordinary pairs" (`ordIdx`), the absence of ordinary triangles and
the lower bound `2(3m² − 3ms)` on the number of ordered ordinary pairs.
-/

open Finset

namespace Erdos960

/-- `M = 7m`. -/
def M (m : ℕ) : ℕ := 7 * m

/-- The base index set: `0 < i < M` with `7 ∤ i`. -/
def I0 (m : ℕ) : Finset ℕ := (Ioo 0 (M m)).filter fun i => i % 7 ≠ 0

/-- The `s ≤ 5` extra indices (multiples of 7), for the size adjustment. -/
def T (m : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | 1 => {7}
  | 2 => {7, 14}
  | 3 => {7, 14, M m - 21}
  | 4 => {7, 14, M m - 21, 21}
  | _ => {7, 14, M m - 21, 21, M m - 28}

/-- The full index set, `|Idx m s| = 6m + s`. -/
def Idx (m s : ℕ) : Finset ℕ := I0 m ∪ T m s

/-- Index-level ordinary pair: distinct `i, j ∈ S` with no third `k ∈ S` such that
`M ∣ i + j + k`. -/
def ordIdx (m : ℕ) (S : Finset ℕ) (i j : ℕ) : Prop :=
  i ∈ S ∧ j ∈ S ∧ i ≠ j ∧ ∀ k ∈ S, k ≠ i → k ≠ j → (i + j + k) % M m ≠ 0

/-- `ordIdx` is decidable (needed to `Finset.filter` by it). -/
instance instDecidableOrdIdx (m : ℕ) (S : Finset ℕ) (i j : ℕ) : Decidable (ordIdx m S i j) :=
  inferInstanceAs
    (Decidable (i ∈ S ∧ j ∈ S ∧ i ≠ j ∧ ∀ k ∈ S, k ≠ i → k ≠ j → (i + j + k) % M m ≠ 0))

/-! ### Basic membership -/

private lemma M_eq (m : ℕ) : M m = 7 * m := rfl

private lemma mem_I0 {m i : ℕ} : i ∈ I0 m ↔ 0 < i ∧ i < 7 * m ∧ i % 7 ≠ 0 := by
  simp [I0, M, and_assoc]

private lemma T0 (m : ℕ) : T m 0 = ∅ := rfl
private lemma T1 (m : ℕ) : T m 1 = {7} := rfl
private lemma T2 (m : ℕ) : T m 2 = {7, 14} := rfl
private lemma T3 (m : ℕ) : T m 3 = {7, 14, 7 * m - 21} := rfl
private lemma T4 (m : ℕ) : T m 4 = {7, 14, 7 * m - 21, 21} := rfl
private lemma T5 (m : ℕ) : T m 5 = {7, 14, 7 * m - 21, 21, 7 * m - 28} := rfl

private lemma mem_T_imp {m s t : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (ht : t ∈ T m s) :
    t % 7 = 0 ∧ 0 < t ∧ t < 7 * m := by
  interval_cases s <;>
    simp only [T0, T1, T2, T3, T4, T5, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty] at ht <;>
    omega

private lemma I0_subset_Idx (m s : ℕ) : I0 m ⊆ Idx m s := Finset.subset_union_left

private lemma T_subset_Idx (m s : ℕ) : T m s ⊆ Idx m s := Finset.subset_union_right

private lemma mem_Idx {m s i : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (h : i ∈ Idx m s) :
    0 < i ∧ i < 7 * m := by
  rcases Finset.mem_union.1 h with h | h
  · have := mem_I0.1 h; exact ⟨this.1, this.2.1⟩
  · have := mem_T_imp hm hs h; exact ⟨this.2.1, this.2.2⟩

theorem Idx_subset {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) : Idx m s ⊆ Ioo 0 (M m) := by
  intro i hi
  have := mem_Idx hm hs hi
  simp only [Finset.mem_Ioo, M_eq]
  exact this

/-! ### Cardinalities -/

private lemma card_res (m a : ℕ) (ha : 0 < a) (ha7 : a < 7) :
    ((I0 m).filter fun i => i % 7 = a).card = m := by
  have himg : ((I0 m).filter fun i => i % 7 = a) = (range m).image fun j => 7 * j + a := by
    ext i
    simp only [Finset.mem_filter, mem_I0, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨i / 7, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injective _ (fun x y h => by omega), Finset.card_range]

private lemma card_I0 (m : ℕ) : (I0 m).card = 6 * m := by
  have himg : I0 m = ((range m) ×ˢ (range 6)).image fun p => 7 * p.1 + p.2 + 1 := by
    ext i
    simp only [mem_I0, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨i / 7, i % 7 - 1, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨q, r, ⟨hq, hr⟩, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range,
    Finset.card_range]
  · ring
  · rintro ⟨q, r⟩ hq ⟨q', r'⟩ hq' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hq hq'
    have h' : 7 * q + r + 1 = 7 * q' + r' + 1 := h
    simp only [Prod.mk.injEq]
    constructor <;> omega

private lemma card_T {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) : (T m s).card = s := by
  interval_cases s
  · rfl
  · rfl
  · rw [T2, Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega),
      Finset.card_singleton]
  · rw [T3, Finset.card_insert_of_notMem
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega),
      Finset.card_singleton]
  · rw [T4, Finset.card_insert_of_notMem
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega),
      Finset.card_singleton]
  · rw [T5, Finset.card_insert_of_notMem
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega),
      Finset.card_singleton]

private lemma disjoint_I0_T {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    Disjoint (I0 m) (T m s) := by
  rw [Finset.disjoint_left]
  intro x hx hxT
  have h1 := mem_I0.1 hx
  have h2 := mem_T_imp hm hs hxT
  omega

theorem card_Idx {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) : (Idx m s).card = 6 * m + s := by
  rw [Idx, Finset.card_union_of_disjoint (disjoint_I0_T hm hs), card_I0, card_T hm hs]

/-! ### The unique third index -/

/-- The unique `k` with `0 < k ≤ M` and `M ∣ i + j + k` (for `0 < i, j < M`). -/
private def k0 (m i j : ℕ) : ℕ := if i + j < 7 * m then 7 * m - i - j else 14 * m - i - j

private lemma k0_sum {m i j : ℕ} (hi : 0 < i) (hi' : i < 7 * m) (_hj : 0 < j) (hj' : j < 7 * m) :
    i + j + k0 m i j = 7 * m ∨ i + j + k0 m i j = 14 * m := by
  unfold k0; split_ifs <;> omega

private lemma k0_bounds {m i j : ℕ} (hi : 0 < i) (hi' : i < 7 * m) (hj : 0 < j) (hj' : j < 7 * m) :
    0 < k0 m i j ∧ k0 m i j ≤ 7 * m := by
  unfold k0; split_ifs <;> omega

private lemma sum_mod_eq_zero_iff {m i j k : ℕ} (hi : 0 < i) (hi' : i < 7 * m) (hj : j < 7 * m)
    (hk : k < 7 * m) : (i + j + k) % (7 * m) = 0 ↔ (i + j + k = 7 * m ∨ i + j + k = 14 * m) := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
    have hq3 : q < 3 := by
      rcases Nat.lt_or_ge q 3 with hlt | hge
      · exact hlt
      · have : 7 * m * 3 ≤ 7 * m * q := Nat.mul_le_mul (le_refl _) hge
        omega
    interval_cases q <;> omega
  · rintro (h | h)
    · rw [h, Nat.mod_self]
    · rw [h, show 14 * m = 7 * m * 2 by ring, Nat.mul_mod_right]

private lemma third_iff {m i j k : ℕ} (hi : 0 < i) (hi' : i < 7 * m) (_hj : 0 < j)
    (hj' : j < 7 * m) (hk : 0 < k) (hk' : k < 7 * m) :
    (i + j + k) % M m = 0 ↔ k = k0 m i j := by
  rw [M_eq, sum_mod_eq_zero_iff hi hi' hj' hk']
  unfold k0
  split_ifs <;> omega

theorem ordIdx_symm {m : ℕ} {S : Finset ℕ} {i j : ℕ} (h : ordIdx m S i j) : ordIdx m S j i := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h2, h1, h3.symm, fun k hk hki hkj => ?_⟩
  rw [show j + i + k = i + j + k by ring]
  exact h4 k hk hkj hki

/-- If a pair of indices is ordinary then its candidate third index is outside `Idx`
or equal to one of the two. -/
private lemma ordIdx_k0 {m s i j : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (h : ordIdx m (Idx m s) i j) :
    k0 m i j ∉ Idx m s ∨ k0 m i j = i ∨ k0 m i j = j := by
  by_cases hmem : k0 m i j ∈ Idx m s
  · by_cases hne1 : k0 m i j = i
    · exact Or.inr (Or.inl hne1)
    · by_cases hne2 : k0 m i j = j
      · exact Or.inr (Or.inr hne2)
      · exfalso
        obtain ⟨hi0, hi1⟩ := mem_Idx hm hs h.1
        obtain ⟨hj0, hj1⟩ := mem_Idx hm hs h.2.1
        obtain ⟨hk0, hk1⟩ := mem_Idx hm hs hmem
        exact h.2.2.2 _ hmem hne1 hne2 ((third_iff hi0 hi1 hj0 hj1 hk0 hk1).2 rfl)
  · exact Or.inl hmem

/-! ### No ordinary triangle -/

private lemma ordIdx_I0_res {m s i j : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (hi : i ∈ I0 m)
    (hj : j ∈ I0 m) (h : ordIdx m (Idx m s) i j) :
    (i % 7 + j % 7) % 7 = 0 ∨ (2 * (i % 7) + j % 7) % 7 = 0 ∨
      (i % 7 + 2 * (j % 7)) % 7 = 0 := by
  obtain ⟨hi0, hi1, hi7⟩ := mem_I0.1 hi
  obtain ⟨hj0, hj1, hj7⟩ := mem_I0.1 hj
  have hsum := k0_sum hi0 hi1 hj0 hj1
  have hbd := k0_bounds hi0 hi1 hj0 hj1
  rcases ordIdx_k0 hm hs h with hnot | heq | heq
  · left
    have h7 : k0 m i j % 7 = 0 := by
      by_contra hc
      exact hnot (I0_subset_Idx m s (mem_I0.2 ⟨by omega, by omega, hc⟩))
    omega
  · right; left; rw [heq] at hsum; omega
  · right; right; rw [heq] at hsum; omega

/-- `{1, 2, 4}` and `{3, 5, 6}` are the two sides: each of the three relations puts
`a` and `b` on opposite sides. -/
private lemma sides {a b : ℕ} (ha : a < 7) (ha0 : a ≠ 0) (hb : b < 7) (hb0 : b ≠ 0)
    (h : (a + b) % 7 = 0 ∨ (2 * a + b) % 7 = 0 ∨ (a + 2 * b) % 7 = 0) :
    ((a = 1 ∨ a = 2 ∨ a = 4) ↔ ¬(b = 1 ∨ b = 2 ∨ b = 4)) := by
  interval_cases a <;> interval_cases b <;> simp_all

private lemma not_ordIdx_T_I0 {m s t x : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (ht : t ∈ T m s)
    (hx : x ∈ I0 m) : ¬ ordIdx m (Idx m s) t x := by
  intro h
  obtain ⟨ht7, ht0, ht1⟩ := mem_T_imp hm hs ht
  obtain ⟨hx0, hx1, hx7⟩ := mem_I0.1 hx
  have hsum := k0_sum ht0 ht1 hx0 hx1
  have hbd := k0_bounds ht0 ht1 hx0 hx1
  have h7 : k0 m t x % 7 ≠ 0 := by omega
  have hmem : k0 m t x ∈ Idx m s :=
    I0_subset_Idx m s (mem_I0.2 ⟨by omega, by omega, h7⟩)
  exact h.2.2.2 _ hmem (by omega) (by omega)
    ((third_iff ht0 ht1 hx0 hx1 (by omega) (by omega)).2 rfl)

private lemma T_pair_false {m s x y : ℕ}
    (hz : ∃ z ∈ T m s, z ≠ x ∧ z ≠ y ∧ x + y + z = 7 * m) (h : ordIdx m (Idx m s) x y) : False := by
  obtain ⟨z, hzT, hzx, hzy, hsum⟩ := hz
  refine h.2.2.2 z (T_subset_Idx m s hzT) hzx hzy ?_
  rw [M_eq, hsum, Nat.mod_self]

/-- Every triple of distinct elements of `T m s` contains a pair whose third index lies in
`T m s` (so that pair is not ordinary). -/
private lemma T_triple_witness {m s a b c : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (ha : a ∈ T m s)
    (hb : b ∈ T m s) (hc : c ∈ T m s) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (∃ z ∈ T m s, z ≠ a ∧ z ≠ b ∧ a + b + z = 7 * m) ∨
      (∃ z ∈ T m s, z ≠ b ∧ z ≠ c ∧ b + c + z = 7 * m) ∨
      (∃ z ∈ T m s, z ≠ a ∧ z ≠ c ∧ a + c + z = 7 * m) := by
  -- write `m = n + 12`, so that no natural subtraction occurs and `omega` stays fast
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 12 := ⟨m - 12, by omega⟩
  have e1 : 7 * (n + 12) - 21 = 7 * n + 63 := by omega
  have e2 : 7 * (n + 12) - 28 = 7 * n + 56 := by omega
  interval_cases s
  · simp only [T0, Finset.notMem_empty] at ha
  · simp only [T1, Finset.mem_singleton] at ha hb
    omega
  · simp only [T2, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    omega
  · simp only [T3, e1, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    simp only [T3, e1, Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact absurd rfl hbc
        | exact absurd rfl hac
        | (refine Or.inl ⟨7, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inl ⟨14, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inl ⟨7 * n + 63, ?_, ?_, ?_, ?_⟩ <;> omega)
  · simp only [T4, e1, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    simp only [T4, e1, Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact absurd rfl hbc
        | exact absurd rfl hac
        | (refine Or.inl ⟨7, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inl ⟨14, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inl ⟨7 * n + 63, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inl ⟨21, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inr (Or.inl ⟨7, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inl ⟨14, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inl ⟨7 * n + 63, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inl ⟨21, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inr ⟨7, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inr ⟨14, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inr ⟨7 * n + 63, ?_, ?_, ?_, ?_⟩) <;> omega)
  · simp only [T5, e1, e2, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    simp only [T5, e1, e2, Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact absurd rfl hbc
        | exact absurd rfl hac
        | (refine Or.inl ⟨7, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inl ⟨14, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inl ⟨7 * n + 63, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inl ⟨21, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inl ⟨7 * n + 56, ?_, ?_, ?_, ?_⟩ <;> omega)
        | (refine Or.inr (Or.inl ⟨7, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inl ⟨14, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inl ⟨7 * n + 63, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inl ⟨21, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inl ⟨7 * n + 56, ?_, ?_, ?_, ?_⟩) <;> omega)
        | (refine Or.inr (Or.inr ⟨7, ?_, ?_, ?_, ?_⟩) <;> omega)

private lemma T_no_triangle {m s a b c : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (ha : a ∈ T m s)
    (hb : b ∈ T m s) (hc : c ∈ T m s) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : ordIdx m (Idx m s) a b) (h2 : ordIdx m (Idx m s) b c) (h3 : ordIdx m (Idx m s) a c) :
    False := by
  rcases T_triple_witness hm hs ha hb hc hab hbc hac with h | h | h
  · exact T_pair_false h h1
  · exact T_pair_false h h2
  · exact T_pair_false h h3

/-- No three pairwise ordinary indices. -/
theorem no_ordinary_triangle {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) {i j k : ℕ}
    (hij : ordIdx m (Idx m s) i j) (hjk : ordIdx m (Idx m s) j k)
    (hik : ordIdx m (Idx m s) i k) : False := by
  have hi := Finset.mem_union.1 hij.1
  have hj := Finset.mem_union.1 hij.2.1
  have hk := Finset.mem_union.1 hjk.2.1
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hk with hk | hk
  · obtain ⟨-, -, hi7⟩ := mem_I0.1 hi
    obtain ⟨-, -, hj7⟩ := mem_I0.1 hj
    obtain ⟨-, -, hk7⟩ := mem_I0.1 hk
    have e1 := sides (a := i % 7) (b := j % 7) (by omega) hi7 (by omega) hj7
      (ordIdx_I0_res hm hs hi hj hij)
    have e2 := sides (a := j % 7) (b := k % 7) (by omega) hj7 (by omega) hk7
      (ordIdx_I0_res hm hs hj hk hjk)
    have e3 := sides (a := i % 7) (b := k % 7) (by omega) hi7 (by omega) hk7
      (ordIdx_I0_res hm hs hi hk hik)
    tauto
  · exact not_ordIdx_T_I0 hm hs hk hj (ordIdx_symm hjk)
  · exact not_ordIdx_T_I0 hm hs hj hi (ordIdx_symm hij)
  · exact not_ordIdx_T_I0 hm hs hj hi (ordIdx_symm hij)
  · exact not_ordIdx_T_I0 hm hs hi hj hij
  · exact not_ordIdx_T_I0 hm hs hi hj hij
  · exact not_ordIdx_T_I0 hm hs hi hk hik
  · exact T_no_triangle hm hs hi hj hk hij.2.2.1 hjk.2.2.1 hik.2.2.1 hij hjk hik

/-! ### Counting ordinary pairs -/

/-- The elements of `I0 m` with residue `a` mod `7`. -/
private def C (m a : ℕ) : Finset ℕ := (I0 m).filter fun i => i % 7 = a

private lemma mem_C {m a i : ℕ} : i ∈ C m a ↔ i ∈ I0 m ∧ i % 7 = a := Finset.mem_filter

private lemma card_C (m a : ℕ) (ha : 0 < a) (ha7 : a < 7) : (C m a).card = m := card_res m a ha ha7

/-- If a pair of `I0`-indices with opposite residues is not ordinary, its third index is one
of the extra indices. -/
private lemma k0_mem_T_of_not_ord {m s x y : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (hx : x ∈ I0 m)
    (hy : y ∈ I0 m) (hxy : x ≠ y) (hres : (x % 7 + y % 7) % 7 = 0)
    (hnot : ¬ ordIdx m (Idx m s) x y) : k0 m x y ∈ T m s := by
  obtain ⟨hx0, hx1, hx7⟩ := mem_I0.1 hx
  obtain ⟨hy0, hy1, hy7⟩ := mem_I0.1 hy
  have hsum := k0_sum hx0 hx1 hy0 hy1
  have hbd := k0_bounds hx0 hx1 hy0 hy1
  have h7 : k0 m x y % 7 = 0 := by omega
  by_contra hcT
  refine hnot ⟨I0_subset_Idx m s hx, I0_subset_Idx m s hy, hxy, fun k hk hkx hky hzero => ?_⟩
  obtain ⟨hk0, hk1⟩ := mem_Idx hm hs hk
  have hkk : k = k0 m x y := (third_iff hx0 hx1 hy0 hy1 hk0 hk1).1 hzero
  subst hkk
  rcases Finset.mem_union.1 hk with hkI | hkT
  · exact (mem_I0.1 hkI).2.2 h7
  · exact hcT hkT

private lemma card_bad {m s a : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (ha : 0 < a) (ha7 : a < 7) :
    (((C m a) ×ˢ (C m (7 - a))).filter fun p : ℕ × ℕ => ¬ ordIdx m (Idx m s) p.1 p.2).card
      ≤ m * s := by
  have hcard : ((C m a) ×ˢ (T m s)).card = m * s := by
    rw [Finset.card_product, card_C m a ha ha7, card_T hm hs]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun p => (p.1, k0 m p.1 p.2)) ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hx, hy⟩, hnot⟩ := hp
    obtain ⟨hxI, hxa⟩ := mem_C.1 hx
    obtain ⟨hyI, hyb⟩ := mem_C.1 hy
    have hxy : x ≠ y := by
      intro h
      rw [h] at hxa
      omega
    exact Finset.mem_coe.2
      (Finset.mem_product.2 ⟨hx, k0_mem_T_of_not_ord hm hs hxI hyI hxy (by omega) hnot⟩)
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
    obtain ⟨hxI, -⟩ := mem_C.1 hp.1.1
    obtain ⟨hyI, -⟩ := mem_C.1 hp.1.2
    obtain ⟨hxI', -⟩ := mem_C.1 hp'.1.1
    obtain ⟨hyI', -⟩ := mem_C.1 hp'.1.2
    obtain ⟨hx0, hx1, -⟩ := mem_I0.1 hxI
    obtain ⟨hy0, hy1, -⟩ := mem_I0.1 hyI
    obtain ⟨hx0', hx1', -⟩ := mem_I0.1 hxI'
    obtain ⟨hy0', hy1', -⟩ := mem_I0.1 hyI'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    subst h1
    have hs1 := k0_sum hx0 hx1 hy0 hy1
    have hs2 := k0_sum hx0 hx1 hy0' hy1'
    rw [h2] at hs1
    have hyy : y = y' := by omega
    rw [hyy]

private lemma card_good {m s a : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (ha : 0 < a) (ha7 : a < 7) :
    m * m - m * s ≤ (((C m a) ×ˢ (C m (7 - a))).filter
      fun p : ℕ × ℕ => ordIdx m (Idx m s) p.1 p.2).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (C m a) ×ˢ (C m (7 - a)))
    (p := fun p : ℕ × ℕ => ordIdx m (Idx m s) p.1 p.2)
  have hP : ((C m a) ×ˢ (C m (7 - a))).card = m * m := by
    rw [Finset.card_product, card_C m a ha ha7, card_C m (7 - a) (by omega) (by omega)]
  have hbad := card_bad hm hs ha ha7
  omega

/-- At least `2(3m² − 3ms)` ORDERED ordinary pairs. -/
theorem card_ordIdx_pairs {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    2 * (3 * m ^ 2 - 3 * m * s) ≤
      (((Idx m s) ×ˢ (Idx m s)).filter fun p : ℕ × ℕ => ordIdx m (Idx m s) p.1 p.2).card := by
  -- the ordered ordinary pairs of `I0`-indices with opposite residues, split according to the
  -- residue of the first coordinate
  set W := ((Idx m s) ×ˢ (Idx m s)).filter fun p : ℕ × ℕ =>
    ordIdx m (Idx m s) p.1 p.2 ∧ p.1 % 7 ≠ 0 ∧ (p.1 % 7 + p.2 % 7) % 7 = 0 with hWdef
  have hfib : W.card = ∑ a ∈ Icc 1 6, (W.filter fun p : ℕ × ℕ => p.1 % 7 = a).card := by
    refine Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1 % 7) (t := Icc 1 6) ?_
    intro p hp
    simp only [Finset.mem_coe, hWdef, Finset.mem_filter] at hp
    simp only [Finset.mem_coe, Finset.mem_Icc]
    omega
  have hsub : ∀ a ∈ Icc 1 6, m * m - m * s ≤ (W.filter fun p : ℕ × ℕ => p.1 % 7 = a).card := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    have hga : m * m - m * s ≤ (((C m a) ×ˢ (C m (7 - a))).filter
        fun p : ℕ × ℕ => ordIdx m (Idx m s) p.1 p.2).card := card_good hm hs (by omega) (by omega)
    refine le_trans hga (Finset.card_le_card ?_)
    rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hx, hy⟩, hord⟩ := hp
    obtain ⟨hxI, hxa⟩ := mem_C.1 hx
    obtain ⟨hyI, hyb⟩ := mem_C.1 hy
    simp only [hWdef, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨I0_subset_Idx m s hxI, I0_subset_Idx m s hyI⟩, hord, by omega, by omega⟩, by omega⟩
  have hsum : 6 * (m * m - m * s) ≤
      ∑ a ∈ Icc 1 6, (W.filter fun p : ℕ × ℕ => p.1 % 7 = a).card := by
    have h1 := Finset.sum_le_sum hsub
    have hcard6 : (Icc 1 6 : Finset ℕ).card = 6 := by simp
    rwa [Finset.sum_const, hcard6, smul_eq_mul] at h1
  have hle : W.card ≤
      (((Idx m s) ×ˢ (Idx m s)).filter fun p : ℕ × ℕ => ordIdx m (Idx m s) p.1 p.2).card := by
    refine Finset.card_le_card ?_
    intro p hp
    rw [hWdef, Finset.mem_filter] at hp
    exact Finset.mem_filter.2 ⟨hp.1, hp.2.1⟩
  have harith : 2 * (3 * m ^ 2 - 3 * m * s) ≤ 6 * (m * m - m * s) := by
    have hle' : m * s ≤ m * m := Nat.mul_le_mul_left m (by omega)
    rw [show m ^ 2 = m * m from sq m, show 3 * m * s = 3 * (m * s) from by ring]
    omega
  omega

end Erdos960

