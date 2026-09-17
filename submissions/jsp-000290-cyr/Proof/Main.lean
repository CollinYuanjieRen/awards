import Mathlib

/-!
# Erdős problem #348: van Doorn's theorem (strong completeness)

Let `a : ℕ → ℕ` be a nondecreasing sequence of positive integers, thought of as a multiset
of positive integers listed in increasing order.  A set `T` of *allowed indices* is
`Complete` if every natural number is the sum of `a i` over some finite set of allowed
indices.  The sequence is `RobustlyComplete` for `m` when removing any `m` indices keeps
completeness.

The main theorem (W. van Doorn) says that if `a` is robustly complete for some `m ≥ 2`,
then there is an *infinite* set of indices whose removal still leaves the sequence complete.
Consequently, for every `n` there is an `n`-element set of indices that can be removed while
keeping completeness, so no pair `(m, n)` with `2 ≤ m < n` answers the question on the
Erdős problems page (in the strong sense of completeness).

Not claimed here: the question under the weak notion of completeness (finitely many exceptions),
including the page's open case `(m, n) = (2, 3)`, and the positive examples `(0, 1)` (powers of
two) and `(1, 2)` (Fibonacci numbers).
-/

namespace Erdos348

/-- Every natural number is a sum of `a i` over a finite set of allowed indices `F ⊆ T`. -/
def Complete (a : ℕ → ℕ) (T : Set ℕ) : Prop :=
  ∀ x : ℕ, ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ T ∧ ∑ i ∈ F, a i = x

/-- `a` stays complete after removing any `m` indices. -/
def RobustlyComplete (a : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = m → Complete a (↑S : Set ℕ)ᶜ

/-- Sum of the allowed terms with index `< k`.  The filter uses classical decidability. -/
noncomputable def prefixSum (a : ℕ → ℕ) (T : Set ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ @Finset.filter ℕ (fun i => i ∈ T) (Classical.decPred _) (Finset.range k), a i

/-- Completeness only improves when the set of allowed indices grows. -/
theorem complete_mono {a : ℕ → ℕ} {T T' : Set ℕ} (h : T ⊆ T') (hT : Complete a T) :
    Complete a T' := by
  intro x
  obtain ⟨F, hFT, hsum⟩ := hT x
  exact ⟨F, hFT.trans h, hsum⟩

/-! ### Basic properties of `prefixSum` -/

/-- `prefixSum` can be computed with any `Finset` whose members are exactly the allowed
indices below `k`. -/
theorem prefixSum_eq_sum (a : ℕ → ℕ) (T : Set ℕ) (k : ℕ) {F : Finset ℕ}
    (hF : ∀ i : ℕ, i ∈ F ↔ i < k ∧ i ∈ T) : prefixSum a T k = ∑ i ∈ F, a i := by
  unfold prefixSum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, hF]

/-- The empty prefix sum vanishes. -/
theorem prefixSum_zero (a : ℕ → ℕ) (T : Set ℕ) : prefixSum a T 0 = 0 := by
  have h : prefixSum a T 0 = ∑ i ∈ (∅ : Finset ℕ), a i := by
    refine prefixSum_eq_sum a T 0 ?_
    intro i
    constructor
    · intro hi; simp at hi
    · rintro ⟨hi, -⟩; omega
  simpa using h

/-- Extending the prefix by an allowed index adds its term. -/
theorem prefixSum_succ_of_mem (a : ℕ → ℕ) {T : Set ℕ} {k : ℕ} (hk : k ∈ T) :
    prefixSum a T (k + 1) = prefixSum a T k + a k := by
  classical
  have h1 : prefixSum a T k = ∑ i ∈ Finset.filter (fun i => i ∈ T) (Finset.range k), a i :=
    prefixSum_eq_sum a T k (by intro i; simp only [Finset.mem_filter, Finset.mem_range])
  have h2 : prefixSum a T (k + 1)
      = ∑ i ∈ insert k (Finset.filter (fun i => i ∈ T) (Finset.range k)), a i := by
    refine prefixSum_eq_sum a T (k + 1) ?_
    intro i
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (rfl | ⟨hi, hi'⟩)
      · exact ⟨by omega, hk⟩
      · exact ⟨by omega, hi'⟩
    · rintro ⟨hi, hi'⟩
      rcases Nat.lt_or_ge i k with h | h
      · exact Or.inr ⟨h, hi'⟩
      · exact Or.inl (by omega)
  have h3 : k ∉ Finset.filter (fun i => i ∈ T) (Finset.range k) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    rintro ⟨h, -⟩
    omega
  rw [h1, h2, Finset.sum_insert h3]
  omega

/-- Extending the prefix by a forbidden index changes nothing. -/
theorem prefixSum_succ_of_notMem (a : ℕ → ℕ) {T : Set ℕ} {k : ℕ} (hk : k ∉ T) :
    prefixSum a T (k + 1) = prefixSum a T k := by
  classical
  have h1 : prefixSum a T k = ∑ i ∈ Finset.filter (fun i => i ∈ T) (Finset.range k), a i :=
    prefixSum_eq_sum a T k (by intro i; simp only [Finset.mem_filter, Finset.mem_range])
  have h2 : prefixSum a T (k + 1)
      = ∑ i ∈ Finset.filter (fun i => i ∈ T) (Finset.range k), a i := by
    refine prefixSum_eq_sum a T (k + 1) ?_
    intro i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hi'⟩; exact ⟨by omega, hi'⟩
    · rintro ⟨hi, hi'⟩
      refine ⟨?_, hi'⟩
      rcases Nat.lt_or_ge i k with h | h
      · exact h
      · exact absurd (by rwa [show i = k by omega] at hi') hk
  rw [h1, h2]

/-- Prefix sums are monotone in the cut-off. -/
theorem prefixSum_mono (a : ℕ → ℕ) (T : Set ℕ) {k l : ℕ} (h : k ≤ l) :
    prefixSum a T k ≤ prefixSum a T l := by
  classical
  have h1 : prefixSum a T k = ∑ i ∈ Finset.filter (fun i => i ∈ T) (Finset.range k), a i :=
    prefixSum_eq_sum a T k (by intro i; simp only [Finset.mem_filter, Finset.mem_range])
  have h2 : prefixSum a T l = ∑ i ∈ Finset.filter (fun i => i ∈ T) (Finset.range l), a i :=
    prefixSum_eq_sum a T l (by intro i; simp only [Finset.mem_filter, Finset.mem_range])
  rw [h1, h2]
  refine Finset.sum_le_sum_of_subset ?_
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨by omega, hi.2⟩

/-- The allowed and the removed terms below `k` add up to the full prefix sum. -/
theorem prefixSum_add_prefixSum_compl (a : ℕ → ℕ) (T : Set ℕ) (k : ℕ) :
    prefixSum a T k + prefixSum a Tᶜ k = ∑ i ∈ Finset.range k, a i := by
  classical
  have h1 : prefixSum a T k = ∑ i ∈ Finset.filter (fun i => i ∈ T) (Finset.range k), a i :=
    prefixSum_eq_sum a T k (by intro i; simp only [Finset.mem_filter, Finset.mem_range])
  have h2 : prefixSum a Tᶜ k
      = ∑ i ∈ Finset.filter (fun i => ¬ (i ∈ T)) (Finset.range k), a i :=
    prefixSum_eq_sum a Tᶜ k
      (by intro i; simp only [Finset.mem_filter, Finset.mem_range, Set.mem_compl_iff])
  rw [h1, h2]
  exact Finset.sum_filter_add_sum_filter_not (Finset.range k) (fun i => i ∈ T) a

/-! ### Lemma A: the growth condition is sufficient for completeness -/

/-- Under the growth condition, every `x` bounded by the prefix sum at `k` is a sum of
distinct allowed terms with indices `< k`. -/
theorem exists_subset_sum_eq_of_le_prefixSum (a : ℕ → ℕ) (T : Set ℕ)
    (hgrow : ∀ k ∈ T, a k ≤ 1 + prefixSum a T k) :
    ∀ k : ℕ, ∀ x : ℕ, x ≤ prefixSum a T k →
      ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ T ∧ (∀ i ∈ F, i < k) ∧ ∑ i ∈ F, a i = x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [prefixSum_zero] at hx
    refine ⟨∅, by simp, by simp, ?_⟩
    simp only [Finset.sum_empty]
    omega
  | succ k ih =>
    intro x hx
    by_cases hk : k ∈ T
    · rw [prefixSum_succ_of_mem a hk] at hx
      by_cases hx' : x ≤ prefixSum a T k
      · obtain ⟨F, h1, h2, h3⟩ := ih x hx'
        exact ⟨F, h1, fun i hi => by have := h2 i hi; omega, h3⟩
      · have hgk := hgrow k hk
        have hak : a k ≤ x := by omega
        have hy : x - a k ≤ prefixSum a T k := by omega
        obtain ⟨F, h1, h2, h3⟩ := ih (x - a k) hy
        have hkF : k ∉ F := by
          intro hmem
          have := h2 k hmem
          omega
        refine ⟨insert k F, ?_, ?_, ?_⟩
        · intro i hi
          simp only [Finset.coe_insert, Set.mem_insert_iff] at hi
          rcases hi with rfl | hi
          · exact hk
          · exact h1 hi
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · omega
          · have := h2 i hi; omega
        · rw [Finset.sum_insert hkF, h3]
          omega
    · rw [prefixSum_succ_of_notMem a hk] at hx
      obtain ⟨F, h1, h2, h3⟩ := ih x hx
      exact ⟨F, h1, fun i hi => by have := h2 i hi; omega, h3⟩

/-- For an infinite set of allowed indices with positive terms, the prefix sums are
unbounded. -/
theorem exists_le_prefixSum (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ a i) {T : Set ℕ} (hT : T.Infinite)
    (n : ℕ) : ∃ k, n ≤ prefixSum a T k := by
  induction n with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨j, hjT, hjk⟩ := hT.exists_notMem_finset (Finset.range k)
    have hkj : k ≤ j := by
      by_contra hc
      exact hjk (Finset.mem_range.mpr (by omega))
    have h1 : prefixSum a T k ≤ prefixSum a T j := prefixSum_mono a T hkj
    have h2 : prefixSum a T (j + 1) = prefixSum a T j + a j := prefixSum_succ_of_mem a hjT
    have h3 := hpos j
    exact ⟨j + 1, by omega⟩

/-- **Lemma A.** An infinite set of allowed indices whose terms satisfy the growth condition
`a k ≤ 1 + prefixSum a T k` is complete. -/
theorem complete_of_growth (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ a i) {T : Set ℕ} (hT : T.Infinite)
    (hgrow : ∀ k ∈ T, a k ≤ 1 + prefixSum a T k) : Complete a T := by
  intro x
  obtain ⟨k, hk⟩ := exists_le_prefixSum a hpos hT x
  obtain ⟨F, h1, -, h3⟩ := exists_subset_sum_eq_of_le_prefixSum a T hgrow k x hk
  exact ⟨F, h1, h3⟩

/-! ### Lemma B: the growth condition is necessary for robust completeness -/

/-- **Lemma B.** If removing any `m` indices keeps the sequence complete, then
`a (k + m) ≤ 1 + ∑_{i < k} a i` for every `k`. -/
theorem robust_growth (a : ℕ → ℕ) (ha : Monotone a) {m : ℕ} (h : RobustlyComplete a m)
    (k : ℕ) : a (k + m) ≤ 1 + ∑ i ∈ Finset.range k, a i := by
  by_contra hc
  have hc' : 1 + ∑ i ∈ Finset.range k, a i < a (k + m) := by omega
  have hcard : (Finset.Ico k (k + m)).card = m := by
    rw [Nat.card_Ico]
    omega
  obtain ⟨F, hFsub, hFsum⟩ := h _ hcard (a (k + m) - 1)
  have hFlt : ∀ i ∈ F, i < k := by
    intro i hi
    by_contra hik
    have hiS : i ∉ Finset.Ico k (k + m) := fun hmem =>
      hFsub (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hmem)
    simp only [Finset.mem_Ico, not_and, not_lt] at hiS
    have hge : k + m ≤ i := hiS (by omega)
    have h1 : a (k + m) ≤ a i := ha hge
    have h2 : a i ≤ ∑ j ∈ F, a j := Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
    omega
  have hsub : F ⊆ Finset.range k := fun i hi => Finset.mem_range.mpr (hFlt i hi)
  have hle : ∑ i ∈ F, a i ≤ ∑ i ∈ Finset.range k, a i := Finset.sum_le_sum_of_subset hsub
  omega

/-! ### The key estimate -/

/-- Splitting off the last two terms of a prefix sum. -/
theorem sum_range_eq_add_two (a : ℕ → ℕ) {k : ℕ} (hk : 2 ≤ k) :
    ∑ i ∈ Finset.range k, a i
      = (∑ i ∈ Finset.range (k - 2), a i) + a (k - 2) + a (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h1 : j + 2 - 2 = j := by omega
  have h2 : j + 2 - 1 = j + 1 := by omega
  rw [h1, h2, Finset.sum_range_succ, Finset.sum_range_succ]

/-- **Key estimate.**  If the terms removed below `k` sum to less than `a (k-2) + a (k-1)`,
then the growth condition holds at `k` for the surviving indices. -/
theorem key_estimate (a : ℕ → ℕ) (ha : Monotone a) {m : ℕ} (hm : 2 ≤ m)
    (hrob : RobustlyComplete a m) (R : Set ℕ) {k : ℕ} (hk : 2 ≤ k)
    (hsmall : prefixSum a R k < a (k - 2) + a (k - 1)) :
    a k ≤ 1 + prefixSum a Rᶜ k := by
  have hsplit := prefixSum_add_prefixSum_compl a R k
  have hrange := sum_range_eq_add_two a hk
  have hB := robust_growth a ha hrob (k - 2)
  have hmono : a k ≤ a (k - 2 + m) := ha (by omega)
  omega

/-! ### The greedy removal in the unbounded case -/

/-- Candidate indices for the greedy step after the state `p = (last index, running sum)`. -/
def greedyCand (a : ℕ → ℕ) (p : ℕ × ℕ) : Set ℕ := {i : ℕ | p.1 + 2 ≤ i ∧ p.2 < a (i - 1)}

/-- One greedy step: take the least candidate index and add its term to the running sum. -/
noncomputable def greedyStep (a : ℕ → ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (sInf (greedyCand a p), p.2 + a (sInf (greedyCand a p)))

/-- The greedy sequence of pairs `(index, running sum)`, started at `(0, a 0)`. -/
noncomputable def greedyPair (a : ℕ → ℕ) (j : ℕ) : ℕ × ℕ :=
  Nat.rec ((0, a 0) : ℕ × ℕ) (fun _ p => greedyStep a p) j

/-- The `j`-th greedily removed index. -/
noncomputable def gIdx (a : ℕ → ℕ) (j : ℕ) : ℕ := (greedyPair a j).1

/-- The sum of the first `j + 1` greedily removed terms. -/
noncomputable def gSum (a : ℕ → ℕ) (j : ℕ) : ℕ := (greedyPair a j).2

/-- The greedy sequence starts at index `0`. -/
theorem gIdx_zero (a : ℕ → ℕ) : gIdx a 0 = 0 := rfl

/-- The greedy running sum starts at `a 0`. -/
theorem gSum_zero (a : ℕ → ℕ) : gSum a 0 = a 0 := rfl

/-- The greedy running sum accumulates the removed terms. -/
theorem gSum_succ (a : ℕ → ℕ) (j : ℕ) : gSum a (j + 1) = gSum a j + a (gIdx a (j + 1)) := rfl

/-- Under unboundedness there is always a candidate for the next greedy step. -/
theorem greedyCand_nonempty (a : ℕ → ℕ) (ha : Monotone a) (hub : ∀ M : ℕ, ∃ i, M < a i)
    (p : ℕ × ℕ) : (greedyCand a p).Nonempty := by
  obtain ⟨i₀, hi₀⟩ := hub p.2
  refine ⟨max (i₀ + 1) (p.1 + 2), ?_⟩
  have h1 : i₀ + 1 ≤ max (i₀ + 1) (p.1 + 2) := le_max_left _ _
  have h2 : p.1 + 2 ≤ max (i₀ + 1) (p.1 + 2) := le_max_right _ _
  have hmem : p.1 + 2 ≤ max (i₀ + 1) (p.1 + 2) ∧ p.2 < a (max (i₀ + 1) (p.1 + 2) - 1) :=
    ⟨h2, lt_of_lt_of_le hi₀ (ha (by omega))⟩
  exact hmem

/-- The defining properties of the greedy step: the indices jump by at least two, and the
running sum stays below the term just before the next removed index. -/
theorem gIdx_succ_spec (a : ℕ → ℕ) (ha : Monotone a) (hub : ∀ M : ℕ, ∃ i, M < a i) (j : ℕ) :
    gIdx a j + 2 ≤ gIdx a (j + 1) ∧ gSum a j < a (gIdx a (j + 1) - 1) :=
  Nat.sInf_mem (greedyCand_nonempty a ha hub (greedyPair a j))

/-- The greedy running sum is the sum of the removed terms so far. -/
theorem gSum_eq_sum (a : ℕ → ℕ) (j : ℕ) :
    gSum a j = ∑ t ∈ Finset.range (j + 1), a (gIdx a t) := by
  induction j with
  | zero => rw [gSum_zero, Finset.sum_range_one, gIdx_zero]
  | succ j ih =>
    rw [Finset.sum_range_succ (fun t => a (gIdx a t)) (j + 1), ← ih, gSum_succ]

/-- **Unbounded case.**  If `a` is unbounded and robustly complete for some `m ≥ 2`, the
greedily chosen infinite index set can be removed while keeping completeness. -/
theorem exists_infinite_removal_of_unbounded (a : ℕ → ℕ) (ha : Monotone a)
    (hpos : ∀ i, 1 ≤ a i) {m : ℕ} (hm : 2 ≤ m) (hrob : RobustlyComplete a m)
    (hub : ∀ M : ℕ, ∃ i, M < a i) : ∃ R : Set ℕ, R.Infinite ∧ Complete a Rᶜ := by
  have hstep : ∀ j, gIdx a j + 2 ≤ gIdx a (j + 1) := fun j => (gIdx_succ_spec a ha hub j).1
  have hsum : ∀ j, gSum a j < a (gIdx a (j + 1) - 1) := fun j => (gIdx_succ_spec a ha hub j).2
  have hsm : StrictMono (gIdx a) :=
    strictMono_nat_of_lt_succ fun j => by have := hstep j; omega
  refine ⟨Set.range (gIdx a), Set.infinite_range_of_injective hsm.injective, ?_⟩
  have hinj : Function.Injective (fun j => gIdx a j + 1) := by
    intro j₁ j₂ h
    have h' : gIdx a j₁ + 1 = gIdx a j₂ + 1 := h
    exact hsm.injective (by omega)
  have hcompl : ((Set.range (gIdx a))ᶜ : Set ℕ).Infinite := by
    refine Set.infinite_of_injective_forall_mem hinj ?_
    intro j hmem
    obtain ⟨t, ht⟩ := hmem
    have ht' : gIdx a t = gIdx a j + 1 := ht
    have h1 : gIdx a j < gIdx a t := by omega
    have h2 : j < t := hsm.lt_iff_lt.mp h1
    have h3 : gIdx a (j + 1) ≤ gIdx a t := hsm.monotone (by omega)
    have h4 := hstep j
    omega
  refine complete_of_growth a hpos hcompl ?_
  intro k hk
  have hk0 : (0 : ℕ) ∈ Set.range (gIdx a) := ⟨0, gIdx_zero a⟩
  have hkne : k ≠ 0 := by
    rintro rfl
    exact hk hk0
  by_cases hk1 : k = 1
  · subst hk1
    have hz : prefixSum a (Set.range (gIdx a))ᶜ 1 = 0 := by
      have h : prefixSum a (Set.range (gIdx a))ᶜ 1 = ∑ i ∈ (∅ : Finset ℕ), a i := by
        refine prefixSum_eq_sum a _ 1 ?_
        intro i
        constructor
        · intro hi; simp at hi
        · rintro ⟨hi1, hi2⟩
          have hi0 : i = 0 := by omega
          subst hi0
          exact absurd hk0 hi2
      simpa using h
    have hB := robust_growth a ha hrob 0
    have h0 : (∑ i ∈ Finset.range 0, a i) = 0 := by simp
    have h1 : a 1 ≤ a (0 + m) := ha (by omega)
    omega
  · have hk2 : 2 ≤ k := by omega
    refine key_estimate a ha hm hrob (Set.range (gIdx a)) hk2 ?_
    have hex : ∃ j, k ≤ gIdx a (j + 1) := ⟨k, le_trans (Nat.le_succ k) hsm.le_apply⟩
    obtain ⟨j, hjspec, hjlt⟩ : ∃ j, k ≤ gIdx a (j + 1) ∧ gIdx a j < k := by
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · rw [h, gIdx_zero]; omega
      · obtain ⟨j', hj'⟩ : ∃ j', Nat.find hex = j' + 1 := ⟨Nat.find hex - 1, by omega⟩
        have hmin := Nat.find_min hex (m := j') (by omega)
        rw [hj']
        omega
    have hbig : ∀ t, j + 1 ≤ t → k ≤ gIdx a t := fun t ht =>
      le_trans hjspec (hsm.monotone ht)
    have hfilter : prefixSum a (Set.range (gIdx a)) k
        = ∑ t ∈ Finset.range (j + 1), a (gIdx a t) := by
      have h1 : prefixSum a (Set.range (gIdx a)) k
          = ∑ i ∈ (Finset.range (j + 1)).image (gIdx a), a i := by
        refine prefixSum_eq_sum a _ k ?_
        intro i
        constructor
        · intro hi
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
          have ht' : t ≤ j := by
            have := Finset.mem_range.mp ht
            omega
          exact ⟨lt_of_le_of_lt (hsm.monotone ht') hjlt, ⟨t, rfl⟩⟩
        · rintro ⟨hik, t, rfl⟩
          refine Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ?_, rfl⟩
          by_contra hc
          have h5 := hbig t (by omega)
          omega
      rw [h1, Finset.sum_image (fun x _ y _ h => hsm.injective h)]
    have hRsum : prefixSum a (Set.range (gIdx a)) k = gSum a j := by
      rw [hfilter, ← gSum_eq_sum]
    rw [hRsum]
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      rw [gSum_zero]
      have h1 : a 0 ≤ a (k - 2) := ha (by omega)
      have h2 : 1 ≤ a (k - 1) := hpos _
      omega
    · obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      subst hj'
      have h1 : gSum a (j' + 1) = gSum a j' + a (gIdx a (j' + 1)) := gSum_succ a j'
      have h2 : gSum a j' < a (gIdx a (j' + 1) - 1) := hsum j'
      have h3 : gIdx a j' + 2 ≤ gIdx a (j' + 1) := hstep j'
      have h5 : a (gIdx a (j' + 1) - 1) ≤ a (k - 2) := ha (by omega)
      have h6 : a (gIdx a (j' + 1)) ≤ a (k - 1) := ha (by omega)
      omega

/-! ### The bounded case -/

/-- **Bounded case.**  If `a` is bounded and robustly complete for some `m ≥ 2`, then the
arithmetic progression `N, N+2, N+4, …` of indices (with `N` where `a` becomes constant)
can be removed while keeping completeness. -/
theorem exists_infinite_removal_of_bounded (a : ℕ → ℕ) (ha : Monotone a)
    (hpos : ∀ i, 1 ≤ a i) {m : ℕ} (hm : 2 ≤ m) (hrob : RobustlyComplete a m)
    {M : ℕ} (hM : ∀ i, a i ≤ M) : ∃ R : Set ℕ, R.Infinite ∧ Complete a Rᶜ := by
  have hbdd : BddAbove (Set.range a) := ⟨M, by rintro x ⟨i, rfl⟩; exact hM i⟩
  have hne : (Set.range a).Nonempty := ⟨a 0, ⟨0, rfl⟩⟩
  obtain ⟨N, hN⟩ : ∃ N, a N = sSup (Set.range a) := Nat.sSup_mem hne hbdd
  have hconst : ∀ i, N ≤ i → a i = a N := by
    intro i hi
    have h1 : a N ≤ a i := ha hi
    have h2 : a i ≤ sSup (Set.range a) := le_csSup hbdd ⟨i, rfl⟩
    omega
  refine ⟨Set.range (fun t : ℕ => N + 2 * t), ?_, ?_⟩
  · refine Set.infinite_range_of_injective ?_
    intro x y h
    have h' : N + 2 * x = N + 2 * y := h
    omega
  · have hpre : ∀ k : ℕ, k ≤ N →
        prefixSum a (Set.range (fun t : ℕ => N + 2 * t))ᶜ k = ∑ i ∈ Finset.range k, a i := by
      intro k hk
      refine prefixSum_eq_sum a _ k ?_
      intro i
      simp only [Finset.mem_range]
      constructor
      · intro hi
        refine ⟨hi, ?_⟩
        intro hmem
        obtain ⟨t, ht⟩ := hmem
        have ht' : N + 2 * t = i := ht
        omega
      · exact fun h => h.1
    have hcompl : ((Set.range (fun t : ℕ => N + 2 * t))ᶜ : Set ℕ).Infinite := by
      refine Set.infinite_of_injective_forall_mem (f := fun t : ℕ => N + 2 * t + 1) ?_ ?_
      · intro x y h
        have h' : N + 2 * x + 1 = N + 2 * y + 1 := h
        omega
      · intro t hmem
        obtain ⟨s, hs⟩ := hmem
        have hs' : N + 2 * s = N + 2 * t + 1 := hs
        omega
    refine complete_of_growth a hpos hcompl ?_
    intro k hk
    by_cases hkN : k < N
    · have h1 := hpre k (by omega)
      have h2 := robust_growth a ha hrob k
      have h3 : a k ≤ a (k + m) := ha (by omega)
      omega
    · have hkN' : N ≤ k := by omega
      have h1 := hpre N le_rfl
      have h2 : prefixSum a (Set.range (fun t : ℕ => N + 2 * t))ᶜ N
          ≤ prefixSum a (Set.range (fun t : ℕ => N + 2 * t))ᶜ k := prefixSum_mono a _ hkN'
      have h3 := robust_growth a ha hrob N
      have h4 : a k = a N := hconst k hkN'
      have h5 : a (N + m) = a N := hconst _ (by omega)
      omega

/-! ### The main theorems -/

/-- **van Doorn's theorem.**  If a nondecreasing sequence of positive integers stays complete
after removing any `m` terms, for some `m ≥ 2`, then there is an infinite set of indices whose
removal still leaves every natural number representable as a sum of distinct remaining terms. -/
theorem exists_infinite_removal (a : ℕ → ℕ) (ha : Monotone a) (hpos : ∀ i, 1 ≤ a i) (m : ℕ)
    (hm : 2 ≤ m) (h : RobustlyComplete a m) :
    ∃ R : Set ℕ, R.Infinite ∧ Complete a Rᶜ := by
  by_cases hub : ∀ M : ℕ, ∃ i, M < a i
  · exact exists_infinite_removal_of_unbounded a ha hpos hm h hub
  · simp only [not_forall, not_exists, not_lt] at hub
    obtain ⟨M, hM⟩ := hub
    exact exists_infinite_removal_of_bounded a ha hpos hm h hM

/-- For every `n` there is an `n`-element set of indices whose removal keeps the sequence
complete, as soon as removing any `m` indices does, for some `m ≥ 2`. -/
theorem exists_removal_card (a : ℕ → ℕ) (ha : Monotone a) (hpos : ∀ i, 1 ≤ a i) (m : ℕ)
    (hm : 2 ≤ m) (h : RobustlyComplete a m) (n : ℕ) :
    ∃ S : Finset ℕ, S.card = n ∧ Complete a (↑S : Set ℕ)ᶜ := by
  obtain ⟨R, hRinf, hRcomp⟩ := exists_infinite_removal a ha hpos m hm h
  obtain ⟨S, hSsub, hScard⟩ := hRinf.exists_subset_card_eq n
  exact ⟨S, hScard, complete_mono (Set.compl_subset_compl.mpr hSsub) hRcomp⟩

/-- No pair `(m, n)` with `2 ≤ m < n` exists under strong completeness (the page's question,
restricted to `m ≥ 2`). -/
theorem strongPairs_ge_two_eq_empty :
    {p : ℕ × ℕ | 2 ≤ p.1 ∧ p.1 < p.2 ∧ ∃ a : ℕ → ℕ, Monotone a ∧ (∀ i, 1 ≤ a i) ∧
      RobustlyComplete a p.1 ∧
      ∀ S : Finset ℕ, S.card = p.2 → ¬ Complete a (↑S : Set ℕ)ᶜ} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨m, n⟩ ⟨hm, -, a, ha, hpos, hrob, hno⟩
  obtain ⟨S, hScard, hScomp⟩ := exists_removal_card a ha hpos m hm hrob n
  exact hno S hScard hScomp

end Erdos348
