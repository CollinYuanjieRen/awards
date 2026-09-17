import Mathlib

/-!
# JSP-000731 / Erdős #880 — a small toolkit on sums of powers of two

This file is a self-contained arithmetic toolkit, used later by the Erdős #880 construction.
Everything here is about `ℕ` and about sums of the form `∑ 2 ^ j`.

The main results are:

* `two_pow_card_sub_one_le_sum`: a set of `k` *distinct* exponents has `∑ 2 ^ j ≥ 2 ^ k - 1`;
* `sum_two_pow_le_of_subset_range`: dually, exponents inside `range N` give
  `∑ 2 ^ j ≤ 2 ^ N - 2 ^ (N - k)`;
* `sum_two_pow_le_of_lt` (the key lemma): the same upper bound holds for a *multiset* of `m`
  exponents, i.e. with repetitions allowed, as soon as the sum is `< 2 ^ N`;
* `exists_bits`: the binary expansion of `q < 2 ^ N` lives inside `range N`, and uses all `N`
  available bits only for `q = 2 ^ N - 1`.

Throughout, subtraction is truncated subtraction on `ℕ`; the proofs therefore first establish the
addition form of each inequality and only then `omega` their way to the stated form.
-/

namespace Erdos880

/-- `a + 1 ≤ 2 ^ a`. -/
theorem succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self

/-- Addition form of `two_pow_card_sub_one_le_sum`, free of truncated subtraction. -/
theorem two_pow_card_le_sum_succ (F : Finset ℕ) : 2 ^ F.card ≤ (∑ j ∈ F, 2 ^ j) + 1 := by
  induction F using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have hmem : a ∉ s := fun ha => absurd (hlt a ha) (lt_irrefl a)
    have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.mpr (hlt x hx)
    have hcard : s.card ≤ a := by
      simpa using Finset.card_le_card hsub
    have hpow : 2 ^ s.card ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hcard
    rw [Finset.card_insert_of_notMem hmem, Finset.sum_insert hmem, pow_succ]
    omega

/-- A set of `k` distinct naturals has `∑ 2^j ≥ 2^k − 1`. -/
theorem two_pow_card_sub_one_le_sum (F : Finset ℕ) : 2 ^ F.card - 1 ≤ ∑ j ∈ F, 2 ^ j := by
  have := two_pow_card_le_sum_succ F
  omega

/-- The full geometric sum: `∑_{j < N} 2 ^ j + 1 = 2 ^ N`. -/
theorem sum_range_two_pow_succ (N : ℕ) : (∑ j ∈ Finset.range N, 2 ^ j) + 1 = 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- Addition form of `sum_two_pow_le_of_subset_range`, free of truncated subtraction. -/
theorem sum_two_pow_add_two_pow_le {N : ℕ} {J : Finset ℕ} (hJ : J ⊆ Finset.range N) :
    (∑ j ∈ J, 2 ^ j) + 2 ^ (N - J.card) ≤ 2 ^ N := by
  have hcard : (Finset.range N \ J).card = N - J.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hJ, Finset.card_range]
  have hsplit : (∑ j ∈ Finset.range N \ J, 2 ^ j) + ∑ j ∈ J, 2 ^ j
      = ∑ j ∈ Finset.range N, 2 ^ j := Finset.sum_sdiff hJ
  have hlow := two_pow_card_le_sum_succ (Finset.range N \ J)
  rw [hcard] at hlow
  have hgeom := sum_range_two_pow_succ N
  omega

/-- For `J ⊆ range N`: `∑_{j∈J} 2^j ≤ 2^N − 2^(N − |J|)`. -/
theorem sum_two_pow_le_of_subset_range {N : ℕ} {J : Finset ℕ} (hJ : J ⊆ Finset.range N) :
    ∑ j ∈ J, 2 ^ j ≤ 2 ^ N - 2 ^ (N - J.card) := by
  have := sum_two_pow_add_two_pow_le hJ
  omega

/-- The key lemma, in the shape needed for strong induction on the size of the multiset. -/
private theorem sum_two_pow_le_of_lt_aux (n : ℕ) :
    ∀ (E : Multiset ℕ) (N : ℕ), Multiset.card E = n →
      (E.map fun j => 2 ^ j).sum < 2 ^ N →
      (E.map fun j => 2 ^ j).sum ≤ 2 ^ N - 2 ^ (N - n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E N hcard h
    by_cases hnd : E.Nodup
    · -- distinct exponents: `E` is a `Finset` contained in `range N`
      have hsum : (⟨E, hnd⟩ : Finset ℕ).sum (fun j => 2 ^ j) = (E.map fun j => 2 ^ j).sum :=
        Finset.sum_mk E hnd _
      have hsub : (⟨E, hnd⟩ : Finset ℕ) ⊆ Finset.range N := by
        intro x hx
        have hxE : x ∈ E := hx
        have hle : 2 ^ x ≤ (E.map fun j => 2 ^ j).sum :=
          Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ (Multiset.mem_map_of_mem _ hxE)
        exact Finset.mem_range.mpr ((Nat.pow_lt_pow_iff_right one_lt_two).mp (lt_of_le_of_lt hle h))
      have hcard' : (⟨E, hnd⟩ : Finset ℕ).card = n := by
        rw [Finset.card_mk, hcard]
      have := sum_two_pow_le_of_subset_range hsub
      rwa [hsum, hcard'] at this
    · -- a repeated exponent `j`: replace two copies of `j` by one copy of `j + 1`
      obtain ⟨j, hj⟩ : ∃ j, 2 ≤ Multiset.count j E := by
        by_contra hcon
        exact hnd (Multiset.nodup_iff_count_le_one.mpr fun a => by
          have := not_exists.mp hcon a; omega)
      have hrep : Multiset.replicate 2 j ≤ E := Multiset.le_count_iff_replicate_le.mp hj
      set E₀ : Multiset ℕ := E - Multiset.replicate 2 j with hE₀
      have hE : E₀ + Multiset.replicate 2 j = E := tsub_add_cancel_of_le hrep
      have hcard₀ : Multiset.card E₀ = n - 2 := by
        rw [hE₀, Multiset.card_sub hrep, hcard, Multiset.card_replicate]
      have hn2 : 2 ≤ n := by
        have : Multiset.card (Multiset.replicate 2 j) ≤ Multiset.card E :=
          Multiset.card_le_card hrep
        simpa [hcard] using this
      -- the two multisets have the same sum of powers
      have hsumE : (E.map fun j => 2 ^ j).sum
          = (E₀.map fun j => 2 ^ j).sum + 2 ^ (j + 1) := by
        rw [← hE, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
          Multiset.sum_replicate, pow_succ]
        ring
      set E' : Multiset ℕ := (j + 1) ::ₘ E₀ with hE'
      have hsumE' : (E'.map fun j => 2 ^ j).sum = (E.map fun j => 2 ^ j).sum := by
        rw [hE', Multiset.map_cons, Multiset.sum_cons, hsumE]; ring
      have hcard' : Multiset.card E' = n - 1 := by
        rw [hE', Multiset.card_cons, hcard₀]; omega
      have hlt : n - 1 < n := by omega
      have key := ih (n - 1) hlt E' N hcard' (by rw [hsumE']; exact h)
      rw [hsumE'] at key
      have hmono : 2 ^ (N - n) ≤ 2 ^ (N - (n - 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- KEY: a sum of `m` powers of two (repetition allowed) that is `< 2^N` is `≤ 2^N − 2^(N − m)`. -/
theorem sum_two_pow_le_of_lt (E : Multiset ℕ) (N : ℕ)
    (h : (E.map fun j => 2 ^ j).sum < 2 ^ N) :
    (E.map fun j => 2 ^ j).sum ≤ 2 ^ N - 2 ^ (N - Multiset.card E) :=
  sum_two_pow_le_of_lt_aux (Multiset.card E) E N rfl h

/-- Binary expansion inside `range N`, with the extra fact that only `2^N − 1` uses all `N` bits. -/
theorem exists_bits (N q : ℕ) (hq : q < 2 ^ N) :
    ∃ J : Finset ℕ, J ⊆ Finset.range N ∧ ∑ j ∈ J, 2 ^ j = q ∧ (J.card = N → q + 1 = 2 ^ N) := by
  induction N generalizing q with
  | zero =>
    have hq0 : q = 0 := by simpa using hq
    exact ⟨∅, by simp, by simp [hq0], by simp [hq0]⟩
  | succ N ih =>
    have hpow : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by rw [pow_succ]; ring
    by_cases hlt : q < 2 ^ N
    · obtain ⟨J, hsub, hsum, _⟩ := ih q hlt
      have hmono : Finset.range N ⊆ Finset.range (N + 1) := fun x hx =>
        Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hx))
      refine ⟨J, hsub.trans hmono, hsum, ?_⟩
      intro hcardJ
      have : J.card ≤ N := by simpa using Finset.card_le_card hsub
      omega
    · have hqle : 2 ^ N ≤ q := by omega
      obtain ⟨J, hsub, hsum, hfull⟩ := ih (q - 2 ^ N) (by omega)
      have hmem : N ∉ J := fun hN => by simpa using hsub hN
      refine ⟨insert N J, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxN | hxJ
        · exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (by
            have := Finset.mem_range.mp (hsub hxJ); omega)
      · rw [Finset.sum_insert hmem, hsum]; omega
      · intro hcardJ
        rw [Finset.card_insert_of_notMem hmem] at hcardJ
        have := hfull (by omega)
        omega

#print axioms Erdos880.sum_two_pow_le_of_lt
#print axioms Erdos880.sum_two_pow_le_of_subset_range
#print axioms Erdos880.exists_bits

end Erdos880
