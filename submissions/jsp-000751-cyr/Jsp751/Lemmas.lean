import Jsp751.Counting

/-!
# JSP-000751 / Erdős #903 — the combinatorial lemmas

Throughout, `v = p ^ 2 + p + 1` and the number of blocks satisfies `v < b < v + p`.
-/

open Finset

namespace Erdos903

/-- The arithmetic heart of (L1): on the range `p + 2 ≤ l ≤ v - 2` the function `l ↦ l² (v - l)`
is at least its value `(p² + 2p)(p² + p)` at the endpoints. -/
theorem sq_mul_lower_bound (p l m : ℕ) (hp : 2 ≤ p) (hl : p + 2 ≤ l) (hm : 2 ≤ m)
    (hlm : l + m = p ^ 2 + p + 1) : (p ^ 2 + 2 * p) * (p ^ 2 + p) ≤ l ^ 2 * m := by
  zify at *
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ p + 1) (by linarith : (0:ℤ) ≤ p - 2))
      (by linarith : (0:ℤ) ≤ p + 2),
    mul_nonneg (by nlinarith : (0:ℤ) ≤ p ^ 2 - 2) (by linarith : (0:ℤ) ≤ l - p - 2),
    mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ l - p - 2) (by linarith : (0:ℤ) ≤ l - p - 2))
      (by linarith : (0:ℤ) ≤ m - 2),
    mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ 2 * p + 2) (by linarith : (0:ℤ) ≤ l - p - 2))
      (by linarith : (0:ℤ) ≤ m - 2)]

section

variable (p : ℕ) {b : ℕ} (hb1 : p ^ 2 + p + 1 < b) (hb2 : b < p ^ 2 + p + 1 + p)
include hb1 hb2

/-- The gap `v < b < v + p` is empty unless `p ≥ 2`. -/
theorem two_le_p : 2 ≤ p := by omega

end

section

variable (p : ℕ) {b : ℕ} {block : Fin b → Finset (Fin (p ^ 2 + p + 1))}
  (h : IsLinearSpace block) (hb1 : p ^ 2 + p + 1 < b) (hb2 : b < p ^ 2 + p + 1 + p)
include h hb1 hb2

/-- (L1) Every block has at most `p + 1` points. -/
theorem card_block_le (i : Fin b) : #(block i) ≤ p + 1 := by
  by_contra hcon
  have hcon' : p + 2 ≤ #(block i) := by omega
  have hp2 : 2 ≤ p := two_le_p p hb1 hb2
  have hlv : #(block i) ≤ p ^ 2 + p + 1 := by
    have hle := Finset.card_le_univ (block i)
    rwa [Fintype.card_fin] at hle
  by_cases hsmall : p ^ 2 + p + 1 - #(block i) ≤ 1
  · -- the block misses at most one point: every other block meets it
    have hsub : univ.erase i ⊆ meeting block i := by
      intro k hk
      rw [mem_erase] at hk
      refine mem_meeting_iff.2 ⟨hk.1, Finset.card_pos.1 ?_⟩
      have h1 := Finset.card_sdiff_add_card_inter (block k) (block i)
      have h2 : #(block k \ block i) ≤ p ^ 2 + p + 1 - #(block i) := by
        have hs : block k \ block i ⊆ (univ : Finset (Fin (p ^ 2 + p + 1))) \ block i := by
          intro y hy
          rw [mem_sdiff] at hy ⊢
          exact ⟨mem_univ y, hy.2⟩
        have hc := Finset.card_le_card hs
        have h3 : #((univ : Finset (Fin (p ^ 2 + p + 1))) \ block i)
            = p ^ 2 + p + 1 - #(block i) := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        rwa [h3] at hc
      have h4 := h.1 k
      omega
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin] at hc1
    have hsum : #(meeting block i) ≤ ∑ k ∈ meeting block i, (#(block k) - 1) := by
      calc #(meeting block i) = ∑ _k ∈ meeting block i, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun k _ => by have := h.1 k; omega
    rw [sum_meeting_card_sub_one h i] at hsum
    rcases (by omega : p ^ 2 + p + 1 - #(block i) = 0 ∨ p ^ 2 + p + 1 - #(block i) = 1)
      with hd | hd
    · rw [hd, Nat.mul_zero] at hsum
      omega
    · rw [hd, Nat.mul_one] at hsum
      omega
  · -- the generic case: the Stanton–Kalbfleisch bound forces too many blocks
    have harith := sq_mul_lower_bound p (#(block i)) (p ^ 2 + p + 1 - #(block i)) hp2
      (by omega) (by omega) (by omega)
    have hSK := stanton_kalbfleisch h i
    have hT := card_meeting_add_one_le (block := block) i
    have hv1 : p ^ 2 + p + 1 - 1 = p ^ 2 + p := by omega
    rw [hv1] at hSK
    have hcancel : p ^ 2 + 2 * p ≤ #(meeting block i) :=
      Nat.le_of_mul_le_mul_right (le_trans harith hSK) (by omega)
    omega

/-- (L3) Every point has degree at least `p + 1`. -/
theorem degree_ge (x : Fin (p ^ 2 + p + 1)) : p + 1 ≤ degree block x := by
  have hp2 : 2 ≤ p := two_le_p p hb1 hb2
  have hsum := sum_card_sub_one_through h x
  have hbound : ∑ i ∈ through block x, (#(block i) - 1) ≤ degree block x * p := by
    calc ∑ i ∈ through block x, (#(block i) - 1) ≤ ∑ _i ∈ through block x, p :=
          Finset.sum_le_sum fun i _ => by have := card_block_le p h hb1 hb2 i; omega
      _ = degree block x * p := by rw [Finset.sum_const, smul_eq_mul, degree]
  rw [hsum] at hbound
  have hv1 : p ^ 2 + p + 1 - 1 = p ^ 2 + p := by omega
  rw [hv1] at hbound
  by_contra hcon
  have hd : degree block x ≤ p := by omega
  have h1 : degree block x * p ≤ p * p := Nat.mul_le_mul_right p hd
  have h2 : p * p = p ^ 2 := by ring
  omega

/-- (L4) Some point has degree exactly `p + 1`. -/
theorem exists_degree_eq : ∃ x, degree block x = p + 1 := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hdeg : ∀ x, p + 2 ≤ degree block x := by
    intro x
    have h1 := degree_ge p h hb1 hb2 x
    have h2 := hcon x
    omega
  have hsum := sum_degree_eq_sum_card (block := block)
  have hlow : (p ^ 2 + p + 1) * (p + 2) ≤ ∑ x, degree block x := by
    calc (p ^ 2 + p + 1) * (p + 2)
        = ∑ _x : Fin (p ^ 2 + p + 1), (p + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun x _ => hdeg x
  have hhigh : ∑ i, #(block i) ≤ b * (p + 1) := by
    calc ∑ i, #(block i) ≤ ∑ _i : Fin b, (p + 1) :=
          Finset.sum_le_sum fun i _ => card_block_le p h hb1 hb2 i
      _ = b * (p + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hsum] at hlow
  have hb : b ≤ p ^ 2 + 2 * p := by omega
  have hmul : b * (p + 1) ≤ (p ^ 2 + 2 * p) * (p + 1) := Nat.mul_le_mul_right (p + 1) hb
  nlinarith [hlow, hhigh, hmul]

/-- A point of degree `p + 1` lies only on blocks with `p + 1` points. -/
theorem card_eq_of_degree_eq {x : Fin (p ^ 2 + p + 1)} (hx : degree block x = p + 1)
    {i : Fin b} (hi : x ∈ block i) : #(block i) = p + 1 := by
  have hcard : #(through block x) = p + 1 := hx
  have hle : ∀ k ∈ through block x, #(block k) - 1 ≤ p := by
    intro k _
    have := card_block_le p h hb1 hb2 k
    omega
  have hconst : ∑ _k ∈ through block x, p = p ^ 2 + p := by
    rw [Finset.sum_const, hcard, smul_eq_mul]
    ring
  have hsum' : ∑ k ∈ through block x, (#(block k) - 1) = ∑ _k ∈ through block x, p := by
    rw [sum_card_sub_one_through h x, hconst]
    omega
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum' i (mem_through_iff.2 hi)
  have h2 := h.1 i
  omega

/-- (L2) If every point of a block has degree `p + 1` then there are exactly `p ^ 2 + p + 1`
blocks. -/
theorem b_eq_of_block_all_degree (j : Fin b)
    (hall : ∀ x ∈ block j, degree block x = p + 1) : b = p ^ 2 + p + 1 := by
  classical
  have hp2 : 2 ≤ p := two_le_p p hb1 hb2
  -- the block itself is long
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 (by have := h.1 j; omega : 0 < #(block j))
  have hcardj : #(block j) = p + 1 := card_eq_of_degree_eq p h hb1 hb2 (hall x₀ hx₀) hx₀
  -- the blocks meeting it are long too
  have hlong : ∀ i ∈ meeting block j, #(block i) = p + 1 := by
    intro i hi
    obtain ⟨hij, ⟨y, hy⟩⟩ := mem_meeting_iff.1 hi
    rw [mem_inter] at hy
    exact card_eq_of_degree_eq p h hb1 hb2 (hall y hy.2) hy.1
  -- how many blocks meet it
  have hmeet : #(meeting block j) = (p + 1) * p := by
    rw [card_meeting_eq h j]
    calc ∑ x ∈ block j, (degree block x - 1) = ∑ _x ∈ block j, p := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [hall x hx]
          omega
      _ = (p + 1) * p := by rw [Finset.sum_const, hcardj, smul_eq_mul]
  set S : Finset (Fin b) := insert j (meeting block j) with hS
  have hjS : j ∉ meeting block j := by
    intro hj
    exact (mem_meeting_iff.1 hj).1 rfl
  have hcardS : #S = p ^ 2 + p + 1 := by
    rw [hS, Finset.card_insert_of_notMem hjS, hmeet]
    ring
  have hlongS : ∀ i ∈ S, #(block i) = p + 1 := by
    intro i hi
    rw [hS, Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact hcardj
    · exact hlong i hi
  -- counting pairs: the long blocks in `S` already cover every pair
  have hchoose : (p ^ 2 + p + 1) * ((p + 1).choose 2) = (p ^ 2 + p + 1).choose 2 := by
    have h1 : p + 1 - 1 = p := by omega
    have h2 : p ^ 2 + p + 1 - 1 = p ^ 2 + p := by omega
    have h3 : (p + 1) * p = p ^ 2 + p := by ring
    have hdvd : 2 ∣ p ^ 2 + p := by
      have h4 : p ^ 2 + p = p * (p + 1) := by ring
      rw [h4]
      exact even_iff_two_dvd.1 (Nat.even_mul_succ_self p)
    rw [Nat.choose_two_right, Nat.choose_two_right, h1, h2, h3, Nat.mul_div_assoc _ hdvd]
  have hsumS : ∑ i ∈ S, (#(block i)).choose 2 = (p ^ 2 + p + 1).choose 2 := by
    have e1 : ∑ i ∈ S, (#(block i)).choose 2 = ∑ _i ∈ S, ((p + 1).choose 2) :=
      Finset.sum_congr rfl fun i hi => by rw [hlongS i hi]
    rw [e1, Finset.sum_const, hcardS, smul_eq_mul, hchoose]
  have htotal := sum_choose_two h (block := block)
  have hsplit : ∑ i ∈ univ \ S, (#(block i)).choose 2 + ∑ i ∈ S, (#(block i)).choose 2
      = ∑ i, (#(block i)).choose 2 := Finset.sum_sdiff (Finset.subset_univ S)
  have hzero : ∑ i ∈ univ \ S, (#(block i)).choose 2 = 0 := by
    rw [hsumS] at hsplit
    omega
  have hempty : (univ : Finset (Fin b)) \ S = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    have h1 := (Finset.sum_eq_zero_iff.1 hzero) i hi
    have h2 : 2 ≤ #(block i) := h.1 i
    have h3 : (2 : ℕ).choose 2 ≤ (#(block i)).choose 2 := Nat.choose_le_choose 2 h2
    simp at h3
    omega
  have hsub : (univ : Finset (Fin b)) ⊆ S := by
    rw [← Finset.sdiff_eq_empty_iff_subset]
    exact hempty
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_card (Finset.subset_univ S)
  rw [Finset.card_univ, Fintype.card_fin, hcardS] at h1 h2
  omega

end

end Erdos903
