import Mathlib

/-!
# Erdős Problem #336: the basis `A = ⋃_{k ≥ 0} (2^{2k}, 2^{2k+1}]` has order `2` but exact order `3`

For `r ≥ 2` let `h(r)` be the maximal finite `k` such that there is a basis `A ⊆ ℕ` of order `r`
(every large integer is the sum of at most `r` integers from `A`) and exact order `k` (every large
integer is the sum of exactly `k` integers from `A`); Erdős asks for `lim h(r)/r²` (OPEN; not
addressed here, nor the Erdős–Graham criterion, the bounds on the limit, or the values of `h`).
The problem page records: "A simple example of the order of a basis differing from the exact
order is given by `A = ⋃_{k ≥ 0} (2^{2k}, 2^{2k+1}]`, which has order `2` but exact order `3`."
This file proves that example.

There is no formal-conjectures statement for #336, so the definitions are ours.  Sums of "`k`
integers from `A`" allow repetition (as for additive bases): `IsSumOfExactly A k n` means `n` is
the sum of a list of `k` elements of `A`, and `IsSumOfAtMost A r n` that some `k ≤ r` works.  The
order of `A` is the least `r` such that every large integer is a sum of at most `r` elements of
`A`, and the exact order the least `k` such that every large integer is a sum of exactly `k`
elements (`sInf`, so `0` when no such `r`/`k` exists).

Proof sketch.  Write `B_k = (4^k, 2·4^k]`.  Sums of exactly two elements cover `[4^j + 3, 4^{j+1}]`
for every `j ≥ 1` (for `n` in that range choose `i ≤ j` with `4^j + 4^i + 2 ≤ n ≤ 2·4^j + 2·4^i`
and split `n = a + b` with `a ∈ B_i`, `b ∈ B_j`), while `4^j + 1` and `4^j + 2` are never sums of
two elements and `4^j + 1 ∈ A`; so every large integer is a sum of at most two elements, but
infinitely many (`2·4^j + 1`) are not in `A`: the order is `2`.  Sums of exactly three elements
cover all large integers (`n = (n − 2) + 2` when `n − 2` is a sum of two, and `4^j + 1 = (4^j − 1) + 2`,
`4^j + 2 = (4^j − 3) + 5`, `4^j + 3 = (4^j − 2) + 5`, `4^j + 4 = (4^j − 1) + 5` otherwise), while
infinitely many integers (`4^j + 1`) are not sums of exactly two, nor of exactly one or zero:
the exact order is `3`.
-/

/-- `A = ⋃_{k ≥ 0} (2^{2k}, 2^{2k+1}]`. -/
def A336 : Set ℕ := {n | ∃ k : ℕ, 2 ^ (2 * k) < n ∧ n ≤ 2 ^ (2 * k + 1)}

/-- `n` is the sum of exactly `k` integers from `A` (repetition allowed). -/
def IsSumOfExactly (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length = k ∧ (∀ a ∈ l, a ∈ A) ∧ l.sum = n

/-- `n` is the sum of at most `r` integers from `A`. -/
def IsSumOfAtMost (A : Set ℕ) (r n : ℕ) : Prop := ∃ k ≤ r, IsSumOfExactly A k n

/-- `A` is a basis of order at most `r`: every large integer is the sum of at most `r` integers
from `A`. -/
def IsBasisOfOrderLE (A : Set ℕ) (r : ℕ) : Prop := ∃ N : ℕ, ∀ n ≥ N, IsSumOfAtMost A r n

/-- `A` has exact order `k` (in the weak sense): every large integer is the sum of exactly `k`
integers from `A`. -/
def IsExactBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop := ∃ N : ℕ, ∀ n ≥ N, IsSumOfExactly A k n

/-- The order of `A`: the least `r` with `IsBasisOfOrderLE A r`. -/
noncomputable def basisOrder (A : Set ℕ) : ℕ := sInf {r | IsBasisOfOrderLE A r}

/-- The exact order of `A`: the least `k` with `IsExactBasisOfOrder A k`. -/
noncomputable def exactOrder (A : Set ℕ) : ℕ := sInf {k | IsExactBasisOfOrder A k}

/-- Membership in `A`: `4^k < n ≤ 2·4^k`. -/
theorem mem_A336_iff (n : ℕ) : n ∈ A336 ↔ ∃ k : ℕ, 4 ^ k < n ∧ n ≤ 2 * 4 ^ k := by
  constructor
  · rintro ⟨k, h1, h2⟩
    refine ⟨k, ?_, ?_⟩
    · rw [pow_mul] at h1; norm_num at h1; exact h1
    · rw [pow_succ, pow_mul] at h2; norm_num at h2; omega
  · rintro ⟨k, h1, h2⟩
    refine ⟨k, ?_, ?_⟩
    · rw [pow_mul]; norm_num; exact h1
    · rw [pow_succ, pow_mul]; norm_num; omega

/-- Membership in `A` from the bounds `4^k < n ≤ 2·4^k`. -/
theorem mem_A336_of (k n : ℕ) (h1 : 4 ^ k < n) (h2 : n ≤ 2 * 4 ^ k) : n ∈ A336 :=
  (mem_A336_iff n).2 ⟨k, h1, h2⟩

/-- `2 ∈ A` (the block `k = 0`). -/
theorem two_mem_A336 : 2 ∈ A336 := mem_A336_of 0 2 (by norm_num) (by norm_num)

/-- `5 ∈ A` (the block `k = 1`). -/
theorem five_mem_A336 : 5 ∈ A336 := mem_A336_of 1 5 (by norm_num) (by norm_num)

/-- `a + b` is a sum of exactly two elements when `a, b ∈ A`. -/
theorem isSumOfExactly_two_of (A : Set ℕ) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
    IsSumOfExactly A 2 (a + b) :=
  ⟨[a, b], rfl, by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb, by simp⟩

/-- Prepending an element of `A` to a sum of exactly `k` elements. -/
theorem isSumOfExactly_succ_of (A : Set ℕ) (k a n : ℕ) (ha : a ∈ A)
    (h : IsSumOfExactly A k n) : IsSumOfExactly A (k + 1) (a + n) := by
  obtain ⟨l, hl, hmem, hsum⟩ := h
  refine ⟨a :: l, by simp [hl], ?_, by simp [hsum]⟩
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ha
  · exact hmem x hx

/-- An element of `A` is a sum of exactly one element of `A`. -/
theorem isSumOfExactly_one_of_mem (A : Set ℕ) (n : ℕ) (hn : n ∈ A) : IsSumOfExactly A 1 n :=
  ⟨[n], rfl, by simpa using hn, by simp⟩

/-- `4^k ≥ 1`. -/
theorem four_pow_pos (k : ℕ) : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)

/-- `4^j = 4^(j-1) · 4` for `j ≥ 1`. -/
theorem four_pow_succ_sub (j : ℕ) (hj : 1 ≤ j) : (4 : ℕ) ^ j = 4 ^ (j - 1) * 4 := by
  rw [← pow_succ]; congr 1; omega

/-- Sums of exactly two elements of `A` cover `[4^j + 3, 4^{j+1}]` for `j ≥ 1`. -/
theorem isSumOfExactly_two_of_mem_Icc (j n : ℕ) (hj : 1 ≤ j) (h1 : 4 ^ j + 3 ≤ n)
    (h2 : n ≤ 4 ^ (j + 1)) : IsSumOfExactly A336 2 n := by
  classical
  rw [pow_succ] at h2
  have hex : ∃ i : ℕ, n ≤ 2 * 4 ^ j + 2 * 4 ^ i := ⟨j, by omega⟩
  have hspec : n ≤ 2 * 4 ^ j + 2 * 4 ^ (Nat.find hex) := Nat.find_spec hex
  have hij : Nat.find hex ≤ j := Nat.find_min' hex (by omega)
  set i := Nat.find hex with hi
  have hpi : 1 ≤ (4:ℕ) ^ i := four_pow_pos i
  have hpj : (4:ℕ) ≤ 4 ^ j := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) hj
    simpa using h
  have hlow : 4 ^ j + 4 ^ i + 2 ≤ n := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h]; norm_num; omega
    · have hnot : ¬ (n ≤ 2 * 4 ^ j + 2 * 4 ^ (i - 1)) := Nat.find_min hex (by omega)
      have e : (4:ℕ) ^ i = 4 ^ (i - 1) * 4 := four_pow_succ_sub i h
      have hle : (4:ℕ) ^ i ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hij
      have ht : 1 ≤ (4:ℕ) ^ (i - 1) := four_pow_pos (i - 1)
      omega
  set a := max (4 ^ i + 1) (n - 2 * 4 ^ j) with ha
  have haa : 4 ^ i + 1 ≤ a := le_max_left _ _
  have hab : n - 2 * 4 ^ j ≤ a := le_max_right _ _
  have hac : a ≤ 2 * 4 ^ i := by
    rw [ha]; exact max_le (by omega) (by omega)
  have had : a ≤ n - 4 ^ j - 1 := by
    rw [ha]; exact max_le (by omega) (by omega)
  have e : a + (n - a) = n := by omega
  rw [← e]
  exact isSumOfExactly_two_of A336 a (n - a) (mem_A336_of i a (by omega) hac)
    (mem_A336_of j (n - a) (by omega) (by omega))

/-- Arithmetic core of the previous lemma: `4^j + c` with `1 ≤ c ≤ 2` is not the sum of
an element of `(4^p, 2·4^p]` and an element of `(4^q, 2·4^q]`. -/
theorem not_two_sum_aux (j c a b p q : ℕ) (hj : 1 ≤ j) (hc : 1 ≤ c) (hc2 : c ≤ 2)
    (hp1 : 4 ^ p < a) (hp2 : a ≤ 2 * 4 ^ p) (hq1 : 4 ^ q < b) (hq2 : b ≤ 2 * 4 ^ q)
    (hsum : a + b = 4 ^ j + c) : False := by
  have hpp : 1 ≤ (4:ℕ) ^ p := four_pow_pos p
  have hpq : 1 ≤ (4:ℕ) ^ q := four_pow_pos q
  have hpj : 1 ≤ (4:ℕ) ^ j := four_pow_pos j
  have hpjle : p ≤ j := by
    by_contra h
    have hh : (4:ℕ) ^ (j + 1) ≤ 4 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at hh
    omega
  have hqjle : q ≤ j := by
    by_contra h
    have hh : (4:ℕ) ^ (j + 1) ≤ 4 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at hh
    omega
  rcases eq_or_lt_of_le hpjle with h | h
  · subst h; omega
  rcases eq_or_lt_of_le hqjle with h' | h'
  · subst h'; omega
  · have hp : (4:ℕ) ^ p ≤ 4 ^ (j - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : (4:ℕ) ^ q ≤ 4 ^ (j - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : (4:ℕ) ^ j = 4 ^ (j - 1) * 4 := four_pow_succ_sub j hj
    omega

/-- `4^j + 1` and `4^j + 2` are not sums of exactly two elements of `A`. -/
theorem not_isSumOfExactly_two_pow_add (j : ℕ) (hj : 1 ≤ j) :
    ¬ IsSumOfExactly A336 2 (4 ^ j + 1) ∧ ¬ IsSumOfExactly A336 2 (4 ^ j + 2) := by
  have main : ∀ c : ℕ, 1 ≤ c → c ≤ 2 → ¬ IsSumOfExactly A336 2 (4 ^ j + c) := by
    rintro c hc1 hc2 ⟨l, hl, hmem, hsum⟩
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hl
    obtain ⟨p, hp1, hp2⟩ := (mem_A336_iff a).1 (hmem a (by simp))
    obtain ⟨q, hq1, hq2⟩ := (mem_A336_iff b).1 (hmem b (by simp))
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hsum
    exact not_two_sum_aux j c a b p q hj hc1 hc2 hp1 hp2 hq1 hq2 hsum
  exact ⟨main 1 (by norm_num) (by norm_num), main 2 (by norm_num) (by norm_num)⟩

/-- Every `n ≥ 5` is the sum of at most two elements of `A`. -/
theorem isSumOfAtMost_two (n : ℕ) (hn : 5 ≤ n) : IsSumOfAtMost A336 2 n := by
  set j := Nat.log 4 n with hjdef
  have hlo : 4 ^ j ≤ n := Nat.pow_log_le_self 4 (by omega)
  have hhi : n < 4 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hj1 : 1 ≤ j := by
    by_contra h
    have : j = 0 := by omega
    rw [this] at hhi; norm_num at hhi; omega
  rw [pow_succ] at hhi
  rcases lt_or_ge (4 ^ j) n with hcase | hcase
  · rcases le_or_gt n (2 * 4 ^ j) with h2 | h2
    · exact ⟨1, by norm_num, isSumOfExactly_one_of_mem A336 n (mem_A336_of j n hcase h2)⟩
    · have hpj : (4:ℕ) ≤ 4 ^ j := by
        have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) hj1
        simpa using h
      exact ⟨2, le_refl 2, isSumOfExactly_two_of_mem_Icc j n hj1 (by omega) (by rw [pow_succ]; omega)⟩
  · have hne : n = 4 ^ j := by omega
    have hj2 : 2 ≤ j := by
      by_contra h
      have : j = 1 := by omega
      rw [this] at hne; norm_num at hne; omega
    have e : (4:ℕ) ^ j = 4 ^ (j - 1) * 4 := four_pow_succ_sub j hj1
    have hpj : (4:ℕ) ≤ 4 ^ (j - 1) := by
      have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) (show 1 ≤ j - 1 by omega)
      simpa using h
    refine ⟨2, le_refl 2, isSumOfExactly_two_of_mem_Icc (j - 1) n (by omega) (by omega) ?_⟩
    rw [show j - 1 + 1 = j by omega]
    omega

/-- `m < 4^m`. -/
theorem self_lt_four_pow (m : ℕ) : m < 4 ^ m := by
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : (2:ℕ) ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
  omega

/-- `2·4^m + 1 ∉ A`. -/
theorem two_mul_four_pow_add_one_not_mem (m : ℕ) : 2 * 4 ^ m + 1 ∉ A336 := by
  intro hmem
  obtain ⟨p, hp1, hp2⟩ := (mem_A336_iff _).1 hmem
  have hlt : (4:ℕ) ^ m < 4 ^ p := by
    have hpp : 1 ≤ (4:ℕ) ^ p := four_pow_pos p
    have hpm : 1 ≤ (4:ℕ) ^ m := four_pow_pos m
    omega
  have hmp : m < p := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  have hh : (4:ℕ) ^ (m + 1) ≤ 4 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ] at hh
  have hpm : 1 ≤ (4:ℕ) ^ m := four_pow_pos m
  omega

/-- Only `0` is a sum of exactly zero elements. -/
theorem isSumOfExactly_zero_iff (A : Set ℕ) (n : ℕ) : IsSumOfExactly A 0 n ↔ n = 0 := by
  constructor
  · rintro ⟨l, hl, -, hsum⟩
    rw [List.length_eq_zero_iff] at hl
    subst hl; simpa using hsum.symm
  · rintro rfl; exact ⟨[], rfl, by simp, by simp⟩

/-- Sums of exactly one element of `A` are the elements of `A`. -/
theorem isSumOfExactly_one_iff (A : Set ℕ) (n : ℕ) : IsSumOfExactly A 1 n ↔ n ∈ A := by
  constructor
  · rintro ⟨l, hl, hmem, hsum⟩
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hsum
    subst hsum; exact hmem a (by simp)
  · exact isSumOfExactly_one_of_mem A n

/-- `2·4^j + 1 ∉ A`, so `A` itself contains only finitely many of any tail: `A` is not a basis of
order `1`. -/
theorem not_isBasisOfOrderLE_one : ¬ IsBasisOfOrderLE A336 1 := by
  rintro ⟨N, hN⟩
  have hNlt : N < 4 ^ N := self_lt_four_pow N
  have hpN : 1 ≤ (4:ℕ) ^ N := four_pow_pos N
  obtain ⟨k, hk, hex⟩ := hN (2 * 4 ^ N + 1) (by omega)
  interval_cases k
  · rw [isSumOfExactly_zero_iff] at hex; omega
  · rw [isSumOfExactly_one_iff] at hex
    exact two_mul_four_pow_add_one_not_mem N hex

/-- Every `n ≥ 20` is the sum of exactly three elements of `A`. -/
theorem isSumOfExactly_three (n : ℕ) (hn : 20 ≤ n) : IsSumOfExactly A336 3 n := by
  set j := Nat.log 4 n with hjdef
  have hlo : 4 ^ j ≤ n := Nat.pow_log_le_self 4 (by omega)
  have hhi : n < 4 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hj2 : 2 ≤ j := by
    by_contra h
    have hh : (4:ℕ) ^ (j + 1) ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hh; omega
  have e : (4:ℕ) ^ j = 4 ^ (j - 1) * 4 := four_pow_succ_sub j (by omega)
  have hp1 : (4:ℕ) ≤ 4 ^ (j - 1) := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) (show 1 ≤ j - 1 by omega)
    simpa using h
  rw [pow_succ] at hhi
  rcases le_or_gt (4 ^ j + 5) n with h | h
  · have h2 : IsSumOfExactly A336 2 (n - 2) :=
      isSumOfExactly_two_of_mem_Icc j (n - 2) (by omega) (by omega) (by rw [pow_succ]; omega)
    have h3 := isSumOfExactly_succ_of A336 2 2 (n - 2) two_mem_A336 h2
    rw [show 2 + (n - 2) = n by omega] at h3
    exact h3
  · rcases le_or_gt n (4 ^ j + 1) with h' | h'
    · have h2 : IsSumOfExactly A336 2 (n - 2) :=
        isSumOfExactly_two_of_mem_Icc (j - 1) (n - 2) (by omega) (by omega)
          (by rw [show j - 1 + 1 = j by omega]; omega)
      have h3 := isSumOfExactly_succ_of A336 2 2 (n - 2) two_mem_A336 h2
      rw [show 2 + (n - 2) = n by omega] at h3
      exact h3
    · have h2 : IsSumOfExactly A336 2 (n - 5) :=
        isSumOfExactly_two_of_mem_Icc (j - 1) (n - 5) (by omega) (by omega)
          (by rw [show j - 1 + 1 = j by omega]; omega)
      have h3 := isSumOfExactly_succ_of A336 2 5 (n - 5) five_mem_A336 h2
      rw [show 5 + (n - 5) = n by omega] at h3
      exact h3

/-- `A` is not an exact basis of order `2` (nor `1`, nor `0`). -/
theorem not_isExactBasisOfOrder_le_two (k : ℕ) (hk : k ≤ 2) : ¬ IsExactBasisOfOrder A336 k := by
  rintro ⟨N, hN⟩
  have hNlt : N < 4 ^ N := self_lt_four_pow N
  have hpN : 1 ≤ (4:ℕ) ^ N := four_pow_pos N
  have hNlt' : N + 1 < 4 ^ (N + 1) := self_lt_four_pow (N + 1)
  interval_cases k
  · have h := hN (N + 1) (by omega)
    rw [isSumOfExactly_zero_iff] at h; omega
  · have h := hN (2 * 4 ^ N + 1) (by omega)
    rw [isSumOfExactly_one_iff] at h
    exact two_mul_four_pow_add_one_not_mem N h
  · have h := hN (4 ^ (N + 1) + 1) (by omega)
    exact (not_isSumOfExactly_two_pow_add (N + 1) (by omega)).1 h

/-- `IsSumOfAtMost` is monotone in the number of summands. -/
theorem isSumOfAtMost_mono (A : Set ℕ) (r r' n : ℕ) (h : r ≤ r') (hs : IsSumOfAtMost A r n) :
    IsSumOfAtMost A r' n := by
  obtain ⟨k, hk, hex⟩ := hs
  exact ⟨k, hk.trans h, hex⟩

/-- `IsBasisOfOrderLE` is monotone in the order. -/
theorem isBasisOfOrderLE_mono (A : Set ℕ) (r r' : ℕ) (h : r ≤ r') (hb : IsBasisOfOrderLE A r) :
    IsBasisOfOrderLE A r' := by
  obtain ⟨N, hN⟩ := hb
  exact ⟨N, fun n hn => isSumOfAtMost_mono A r r' n h (hN n hn)⟩

/-- **Erdős #336, the page's example**: `A = ⋃_{k ≥ 0} (2^{2k}, 2^{2k+1}]` has order `2` but exact
order `3`. -/
theorem erdos_336_example : basisOrder A336 = 2 ∧ exactOrder A336 = 3 := by
  constructor
  · show sInf {r | IsBasisOfOrderLE A336 r} = 2
    have hmem : (2:ℕ) ∈ {r | IsBasisOfOrderLE A336 r} := ⟨5, fun n hn => isSumOfAtMost_two n hn⟩
    have hle : sInf {r | IsBasisOfOrderLE A336 r} ≤ 2 := Nat.sInf_le hmem
    have hsm : sInf {r | IsBasisOfOrderLE A336 r} ∈ {r | IsBasisOfOrderLE A336 r} :=
      Nat.sInf_mem ⟨2, hmem⟩
    by_contra hcon
    exact not_isBasisOfOrderLE_one (isBasisOfOrderLE_mono A336 _ 1 (by omega) hsm)
  · show sInf {k | IsExactBasisOfOrder A336 k} = 3
    have hmem : (3:ℕ) ∈ {k | IsExactBasisOfOrder A336 k} :=
      ⟨20, fun n hn => isSumOfExactly_three n hn⟩
    have hle : sInf {k | IsExactBasisOfOrder A336 k} ≤ 3 := Nat.sInf_le hmem
    have hsm : sInf {k | IsExactBasisOfOrder A336 k} ∈ {k | IsExactBasisOfOrder A336 k} :=
      Nat.sInf_mem ⟨3, hmem⟩
    by_contra hcon
    exact not_isExactBasisOfOrder_le_two _ (by omega) hsm
