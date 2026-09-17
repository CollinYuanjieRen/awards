import Mathlib

/-!
# Erdős Problem #708: Gallai's observation `g(2) = 2`

Erdős and Surányi (1959) define `g(n)` as the least `g` such that for every set `A ⊆ [2, ∞)` of
`n` integers and every set `I` of `max A` consecutive integers there is `B ⊆ I` with `|B| = g`
and `∏_{a ∈ A} a ∣ ∏_{b ∈ B} b`; Erdős asked whether `g(n) ≤ (2 + o(1)) n` (OPEN, $100; not
addressed here).  The problem page records that "Gallai was the first to consider problems of
this type, and observed that `g(2) = 2` and `g(3) ≥ 4`."  This file proves `g(2) = 2`:

* `GoodSize n k` is the defining property ("every `A` of size `n` and every block
  `I = [N, N + max A)` of `max A` consecutive integers admit `B ⊆ I` with `|B| = k` and
  `∏ A ∣ ∏ B`"); `g n = sInf {k | GoodSize n k}`.
* `goodSize_two_two : GoodSize 2 2` (for `A = {a, b}` with `2 ≤ a < b`: the block contains a
  multiple of `b`; if it also contains a different multiple of `a` take both, otherwise the
  multiple of `b` is a multiple of `lcm a b` and any other multiple of `gcd a b` in the block
  completes it, since `lcm a b * gcd a b = a * b`);
* `not_goodSize_two_one` and `not_goodSize_two_zero` (`A = {2, 3}`, `I = {1, 2, 3}`), whence
  `erdos_708_g_two : IsLeast {k | GoodSize 2 k} 2` and `g 2 = 2`.

`g(3) ≥ 4`, `g(3) = 4` and the `c_n` question are not claimed.  There is no formal-conjectures
rendering of this problem; the definitions are ours and follow the page verbatim (`I` is the
block `Finset.Ico N (N + A.sup id)`, so every set of `max A` consecutive natural numbers occurs).
-/

open Finset

namespace Erdos708

/-- `GoodSize n k`: for every `A ⊆ [2, ∞)` with `|A| = n` and every block
`I = [N, N + max A)` of `max A` consecutive integers, some `B ⊆ I` with `|B| = k` has
`∏_{a ∈ A} a ∣ ∏_{b ∈ B} b`. -/
def GoodSize (n k : ℕ) : Prop :=
  ∀ A : Finset ℕ, (∀ a ∈ A, 2 ≤ a) → A.card = n →
    ∀ N : ℕ, ∃ B ⊆ Finset.Ico N (N + A.sup id), B.card = k ∧ ∏ a ∈ A, a ∣ ∏ b ∈ B, b

/-- `g n` is the least `k` with `GoodSize n k` (Erdős–Surányi). -/
noncomputable def g (n : ℕ) : ℕ := sInf {k | GoodSize n k}

/-- Any block of `m ≥ 1` consecutive integers contains a multiple of `m`, and of every `d ∣ m`. -/
theorem exists_dvd_mem_Ico (N m : ℕ) (hm : 0 < m) : ∃ x ∈ Finset.Ico N (N + m), m ∣ x := by
  have hdm := Nat.div_add_mod N m
  have hlt : N % m < m := Nat.mod_lt _ hm
  rcases Nat.eq_zero_or_pos (N % m) with h0 | h0
  · exact ⟨N, Finset.mem_Ico.2 ⟨le_refl _, by omega⟩, Nat.dvd_of_mod_eq_zero h0⟩
  · refine ⟨m * (N / m + 1), Finset.mem_Ico.2 ⟨?_, ?_⟩, dvd_mul_right _ _⟩ <;>
      · rw [Nat.mul_add, Nat.mul_one]; omega

/-- If `2 * d ≤ m` and `0 < d`, a block of `m` consecutive integers contains two distinct
multiples of `d`. -/
theorem exists_two_dvd_mem_Ico (N d m : ℕ) (hd : 0 < d) (h : 2 * d ≤ m) :
    ∃ x ∈ Finset.Ico N (N + m), ∃ y ∈ Finset.Ico N (N + m), x ≠ y ∧ d ∣ x ∧ d ∣ y := by
  obtain ⟨x, hx, hdx⟩ := exists_dvd_mem_Ico N d hd
  obtain ⟨y, hy, hdy⟩ := exists_dvd_mem_Ico (N + d) d hd
  rw [Finset.mem_Ico] at hx hy
  refine ⟨x, Finset.mem_Ico.2 ⟨hx.1, by omega⟩, y, Finset.mem_Ico.2 ⟨by omega, by omega⟩,
    by omega, hdx, hdy⟩

/-- The key case analysis for `g(2) ≤ 2`, for `2 ≤ a < b`: a block of `b` consecutive integers
contains a two-element subset whose product is divisible by `a * b`. -/
theorem goodSize_two_aux (a b N : ℕ) (ha : 2 ≤ a) (hab : a < b) :
    ∃ B ⊆ Finset.Ico N (N + b), B.card = 2 ∧ a * b ∣ ∏ x ∈ B, x := by
  have hb : 0 < b := by omega
  have ha0 : 0 < a := by omega
  obtain ⟨y, hy, hby⟩ := exists_dvd_mem_Ico N b hb
  by_cases hc : ∃ x ∈ Finset.Ico N (N + b), a ∣ x ∧ x ≠ y
  · obtain ⟨x, hx, hax, hxy⟩ := hc
    refine ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · exact Finset.card_pair hxy
    · rw [Finset.prod_pair hxy]
      exact mul_dvd_mul hax hby
  · push Not at hc
    obtain ⟨x0, hx0, hax0⟩ := exists_dvd_mem_Ico N a ha0
    have hx0' : x0 ∈ Finset.Ico N (N + b) := by
      rw [Finset.mem_Ico] at hx0 ⊢; omega
    have hay : a ∣ y := by
      have := hc x0 hx0' hax0
      rwa [this] at hax0
    have hlcm : Nat.lcm a b ∣ y := Nat.lcm_dvd hay hby
    set d := Nat.gcd a b with hdef
    have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ ha0
    have hda : d ∣ a := Nat.gcd_dvd_left a b
    have hdb : d ∣ b := Nat.gcd_dvd_right a b
    have hdle : d ≤ a := Nat.le_of_dvd ha0 hda
    have h2d : 2 * d ≤ b := by
      obtain ⟨q, hq⟩ := hdb
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · interval_cases q <;> omega
      · calc 2 * d ≤ q * d := Nat.mul_le_mul_right d hq2
          _ = b := by rw [hq]; ring
    obtain ⟨x1, hx1, x2, hx2, hne, hd1, hd2⟩ := exists_two_dvd_mem_Ico N d b hd0 h2d
    have key : ∀ x ∈ Finset.Ico N (N + b), d ∣ x → x ≠ y →
        ∃ B ⊆ Finset.Ico N (N + b), B.card = 2 ∧ a * b ∣ ∏ z ∈ B, z := by
      intro x hx hdx hxy
      refine ⟨{x, y}, ?_, Finset.card_pair hxy, ?_⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      · rw [Finset.prod_pair hxy, ← Nat.gcd_mul_lcm a b]
        exact mul_dvd_mul hdx hlcm
    rcases eq_or_ne x1 y with rfl | h1
    · exact key x2 hx2 hd2 (Ne.symm hne)
    · exact key x1 hx1 hd1 h1

/-- Gallai: `g(2) ≤ 2`. -/
theorem goodSize_two_two : GoodSize 2 2 := by
  intro A hA hcard N
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have ha2 : 2 ≤ a := hA a (by simp)
  have hb2 : 2 ≤ b := hA b (by simp)
  have hsup : ({a, b} : Finset ℕ).sup id = max a b := by
    simp [Finset.sup_insert, Finset.sup_singleton]
  rw [hsup, Finset.prod_pair hab]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [max_eq_right h.le]
    exact goodSize_two_aux a b N ha2 h
  · rw [max_eq_left h.le]
    obtain ⟨B, hB, hBcard, hdvd⟩ := goodSize_two_aux b a N hb2 h
    exact ⟨B, hB, hBcard, by rwa [mul_comm] at hdvd⟩

/-- `A = {2, 3}`, `I = {1, 2, 3}`: no single element of `I` is divisible by `6`. -/
theorem not_goodSize_two_one : ¬ GoodSize 2 1 := by
  intro h
  obtain ⟨B, hB, hBcard, hdvd⟩ := h {2, 3} (by decide) (by decide) 1
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hBcard
  have hx : x ∈ Finset.Ico 1 (1 + ({2, 3} : Finset ℕ).sup id) := hB (by simp)
  have hsup : ({2, 3} : Finset ℕ).sup id = 3 := by decide
  rw [hsup, Finset.mem_Ico] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [Finset.prod_singleton] at hdvd
  have h6 : (6 : ℕ) ∣ x := by
    have h23 : ∏ a ∈ ({2, 3} : Finset ℕ), a = 6 := by decide
    rwa [h23] at hdvd
  omega

/-- `A = {2, 3}`: the empty product `1` is not divisible by `6`. -/
theorem not_goodSize_two_zero : ¬ GoodSize 2 0 := by
  intro h
  obtain ⟨B, _, hBcard, hdvd⟩ := h {2, 3} (by decide) (by decide) 1
  rw [Finset.card_eq_zero.mp hBcard, Finset.prod_empty] at hdvd
  have h23 : ∏ a ∈ ({2, 3} : Finset ℕ), a = 6 := by decide
  rw [h23] at hdvd
  omega

/-- **Gallai's observation (Erdős #708).**  `2` is the least `k` with `GoodSize 2 k`. -/
theorem erdos_708_g_two : IsLeast {k | GoodSize 2 k} 2 := by
  refine ⟨goodSize_two_two, fun k hk => ?_⟩
  by_contra hlt
  push Not at hlt
  interval_cases k
  · exact not_goodSize_two_zero hk
  · exact not_goodSize_two_one hk

/-- `g(2) = 2`. -/
theorem g_two : g 2 = 2 := by
  exact erdos_708_g_two.csInf_eq

end Erdos708

open Erdos708 in
/-- **Erdős #708, Gallai's observation, closed form**: `g 2 = 2`, i.e. `2` is the least `k` such
that every `2`-element `A ⊆ [2, ∞)` and every block of `max A` consecutive integers admit a
`k`-element sub-block whose product is divisible by `∏ A`. -/
theorem erdos_708_g_two_closed : g 2 = 2 ∧ IsLeast {k | GoodSize 2 k} 2 := by
  exact ⟨g_two, erdos_708_g_two⟩
