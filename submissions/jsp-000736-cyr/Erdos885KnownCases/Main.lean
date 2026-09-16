import Mathlib

/-!
# Erdős Problem #885: common factor differences, the cases `k = 2` and `k = 3`

For `n ≥ 1` let `D(n) = {|a − b| : n = ab}` be the factor-difference set of `n`.  Erdős asked
whether for every `k ≥ 1` there are integers `N₁ < ⋯ < N_k` with `|⋂ D(Nᵢ)| ≥ k`.  The problem is
OPEN in general; Erdős–Rosenfeld (1997) proved it for `k = 2`, Jiménez-Urroz (1999) for `k = 3`,
and Bremner (2019) for `k = 4`.  This file proves the cases `k = 2` and `k = 3` by explicit
certificates, in the exact shape of the formal-conjectures statements
`Erdos885.erdos_885.variants.k_eq_2` and `k_eq_3` (tagged "research solved" with `sorry`):

* `k = 2`: `D(12) ∩ D(42) ⊇ {1, 11}` (`12 = 3·4 = 1·12`, `42 = 6·7 = 3·14`);
* `k = 3`: `D(112) ∩ D(952) ∩ D(3240) ⊇ {6, 54, 111}` (`112 = 8·14 = 2·56 = 1·112`,
  `952 = 28·34 = 14·68 = 8·119`, `3240 = 54·60 = 36·90 = 24·135`).

The case `k = 4` (Bremner) and the general question are not addressed.
-/

open Nat Set Finset

/-- For integer `n ≥ 1` we define the factor difference set of `n` by `D(n) = {|a − b| : n = ab}`
(formal-conjectures definition). -/
def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

/-- If `n = a * b` and `d = |a - b|` (as integers) then `d` is a factor difference of `n`. -/
private theorem mem_factorDifferenceSet {n a b d : ℕ} (hn : n = a * b)
    (hd : (d : ℤ) = |(a : ℤ) - b|) : d ∈ factorDifferenceSet n :=
  ⟨a, b, hn, hd⟩

/-- For `n ≥ 1` every factor difference of `n` is at most `n`: if `n = a * b` with `a, b ≥ 1`
then `|a - b| ≤ max a b ≤ a * b = n`. -/
private theorem factorDifferenceSet_subset_Iic {n : ℕ} (hn : 1 ≤ n) :
    factorDifferenceSet n ⊆ Set.Iic n := by
  rintro d ⟨a, b, rfl, hd⟩
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hn)
  have hb : 1 ≤ b := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hn)
  have ha' : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  have hle : (d : ℤ) ≤ ((a * b : ℕ) : ℤ) := by
    push_cast
    rw [hd, abs_le]
    constructor <;> nlinarith
  exact Set.mem_Iic.2 (by exact_mod_cast hle)

/-- For `n ≥ 1` the factor difference set of `n` is finite. -/
private theorem factorDifferenceSet_finite {n : ℕ} (hn : 1 ≤ n) :
    (factorDifferenceSet n).Finite :=
  (Set.finite_Iic n).subset (factorDifferenceSet_subset_Iic hn)

/-- Erdős–Rosenfeld, `k = 2`: `N₁ = 12`, `N₂ = 42`, common differences `1` and `11`. -/
theorem erdos_885_k_eq_2 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 2 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2 := by
  have h1_12 : (1 : ℕ) ∈ factorDifferenceSet 12 :=
    mem_factorDifferenceSet (a := 3) (b := 4) (by norm_num) (by norm_num)
  have h11_12 : (11 : ℕ) ∈ factorDifferenceSet 12 :=
    mem_factorDifferenceSet (a := 1) (b := 12) (by norm_num) (by norm_num)
  have h1_42 : (1 : ℕ) ∈ factorDifferenceSet 42 :=
    mem_factorDifferenceSet (a := 6) (b := 7) (by norm_num) (by norm_num)
  have h11_42 : (11 : ℕ) ∈ factorDifferenceSet 42 :=
    mem_factorDifferenceSet (a := 3) (b := 14) (by norm_num) (by norm_num)
  refine ⟨{12, 42}, by decide, by decide, ?_⟩
  have hsub : ({1, 11} : Set ℕ) ⊆ ⋂ n ∈ ({12, 42} : Finset ℕ), factorDifferenceSet n := by
    refine Set.subset_iInter₂ fun n hn d hd => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hn with rfl | rfl <;> rcases hd with rfl | rfl
    exacts [h1_12, h11_12, h1_42, h11_42]
  have hfin : (⋂ n ∈ ({12, 42} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (n := 12) (by norm_num)).subset
      (Set.iInter₂_subset (12 : ℕ) (by decide))
  have hcard := Set.ncard_le_ncard hsub hfin
  rwa [Set.ncard_pair (by norm_num : (1 : ℕ) ≠ 11)] at hcard

/-- Jiménez-Urroz, `k = 3`: `112, 952, 3240`, common differences `6`, `54`, `111`. -/
theorem erdos_885_k_eq_3 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3 := by
  have h6_112 : (6 : ℕ) ∈ factorDifferenceSet 112 :=
    mem_factorDifferenceSet (a := 8) (b := 14) (by norm_num) (by norm_num)
  have h54_112 : (54 : ℕ) ∈ factorDifferenceSet 112 :=
    mem_factorDifferenceSet (a := 2) (b := 56) (by norm_num) (by norm_num)
  have h111_112 : (111 : ℕ) ∈ factorDifferenceSet 112 :=
    mem_factorDifferenceSet (a := 1) (b := 112) (by norm_num) (by norm_num)
  have h6_952 : (6 : ℕ) ∈ factorDifferenceSet 952 :=
    mem_factorDifferenceSet (a := 28) (b := 34) (by norm_num) (by norm_num)
  have h54_952 : (54 : ℕ) ∈ factorDifferenceSet 952 :=
    mem_factorDifferenceSet (a := 14) (b := 68) (by norm_num) (by norm_num)
  have h111_952 : (111 : ℕ) ∈ factorDifferenceSet 952 :=
    mem_factorDifferenceSet (a := 8) (b := 119) (by norm_num) (by norm_num)
  have h6_3240 : (6 : ℕ) ∈ factorDifferenceSet 3240 :=
    mem_factorDifferenceSet (a := 54) (b := 60) (by norm_num) (by norm_num)
  have h54_3240 : (54 : ℕ) ∈ factorDifferenceSet 3240 :=
    mem_factorDifferenceSet (a := 36) (b := 90) (by norm_num) (by norm_num)
  have h111_3240 : (111 : ℕ) ∈ factorDifferenceSet 3240 :=
    mem_factorDifferenceSet (a := 24) (b := 135) (by norm_num) (by norm_num)
  refine ⟨{112, 952, 3240}, by decide, by decide, ?_⟩
  have hsub : ({6, 54, 111} : Set ℕ) ⊆
      ⋂ n ∈ ({112, 952, 3240} : Finset ℕ), factorDifferenceSet n := by
    refine Set.subset_iInter₂ fun n hn d hd => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hn with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
    exacts [h6_112, h54_112, h111_112, h6_952, h54_952, h111_952,
      h6_3240, h54_3240, h111_3240]
  have hfin : (⋂ n ∈ ({112, 952, 3240} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (n := 112) (by norm_num)).subset
      (Set.iInter₂_subset (112 : ℕ) (by decide))
  have hcard := Set.ncard_le_ncard hsub hfin
  have h3 : ({6, 54, 111} : Set ℕ).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨6, 54, 111, by norm_num, by norm_num, by norm_num, rfl⟩
  rwa [h3] at hcard

/-- **Erdős #885, the known cases `k = 2` (Erdős–Rosenfeld) and `k = 3` (Jiménez-Urroz).**  The
case `k = 4` (Bremner) and the general question are not claimed. -/
theorem erdos_885_k_two_and_three :
    (∃ Ns : Finset ℕ, (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = 2 ∧
        (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2) ∧
      (∃ Ns : Finset ℕ, (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = 3 ∧
        (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3) :=
  ⟨erdos_885_k_eq_2, erdos_885_k_eq_3⟩
