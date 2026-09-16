import Mathlib

/-!
# Erdős Problem #291, part (ii): `gcd (a n) (L n) > 1` infinitely often

Let `L n` be the least common multiple of `1, …, n` and write `∑_{k ≤ n} 1/k = a n / L n`, so
`a n = ∑_{k ≤ n} L n / k`.  Erdős and Graham asked whether `gcd (a n) (L n) = 1` and
`gcd (a n) (L n) > 1` each occur for infinitely many `n`.  The second question was answered by
Steinerberger's observation (recorded on erdosproblems.com/291): whenever the leading base-`3`
digit of `n` is `2`, i.e. `2 · 3^j ≤ n < 3^(j+1)`, the prime `3` divides `a n`; and `3 ∣ L n` as
soon as `n ≥ 3`, so `gcd (a n) (L n) > 1` for every such `n ≥ 3` (e.g. all `n = 2 · 3^j`, `j ≥ 1`).
The first question is open and is not addressed here.

The definitions `L` and `a` and the statement are those of the formal-conjectures rendering
`Erdos291.erdos_291.parts.ii`.
-/

open Finset

/-- `L n` is the least common multiple of `{1, …, n}`. -/
def L (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm (fun x ↦ x)

/-- `a n` is defined by `∑_{1 ≤ k ≤ n} 1 / k = a n / L n`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, L n / k

/-- Sanity values, as in the formal-conjectures file. -/
theorem L_a_eval :
    L 1 = 1 ∧ L 2 = 2 ∧ L 3 = 6 ∧ L 4 = 12 ∧
      a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 11 ∧ a 4 = 25 := by
  decide

/-- Every element of `Finset.Icc 1 n` divides `L n`. -/
theorem dvd_L {m n : ℕ} (hm : m ∈ Finset.Icc 1 n) : m ∣ L n :=
  Finset.dvd_lcm hm

/-- `L n` is positive, since none of `1, …, n` vanishes. -/
theorem L_pos (n : ℕ) : 0 < L n := by
  refine Nat.pos_of_ne_zero fun h ↦ ?_
  obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h
  have hx0' : x = 0 := hx0
  rw [Finset.mem_Icc] at hx
  omega

/-- Steinerberger's observation: if `2 * 3 ^ j ≤ n < 3 ^ (j + 1)` then `3 ∣ a n`. -/
theorem three_dvd_a (j n : ℕ) (h₁ : 2 * 3 ^ j ≤ n) (h₂ : n < 3 ^ (j + 1)) : 3 ∣ a n := by
  have hp : 0 < 3 ^ j := by positivity
  have hmem₁ : 3 ^ j ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hp, by omega⟩
  have hmem₂ : 2 * 3 ^ j ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, h₁⟩
  have hne : (3 : ℕ) ^ j ≠ 2 * 3 ^ j := by omega
  have hfilter : Finset.filter (fun m ↦ 3 ^ j ∣ m) (Finset.Icc 1 n) = {3 ^ j, 2 * 3 ^ j} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hm1, hm2⟩, c, rfl⟩
      have hc : c < 3 := by
        by_contra hc
        have h3 : 3 ^ j * 3 ≤ 3 ^ j * c := Nat.mul_le_mul_left _ (by omega)
        rw [pow_succ] at h₂
        omega
      interval_cases c
      · omega
      · exact Or.inl (by ring)
      · exact Or.inr (by ring)
    · rintro (rfl | rfl)
      · exact ⟨⟨hp, by omega⟩, dvd_rfl⟩
      · exact ⟨⟨by omega, h₁⟩, dvd_mul_left _ 2⟩
  have hB : (3 : ℕ) ∣ ∑ m ∈ Finset.filter (fun m ↦ 3 ^ j ∣ m) (Finset.Icc 1 n),
      L n / m := by
    rw [hfilter, Finset.sum_pair hne]
    obtain ⟨X, hX⟩ := dvd_L hmem₂
    have e1 : L n / 3 ^ j = 2 * X := by
      rw [hX, show 2 * 3 ^ j * X = 3 ^ j * (2 * X) by ring, Nat.mul_div_cancel_left _ hp]
    have e2 : L n / (2 * 3 ^ j) = X := by
      rw [hX, Nat.mul_div_cancel_left _ (by omega)]
    rw [e1, e2]
    omega
  have hA : (3 : ℕ) ∣ ∑ m ∈ Finset.filter (fun m ↦ ¬3 ^ j ∣ m) (Finset.Icc 1 n),
      L n / m := by
    refine Finset.dvd_sum fun m hm ↦ ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hm2⟩, hmd⟩ := hm
    obtain ⟨i, t, ht, rfl⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (n := m) (by omega) 3 (by norm_num)
    have hmem : 3 ^ i * t ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hm1, hm2⟩
    have hij : i < j := by
      by_contra hij
      exact hmd ((pow_dvd_pow 3 (by omega)).trans (dvd_mul_right _ _))
    have hcop : Nat.Coprime (3 ^ (i + 1)) t :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr ht)
    have hd1 : 3 ^ (i + 1) ∣ L n := (pow_dvd_pow 3 (by omega)).trans (dvd_L hmem₁)
    have hd2 : t ∣ L n := (dvd_mul_left t (3 ^ i)).trans (dvd_L hmem)
    have hmul : 3 * (3 ^ i * t) ∣ L n := by
      have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hd1 hd2
      rwa [show 3 ^ (i + 1) * t = 3 * (3 ^ i * t) by ring] at h
    obtain ⟨Y, hY⟩ := hmul
    refine ⟨Y, ?_⟩
    rw [hY, show 3 * (3 ^ i * t) * Y = 3 ^ i * t * (3 * Y) by ring,
      Nat.mul_div_cancel_left _ hm1]
  have hsplit : ∑ m ∈ Finset.filter (fun m ↦ 3 ^ j ∣ m) (Finset.Icc 1 n), L n / m +
      ∑ m ∈ Finset.filter (fun m ↦ ¬3 ^ j ∣ m) (Finset.Icc 1 n), L n / m = a n :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  rw [← hsplit]
  exact Nat.dvd_add hB hA

/-- For `n ≥ 3`, `3 ∣ L n`. -/
theorem three_dvd_L (n : ℕ) (hn : 3 ≤ n) : 3 ∣ L n :=
  dvd_L (Finset.mem_Icc.mpr ⟨by omega, hn⟩)

/-- **Erdős Problem #291, part (ii).**  `gcd (a n) (L n) > 1` for infinitely many `n`. -/
theorem erdos_291_part_ii : {n : ℕ | Nat.gcd (a n) (L n) > 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ ↦ 2 * 3 ^ (j + 1)) ?_ ?_
  · intro x y hxy
    simp only at hxy
    have h : (3 : ℕ) ^ (x + 1) = 3 ^ (y + 1) := by omega
    have := Nat.pow_right_injective (by norm_num) h
    omega
  · intro j
    have hp : 0 < 3 ^ (j + 1) := by positivity
    have h3 : 3 ≤ 3 ^ (j + 1) := Nat.le_self_pow (by omega) 3
    have h₂ : 2 * 3 ^ (j + 1) < 3 ^ (j + 1 + 1) := by rw [pow_succ]; omega
    have hda := three_dvd_a (j + 1) (2 * 3 ^ (j + 1)) le_rfl h₂
    have hdL := three_dvd_L (2 * 3 ^ (j + 1)) (by omega)
    have hd : 3 ∣ Nat.gcd (a (2 * 3 ^ (j + 1))) (L (2 * 3 ^ (j + 1))) := Nat.dvd_gcd hda hdL
    have hpos : 0 < Nat.gcd (a (2 * 3 ^ (j + 1))) (L (2 * 3 ^ (j + 1))) :=
      Nat.gcd_pos_of_pos_right _ (L_pos _)
    have hge := Nat.le_of_dvd hpos hd
    show 1 < Nat.gcd (a (2 * 3 ^ (j + 1))) (L (2 * 3 ^ (j + 1)))
    omega

/-- The same statement as a negation (`Set.Infinite` is by definition `¬ Set.Finite`), used as the
graded root because its head symbol is a negation. -/
theorem erdos_291_part_ii_not_finite : ¬ {n : ℕ | Nat.gcd (a n) (L n) > 1}.Finite :=
  erdos_291_part_ii
