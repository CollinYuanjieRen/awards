import Mathlib

/-!
# Massias's 11/32 square-sum-free construction (Erdős #438, scoped)

Massias's set consists of all integers `≡ 1,5,9,13,14,17,21,25,26,29,30 (mod 32)`.  This file shows
that such a set is square-sum-free (no two elements sum to a perfect square) and has density `11/32`
along `N = 32 q`.  Authored independently from the design certificate.
-/

namespace Erdos438

/-- the 11 residues mod 32 of Massias's construction -/
def R : Finset ℕ := {1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30}

/-- Massias's set inside `{1, …, N}`: the integers whose residue mod 32 lies in `R`. -/
def A (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun x => x % 32 ∈ R)

/-- every residue of `R` is between `1` and `30` (used for block bookkeeping). -/
private theorem R_bounds : ∀ r ∈ R, 1 ≤ r ∧ r ≤ 30 := by decide

/-- the squares mod 32: `t * t % 32` lands in `{0,1,4,9,16,17,25}` for every `t < 32`. -/
private theorem sq_res (t : ℕ) (ht : t < 32) :
    (t * t) % 32 ∈ ({0, 1, 4, 9, 16, 17, 25} : Finset ℕ) := by
  interval_cases t <;> decide

/-- no ordered pair of residues in `R` sums (mod 32) to a square residue. -/
private theorem pair_res :
    ∀ u ∈ R, ∀ v ∈ R, (u + v) % 32 ∉ ({0, 1, 4, 9, 16, 17, 25} : Finset ℕ) := by
  decide

/-- every perfect square is `≡ 0,1,4,9,16,17,25 (mod 32)` -/
theorem sq_mod_32 {m : ℕ} (h : IsSquare m) : m % 32 ∈ ({0, 1, 4, 9, 16, 17, 25} : Finset ℕ) := by
  obtain ⟨r, rfl⟩ := h
  rw [Nat.mul_mod]
  exact sq_res (r % 32) (Nat.mod_lt _ (by norm_num))

/-- the construction is square-sum-free: no two of its elements sum to a perfect square -/
theorem A_sum_not_square {N a b : ℕ} (ha : a ∈ A N) (hb : b ∈ A N) : ¬ IsSquare (a + b) := by
  intro hsq
  simp only [A, Finset.mem_filter] at ha hb
  have hasum := sq_mod_32 hsq
  rw [Nat.add_mod] at hasum
  exact pair_res _ ha.2 _ hb.2 hasum

/-- exactly 11 elements per full block of 32: the density is 11/32 along `N = 32 q` -/
theorem A_card_block (q : ℕ) : (A (32 * q)).card = 11 * q := by
  -- `A (32 q)` is the disjoint union of `q` translated copies of `R`.
  have hbij : A (32 * q)
      = (Finset.range q).biUnion (fun i => R.image (fun r => 32 * i + r)) := by
    ext x
    simp only [A, Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, hr⟩
      have hb := R_bounds _ hr
      exact ⟨x / 32, by omega, x % 32, hr, by omega⟩
    · rintro ⟨i, hi, r, hr, rfl⟩
      have hb := R_bounds _ hr
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hmod : (32 * i + r) % 32 = r := by omega
      rw [hmod]; exact hr
  have hdisj : ∀ i ∈ Finset.range q, ∀ j ∈ Finset.range q, i ≠ j →
      Disjoint (R.image (fun r => 32 * i + r)) (R.image (fun r => 32 * j + r)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [Finset.mem_image] at hxi hxj
    obtain ⟨r, hr, hrx⟩ := hxi
    obtain ⟨s, hs, hsx⟩ := hxj
    have hbr := R_bounds _ hr
    have hbs := R_bounds _ hs
    omega
  rw [hbij, Finset.card_biUnion hdisj]
  have hcard : ∀ i ∈ Finset.range q, (R.image (fun r => 32 * i + r)).card = 11 := by
    intro i _
    have hinj : Function.Injective (fun r : ℕ => 32 * i + r) := fun a b hab => by simpa using hab
    rw [Finset.card_image_of_injective _ hinj]
    decide
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]

/-- Massias's density bound: for every `N`, at least `11 ⌊N/32⌋` elements. -/
theorem A_card_ge (N : ℕ) : 11 * (N / 32) ≤ (A N).card := by
  have hsub : A (32 * (N / 32)) ⊆ A N := by
    unfold A
    apply Finset.filter_subset_filter
    exact Finset.Icc_subset_Icc_right (by omega)
  calc 11 * (N / 32) = (A (32 * (N / 32))).card := (A_card_block (N / 32)).symm
    _ ≤ (A N).card := Finset.card_le_card hsub

/-- the headline scoped statement -/
theorem massias_square_sum_free (q : ℕ) :
    (∀ a ∈ A (32 * q), ∀ b ∈ A (32 * q), ¬ IsSquare (a + b)) ∧ (A (32 * q)).card = 11 * q :=
  ⟨fun _ ha _ hb => A_sum_not_square ha hb, A_card_block q⟩

#print axioms sq_mod_32
#print axioms A_sum_not_square
#print axioms A_card_block
#print axioms A_card_ge
#print axioms massias_square_sum_free

end Erdos438
