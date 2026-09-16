import Mathlib

/-! Dyadic classes of occurrence weights, preserving repeated values. -/

namespace Jsp285

/-- The occurrence indices whose weights have dyadic logarithm `j`. -/
def dyadicBin {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (j : ℕ) : Finset ι :=
  Y.filter fun i ↦ Nat.log 2 (v i) = j

/-- The weight in one dyadic bin lies between its cardinality times the lower
endpoint and twice that quantity. -/
lemma dyadicBin_weight_bounds {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (j : ℕ)
    (hpos : ∀ i ∈ Y, 0 < v i) :
    (dyadicBin v Y j).card * 2 ^ j ≤ ∑ i ∈ dyadicBin v Y j, v i ∧
      (∑ i ∈ dyadicBin v Y j, v i) ≤
        2 * ((dyadicBin v Y j).card * 2 ^ j) := by
  constructor
  · calc
      (dyadicBin v Y j).card * 2 ^ j =
          ∑ _i ∈ dyadicBin v Y j, 2 ^ j := by simp
      _ ≤ ∑ i ∈ dyadicBin v Y j, v i := by
        apply Finset.sum_le_sum
        intro i hi
        have hilog := (Finset.mem_filter.mp hi).2
        have hipos := hpos i (Finset.filter_subset _ _ hi)
        simpa [hilog] using Nat.pow_log_le_self 2 hipos.ne'
  · calc
      (∑ i ∈ dyadicBin v Y j, v i) ≤
          ∑ _i ∈ dyadicBin v Y j, 2 * 2 ^ j := by
        apply Finset.sum_le_sum
        intro i hi
        have hilog := (Finset.mem_filter.mp hi).2
        have hiupper := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (v i)
        rw [hilog, pow_succ] at hiupper
        simpa [mul_comm] using hiupper.le
      _ = 2 * ((dyadicBin v Y j).card * 2 ^ j) := by simp; ring

/-- Positive weights bounded by `N` are partitioned by their dyadic logarithms. -/
lemma sum_dyadicBins {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (N : ℕ)
    (hY : ∀ i ∈ Y, 0 < v i ∧ v i ≤ N) :
    (∑ j ∈ Finset.range (Nat.log 2 N + 1),
      ∑ i ∈ dyadicBin v Y j, v i) = ∑ i ∈ Y, v i := by
  rw [← Finset.sum_biUnion]
  · congr 1
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_range, dyadicBin,
      Finset.mem_filter]
    constructor
    · rintro ⟨j, _, hiY, _⟩
      exact hiY
    · intro hiY
      refine ⟨Nat.log 2 (v i), ?_, hiY, rfl⟩
      exact Nat.lt_succ_of_le <| Nat.log_mono_right (hY i hiY).2
  · change Set.PairwiseDisjoint
      (Finset.range (Nat.log 2 N + 1) : Set ℕ)
      (fun j ↦ Y.filter fun i ↦ Nat.log 2 (v i) = j)
    exact Set.pairwiseDisjoint_filter
      (fun i : ι ↦ Nat.log 2 (v i))
      (Finset.range (Nat.log 2 N + 1) : Set ℕ) Y

/-- Classwise balance in every dyadic weight class implies total weight balance. -/
theorem dyadic_weight_balance {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y S : Finset ι) (N a b c : ℕ)
    (hY : ∀ i ∈ Y, 0 < v i ∧ v i ≤ N) (hS : S ⊆ Y)
    (hclasses : ∀ j ∈ Finset.range (Nat.log 2 N + 1),
      a * (dyadicBin v Y j).card ≤ b * (dyadicBin v S j).card ∧
      b * (dyadicBin v S j).card ≤ c * (dyadicBin v Y j).card) :
    a * (∑ i ∈ Y, v i) ≤ 2 * b * (∑ i ∈ S, v i) ∧
      b * (∑ i ∈ S, v i) ≤ 2 * c * (∑ i ∈ Y, v i) := by
  have hSweights : ∀ i ∈ S, 0 < v i ∧ v i ≤ N := fun i hi ↦ hY i (hS hi)
  rw [← sum_dyadicBins v Y N hY, ← sum_dyadicBins v S N hSweights]
  constructor
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hYbounds := dyadicBin_weight_bounds v Y j (fun i hi ↦ (hY i hi).1)
    have hSbounds := dyadicBin_weight_bounds v S j (fun i hi ↦ (hSweights i hi).1)
    calc
      a * (∑ i ∈ dyadicBin v Y j, v i) ≤
          a * (2 * ((dyadicBin v Y j).card * 2 ^ j)) :=
        Nat.mul_le_mul_left a hYbounds.2
      _ = 2 * (a * (dyadicBin v Y j).card) * 2 ^ j := by ring
      _ ≤ 2 * (b * (dyadicBin v S j).card) * 2 ^ j :=
        Nat.mul_le_mul_right (2 ^ j) <|
          Nat.mul_le_mul_left 2 (hclasses j hj).1
      _ = 2 * b * ((dyadicBin v S j).card * 2 ^ j) := by ring
      _ ≤ 2 * b * (∑ i ∈ dyadicBin v S j, v i) :=
        Nat.mul_le_mul_left (2 * b) hSbounds.1
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hYbounds := dyadicBin_weight_bounds v Y j (fun i hi ↦ (hY i hi).1)
    have hSbounds := dyadicBin_weight_bounds v S j (fun i hi ↦ (hSweights i hi).1)
    calc
      b * (∑ i ∈ dyadicBin v S j, v i) ≤
          b * (2 * ((dyadicBin v S j).card * 2 ^ j)) :=
        Nat.mul_le_mul_left b hSbounds.2
      _ = 2 * (b * (dyadicBin v S j).card) * 2 ^ j := by ring
      _ ≤ 2 * (c * (dyadicBin v Y j).card) * 2 ^ j :=
        Nat.mul_le_mul_right (2 ^ j) <|
          Nat.mul_le_mul_left 2 (hclasses j hj).2
      _ = 2 * c * ((dyadicBin v Y j).card * 2 ^ j) := by ring
      _ ≤ 2 * c * (∑ i ∈ dyadicBin v Y j, v i) :=
        Nat.mul_le_mul_left (2 * c) hYbounds.1

end Jsp285
