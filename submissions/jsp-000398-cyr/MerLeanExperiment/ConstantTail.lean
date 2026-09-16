import MerLeanExperiment.MeanFrequency

open Set
open Classical
open scoped BigOperators

namespace Erdos492Real

noncomputable section

theorem constant_tail_sign_sum_bound (f : ℕ → ℝ) (c : ℝ) {L N : ℕ}
    (hc : c = 1 ∨ c = -1)
    (hsign : ∀ m ∈ Finset.Icc 1 N, f m = 1 ∨ f m = -1)
    (hLN : L ≤ N) (hN : 0 < N)
    (htail : ∀ m ∈ Finset.Icc (L + 1) N, f m = c) :
    1 - 2 * (L : ℝ) / N ≤
      |∑ m ∈ Finset.Icc 1 N, f m| / N := by
  classical
  let A := Finset.Icc 1 L
  let B := Finset.Icc (L + 1) N
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    simp [A, B]
    omega
  have hunion : A ∪ B = Finset.Icc 1 N := by
    ext m
    simp [A, B]
    omega
  have hcardA : A.card = L := by
    simp [A, Nat.card_Icc]
  have hcardB : B.card = N - L := by
    simp [B, Nat.card_Icc]
  have hcabs : |c| = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hcsq : c * c = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hlowA : -(L : ℝ) ≤ ∑ m ∈ A, c * f m := by
    calc
      -(L : ℝ) = ∑ _m ∈ A, (-1 : ℝ) := by simp [hcardA]
      _ ≤ ∑ m ∈ A, c * f m := by
        apply Finset.sum_le_sum
        intro m hm
        have hmN : m ∈ Finset.Icc 1 N := by
          have := Finset.mem_Icc.mp hm
          exact Finset.mem_Icc.mpr ⟨this.1, this.2.trans hLN⟩
        rcases hc with rfl | rfl <;>
          rcases hsign m hmN with hfm | hfm <;> rw [hfm] <;> norm_num
  have hsumB : (∑ m ∈ B, c * f m) = (N - L : ℕ) := by
    calc
      _ = ∑ _m ∈ B, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [htail m (by simpa [B] using hm), hcsq]
      _ = (N - L : ℕ) := by simp [hcardB]
  have htotal : (N : ℝ) - 2 * L ≤ c * ∑ m ∈ Finset.Icc 1 N, f m := by
    rw [← hunion, Finset.sum_union hdis, mul_add,
      Finset.mul_sum, Finset.mul_sum, hsumB]
    norm_num
    rw [Nat.cast_sub hLN]
    linarith
  have habs : c * ∑ m ∈ Finset.Icc 1 N, f m ≤
      |∑ m ∈ Finset.Icc 1 N, f m| := by
    calc
      c * ∑ m ∈ Finset.Icc 1 N, f m
          ≤ |c * ∑ m ∈ Finset.Icc 1 N, f m| := le_abs_self _
      _ = |∑ m ∈ Finset.Icc 1 N, f m| := by rw [abs_mul, hcabs, one_mul]
  have hmain : (N : ℝ) - 2 * L ≤ |∑ m ∈ Finset.Icc 1 N, f m| :=
    htotal.trans habs
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    1 - 2 * (L : ℝ) / N = ((N : ℝ) - 2 * L) / N := by field_simp
    _ ≤ |∑ m ∈ Finset.Icc 1 N, f m| / N :=
      div_le_div_of_nonneg_right hmain hNreal.le

theorem signedMean_abs_lower_bound_of_constant_tail (a : ℕ → ℝ) (α c : ℝ)
    {L N : ℕ} (hc : c = 1 ∨ c = -1) (hLN : L ≤ N) (hN : 0 < N)
    (htail : ∀ m ∈ Finset.Icc (L + 1) N,
      (if (m : ℝ) * α ∈ sequenceRegion a (2 : ℝ)⁻¹ then (1 : ℝ) else -1) = c) :
    1 - 2 * (L : ℝ) / N ≤ |signedMean a α N| := by
  let f : ℕ → ℝ := fun m =>
    if (m : ℝ) * α ∈ sequenceRegion a (2 : ℝ)⁻¹ then 1 else -1
  have hbound := constant_tail_sign_sum_bound f c hc (L := L) (N := N)
    (by
      intro m hm
      by_cases hm : (m : ℝ) * α ∈ sequenceRegion a (2 : ℝ)⁻¹
      · left
        simp [f, hm]
      · right
        simp [f, hm]) hLN hN (by simpa [f] using htail)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  simpa [signedMean, f, abs_div, abs_of_pos hNreal] using hbound

end

end Erdos492Real
