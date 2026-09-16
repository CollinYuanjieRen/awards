import Mathlib.Tactic

namespace Erdos441

/-- Integer telescoping, including the adjacent empty interval. -/
theorem sum_Icc_backward_sub (f : ℤ → ℝ) (a b : ℤ) (hab : a ≤ b + 1) :
    ∑ i ∈ Finset.Icc a b, (f i - f (i - 1)) = f b - f (a - 1) := by
  have haux (n : ℕ) :
      ∑ i ∈ Finset.Icc a (a + n - 1), (f i - f (i - 1)) =
        f (a + n - 1) - f (a - 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have htop : a + ((n + 1 : ℕ) : ℤ) - 1 = a + n := by omega
      have hset : Finset.Icc a (a + n) =
          insert (a + n) (Finset.Icc a (a + n - 1)) := by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [htop, hset, Finset.sum_insert (by simp), ih]
      ring
  let n := (b + 1 - a).toNat
  have he : a + (n : ℤ) - 1 = b := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    ring
  simpa only [he] using haux n

theorem sum_card_sdiff_Icc (F : ℤ → Finset ℤ) (a b : ℤ) (hab : a ≤ b + 1)
    (hmono : ∀ i ∈ Finset.Icc a b, F (i - 1) ⊆ F i) :
    ∑ i ∈ Finset.Icc a b, ((F i \ F (i - 1)).card : ℝ) =
      (F b).card - (F (a - 1)).card := by
  calc
    _ = ∑ i ∈ Finset.Icc a b, ((F i).card - (F (i - 1)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h : ((F i \ F (i - 1)).card : ℝ) + (F (i - 1)).card = (F i).card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card (hmono i hi)
      linarith
    _ = _ := sum_Icc_backward_sub (fun i => ((F i).card : ℝ)) a b hab

theorem sum_Icc_zpow_mul_sub_one (q : ℝ) (hq : q ≠ 0) (a b : ℤ)
    (hab : a ≤ b + 1) :
    ∑ i ∈ Finset.Icc a b, q ^ i * (q - 1) = q ^ (b + 1) - q ^ a := by
  have h := sum_Icc_backward_sub (fun i => q ^ (i + 1)) a b hab
  simp only [sub_add_cancel] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_add_one₀ hq]
  ring

end Erdos441

#print axioms Erdos441.sum_Icc_backward_sub
#print axioms Erdos441.sum_card_sdiff_Icc
#print axioms Erdos441.sum_Icc_zpow_mul_sub_one
