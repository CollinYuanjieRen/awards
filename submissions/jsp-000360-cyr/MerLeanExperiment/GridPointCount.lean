import MerLeanExperiment.GridPoints

namespace Erdos441

theorem grid_points_card (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ((gridPoints α β).card : ℤ) =
      ⌊α * β⌋ + ⌊min (α * β) (β / α - 1)⌋ + 1 := by
  let A : ℤ := ⌊α * β⌋
  let C : ℤ := ⌊min (α * β) (β / α - 1)⌋
  have hβ : 0 ≤ β := le_trans (le_of_lt hα) hαβ
  have hprod : 0 ≤ α * β := mul_nonneg (le_of_lt hα) hβ
  have hdiv : 1 ≤ β / α := (le_div_iff₀ hα).mpr (by simpa using hαβ)
  have hmin : 0 ≤ min (α * β) (β / α - 1) := by
    exact le_min hprod (by linarith)
  have hA : 0 ≤ A := by exact Int.floor_nonneg.mpr hprod
  have hC : 0 ≤ C := by exact Int.floor_nonneg.mpr hmin
  have hceil : ⌈-min (α * β) (β / α - 1)⌉ = -C := by
    simp [C, Int.ceil_neg]
  have hdis : Disjoint (Finset.Icc (1 : ℤ) A) (Finset.Icc (-C) 0) := by
    rw [Finset.disjoint_left]
    intro z hzpos hzneg
    simp only [Finset.mem_Icc] at hzpos hzneg
    omega
  have hcardA : ((Finset.Icc (1 : ℤ) A).card : ℤ) = A + 1 - 1 :=
    Int.card_Icc_of_le 1 A (by omega)
  have hcardC : ((Finset.Icc (-C) 0).card : ℤ) = 0 + 1 - (-C) :=
    Int.card_Icc_of_le (-C) 0 (by omega)
  rw [gridPoints, hceil, Finset.card_union_of_disjoint hdis]
  rw [Nat.cast_add, hcardA, hcardC]
  dsimp [A, C]
  omega

theorem grid_points_mono (α β γ : ℝ) (hα : 0 < α) (hβγ : β ≤ γ) :
    gridPoints α β ⊆ gridPoints α γ := by
  intro z hz
  rw [mem_gridPoints] at hz ⊢
  have hmul : α * β ≤ α * γ := mul_le_mul_of_nonneg_left hβγ (le_of_lt hα)
  have hdiv : β / α ≤ γ / α := div_le_div_of_nonneg_right hβγ (le_of_lt hα)
  have hmin : min (α * β) (β / α - 1) ≤ min (α * γ) (γ / α - 1) :=
    min_le_min hmul (by linarith)
  rcases hz with hz | hz
  · exact Or.inl ⟨hz.1, hz.2.trans hmul⟩
  · exact Or.inr ⟨by linarith, hz.2⟩

end Erdos441
