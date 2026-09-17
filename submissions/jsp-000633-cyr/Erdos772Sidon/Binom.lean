import Erdos772Sidon.Definitions

/-! Binomial estimates for the averaging argument. -/

namespace Erdos772

/-- Arithmetic skeleton of the inductive step of `choose_sub_mul_pow_le`. -/
private theorem pow_succ_step {C P Q X Y u v j : ℕ} (hu : 0 < u) (key : u * P = Q * v)
    (IH : Q * X ^ j ≤ C * Y ^ j) (hle : v * X ≤ Y * u) :
    P * X ^ (j + 1) ≤ C * Y ^ (j + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ hu
  calc P * X ^ (j + 1) * u = u * P * (X ^ j * X) := by ring
    _ = Q * v * (X ^ j * X) := by rw [key]
    _ = Q * X ^ j * (v * X) := by ring
    _ ≤ C * Y ^ j * (Y * u) := Nat.mul_le_mul IH hle
    _ = C * Y ^ (j + 1) * u := by ring

private theorem sub_mul_le_mul_sub {j s n : ℕ} (hj : j ≤ s) (hs : s ≤ n) :
    (s - j) * n ≤ s * (n - j) := by
  obtain ⟨p, hp⟩ : ∃ p, n = p + j := ⟨n - j, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, s = q + j := ⟨s - j, by omega⟩
  subst hp
  subst hq
  have hqp : q ≤ p := by omega
  simp only [Nat.add_sub_cancel]
  nlinarith

private theorem choose_sub_mul_pow_le_aux (n s : ℕ) (hs : s ≤ n) :
    ∀ j, j ≤ s → (n - j).choose (s - j) * n ^ j ≤ n.choose s * s ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    have IH := ih (Nat.le_of_succ_le hj)
    have hA : n - (j + 1) + 1 = n - j := by omega
    have hB : s - (j + 1) + 1 = s - j := by omega
    have key : (n - j) * (n - (j + 1)).choose (s - (j + 1))
        = (n - j).choose (s - j) * (s - j) := by
      have h := Nat.add_one_mul_choose_eq (n - (j + 1)) (s - (j + 1))
      rw [hA, hB] at h
      exact h
    exact pow_succ_step (by omega) key IH (sub_mul_le_mul_sub (by omega) hs)

theorem choose_sub_mul_pow_le (n s j : ℕ) (hj : j ≤ s) (hs : s ≤ n) :
    (n - j).choose (s - j) * n ^ j ≤ n.choose s * s ^ j :=
  choose_sub_mul_pow_le_aux n s hs j hj

theorem choose_four_le_three (n s : ℕ) (hs : s ≤ n) :
    (n - 4).choose (s - 4) ≤ (n - 3).choose (s - 3) := by
  rcases Nat.lt_or_ge s 4 with h | h
  · have e1 : s - 4 = 0 := by omega
    rw [e1, Nat.choose_zero_right]
    exact Nat.choose_pos (by omega)
  · have e1 : n - 3 = (n - 4) + 1 := by omega
    have e2 : s - 3 = (s - 4) + 1 := by omega
    rw [e1, e2, Nat.choose_succ_succ']
    exact Nat.le_add_right _ _

theorem card_powersetCard_filter_subset_le (A T : Finset ℕ) (hT : T ⊆ A) (s : ℕ) :
    ((A.powersetCard s).filter (fun S => T ⊆ S)).card ≤ (A.card - T.card).choose (s - T.card) := by
  classical
  have hcard : ((A \ T).powersetCard (s - T.card)).card
      = (A.card - T.card).choose (s - T.card) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hT]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun S => S \ T) ?_ ?_
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨hSA, hScard⟩, hTS⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff hSA (Finset.Subset.refl T), ?_⟩
    rw [Finset.card_sdiff_of_subset hTS, hScard]
  · intro S₁ h₁ S₂ h₂ h
    simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    have e₁ := Finset.sdiff_union_of_subset h₁.2
    have e₂ := Finset.sdiff_union_of_subset h₂.2
    simp only at h
    rw [← e₁, ← e₂, h]

end Erdos772
