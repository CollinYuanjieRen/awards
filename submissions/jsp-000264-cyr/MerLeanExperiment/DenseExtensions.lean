import Mathlib

namespace ReciprocalSquares

open scoped BigOperators

/-- Elements outside a base which extend it to a member of the given family. -/
def extensions {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (G : Finset (Finset ι)) (A : Finset ι) : Finset ι :=
  (F \ A).filter fun q => insert q A ∈ G

/-- Extension elements are in bijection with containing members of the family. -/
theorem extensions_card_eq {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (G : Finset (Finset ι)) (A : Finset ι) (r : ℕ)
    (hA : A ∈ F.powersetCard r)
    (hG : G ⊆ F.powersetCard (r + 1)) :
    (extensions F G A).card = (G.filter fun B => A ⊆ B).card := by
  apply Finset.card_bij (fun q _ => insert q A)
  · intro q hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).2, Finset.subset_insert _ _⟩
  · intro q hq q' hq' heq
    have hqnot : q ∉ A := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq).1).2
    exact (Finset.insert_inj hqnot).mp heq
  · intro B hB
    obtain ⟨hBG, hAB⟩ := Finset.mem_filter.mp hB
    have hBcard := (Finset.mem_powersetCard.mp (hG hBG)).2
    have hAcard := (Finset.mem_powersetCard.mp hA).2
    obtain ⟨q, hqnot, heq⟩ := Finset.exists_eq_insert_iff.mpr
      (show A ⊆ B ∧ A.card + 1 = B.card from ⟨hAB, by omega⟩)
    have hqB : q ∈ B := heq ▸ Finset.mem_insert_self q A
    have hqF : q ∈ F := (Finset.mem_powersetCard.mp (hG hBG)).1 hqB
    refine ⟨q, ?_, heq⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_sdiff.mpr ⟨hqF, hqnot⟩, heq.symm ▸ hBG⟩

/-- Exact incidence count between bases and their one-element extensions. -/
theorem sum_extensions_card {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (G : Finset (Finset ι)) (r : ℕ)
    (hG : G ⊆ F.powersetCard (r + 1)) :
    (∑ A ∈ F.powersetCard r, (extensions F G A).card) = (r + 1) * G.card := by
  have hfilter : ∀ B ∈ G,
      ((F.powersetCard r).filter fun A => A ⊆ B) = B.powersetCard r := by
    intro B hB
    have hBF := (Finset.mem_powersetCard.mp (hG hB)).1
    ext A
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hAF, hAc⟩, hAB⟩
      exact ⟨hAB, hAc⟩
    · rintro ⟨hAB, hAc⟩
      exact ⟨⟨hAB.trans hBF, hAc⟩, hAB⟩
  calc
    (∑ A ∈ F.powersetCard r, (extensions F G A).card) =
        ∑ A ∈ F.powersetCard r, (G.filter fun B => A ⊆ B).card := by
      apply Finset.sum_congr rfl
      intro A hA
      exact extensions_card_eq F G A r hA hG
    _ = ∑ B ∈ G, ((F.powersetCard r).filter fun A => A ⊆ B).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun A B : Finset ι => A ⊆ B)
    _ = ∑ _B ∈ G, (r + 1) := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [hfilter B hB, Finset.card_powersetCard,
        (Finset.mem_powersetCard.mp (hG hB)).2, Nat.choose_succ_self_right]
    _ = (r + 1) * G.card := by simp [mul_comm]

/-- A dense family of uniform subsets has a base with a proportionally dense
extension set. The weights may be zero; only existence of a base is required. -/
theorem exists_dense_extensions
    {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (G : Finset (Finset ι)) (r u v : ℕ)
    (hr : r < F.card)
    (hG : G ⊆ F.powersetCard (r + 1))
    (hdensity : u * (F.powersetCard (r + 1)).card ≤ v * G.card) :
    ∃ A ∈ F.powersetCard r,
      u * (F.card - r) ≤ v * (extensions F G A).card := by
  have hnonempty : (F.powersetCard r).Nonempty := Finset.powersetCard_nonempty.mpr hr.le
  have hfull : (F.powersetCard r).card * (F.card - r) =
      (r + 1) * (F.powersetCard (r + 1)).card := by
    rw [Finset.card_powersetCard, Finset.card_powersetCard]
    simpa only [mul_comm] using (Nat.choose_succ_right_eq F.card r).symm
  by_contra h
  push Not at h
  have hlt := Finset.sum_lt_sum_of_nonempty hnonempty (fun A hA => h A hA)
  rw [← Finset.mul_sum, sum_extensions_card F G r hG] at hlt
  simp only [Finset.sum_const, smul_eq_mul] at hlt
  have hrhs : (F.powersetCard r).card * (u * (F.card - r)) =
      (r + 1) * (u * (F.powersetCard (r + 1)).card) := by
    calc
      (F.powersetCard r).card * (u * (F.card - r)) =
          u * ((F.powersetCard r).card * (F.card - r)) := by ring
      _ = u * ((r + 1) * (F.powersetCard (r + 1)).card) := by rw [hfull]
      _ = _ := by ring
  rw [hrhs] at hlt
  have hbound : (r + 1) * (u * (F.powersetCard (r + 1)).card) ≤
      v * ((r + 1) * G.card) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left (r + 1) hdensity
  exact (not_lt_of_ge hbound) hlt

end ReciprocalSquares
