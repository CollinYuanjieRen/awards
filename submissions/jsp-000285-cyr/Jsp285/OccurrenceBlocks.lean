import Jsp285.FiniteMultiset
import Jsp285.InfiniteConstants

/-! Long occurrence blocks contain arithmetic progressions with small steps. -/

namespace Jsp285

/-- A linearly bounded positive occurrence sequence supplies an `L`-term AP
whose step is at most `L / 16` in the standard geometric index block. -/
theorem exists_small_step_block_AP
    (b : ℕ → ℕ) (hpos : ∀ j : ℕ, 0 < b j) (I₀ L : ℕ) (hL : 2 ≤ L)
    (hstart : I₀ ≤ finiteCoefficient * L)
    (hbound : ∀ j : ℕ, I₀ ≤ j → b j ≤ j / infiniteScale) :
    ∃ a d : ℕ, 0 < d ∧ 16 * d ≤ L ∧
      ∀ k < L, a + k * d ∈ occurrenceSums b
        (Finset.Ico (finiteCoefficient * L) (2 * finiteCoefficient * L)) := by
  let B := Finset.Ico (finiteCoefficient * L) (2 * finiteCoefficient * L)
  have hbox : ∀ j ∈ B, 0 < b j ∧ b j ≤ L := by
    intro j hj
    have hjIco := Finset.mem_Ico.mp hj
    have hjstart : I₀ ≤ j := hstart.trans hjIco.1
    have hscale : 2 * finiteCoefficient * L ≤ infiniteScale * L := by
      exact Nat.mul_le_mul_right L two_mul_finiteCoefficient_le_infiniteScale
    have hjscale : j ≤ infiniteScale * L := hjIco.2.le.trans hscale
    exact ⟨hpos j, (hbound j hjstart).trans (Nat.div_le_of_le_mul hjscale)⟩
  have hBcardEq : B.card = finiteCoefficient * L := by
    dsimp only [B]
    rw [Nat.card_Ico]
    have hrewrite : 2 * finiteCoefficient * L =
        2 * (finiteCoefficient * L) := by ring
    rw [hrewrite]
    omega
  have hBcard : finiteCoefficient * L ≤ B.card := hBcardEq.ge
  obtain ⟨a, d, hd, hterms⟩ :=
    finite_multiset_AP L (by omega) b B hbox hBcard
  let T := ∑ j ∈ B, b j
  have hDT : infiniteScale * T ≤
      2 * finiteCoefficient ^ 2 * L ^ 2 := by
    calc
      infiniteScale * T = ∑ j ∈ B, infiniteScale * b j := by
        simp only [T, Finset.mul_sum]
      _ ≤ ∑ _j ∈ B, 2 * finiteCoefficient * L := by
        apply Finset.sum_le_sum
        intro j hj
        have hjIco := Finset.mem_Ico.mp hj
        have hjstart : I₀ ≤ j := hstart.trans hjIco.1
        calc
          infiniteScale * b j ≤ infiniteScale * (j / infiniteScale) :=
            Nat.mul_le_mul_left infiniteScale (hbound j hjstart)
          _ ≤ j := Nat.mul_div_le j infiniteScale
          _ ≤ 2 * finiteCoefficient * L := hjIco.2.le
      _ = B.card * (2 * finiteCoefficient * L) := by simp
      _ = 2 * finiteCoefficient ^ 2 * L ^ 2 := by
        rw [hBcardEq]
        ring
  have hlastMem := hterms (L - 1) (by omega)
  have hlastMass := occurrenceSum_le_mass hlastMem
  have hlast : (L - 1) * d ≤ T := by
    change a + (L - 1) * d ≤ T at hlastMass
    omega
  have hLtwice : L ≤ 2 * (L - 1) := by omega
  have hfirst : L * (infiniteScale * d) ≤
      2 * infiniteScale * ((L - 1) * d) := by
    have h := Nat.mul_le_mul_right (infiniteScale * d) hLtwice
    nlinarith
  have hlastScaled : 2 * infiniteScale * ((L - 1) * d) ≤
      2 * infiniteScale * T :=
    Nat.mul_le_mul_left (2 * infiniteScale) hlast
  have hDTscaled : 2 * infiniteScale * T ≤
      4 * finiteCoefficient ^ 2 * L ^ 2 := by
    have h := Nat.mul_le_mul_left 2 hDT
    nlinarith
  have hcancelL : infiniteScale * d ≤
      4 * finiteCoefficient ^ 2 * L := by
    apply Nat.le_of_mul_le_mul_left (c := L) (hc := by omega)
    calc
      L * (infiniteScale * d) ≤ 2 * infiniteScale * ((L - 1) * d) := hfirst
      _ ≤ 2 * infiniteScale * T := hlastScaled
      _ ≤ 4 * finiteCoefficient ^ 2 * L ^ 2 := hDTscaled
      _ = L * (4 * finiteCoefficient ^ 2 * L) := by ring
  have hfactor : 0 < 4 * finiteCoefficient ^ 2 := by
    have := finiteCoefficient_pos
    positivity
  have hstep : 16 * d ≤ L := by
    refine Nat.le_of_mul_le_mul_left ?_ hfactor
    calc
      (4 * finiteCoefficient ^ 2) * (16 * d) = infiniteScale * d := by
          simp only [infiniteScale]
          ring
      _ ≤ 4 * finiteCoefficient ^ 2 * L := hcancelL
  exact ⟨a, d, hd, hstep, hterms⟩

end Jsp285
