import Jsp285.OccurrencePivot

/-! Convert balanced occurrence masses and modular coverage into sum-tree leaf bounds. -/

namespace Jsp285

/-- Modularly diverse base occurrences and balanced pair masses give the
cardinality and interval bounds required of a sum-tree leaf. -/
theorem pair_leaf_bounds {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (B P : Finset ι) (N W H a b : ℕ)
    (hH : 0 < H) (hdisj : Disjoint B P)
    (hposP : ∀ i ∈ P, 0 < v i ∧ v i ≤ N)
    (hdivB : ∀ e : ℕ, 1 < e → e ≤ N →
      e - 1 ≤ (B.filter fun i ↦ ¬e ∣ v i).card)
    (hlower : a * W ≤ 2 * H * (∑ i ∈ P, v i))
    (hupper : H * ((∑ i ∈ B, v i) + ∑ i ∈ P, v i) ≤ 4 * b * W) :
    a * ((W / H) / 16) ≤ (occurrenceSums v (B ∪ P)).card ∧
      occurrenceSums v (B ∪ P) ⊆
        Finset.Icc 0 (40 * b * (W / H + 1)) := by
  have hcover : ∀ i ∈ P, ∀ z : ZMod (v i),
      ∃ x ∈ occurrenceSums v B, (x : ZMod (v i)) = z := by
    intro i hi z
    have hvipos := (hposP i hi).1
    let _ : NeZero (v i) := ⟨hvipos.ne'⟩
    have hmod := occurrenceSums_mod_eq_univ_of_divisor_diverse
      hvipos v B (by
        intro e he hedvd
        apply hdivB e he
        exact (Nat.le_of_dvd hvipos hedvd).trans (hposP i hi).2)
    have hz : z ∈ (occurrenceSums v B).image
        (fun x : ℕ ↦ (x : ZMod (v i))) := by
      rw [hmod]
      exact Finset.mem_univ z
    exact Finset.mem_image.mp hz
  have hpivot := card_occurrenceSums_add_pivots v B P hdisj
    (fun i hi ↦ (hposP i hi).1) hcover
  have hmassCard : (∑ i ∈ P, v i) ≤
      (occurrenceSums v (B ∪ P)).card := by
    omega
  have hquot : H * (W / H) ≤ W := Nat.mul_div_le W H
  have haquot : a * (W / H) ≤ 2 * (∑ i ∈ P, v i) := by
    have hscaled := Nat.mul_le_mul_left a hquot
    nlinarith
  have htwo : 2 * ((W / H) / 16) ≤ W / H := by
    have hsixteen := Nat.mul_div_le (W / H) 16
    omega
  have hKmass : a * ((W / H) / 16) ≤ ∑ i ∈ P, v i := by
    have hscaled := Nat.mul_le_mul_left a htwo
    nlinarith
  constructor
  · exact hKmass.trans hmassCard
  · intro x hx
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.zero_le x, ?_⟩
    have hxmass := occurrenceSum_le_mass hx
    rw [Finset.sum_union hdisj] at hxmass
    have hWlt : W < H * (W / H + 1) := Nat.lt_mul_div_succ W hH
    have htotal : (∑ i ∈ B, v i) + ∑ i ∈ P, v i ≤
        4 * b * (W / H + 1) := by
      nlinarith
    calc
      x ≤ (∑ i ∈ B, v i) + ∑ i ∈ P, v i := hxmass
      _ ≤ 4 * b * (W / H + 1) := htotal
      _ = 4 * (b * (W / H + 1)) := by ring
      _ ≤ 40 * (b * (W / H + 1)) :=
        Nat.mul_le_mul_right (b * (W / H + 1)) (by omega)
      _ = 40 * b * (W / H + 1) := by ring

end Jsp285
