import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

namespace ReciprocalSquares

/-- Centered representatives in a bounded interval are counted without reference to the modulus. -/
theorem card_bounded_centered_frequencies (m K : ℕ) [NeZero m] :
    (Finset.univ.filter (fun h : ZMod m => h.valMinAbs.natAbs ≤ K)).card ≤ 2 * K + 1 := by
  let F := Finset.univ.filter (fun h : ZMod m => h.valMinAbs.natAbs ≤ K)
  have hsub : F.image ZMod.valMinAbs ⊆ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro z hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hz
    have hbound := (Finset.mem_filter.mp hh).2
    have habs : |h.valMinAbs| ≤ (K : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hbound
    exact Finset.mem_Icc.mpr (abs_le.mp habs)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective F ZMod.injective_valMinAbs, Int.card_Icc] at hcard
  have hid : ((K : ℤ) + 1 - -(K : ℤ)).toNat = 2 * K + 1 := by omega
  rwa [hid] at hcard

theorem centered_frequency_abs_bound (m : ℕ) [NeZero m] (h : ZMod m) :
    2 * |h.valMinAbs| ≤ (m : ℤ) := by
  have hbound := ZMod.natAbs_valMinAbs_le h
  have hnat : 2 * h.valMinAbs.natAbs ≤ m := by omega
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hnat

end ReciprocalSquares
