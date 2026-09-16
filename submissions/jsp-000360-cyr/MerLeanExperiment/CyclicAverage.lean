import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos441

theorem exists_cyclic_average (m k : ℕ) (hm : 0 < m) (hk : k ≤ m)
    (f : Fin m → ℝ) :
    ∃ offset : Fin m,
      Function.Injective (fun h : Fin k => offset + Fin.castLE hk h) ∧
      (k : ℝ) / m * (∑ s : Fin m, f s) ≤
        ∑ h : Fin k, f (offset + Fin.castLE hk h) := by
  classical
  let : NeZero m := ⟨by omega⟩
  have hshift (h : Fin k) :
      (∑ offset : Fin m, f (offset + Fin.castLE hk h)) = ∑ s : Fin m, f s := by
    exact Fintype.sum_equiv (Equiv.addRight (Fin.castLE hk h)) _ _ (fun _ => rfl)
  have htotal : (∑ offset : Fin m, ∑ h : Fin k, f (offset + Fin.castLE hk h)) =
      (k : ℝ) * ∑ s : Fin m, f s := by
    rw [Finset.sum_comm]
    simp_rw [hshift]
    simp
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have havg :
      (∑ _offset : Fin m, (k : ℝ) / m * (∑ s : Fin m, f s)) ≤
        ∑ offset : Fin m, ∑ h : Fin k, f (offset + Fin.castLE hk h) := by
    rw [htotal]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hmR]
    ring_nf
    exact le_rfl
  obtain ⟨offset, _, hoff⟩ := Finset.exists_le_of_sum_le
    (show (Finset.univ : Finset (Fin m)).Nonempty from ⟨⟨0, hm⟩, Finset.mem_univ _⟩) havg
  refine ⟨offset, ?_, hoff⟩
  intro i j hij
  exact Fin.castLE_injective hk (add_left_cancel hij)

end Erdos441

#print axioms Erdos441.exists_cyclic_average
