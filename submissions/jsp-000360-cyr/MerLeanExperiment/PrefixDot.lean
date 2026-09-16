import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

namespace Erdos441

open scoped BigOperators

theorem dot_le_of_prefix_le {n : ℕ} (u v w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hanti : Antitone w)
    (hp : ∀ t : Fin n, ∑ i ∈ Finset.Iic t, u i ≤ ∑ i ∈ Finset.Iic t, v i) :
    ∑ i, u i * w i ≤ ∑ i, v i * w i := by
  induction n with
  | zero => simp
  | succ n ih =>
      let last : Fin (n + 1) := Fin.last n
      let u' : Fin n → ℝ := fun i ↦ u i.castSucc
      let v' : Fin n → ℝ := fun i ↦ v i.castSucc
      let w' : Fin n → ℝ := fun i ↦ w i.castSucc - w last
      have hw' : ∀ i, 0 ≤ w' i := by
        intro i
        exact sub_nonneg.mpr (hanti (Fin.le_last i.castSucc))
      have hanti' : Antitone w' := by
        intro i j hij
        exact sub_le_sub_right (hanti (Fin.castSucc_le_castSucc_iff.mpr hij)) _
      have hp' : ∀ t : Fin n,
          ∑ i ∈ Finset.Iic t, u' i ≤ ∑ i ∈ Finset.Iic t, v' i := by
        intro t
        have h := hp t.castSucc
        have hiic : Finset.Iic t.castSucc = (Finset.Iic t).map Fin.castSuccEmb := by
          ext i
          simp only [Finset.mem_Iic, Finset.mem_map, Fin.castSuccEmb_apply]
          constructor
          · intro hi
            have hv : i.val ≤ t.val := hi
            exact ⟨⟨i, lt_of_le_of_lt hv t.isLt⟩, Fin.mk_le_mk.mpr hv, rfl⟩
          · rintro ⟨j, hj, rfl⟩
            exact Fin.castSucc_le_castSucc_iff.mpr hj
        rw [hiic] at h
        simpa only [Finset.sum_map, Fin.castSuccEmb_apply, u', v'] using h
      have hind := ih u' v' w' hw' hanti' hp'
      have htotal : (∑ i, u i) ≤ ∑ i, v i := by
        have h := hp last
        have hiic : Finset.Iic last = Finset.univ := by
          ext i
          simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
          exact Fin.le_last i
        simpa [hiic] using h
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      change (∑ i : Fin n, u' i * w i.castSucc) + u last * w last ≤
        (∑ i : Fin n, v' i * w i.castSucc) + v last * w last
      have hwdecomp : ∀ i : Fin n, w i.castSucc = w' i + w last := by
        intro i
        dsimp [w']
        ring
      simp_rw [hwdecomp]
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hlast : 0 ≤ w last := hw last
      have htotal' :
          (∑ i : Fin n, u' i) + u last ≤ (∑ i : Fin n, v' i) + v last := by
        simpa [u', v', last, Fin.sum_univ_castSucc] using htotal
      have huMul : (∑ i : Fin n, u' i * w last) = (∑ i : Fin n, u' i) * w last :=
        (Finset.sum_mul Finset.univ u' (w last)).symm
      have hvMul : (∑ i : Fin n, v' i * w last) = (∑ i : Fin n, v' i) * w last :=
        (Finset.sum_mul Finset.univ v' (w last)).symm
      rw [huMul, hvMul]
      nlinarith [mul_le_mul_of_nonneg_right htotal' hlast]

end Erdos441
