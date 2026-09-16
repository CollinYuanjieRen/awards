import MerLeanExperiment.ShiftAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.PrimeFin

namespace Erdos441

theorem shift_product_pos {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) :
    0 < shiftProductNat M r ell := by
  apply Int.natAbs_pos.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro ij hij
  have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
  exact shift_factor_ne_zero M r ell hr hsize ij.1 ij.2 (ne_of_lt hlt)

theorem shift_product_rough {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) (z : ℝ)
    (hrough : ∀ i j, i < j → ∀ p : ℕ, p.Prime →
      (p : ℤ) ∣ shiftFactor M r ell i j → z < (p : ℝ)) :
    ∀ p ∈ (shiftProductNat M r ell).primeFactors, z < (p : ℝ) := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  let : Fact p.Prime := ⟨hprime⟩
  have hn : p ∣ (shiftProduct M r ell).natAbs := Nat.dvd_of_mem_primeFactors hp
  have hdiv : (p : ℤ) ∣ shiftProduct M r ell := Int.natCast_dvd.mpr hn
  have hz : ∏ ij ∈ shiftPairs K, (shiftFactor M r ell ij.1 ij.2 : ZMod p) = 0 := by
    simpa [shiftProduct] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (shiftProduct M r ell) p).mpr hdiv
  obtain ⟨ij, hij, hf⟩ := Finset.prod_eq_zero_iff.mp hz
  have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
  exact hrough ij.1 ij.2 hlt p hprime
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hf)

theorem shift_product_bound {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (Y : ℝ) (_hY : 0 ≤ Y)
    (hpoints : ∀ i, 0 ≤ (shiftedPoint M r ell i : ℝ) ∧
      (shiftedPoint M r ell i : ℝ) ≤ Y) :
    (shiftProductNat M r ell : ℝ) ≤ Y ^ (shiftPairs K).card := by
  have hfactor (ij : Fin K × Fin K) (hij : ij ∈ shiftPairs K) :
      ((shiftFactor M r ell ij.1 ij.2).natAbs : ℝ) ≤ Y := by
    have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
    have hd : r ij.2 - r ij.1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => (ne_of_lt hlt) (hr h).symm)
    have hdp : 0 < (r ij.2 - r ij.1).natAbs := Int.natAbs_pos.mpr hd
    have heq := shift_factor_mul_difference M r ell ij.1 ij.2 hd
      (hsize ij.1 ij.2 (ne_of_lt hlt))
    have hnat : (shiftFactor M r ell ij.1 ij.2).natAbs ≤
        (shiftedPoint M r ell ij.2 - shiftedPoint M r ell ij.1).natAbs := by
      calc
        _ ≤ (r ij.2 - r ij.1).natAbs * (shiftFactor M r ell ij.1 ij.2).natAbs := by
          exact Nat.le_mul_of_pos_left _ hdp
        _ = _ := by rw [← Int.natAbs_mul, heq]
    have hdiff : ((shiftedPoint M r ell ij.2 - shiftedPoint M r ell ij.1).natAbs : ℝ) ≤ Y := by
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, abs_le]
      have hi := hpoints ij.1
      have hj := hpoints ij.2
      constructor <;> linarith
    exact (Nat.cast_le.mpr hnat).trans hdiff
  calc
    (shiftProductNat M r ell : ℝ) =
        ∏ ij ∈ shiftPairs K, ((shiftFactor M r ell ij.1 ij.2).natAbs : ℝ) := by
      simp [shiftProductNat, shiftProduct, Finset.abs_prod]
    _ ≤ ∏ _ij ∈ shiftPairs K, Y :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) hfactor
    _ = Y ^ (shiftPairs K).card := by simp

end Erdos441

#print axioms Erdos441.shift_product_pos
#print axioms Erdos441.shift_product_rough
#print axioms Erdos441.shift_product_bound
