import MerLeanExperiment.PackingCellUnion
import MerLeanExperiment.PackingBadBridge
import MerLeanExperiment.ShiftSelection
import MerLeanExperiment.ShiftProduct
import MerLeanExperiment.UniformExceptions
import MerLeanExperiment.ShortError

namespace Erdos441

theorem eventually_packing_cell_union {K : ℕ} (M : ℕ) (hM : 3 ≤ M) (hK : 2 * K ≤ M) (r : Fin K → ℤ) (hr : Function.Injective r) (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) (c0 B delta : ℝ) (hc0 : 0 < c0) (hB : 0 < B) (hdelta : 0 ≤ delta) (ε : ℝ) (hε : 0 < ε) : ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ c : Fin K → ℝ, (∀ i, c0 ≤ c i) → (∀ i, c i + delta ≤ B) → (∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤ (shiftParityWeight (r i) (r j) : ℝ) * c i * c j) → ∀ A : Finset ℕ, LcmBounded N A → ((packingCellUnion A r c delta (Real.sqrt (N : ℝ))).card : ℝ) ≤ (delta / 2 + ε) * Real.sqrt (N : ℝ) := by
  classical
  let C : ℝ := B + (shiftPairs K).card + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by
    dsimp [C]
    have : (0 : ℝ) ≤ (shiftPairs K).card := Nat.cast_nonneg _
    linarith
  have hcut : 0 < 8 * Real.log (M : ℝ) := by
    have hMr : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
    exact mul_pos (by norm_num) (Real.log_pos hMr)
  obtain ⟨Xsel, _, hsel⟩ := exists_rough_shifted_points M hM c0 hc0
  obtain ⟨Xexc, hexc⟩ := Filter.eventually_atTop.mp
    (eventually_rough_coprime_exceptions (8 * Real.log M) C hcut hC
      (ε / 2) (by positivity))
  obtain ⟨Xerr, herr⟩ := Filter.eventually_atTop.mp
    (eventually_short_interval_error K B hB.le (ε / 2) (by positivity))
  let N0 : ℕ := max 1 (max ⌈Xsel⌉₊ (max ⌈Xexc⌉₊ (max ⌈Xerr⌉₊ ⌈(2 * B) ^ 2⌉₊)))
  refine ⟨N0, le_max_left _ _, ?_⟩
  intro N hN c hc0c hcB hsep A hA
  have hN1 : 1 ≤ N := by dsimp [N0] at hN; omega
  have hNpos : 0 < N := by omega
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNsel : Xsel ≤ (N : ℝ) := (Nat.le_ceil Xsel).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hNexc : Xexc ≤ (N : ℝ) := (Nat.le_ceil Xexc).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hNerr : Xerr ≤ (N : ℝ) := (Nat.le_ceil Xerr).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hNB : (2 * B) ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  let R := Real.sqrt (N : ℝ)
  let Q := (N : ℝ) ^ (1 / 4 : ℝ)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have hR2 : R ^ 2 = (N : ℝ) := Real.sq_sqrt hx0
  have hBR : 2 * B ≤ R := by nlinarith
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hx0 _
  have hQR : Q ≤ R := by
    dsimp only [R]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hcpos (i : Fin K) : 0 < c i := hc0.trans_le (hc0c i)
  have hcB' (i : Fin K) : c i ≤ B := by have := hcB i; linarith
  obtain ⟨ell, hpoints, hrough⟩ := hsel (N : ℝ) hNsel K hK r hr hsize c hc0c
  let D := shiftProductNat M r ell
  have hDpos : 0 < D := shift_product_pos M r ell hr hsize
  have hpointsN (i : Fin K) : 0 ≤ (shiftedPoint M r ell i : ℝ) ∧
      (shiftedPoint M r ell i : ℝ) ≤ N := by
    refine ⟨(mul_pos (hcpos i) hRpos).le.trans (hpoints i).1.le, ?_⟩
    calc
      _ ≤ c i * (R + Q) := (hpoints i).2.le
      _ ≤ B * (R + Q) := mul_le_mul_of_nonneg_right (hcB' i) (by positivity)
      _ ≤ 2 * B * R := by nlinarith [mul_le_mul_of_nonneg_left hQR hB.le]
      _ ≤ (N : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hBR hR0]
  have hDsize : (D : ℝ) ≤ (N : ℝ) ^ C := by
    calc
      _ ≤ (N : ℝ) ^ (shiftPairs K).card :=
        shift_product_bound M r ell hr hsize (N : ℝ) hx0 hpointsN
      _ ≤ (N : ℝ) ^ C := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le hx1
        dsimp [C]
        linarith
  have hDrough : ∀ p ∈ D.primeFactors,
      Real.log (N : ℝ) / (8 * Real.log M) ≤ (p : ℝ) := by
    intro p hp
    exact (shift_product_rough M r ell _ hrough p hp).le
  have hfloor : (0 : ℤ) ≤ ⌊B * R⌋ := Int.floor_nonneg.mpr (by positivity)
  have hlength : ((⌊B * R⌋ - 0 : ℤ) : ℝ) ≤ C * R := by
    push_cast
    simpa only [sub_zero] using
      (Int.floor_le _).trans (mul_le_mul_of_nonneg_right hBC hR0)
  have hbadInt := hexc (N : ℝ) hNexc D hDpos hDsize hDrough 0 ⌊B * R⌋ hfloor hlength
  have hbad : ((packingBadPoints A D B R).card : ℝ) ≤ ε / 2 * R := by
    have hb := packing_bad_points_le_exceptions N A hA D B R
    have hbR : ((packingBadPoints A D B R).card : ℝ) ≤
        (((realIntIoc 0 (B * R)).filter fun n => ¬ Nat.Coprime n.natAbs D).card : ℝ) :=
      Nat.cast_le.mpr hb
    exact hbR.trans (by simpa [realIntIoc] using hbadInt)
  have hshort : (∑ i : Fin K, (c i * Q + 1)) ≤ (K : ℝ) * B * Q + K := by
    calc
      _ ≤ ∑ _i : Fin K, (B * Q + 1) := by
        apply Finset.sum_le_sum
        intro i _
        linarith [mul_le_mul_of_nonneg_right (hcB' i) hQ0]
      _ = _ := by simp; ring
  have hcount := packing_cell_union_bound M N (by omega) hNpos r ell hr hsize
    c (fun i => c i * Q) hcpos (fun i => mul_nonneg (hcpos i).le hQ0)
    delta B hdelta hcB
    (fun i => ⟨(hpoints i).1, by
      change (shiftedPoint M r ell i : ℝ) ≤
        c i * Real.sqrt (N : ℝ) + c i * (N : ℝ) ^ (1 / 4 : ℝ)
      nlinarith [(hpoints i).2]⟩)
    hsep A hA
  have herror := herr (N : ℝ) hNerr
  change ((packingCellUnion A r c delta R).card : ℝ) ≤ (delta / 2 + ε) * R
  change ((packingCellUnion A r c delta R).card : ℝ) ≤
    delta * R / 2 + (∑ i, (c i * Q + 1)) + (packingBadPoints A D B R).card at hcount
  change (K : ℝ) * B * Q + K ≤ ε / 2 * R at herror
  linarith

end Erdos441

#print axioms Erdos441.eventually_packing_cell_union
