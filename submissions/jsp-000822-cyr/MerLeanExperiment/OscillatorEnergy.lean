import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp

open Set

namespace DiskDiscrepancy

noncomputable section

/-- The positive coefficient in the rational oscillator equation. -/
abbrev oscillatorCoeff (t : ℝ) : ℝ :=
  1 + 1 / (4 * t ^ 2)

/-- The decreasing energy for the rational oscillator. -/
abbrev oscillatorUpperEnergy (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  oscillatorCoeff t * u t ^ 2 + v t ^ 2

/-- The increasing energy for the rational oscillator. -/
abbrev oscillatorLowerEnergy (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  u t ^ 2 + v t ^ 2 / oscillatorCoeff t

/-- The rational oscillator coefficient is at least one away from zero. -/
theorem one_le_oscillatorCoeff {t : ℝ} (_ht : t ≠ 0) : 1 ≤ oscillatorCoeff t := by
  unfold oscillatorCoeff
  have hden : 0 ≤ 4 * t ^ 2 := mul_nonneg (by norm_num) (sq_nonneg t)
  have hinv : 0 ≤ 1 / (4 * t ^ 2) := div_nonneg zero_le_one hden
  linarith

/-- Energy bounds for a solution of `u' = v`, `v' = -q u` on the positive half-line.

This is a generic calculus lemma. Its differential-equation hypotheses must be instantiated by
the concrete angular kernel before it is used in a final disk-discrepancy theorem. -/
theorem oscillator_energy_bounds {u v : ℝ → ℝ}
    (hu : ∀ t : ℝ, 0 < t → HasDerivAt u (v t) t)
    (hv : ∀ t : ℝ, 0 < t → HasDerivAt v (-oscillatorCoeff t * u t) t)
    (hu_lower : 1 / 4 ≤ u 1 ^ 2) (hu_upper : u 1 ^ 2 ≤ 1)
    (hv_upper : v 1 ^ 2 ≤ 9 / 4) :
    ∀ t : ℝ, 1 ≤ t → 1 / 4 ≤ u t ^ 2 + v t ^ 2 ∧
      u t ^ 2 + v t ^ 2 ≤ 7 / 2 := by
  have hq_deriv : ∀ t : ℝ, 0 < t →
      HasDerivAt oscillatorCoeff (-1 / (2 * t ^ 3)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.ne'
    have hsq : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_id t).fun_pow 2
    have hinv := hsq.inv (pow_ne_zero 2 ht0)
    have hscaled := (hasDerivAt_const t (1 / 4 : ℝ)).mul hinv
    have hsum := (hasDerivAt_const t (1 : ℝ)).add hscaled
    rw [show oscillatorCoeff =
      (fun x : ℝ ↦ 1) + (fun x : ℝ ↦ 1 / 4) * (fun s : ℝ ↦ s ^ 2)⁻¹ by
        funext s
        simp [oscillatorCoeff, div_eq_mul_inv, mul_comm]]
    apply hsum.congr_deriv
    field_simp [ht0]
    ring
  have hH_deriv : ∀ t : ℝ, 0 < t → HasDerivAt
      (oscillatorUpperEnergy u v) (-u t ^ 2 / (2 * t ^ 3)) t := by
    intro t ht
    have hq := hq_deriv t ht
    have hu_t := hu t ht
    have hv_t := hv t ht
    have hraw := (hq.mul (hu_t.fun_pow 2)).add (hv_t.fun_pow 2)
    rw [show oscillatorUpperEnergy u v =
      oscillatorCoeff * (fun s ↦ u s ^ 2) + (fun s ↦ v s ^ 2) by
        funext s
        rfl]
    apply hraw.congr_deriv
    field_simp [ht.ne']
    ring
  have hG_deriv : ∀ t : ℝ, 0 < t → HasDerivAt
      (oscillatorLowerEnergy u v)
        (v t ^ 2 / (2 * t ^ 3 * oscillatorCoeff t ^ 2)) t := by
    intro t ht
    have hq := hq_deriv t ht
    have hu_t := hu t ht
    have hv_t := hv t ht
    have hq0 : oscillatorCoeff t ≠ 0 := by
      have := one_le_oscillatorCoeff ht.ne'
      positivity
    have hraw := (hu_t.fun_pow 2).add ((hv_t.fun_pow 2).div hq hq0)
    rw [show oscillatorLowerEnergy u v =
      (fun s ↦ u s ^ 2) + (fun s ↦ v s ^ 2) / oscillatorCoeff by
        funext s
        rfl]
    apply hraw.congr_deriv
    field_simp [oscillatorCoeff, ht.ne', hq0]
    ring
  have hH_anti : AntitoneOn (oscillatorUpperEnergy u v) (Ici 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (D := Ici 1) (convex_Ici 1)
    · intro t ht
      exact (hH_deriv t (lt_of_lt_of_le one_pos ht)).continuousAt.continuousWithinAt
    · intro t ht
      have ht_pos : 0 < t := by
        have : 1 < t := by simpa only [interior_Ici, mem_Ioi] using ht
        linarith
      exact (hH_deriv t ht_pos).hasDerivWithinAt
    · intro t ht
      have ht_pos : 0 < t := by
        have : 1 < t := by simpa only [interior_Ici, mem_Ioi] using ht
        linarith
      apply div_nonpos_of_nonpos_of_nonneg
      · exact neg_nonpos.mpr (sq_nonneg _)
      · positivity
  have hG_mono : MonotoneOn (oscillatorLowerEnergy u v) (Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (D := Ici 1) (convex_Ici 1)
    · intro t ht
      exact (hG_deriv t (lt_of_lt_of_le one_pos ht)).continuousAt.continuousWithinAt
    · intro t ht
      have ht_pos : 0 < t := by
        have : 1 < t := by simpa only [interior_Ici, mem_Ioi] using ht
        linarith
      exact (hG_deriv t ht_pos).hasDerivWithinAt
    · intro t ht
      have ht_pos : 0 < t := by
        have : 1 < t := by simpa only [interior_Ici, mem_Ioi] using ht
        linarith
      positivity
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos ht)
  have hq : 1 ≤ oscillatorCoeff t := one_le_oscillatorCoeff ht0
  have hG_le : oscillatorLowerEnergy u v t ≤ u t ^ 2 + v t ^ 2 := by
    unfold oscillatorLowerEnergy
    have hq_pos : 0 < oscillatorCoeff t := lt_of_lt_of_le zero_lt_one hq
    have := div_le_self (sq_nonneg (v t)) hq
    linarith
  have hE_le : u t ^ 2 + v t ^ 2 ≤ oscillatorUpperEnergy u v t := by
    unfold oscillatorUpperEnergy
    nlinarith [sq_nonneg (u t)]
  have hG1 : 1 / 4 ≤ oscillatorLowerEnergy u v 1 := by
    unfold oscillatorLowerEnergy
    have hnonneg : 0 ≤ v 1 ^ 2 / oscillatorCoeff 1 := by
      unfold oscillatorCoeff
      positivity
    linarith
  have hH1 : oscillatorUpperEnergy u v 1 ≤ 7 / 2 := by
    norm_num [oscillatorUpperEnergy, oscillatorCoeff]
    linarith
  constructor
  · exact hG1.trans ((hG_mono (by simp) ht ht).trans hG_le)
  · exact hE_le.trans ((hH_anti (by simp) ht ht).trans hH1)

end

end DiskDiscrepancy
