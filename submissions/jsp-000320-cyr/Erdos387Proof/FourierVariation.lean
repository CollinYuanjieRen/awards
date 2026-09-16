import Erdos387Proof.FiniteAbel
import Erdos387Proof.TentFourier

/-! Finite variation of Fourier weights as the reciprocal modulus decreases. -/

namespace Erdos387Proof.FourierVariation

open scoped BigOperators
open Erdos387Proof.FiniteAbel

noncomputable def unitPhase (x : ℝ) : ℂ := Complex.exp (Complex.I * x)

@[simp] theorem norm_unitPhase (x : ℝ) : ‖unitPhase x‖ = 1 := by
  simp [unitPhase]

theorem norm_unitPhase_sub_le (x y : ℝ) :
    ‖unitPhase x - unitPhase y‖ ≤ |x - y| := by
  have hid : unitPhase x - unitPhase y =
      (unitPhase (x - y) - 1) * unitPhase y := by
    unfold unitPhase
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hid, norm_mul, norm_unitPhase, mul_one]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

noncomputable def elementaryWeight (c u : ℝ) : ℂ :=
  (u : ℂ) * unitPhase (c * u)

theorem norm_elementaryWeight (c u : ℝ) :
    ‖elementaryWeight c u‖ = |u| := by
  simp [elementaryWeight]

theorem norm_elementaryWeight_sub_le {c u v U : ℝ}
    (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ U) :
    ‖elementaryWeight c u - elementaryWeight c v‖ ≤
      (1 + |c| * U) * (u - v) := by
  have hu0 : 0 ≤ u := hv.trans hvu
  have hid : elementaryWeight c u - elementaryWeight c v =
      ((u - v : ℝ) : ℂ) * unitPhase (c * u) +
        (v : ℂ) * (unitPhase (c * u) - unitPhase (c * v)) := by
    unfold elementaryWeight
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖((u - v : ℝ) : ℂ) * unitPhase (c * u)‖ +
        ‖(v : ℂ) * (unitPhase (c * u) - unitPhase (c * v))‖ := norm_add_le _ _
    _ = (u - v) + v * ‖unitPhase (c * u) - unitPhase (c * v)‖ := by
      rw [norm_mul, norm_mul, norm_unitPhase, mul_one,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hv, abs_of_nonneg (sub_nonneg.mpr hvu)]
    _ ≤ (u - v) + v * (|c| * (u - v)) := by
      gcongr
      simpa [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr hvu)] using
        norm_unitPhase_sub_le (c * u) (c * v)
    _ ≤ (1 + |c| * U) * (u - v) := by
      have h := mul_le_mul_of_nonneg_right (hvu.trans hu)
        (mul_nonneg (abs_nonneg c) (sub_nonneg.mpr hvu))
      nlinarith

/-- A finite exponential sum, including its reciprocal-modulus prefactor. -/
noncomputable def finiteWeight {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    (u : ℝ) : ℂ := ∑ n ∈ s, (w n : ℂ) * elementaryWeight (c n) u

theorem norm_finiteWeight_le {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hw : ∀ n ∈ s, 0 ≤ w n) :
    ‖finiteWeight s w c u‖ ≤ (∑ n ∈ s, w n) * u := by
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  simp [norm_elementaryWeight, abs_of_nonneg hu, abs_of_nonneg (hw n hn)]

theorem norm_finiteWeight_sub_le {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    {u v U C : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ U)
    (hw : ∀ n ∈ s, 0 ≤ w n) (hc : ∀ n ∈ s, |c n| ≤ C) :
    ‖finiteWeight s w c u - finiteWeight s w c v‖ ≤
      (∑ n ∈ s, w n) * (1 + C * U) * (u - v) := by
  have hU : 0 ≤ U := hv.trans (hvu.trans hu)
  unfold finiteWeight
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ s, ‖(w n : ℂ) * elementaryWeight (c n) u -
        (w n : ℂ) * elementaryWeight (c n) v‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, w n * (1 + C * U) * (u - v) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw n hn)]
      calc
        _ ≤ w n * ((1 + |c n| * U) * (u - v)) :=
          mul_le_mul_of_nonneg_left (norm_elementaryWeight_sub_le hv hvu hu) (hw n hn)
        _ ≤ _ := by
          rw [mul_assoc (w n)]
          apply mul_le_mul_of_nonneg_left _ (hw n hn)
          apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hvu)
          exact add_le_add_right (mul_le_mul_of_nonneg_right (hc n hn) hU) 1
    _ = _ := by simp only [Finset.sum_mul]

/-- The total variation telescopes in `u`; the bound does not grow with the
number of moduli. Positivity of the original tent weights is retained. -/
theorem variationMass_finiteWeight_le {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    (u : ℕ → ℝ) (N : ℕ) {U C : ℝ}
    (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hu : ∀ n, 0 ≤ u n) (hmono : Antitone u) (hbound : u 0 ≤ U)
    (hw : ∀ n ∈ s, 0 ≤ w n) (hc : ∀ n ∈ s, |c n| ≤ C) :
    variationMass (fun n => finiteWeight s w c (u n)) N ≤
      (∑ n ∈ s, w n) * (2 * U + C * U ^ 2) := by
  let M := ∑ n ∈ s, w n
  have hM : 0 ≤ M := Finset.sum_nonneg hw
  have hnU (n : ℕ) : u n ≤ U := (hmono (Nat.zero_le n)).trans hbound
  have hdiff : (∑ n ∈ Finset.range (N - 1),
      ‖finiteWeight s w c (u (n + 1)) - finiteWeight s w c (u n)‖) ≤
      M * (1 + C * U) * (u 0 - u (N - 1)) := by
    calc
      _ ≤ ∑ n ∈ Finset.range (N - 1),
          M * (1 + C * U) * (u n - u (n + 1)) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_sub_rev]
        exact norm_finiteWeight_sub_le s w c (hu _) (hmono (by omega)) (hnU _) hw hc
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        induction N - 1 with
        | zero => simp
        | succ j ih => rw [Finset.sum_range_succ, ih]; ring
  have hend := norm_finiteWeight_le s w c (hu (N - 1)) hw
  change ‖finiteWeight s w c (u (N - 1))‖ + _ ≤ _
  calc
    _ ≤ M * u (N - 1) + M * (1 + C * U) * (u 0 - u (N - 1)) :=
      add_le_add hend hdiff
    _ ≤ M * U + M * (1 + C * U) * U := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hnU _) hM
      · exact mul_le_mul_of_nonneg_left (by linarith [hu (N - 1)])
          (mul_nonneg hM (by positivity))
    _ = _ := by ring

open Erdos387Proof.TentFourier

noncomputable def tentWeight (X : ℕ) (h i : ℤ) (u : ℝ) : ℂ :=
  finiteWeight (supportInterval X) (tent X)
    (fun n => 2 * Real.pi * (h : ℝ) * ((n + i : ℤ) : ℝ)) u

/-- The finite weight is the actual Fourier coefficient, including the
linear phase that appears after CRT reciprocity. -/
theorem tentWeight_inv_eq (X q : ℕ) [NeZero q] (h i : ℤ) :
    tentWeight X h i (q : ℝ)⁻¹ =
      ZMod.stdAddChar ((h : ZMod q) * (i : ZMod q)) *
        coefficient X q (h : ZMod q) := by
  unfold tentWeight finiteWeight elementaryWeight coefficient
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have heq : unitPhase
      (2 * Real.pi * (h : ℝ) * ((n + i : ℤ) : ℝ) * (q : ℝ)⁻¹) =
      ZMod.stdAddChar ((h : ZMod q) * (i : ZMod q)) *
        ZMod.stdAddChar ((h : ZMod q) * (n : ZMod q)) := by
    rw [← AddChar.map_add_eq_mul]
    rw [show (h : ZMod q) * (i : ZMod q) + (h : ZMod q) * (n : ZMod q) =
      ((h * (n + i) : ℤ) : ZMod q) by push_cast; ring]
    rw [ZMod.stdAddChar_coe]
    unfold unitPhase
    congr 1
    push_cast
    ring
  rw [heq]
  push_cast
  ring

theorem variationMass_tentWeight_le (X : ℕ) (h i : ℤ) (u : ℕ → ℝ) (N : ℕ)
    {U H : ℝ} (hX : 0 < X) (hU : 0 ≤ U) (hH : 0 ≤ H)
    (hh : |(h : ℝ)| ≤ H) (hi : |i| ≤ (X : ℤ))
    (hu : ∀ n, 0 ≤ u n) (hmono : Antitone u) (hbound : u 0 ≤ U) :
    variationMass (fun n => tentWeight X h i (u n)) N ≤
      8 * X * U + 128 * H * (X : ℝ)^2 * U^2 := by
  have hc : ∀ n ∈ supportInterval X,
      |2 * Real.pi * (h : ℝ) * ((n + i : ℤ) : ℝ)| ≤ 32 * H * X := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    change -(X : ℤ) ≤ n ∧ n ≤ 3 * (X : ℤ) - 1 at hn'
    have hi' := abs_le.mp hi
    have habs : |((n + i : ℤ) : ℝ)| ≤ 4 * (X : ℝ) := by
      rw [abs_le]
      constructor
      · exact_mod_cast (show -(4 * (X : ℤ)) ≤ n + i by omega)
      · exact_mod_cast (show n + i ≤ 4 * (X : ℤ) by omega)
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ 2 * 4 * H * (4 * X) := by
        gcongr
        exact Real.pi_lt_four.le
      _ = _ := by ring
  have hvar := variationMass_finiteWeight_le (supportInterval X) (tent X)
    (fun n => 2 * Real.pi * (h : ℝ) * ((n + i : ℤ) : ℝ)) u N hU
      (C := 32 * H * X) (by positivity) hu hmono hbound
      (fun n _ => tent_nonneg X n) hc
  apply hvar.trans
  calc
    _ ≤ (4 * X) * (2 * U + (32 * H * X) * U^2) :=
      mul_le_mul_of_nonneg_right (sum_tent_le_four_mul hX) (by positivity)
    _ = _ := by ring

theorem variationMass_tentWeight_reciprocal_le
    (X : ℕ) (h i : ℤ) (q : ℕ → ℕ) (N : ℕ) {R H : ℝ}
    (hX : 0 < X) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hh : |(h : ℝ)| ≤ H) (hi : |i| ≤ (X : ℤ))
    (hq : ∀ n, 0 < q n) (hmono : Monotone q)
    (hbound : (X : ℝ) / q 0 ≤ R) :
    variationMass (fun n => tentWeight X h i (q n : ℝ)⁻¹) N ≤
      8 * R + 128 * H * R^2 := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hu : Antitone (fun n => (q n : ℝ)⁻¹) := by
    intro a b hab
    apply inv_anti₀ (by exact_mod_cast hq a)
    exact_mod_cast hmono hab
  have hb : (q 0 : ℝ)⁻¹ ≤ R / X := by
    apply (le_div_iff₀ hXR).mpr
    simpa [div_eq_mul_inv, mul_comm] using hbound
  have hv := variationMass_tentWeight_le X h i (fun n => (q n : ℝ)⁻¹) N
    hX (U := R / X) (div_nonneg hR hXR.le) hH hh hi
    (fun n => inv_nonneg.mpr (Nat.cast_nonneg _)) hu hb
  apply hv.trans_eq
  field_simp

end Erdos387Proof.FourierVariation
