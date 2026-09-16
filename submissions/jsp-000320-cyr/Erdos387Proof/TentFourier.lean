import Mathlib
import Waring.Analytic.FourierCoefficientSum

/-!
# A finite tent weight and its exact Fourier expansion

The integer intervals may be longer than the Fourier modulus. All identities
use finite sums, so no analytic summation or limiting argument is assumed.
-/

namespace Erdos387Proof.TentFourier

open scoped BigOperators

noncomputable def leftInterval (X : ℕ) : Finset ℤ :=
  Finset.Icc (-(X : ℤ)) (2 * (X : ℤ))

noncomputable def rightInterval (X : ℕ) : Finset ℤ :=
  Finset.Icc 0 ((X : ℤ) - 1)

noncomputable def supportInterval (X : ℕ) : Finset ℤ :=
  Finset.Icc (-(X : ℤ)) (3 * (X : ℤ) - 1)

/-- The normalized convolution of the two integer interval indicators. -/
noncomputable def tent (X : ℕ) (n : ℤ) : ℝ :=
  (X : ℝ)⁻¹ * ∑ j ∈ rightInterval X,
    if n - j ∈ leftInterval X then (1 : ℝ) else 0

theorem card_rightInterval (X : ℕ) : (rightInterval X).card = X := by
  simp only [rightInterval, Int.card_Icc]
  omega

theorem card_leftInterval (X : ℕ) :
    (leftInterval X).card = 3 * X + 1 := by
  simp only [leftInterval, Int.card_Icc]
  omega

theorem tent_nonneg (X : ℕ) (n : ℤ) : 0 ≤ tent X n := by
  unfold tent
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro j _
  split <;> positivity

theorem tent_eq_one {X : ℕ} (hX : 0 < X) {n : ℤ}
    (hn0 : 0 ≤ n) (hnX : n ≤ X) : tent X n = 1 := by
  have hmem : ∀ j ∈ rightInterval X, n - j ∈ leftInterval X := by
    intro j hj
    simp only [rightInterval, Finset.mem_Icc] at hj
    simp only [leftInterval, Finset.mem_Icc]
    omega
  simp only [tent, Finset.sum_congr rfl (fun j hj => if_pos (hmem j hj)),
    Finset.sum_const, nsmul_eq_mul, mul_one, card_rightInterval]
  exact inv_mul_cancel₀ (by exact_mod_cast hX.ne')

theorem add_mem_support {X : ℕ} {i j : ℤ}
    (hi : i ∈ leftInterval X) (hj : j ∈ rightInterval X) :
    i + j ∈ supportInterval X := by
  simp only [leftInterval, rightInterval, supportInterval, Finset.mem_Icc] at *
  omega

theorem tent_eq_zero_of_not_mem {X : ℕ} {n : ℤ}
    (hn : n ∉ supportInterval X) : tent X n = 0 := by
  unfold tent
  have hzero : ∀ j ∈ rightInterval X, n - j ∉ leftInterval X := by
    intro j hj hi
    have := add_mem_support hi hj
    simp only [sub_add_cancel] at this
    exact hn this
  simp only [Finset.sum_congr rfl (fun j hj => if_neg (hzero j hj)),
    Finset.sum_const_zero, mul_zero]

/-- Translation of one convolution fibre, valid for any additive target. -/
theorem sum_indicator_sub {R : Type*} [AddCommMonoid R]
    (X : ℕ) (f : ℤ → R) {j : ℤ} (hj : j ∈ rightInterval X) :
    (∑ n ∈ supportInterval X,
      if n - j ∈ leftInterval X then f n else 0) =
      ∑ i ∈ leftInterval X, f (i + j) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun n _ => n - j)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro a _ b _ hab
    omega
  · intro i hi
    refine ⟨i + j, ?_, by omega⟩
    simp only [Finset.mem_filter, add_sub_cancel_right]
    exact ⟨add_mem_support hi hj, hi⟩
  · intro n _
    simp

/-- Total mass of the real tent, over its explicit finite support. -/
theorem sum_tent {X : ℕ} (hX : 0 < X) :
    (∑ n ∈ supportInterval X, tent X n) = 3 * (X : ℝ) + 1 := by
  unfold tent
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ j ∈ rightInterval X,
      (∑ n ∈ supportInterval X,
        if n - j ∈ leftInterval X then (1 : ℝ) else 0) =
        ((leftInterval X).card : ℝ) := by
    intro j hj
    simpa using sum_indicator_sub X (fun _ => (1 : ℝ)) hj
  simp_rw [Finset.sum_congr rfl hinner]
  simp only [Finset.sum_const, nsmul_eq_mul, card_rightInterval, card_leftInterval]
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  push_cast
  field_simp

theorem sum_tent_le_four_mul {X : ℕ} (hX : 0 < X) :
    (∑ n ∈ supportInterval X, tent X n) ≤ 4 * (X : ℝ) := by
  rw [sum_tent hX]
  have : (1 : ℝ) ≤ X := by exact_mod_cast hX
  linarith

/-- Push any complex test function through the finite convolution. -/
theorem sum_tent_mul (X : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ supportInterval X, (tent X n : ℂ) * f n) =
      (X : ℂ)⁻¹ * ∑ j ∈ rightInterval X,
        ∑ i ∈ leftInterval X, f (i + j) := by
  unfold tent
  push_cast
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero,
    ite_mul, one_mul, zero_mul] using sum_indicator_sub X f hj

/-- Positive-sign Fourier coefficient of a finite integer set. -/
noncomputable def intervalCoefficient (q : ℕ) [NeZero q]
    (s : Finset ℤ) (h : ZMod q) : ℂ :=
  ∑ n ∈ s, ZMod.stdAddChar (h * (n : ZMod q))

/-- Normalized Fourier coefficient of the periodized tent. -/
noncomputable def coefficient (X q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ n ∈ supportInterval X,
    (tent X n : ℂ) * ZMod.stdAddChar (h * (n : ZMod q))

theorem coefficient_eq_product (X q : ℕ) [NeZero q] (h : ZMod q) :
    coefficient X q h =
      intervalCoefficient q (leftInterval X) h *
        intervalCoefficient q (rightInterval X) h / ((X : ℂ) * (q : ℂ)) := by
  rw [coefficient, sum_tent_mul]
  have hexp :
      (∑ j ∈ rightInterval X, ∑ i ∈ leftInterval X,
        ZMod.stdAddChar (h * ((i + j : ℤ) : ZMod q))) =
        intervalCoefficient q (leftInterval X) h *
          intervalCoefficient q (rightInterval X) h := by
    simp only [intervalCoefficient, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [← AddChar.map_add_eq_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem coefficient_zero {X : ℕ} (hX : 0 < X) (q : ℕ) [NeZero q] :
    coefficient X q 0 = (3 * (X : ℂ) + 1) / (q : ℂ) := by
  unfold coefficient
  simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (sum_tent hX)
  push_cast at h
  rw [h]
  ring

/-- The finite weighted mass in one progression. -/
noncomputable def progressionMass (X q : ℕ) [NeZero q] (a : ZMod q) : ℝ :=
  ∑ n ∈ supportInterval X, if (n : ZMod q) = a then tent X n else 0

/-- Exact finite Fourier inversion, with no interval-length restriction. -/
theorem progressionMass_eq_fourier (X q : ℕ) [NeZero q] (a : ZMod q) :
    (progressionMass X q a : ℂ) =
      ∑ h : ZMod q, ZMod.stdAddChar (-h * a) * coefficient X q h := by
  classical
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have horth : ∀ n : ℤ,
      (∑ h : ZMod q, ZMod.stdAddChar (h * ((n : ZMod q) - a))) =
        if (n : ZMod q) = a then (q : ℂ) else 0 := by
    intro n
    simpa only [sub_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
      AddChar.sum_mulShift ((n : ZMod q) - a) (ZMod.isPrimitive_stdAddChar q)
  symm
  calc
    _ = (q : ℂ)⁻¹ * ∑ n ∈ supportInterval X,
        (tent X n : ℂ) * ∑ h : ZMod q,
          ZMod.stdAddChar (h * ((n : ZMod q) - a)) := by
      simp only [coefficient, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro h hh
      rw [show h * ((n : ZMod q) - a) = -h * a + h * (n : ZMod q) by ring,
        AddChar.map_add_eq_mul]
      ring
    _ = progressionMass X q a := by
      simp_rw [horth]
      rw [Finset.mul_sum]
      unfold progressionMass
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      by_cases ha : (n : ZMod q) = a
      · simp only [ha, if_true]
        field_simp
      · simp [ha]

/-- The geometric estimate is independent of the interval length. -/
theorem norm_intervalCoefficient_Ioc_le {q : ℕ} [NeZero q]
    (A : ℤ) (m : ℕ) {h : ZMod q} (hh : h ≠ 0) :
    ‖intervalCoefficient q (Finset.Ioc A (A + m)) h‖ ≤
      (q : ℝ) / (2 * (h.valMinAbs.natAbs : ℝ)) := by
  have heq : intervalCoefficient q (Finset.Ioc A (A + m)) h =
      Waring.Analytic.intervalFourierCoefficient A m (-h) := by
    unfold intervalCoefficient Waring.Analytic.intervalFourierCoefficient
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    ring
  rw [heq]
  simpa using Waring.Analytic.norm_intervalFourierCoefficient_le_leastResidue
    A m (neg_ne_zero.mpr hh)

/-- Quadratic decay of the normalized tent coefficients. -/
theorem norm_coefficient_le {X q : ℕ} [NeZero q] (hX : 0 < X)
    {h : ZMod q} (hh : h ≠ 0) :
    ‖coefficient X q h‖ ≤
      (q : ℝ) / (4 * X * (h.valMinAbs.natAbs : ℝ) ^ 2) := by
  have hleft : leftInterval X =
      Finset.Ioc (-(X : ℤ) - 1) (-(X : ℤ) - 1 + (3 * X + 1 : ℕ)) := by
    ext n
    simp only [leftInterval, Finset.mem_Icc, Finset.mem_Ioc]
    push_cast
    omega
  have hright : rightInterval X = Finset.Ioc (-1 : ℤ) (-1 + (X : ℤ)) := by
    ext n
    simp only [rightInterval, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hl := norm_intervalCoefficient_Ioc_le (-(X : ℤ) - 1) (3 * X + 1) hh
  have hr := norm_intervalCoefficient_Ioc_le (-1) X hh
  rw [← hleft] at hl
  rw [← hright] at hr
  rw [coefficient_eq_product, norm_div, norm_mul, norm_mul,
    Complex.norm_natCast, Complex.norm_natCast]
  calc
    _ ≤ ((q : ℝ) / (2 * (h.valMinAbs.natAbs : ℝ))) *
        ((q : ℝ) / (2 * (h.valMinAbs.natAbs : ℝ))) / (X * q) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul hl hr (norm_nonneg _) (by positivity)) (by positivity)
    _ = _ := by
      have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
      field_simp
      ring

/-- Summable quadratic decay gives a tail bound uniform in the modulus.
In particular it also covers an empty tail when `H ≥ q / 2`. -/
theorem sum_norm_coefficient_tail_le {X q : ℕ} [NeZero q]
    (hX : 0 < X) {H : ℕ} (hH : 0 < H) :
    (∑ h : ZMod q with H < h.valMinAbs.natAbs, ‖coefficient X q h‖) ≤
      (q : ℝ) / (2 * X * H) := by
  classical
  let T := (Finset.univ : Finset (ZMod q)).filter
    (fun h => H < h.valMinAbs.natAbs)
  let distance : ZMod q → ℕ := fun h => h.valMinAbs.natAbs
  have hmap : ∀ h ∈ T, distance h ∈ Finset.Ioc H (q / 2) := by
    intro h hh
    exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_filter.mp hh).2, ZMod.natAbs_valMinAbs_le h⟩
  have hbound :
      (∑ h ∈ T, ‖coefficient X q h‖) ≤
        ∑ h ∈ T, (q : ℝ) / (4 * X * (distance h : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro h hh
    apply norm_coefficient_le hX
    intro hz
    have := (Finset.mem_filter.mp hh).2
    simp [hz] at this
  change (∑ h ∈ T, ‖coefficient X q h‖) ≤ _
  apply hbound.trans
  rw [← Finset.sum_fiberwise_of_maps_to' hmap
    (fun d => (q : ℝ) / (4 * X * (d : ℝ) ^ 2))]
  have hfiber : ∀ d ∈ Finset.Ioc H (q / 2),
      ((T.filter (fun h => distance h = d)).card : ℝ) ≤ 2 := by
    intro d hd
    have hc : (T.filter (fun h => distance h = d)).card ≤ 2 := by
      apply le_trans (Finset.card_le_card ?_)
        (Waring.Analytic.card_leastResidueFiber_le_two (Finset.mem_Ioc.mp hd).2)
      intro h hh
      simp only [Waring.Analytic.leastResidueFiber, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp hh).2
    exact_mod_cast hc
  calc
    _ ≤ ∑ d ∈ Finset.Ioc H (q / 2),
        (q : ℝ) / (2 * X) * ((d : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc
        _ ≤ 2 * ((q : ℝ) / (4 * X * (d : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right (hfiber d hd) (by positivity)
        _ = _ := by ring
    _ = (q : ℝ) / (2 * X) *
        ∑ d ∈ Finset.Ioc H (q / 2), ((d : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (q : ℝ) / (2 * X) * (H : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases hle : H ≤ q / 2
      · exact (sum_Ioc_inv_sq_le_sub hH.ne' hle).trans (sub_le_self _ (by positivity))
      · rw [Finset.Ioc_eq_empty_of_le (by omega), Finset.sum_empty]
        positivity
    _ = _ := by ring

/-- A finite Fourier truncation approximates each progression mass with
an explicit error; all omitted phases have norm one. -/
theorem norm_progressionMass_sub_partialSum_le {X q : ℕ} [NeZero q]
    (hX : 0 < X) {H : ℕ} (hH : 0 < H) (a : ZMod q) :
    ‖(progressionMass X q a : ℂ) -
      ∑ h : ZMod q with h.valMinAbs.natAbs ≤ H,
        ZMod.stdAddChar (-h * a) * coefficient X q h‖ ≤
      (q : ℝ) / (2 * X * H) := by
  classical
  rw [progressionMass_eq_fourier]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ZMod q)) (fun h => h.valMinAbs.natAbs ≤ H)
    (fun h => ZMod.stdAddChar (-h * a) * coefficient X q h)
  simp only [not_le] at hsplit
  rw [← hsplit, add_sub_cancel_left]
  calc
    _ ≤ ∑ h : ZMod q with H < h.valMinAbs.natAbs,
        ‖ZMod.stdAddChar (-h * a) * coefficient X q h‖ := norm_sum_le _ _
    _ = ∑ h : ZMod q with H < h.valMinAbs.natAbs,
        ‖coefficient X q h‖ := by simp
    _ ≤ _ := sum_norm_coefficient_tail_le hX hH

end Erdos387Proof.TentFourier
