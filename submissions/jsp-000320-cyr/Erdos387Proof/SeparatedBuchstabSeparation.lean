import Erdos387Proof.SeparatedBuchstabDecomposition
import Waring.Analytic.FourierCoefficientSum

/-!
# Exact finite separation of the residual Buchstab roughness mask

The residual rho(m,p_last(u)) is a comparison of two finite cutoffs.
Fourier inversion of the interval [0,y] modulo 2*y+1 separates this
comparison with coefficient mass at most 1+log(2*y+1). All sums are finite;
no Mellin inversion or cancellation hypothesis is used.
-/

namespace Erdos387Proof.SeparatedBuchstabSeparation

open scoped BigOperators
open SeparatedBuchstabDecomposition

/-- The sentinel y handles integers with no prime divisor below y,
including m=1. -/
noncomputable def cutoffSet (y m : ℕ) : Finset ℕ :=
  insert y ((Nat.primesBelow y).filter (fun p => p ∣ m))

theorem cutoffSet_nonempty (y m : ℕ) : (cutoffSet y m).Nonempty := by
  classical
  exact ⟨y, Finset.mem_insert_self _ _⟩

noncomputable def roughCutoff (y m : ℕ) : ℕ :=
  (cutoffSet y m).min' (cutoffSet_nonempty y m)

theorem roughCutoff_le (y m : ℕ) : roughCutoff y m ≤ y := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

/-- This is an exact cutoff identity, also for m=0 or m=1. -/
theorem rough_iff_le_cutoff (y m p : ℕ) (hp : p ≤ y) :
    Erdos387.IsZRough p m ↔ p ≤ roughCutoff y m := by
  classical
  unfold roughCutoff
  rw [Finset.le_min'_iff]
  constructor
  · intro h v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hp
    · obtain ⟨hv,hvm⟩ := Finset.mem_filter.mp hv
      obtain ⟨hvy,hprime⟩ := Nat.mem_primesBelow.mp hv
      by_contra hlt
      exact h v hprime (by omega) hvm
  · intro h v hv hvp hvm
    have hmem : v ∈ cutoffSet y m := by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨hvp.trans_le hp,hv⟩,hvm⟩
    have := h v hmem
    omega

theorem roughIndicator_eq_cutoff (y m p : ℕ) (hp : p ≤ y) :
    roughIndicator p m = if p ≤ roughCutoff y m then 1 else 0 := by
  classical
  simp only [roughIndicator, rough_iff_le_cutoff y m p hp]

/-- The normalized Fourier coefficient of [0,y] modulo 2*y+1. -/
noncomputable def thresholdCoefficient (y : ℕ) (h : ZMod (2*y+1)) : ℂ :=
  ((2*y+1 : ℕ) : ℂ)⁻¹ * Waring.Analytic.intervalFourierCoefficient (-1) (y+1) h

/-- Integer-interval and natural-range forms of the same coefficient. -/
theorem intervalCoefficient_eq_range (y : ℕ) (h : ZMod (2*y+1)) :
    Waring.Analytic.intervalFourierCoefficient (-1) (y+1) h =
      ∑ d ∈ Finset.range (y+1), ZMod.stdAddChar (-(h*(d : ZMod (2*y+1)))) := by
  classical
  unfold Waring.Analytic.intervalFourierCoefficient
  apply Finset.sum_bij (fun n _ => n.toNat)
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_range]
    omega
  · intro a ha b hb he
    simp only [Finset.mem_Ioc] at ha hb
    omega
  · intro d hd
    simp only [Finset.mem_range] at hd
    refine ⟨(d : ℤ), ?_, by simp⟩
    simp only [Finset.mem_Ioc]
    omega
  · intro n hn
    have hn0 : 0 ≤ n := by simp only [Finset.mem_Ioc] at hn; omega
    rw [← Int.natCast_toNat_eq_self.mpr hn0]
    simp

/-- The no-wrap fact is why the Fourier modulus is 2*y+1. -/
theorem threshold_cast_eq_iff (y a b d : ℕ) (ha : a ≤ y) (hb : b ≤ y) (hd : d ≤ y) :
    (d : ZMod (2*y+1)) = (b : ZMod (2*y+1)) - (a : ZMod (2*y+1)) ↔ d+a=b := by
  rw [eq_sub_iff_add_eq, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The inverse Fourier expansion of the comparison a≤b, with both
arguments in [0,y]. It is exact at equality and at both endpoints. -/
theorem threshold_fourier (y a b : ℕ) (ha : a ≤ y) (hb : b ≤ y) :
    (if a ≤ b then (1 : ℂ) else 0) =
      ∑ h : ZMod (2*y+1), thresholdCoefficient y h *
        ZMod.stdAddChar (-(h*(a : ZMod (2*y+1)))) *
        ZMod.stdAddChar (h*(b : ZMod (2*y+1))) := by
  classical
  let q := 2*y+1
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by dsimp [q]; omega)
  have horth (d : ℕ) :
      (∑ h : ZMod q, ZMod.stdAddChar (h*((b : ZMod q)-(a : ZMod q)-(d : ZMod q)))) =
        if (d : ZMod q) = (b : ZMod q)-(a : ZMod q) then (q : ℂ) else 0 := by
    simpa only [sub_eq_zero, eq_comm, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
      AddChar.sum_mulShift ((b : ZMod q)-(a : ZMod q)-(d : ZMod q))
        (ZMod.isPrimitive_stdAddChar q)
  symm
  calc
    _ = (q : ℂ)⁻¹ * ∑ d ∈ Finset.range (y+1),
        ∑ h : ZMod q,
          ZMod.stdAddChar (h*((b : ZMod q)-(a : ZMod q)-(d : ZMod q))) := by
      simp only [thresholdCoefficient, intervalCoefficient_eq_range, Finset.sum_mul,
        mul_assoc, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro h hh
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (q : ℂ)⁻¹ * ∑ d ∈ Finset.range (y+1),
        if d+a=b then (q : ℂ) else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [horth]
      simp only [threshold_cast_eq_iff y a b d ha hb (by simp only [Finset.mem_range] at hd; omega)]
    _ = _ := by
      by_cases hab : a ≤ b
      · have hmem : b-a ∈ Finset.range (y+1) := by simp only [Finset.mem_range]; omega
        have he (d : ℕ) : d+a=b ↔ d=b-a := by omega
        simp only [he, Finset.sum_ite_eq', hmem, if_true, inv_mul_cancel₀ hq, hab]
      · have he (d : ℕ) : ¬d+a=b := by omega
        simp [he,hab]

/-- The total coefficient mass is logarithmic, by the proven finite
geometric-sum and harmonic estimates in Waring.Analytic. -/
theorem sum_norm_thresholdCoefficient_le (y : ℕ) :
    (∑ h : ZMod (2*y+1), ‖thresholdCoefficient y h‖) ≤
      Real.log (2*y+1 : ℕ) + 1 := by
  have hq : ((2*y+1 : ℕ) : ℝ) ≠ 0 := by positivity
  calc
    _ = ((2*y+1 : ℕ) : ℝ)⁻¹ *
        ∑ h : ZMod (2*y+1), ‖Waring.Analytic.intervalFourierCoefficient (-1) (y+1) h‖ := by
      simp only [thresholdCoefficient, norm_mul, norm_inv, Complex.norm_natCast, Finset.mul_sum]
    _ ≤ ((2*y+1 : ℕ) : ℝ)⁻¹ *
        (((2*y+1 : ℕ) : ℝ) * (Real.log (2*y+1 : ℕ)+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Waring.Analytic.sum_norm_intervalFourierCoefficient_le (2*y+1) (-1) (y+1) (by omega)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]

/-- The two Fourier factors separately have norm one. Multiplying an
existing coefficient by either factor preserves its norm. -/
theorem norm_twisted_weight (y : ℕ) (h : ZMod (2*y+1)) (a : ZMod (2*y+1)) (w : ℂ) :
    ‖w*ZMod.stdAddChar (h*a)‖ = ‖w‖ := by simp

/-- Exact weighted finite separation. W may retain all original signed
weights, phases, coprimality masks and product constraints. -/
theorem weighted_threshold_separation {α β : Type*} (U : Finset α) (V : Finset β)
    (y : ℕ) (a : α → ℕ) (b : β → ℕ)
    (ha : ∀ u ∈ U, a u ≤ y) (hb : ∀ m ∈ V, b m ≤ y) (W : α → β → ℂ) :
    (∑ u ∈ U, ∑ m ∈ V, if a u ≤ b m then W u m else 0) =
      ∑ h : ZMod (2*y+1), thresholdCoefficient y h *
        ∑ u ∈ U, ∑ m ∈ V,
          ZMod.stdAddChar (-(h*(a u : ZMod (2*y+1)))) *
          ZMod.stdAddChar (h*(b m : ZMod (2*y+1))) * W u m := by
  classical
  calc
    _ = ∑ u ∈ U, ∑ m ∈ V,
        (∑ h : ZMod (2*y+1), thresholdCoefficient y h *
          ZMod.stdAddChar (-(h*(a u : ZMod (2*y+1)))) *
          ZMod.stdAddChar (h*(b m : ZMod (2*y+1)))) * W u m := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro m hm
      rw [← threshold_fourier y (a u) (b m) (ha u hu) (hb m hm)]
      split_ifs <;> simp
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]

/-- Application to the actual residual Buchstab mask; in particular the
m-dependent Fourier weight is retained exactly. -/
theorem weighted_rough_separation {α : Type*} (U : Finset α) (V : Finset ℕ)
    (y : ℕ) (p : α → ℕ) (hp : ∀ u ∈ U, p u ≤ y) (W : α → ℕ → ℂ) :
    (∑ u ∈ U, ∑ m ∈ V, roughIndicator (p u) m * W u m) =
      ∑ h : ZMod (2*y+1), thresholdCoefficient y h *
        ∑ u ∈ U, ∑ m ∈ V,
          ZMod.stdAddChar (-(h*(p u : ZMod (2*y+1)))) *
          ZMod.stdAddChar (h*(roughCutoff y m : ZMod (2*y+1))) * W u m := by
  rw [← weighted_threshold_separation U V y p (roughCutoff y) hp (fun m _ => roughCutoff_le y m) W]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro m hm
  rw [roughIndicator_eq_cutoff y m (p u) (hp u hu)]
  split_ifs <;> simp

/-- Source-facing separated coefficients. The original complex sign or
coefficient α(u) and the original m-weight β(m) each acquire only a unit
character. The original two-variable phase or mask F remains unchanged. -/
theorem weighted_rough_separation_factors {α : Type*} (U : Finset α) (V : Finset ℕ)
    (y : ℕ) (p : α → ℕ) (hp : ∀ u ∈ U, p u ≤ y)
    (a : α → ℂ) (b : ℕ → ℂ) (F : α → ℕ → ℂ) :
    (∑ u ∈ U, ∑ m ∈ V, roughIndicator (p u) m * a u * b m * F u m) =
      ∑ h : ZMod (2*y+1), thresholdCoefficient y h *
        ∑ u ∈ U, ∑ m ∈ V,
          (a u * ZMod.stdAddChar (-(h*(p u : ZMod (2*y+1))))) *
          (b m * ZMod.stdAddChar (h*(roughCutoff y m : ZMod (2*y+1)))) * F u m := by
  calc
    _ = ∑ u ∈ U, ∑ m ∈ V, roughIndicator (p u) m * (a u * b m * F u m) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = _ := by
      rw [weighted_rough_separation U V y p hp]
      apply Finset.sum_congr rfl
      intro h hh
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro m hm
      ring

/-- An unconditional norm bound after exact separation. The remaining
frequency sums are explicit obligations; no cancellation is assumed. -/
theorem norm_weighted_rough_le {α : Type*} (U : Finset α) (V : Finset ℕ)
    (y : ℕ) (p : α → ℕ) (hp : ∀ u ∈ U, p u ≤ y) (W : α → ℕ → ℂ) :
    ‖∑ u ∈ U, ∑ m ∈ V, roughIndicator (p u) m * W u m‖ ≤
      ∑ h : ZMod (2*y+1), ‖thresholdCoefficient y h‖ *
        ‖∑ u ∈ U, ∑ m ∈ V,
          ZMod.stdAddChar (-(h*(p u : ZMod (2*y+1)))) *
          ZMod.stdAddChar (h*(roughCutoff y m : ZMod (2*y+1))) * W u m‖ := by
  rw [weighted_rough_separation U V y p hp W]
  simpa only [norm_mul] using norm_sum_le (Finset.univ : Finset (ZMod (2*y+1)))
    (fun h => thresholdCoefficient y h *
      ∑ u ∈ U, ∑ m ∈ V,
        ZMod.stdAddChar (-(h*(p u : ZMod (2*y+1)))) *
        ZMod.stdAddChar (h*(roughCutoff y m : ZMod (2*y+1))) * W u m)

end Erdos387Proof.SeparatedBuchstabSeparation
