import ErdosProblems.Erdos387.ProgressionFourier
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact finite separation of a three-factor product cut. A logarithmic
integer grid has a strict rounding margin at adjacent integer products;
finite cyclic Fourier inversion then separates the three factors. -/

set_option autoImplicit false
namespace Erdos387Proof.FiniteLogSeparator
open Erdos387
open scoped BigOperators

def grid (X : ℕ) : ℕ := 4*(X+1)
noncomputable def label (X n : ℕ) : ℤ := ⌊(grid X : ℝ)*Real.log (n : ℝ)⌋
noncomputable def cut (X A : ℕ) : ℤ := if A=0 then -1 else label X A
noncomputable def totalLabel (X D r s : ℕ) : ℤ := label X D+label X r+label X s

theorem label_nonneg (X n : ℕ) : 0 ≤ label X n := by
  apply Int.floor_nonneg.mpr
  exact mul_nonneg (by positivity) (Real.log_natCast_nonneg n)

theorem totalLabel_nonneg (X D r s : ℕ) : 0 ≤ totalLabel X D r s :=
  add_nonneg (add_nonneg (label_nonneg X D) (label_nonneg X r)) (label_nonneg X s)

theorem log_product {D r s : ℕ} (hD : 0<D) (hr : 0<r) (hs : 0<s) :
    Real.log (D*r*s : ℕ) = Real.log (D : ℝ)+Real.log (r : ℝ)+Real.log (s : ℝ) := by
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  rw [Real.log_mul (mul_ne_zero hDR hrR) hsR,Real.log_mul hDR hrR]

theorem totalLabel_le_scaled_log {X D r s : ℕ} (hD : 0<D) (hr : 0<r) (hs : 0<s) :
    (totalLabel X D r s : ℝ) ≤ (grid X : ℝ)*Real.log (D*r*s : ℕ) := by
  have h₁ := Int.floor_le ((grid X : ℝ)*Real.log (D : ℝ))
  have h₂ := Int.floor_le ((grid X : ℝ)*Real.log (r : ℝ))
  have h₃ := Int.floor_le ((grid X : ℝ)*Real.log (s : ℝ))
  rw [log_product hD hr hs]
  dsimp [totalLabel,label]
  push_cast
  linarith

theorem scaled_log_sub_three_lt_totalLabel {X D r s : ℕ}
    (hD : 0<D) (hr : 0<r) (hs : 0<s) :
    (grid X : ℝ)*Real.log (D*r*s : ℕ)-3 < (totalLabel X D r s : ℝ) := by
  have h₁ := Int.sub_one_lt_floor ((grid X : ℝ)*Real.log (D : ℝ))
  have h₂ := Int.sub_one_lt_floor ((grid X : ℝ)*Real.log (r : ℝ))
  have h₃ := Int.sub_one_lt_floor ((grid X : ℝ)*Real.log (s : ℝ))
  rw [log_product hD hr hs]
  dsimp [totalLabel,label]
  push_cast
  linarith

/-- The gap at two consecutive positive integers is large enough after
multiplication by the grid. -/
theorem log_successor_gap {A : ℕ} (hA : 0<A) :
    (1 : ℝ)/((A : ℝ)+1) ≤ Real.log ((A : ℝ)+1)-Real.log (A : ℝ) := by
  have hAR : (0 : ℝ)<A := by exact_mod_cast hA
  have hAp : (0 : ℝ)<(A : ℝ)+1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hAR hAp)
  rw [Real.log_div hAR.ne' hAp.ne'] at h
  have he : (A : ℝ)/((A : ℝ)+1)-1 = -(1/((A : ℝ)+1)) := by
    field_simp
    ring
  rw [he] at h
  linarith

theorem scaled_gap {X A : ℕ} (hA : 0<A) (hAX : A≤X) :
    (4 : ℝ) ≤ (grid X : ℝ)*(Real.log ((A : ℝ)+1)-Real.log (A : ℝ)) := by
  have hden : (0 : ℝ)<(A : ℝ)+1 := by positivity
  have hfour : (4 : ℝ) ≤ (grid X : ℝ)/((A : ℝ)+1) := by
    apply (le_div_iff₀ hden).mpr
    have hAXR : (A : ℝ)≤X := by exact_mod_cast hAX
    simp only [grid,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    linarith
  exact hfour.trans (by simpa only [div_eq_mul_inv,one_mul] using
    mul_le_mul_of_nonneg_left (log_successor_gap hA) (show (0 : ℝ)≤grid X by positivity))

/-- Exact threshold comparison, including cutoff zero. Equal products are
included; the next integer product is separated by a strict floor margin. -/
theorem product_le_iff_totalLabel_le {X A D r s : ℕ}
    (hD : 0<D) (hr : 0<r) (hs : 0<s) (hAX : A≤X) :
    D*r*s≤A ↔ totalLabel X D r s≤cut X A := by
  have hP : 0<D*r*s := Nat.mul_pos (Nat.mul_pos hD hr) hs
  by_cases hA : A=0
  · rw [cut,if_pos hA]
    subst A
    have hL := totalLabel_nonneg X D r s
    omega
  · rw [cut,if_neg hA]
    constructor
    · intro hPA
      apply Int.le_floor.mpr
      exact (totalLabel_le_scaled_log hD hr hs).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hP)
          (by exact_mod_cast hPA)) (by positivity))
    · intro hL
      by_contra hnot
      have hPA : A+1≤D*r*s := by omega
      have hlog : Real.log ((A : ℝ)+1) ≤ Real.log (D*r*s : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hPA)
      have hgap := scaled_gap (Nat.pos_of_ne_zero hA) hAX
      have hmul := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ)≤grid X by positivity)
      have hfloor : (totalLabel X D r s : ℝ) ≤ (grid X : ℝ)*Real.log (A : ℝ) :=
        (by exact_mod_cast hL : (totalLabel X D r s : ℝ) ≤ label X A).trans (Int.floor_le _)
      have hround := scaled_log_sub_three_lt_totalLabel (X := X) hD hr hs
      nlinarith

/-- Both inequalities of the product window use the same labels. -/
theorem product_window_iff {X A D r s : ℕ}
    (hD : 0<D) (hr : 0<r) (hs : 0<s) (hAX : A≤X) :
    A<D*r*s ∧ D*r*s≤X ↔
      totalLabel X D r s ∈ Finset.Ioc (cut X A) (cut X X) := by
  rw [Finset.mem_Ioc,← product_le_iff_totalLabel_le hD hr hs le_rfl]
  have h := product_le_iff_totalLabel_le hD hr hs hAX
  omega

/-- The precise near-divisor floor agrees with the logarithmic interval. -/
theorem near_product_window_iff {B X D r s : ℕ} (hB : 0<B)
    (hD : 0<D) (hr : 0<r) (hs : 0<s) :
    X/2<B*(D*r*s) ∧ D*r*s≤X ↔
      totalLabel X D r s ∈ Finset.Ioc (cut X ((X/2)/B)) (cut X X) := by
  have hA : (X/2)/B≤X := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  rw [← product_window_iff hD hr hs hA,Nat.div_lt_iff_lt_mul hB,mul_comm (D*r*s) B]


def modulus (X : ℕ) : ℕ := 3*grid X*X+1
instance modulus_neZero (X : ℕ) : NeZero (modulus X) := ⟨by unfold modulus; omega⟩

theorem label_le_grid_mul {X n : ℕ} (hn : 0<n) (hnX : n≤X) :
    label X n ≤ (grid X*X : ℕ) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hnXR : (n : ℝ)≤X := by exact_mod_cast hnX
  have hlog : Real.log (n : ℝ)≤X := (Real.log_le_sub_one_of_pos hnR).trans (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ)≤grid X by positivity)
  unfold label
  apply Int.floor_le_iff.mpr
  push_cast
  linarith

theorem totalLabel_lt_modulus {X D r s : ℕ}
    (hD : 0<D) (hr : 0<r) (hs : 0<s) (hDX : D≤X) (hrX : r≤X) (hsX : s≤X) :
    totalLabel X D r s < modulus X := by
  have hd := label_le_grid_mul hD hDX
  have hr' := label_le_grid_mul hr hrX
  have hs' := label_le_grid_mul hs hsX
  dsimp [totalLabel,modulus]
  push_cast at hd hr' hs' ⊢
  nlinarith

theorem cut_lower (X A : ℕ) : -1 ≤ cut X A := by
  unfold cut
  split
  · rfl
  · have := label_nonneg X A
    omega

theorem cut_le_grid_mul {X A : ℕ} (hAX : A≤X) : cut X A ≤ (grid X*X : ℕ) := by
  unfold cut
  split
  · exact (by norm_num : (-1 : ℤ)≤0).trans (Int.natCast_nonneg _)
  · exact label_le_grid_mul (by omega) hAX

theorem cut_mono {X A : ℕ} (hAX : A≤X) : cut X A≤cut X X := by
  by_cases hA : A=0
  · simpa only [cut,if_pos hA] using cut_lower X X
  · have hX : X≠0 := by omega
    simp only [cut,if_neg hA,if_neg hX,label]
    apply Int.floor_mono
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hA
    · exact_mod_cast hAX


theorem interval_bounds {X A : ℕ} {v : ℤ}
    (hv : v ∈ Finset.Ioc (cut X A) (cut X X)) :
    0≤v ∧ v<(modulus X : ℤ) := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hv
  have hl := cut_lower X A
  have hu := cut_le_grid_mul (X := X) le_rfl
  constructor
  · omega
  · dsimp [modulus]
    push_cast at hu ⊢
    nlinarith [show (0 : ℤ)≤(grid X : ℤ)*X by positivity]

noncomputable def intervalLength (X A : ℕ) : ℕ := (cut X X-cut X A).toNat

theorem interval_endpoint {X A : ℕ} (hAX : A≤X) :
    cut X A+(intervalLength X A : ℤ)=cut X X := by
  dsimp [intervalLength]
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr (cut_mono hAX))]
  omega

theorem intervalLength_le_modulus {X A : ℕ} (hAX : A≤X) :
    intervalLength X A≤modulus X := by
  have he := interval_endpoint hAX
  have hl := cut_lower X A
  have hu := cut_le_grid_mul (X := X) le_rfl
  have h : (intervalLength X A : ℤ)≤modulus X := by
    dsimp [modulus]
    push_cast at hu ⊢
    nlinarith [show (0 : ℤ)≤(grid X : ℤ)*X by positivity]
  exact_mod_cast h

noncomputable def coefficient (X A : ℕ) (h : ZMod (modulus X)) : ℂ :=
  ProgressionFourier.intCoefficient (modulus X) (Finset.Ioc (cut X A) (cut X X)) h /
    (modulus X : ℂ)

noncomputable def character (X : ℕ) (h : ZMod (modulus X)) (n : ℕ) : ℂ :=
  ZMod.stdAddChar (-h*(label X n : ZMod (modulus X)))

theorem norm_character (X n : ℕ) (h : ZMod (modulus X)) : ‖character X h n‖=1 := by
  exact Waring.Analytic.norm_stdAddChar (modulus X) _

/-- The total absolute coefficient mass, rather than the number of Fourier
frequencies, controls the cost of separating the product constraint. -/
theorem sum_norm_coefficient_le {X A : ℕ} (hAX : A≤X) :
    (∑ h : ZMod (modulus X), ‖coefficient X A h‖)≤Real.log (modulus X : ℝ)+1 := by
  simp_rw [coefficient,norm_div,Complex.norm_natCast]
  rw [← Finset.sum_div]
  have hq : (0 : ℝ)<modulus X := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (modulus X))
  apply (div_le_iff₀ hq).mpr
  have h := ProgressionFourier.sum_norm_intCoefficient_Ioc_le
    (modulus X) (cut X A) (intervalLength X A) (intervalLength_le_modulus hAX)
  rw [interval_endpoint hAX] at h
  simpa only [mul_comm] using h

theorem card_residueClass_eq_indicator {X A D r s : ℕ}
    (hD : 0<D) (hr : 0<r) (hs : 0<s) (hDX : D≤X) (hrX : r≤X) (hsX : s≤X)
    (hAX : A≤X) :
    (ProgressionFourier.intResidueClass (modulus X)
      (Finset.Ioc (cut X A) (cut X X)) (totalLabel X D r s : ZMod (modulus X))).card =
        if A<D*r*s ∧ D*r*s≤X then 1 else 0 := by
  classical
  have he : ProgressionFourier.intResidueClass (modulus X)
      (Finset.Ioc (cut X A) (cut X X)) (totalLabel X D r s : ZMod (modulus X)) =
      (Finset.Ioc (cut X A) (cut X X)).filter (fun v => v=totalLabel X D r s) := by
    apply Finset.filter_congr
    intro v hv
    obtain ⟨hv0,hvq⟩ := interval_bounds hv
    rw [ZMod.intCast_eq_intCast_iff',Int.emod_eq_of_lt hv0 hvq,
      Int.emod_eq_of_lt (totalLabel_nonneg X D r s)
        (totalLabel_lt_modulus hD hr hs hDX hrX hsX)]
  rw [he,Finset.filter_eq']
  by_cases hP : A<D*r*s ∧ D*r*s≤X
  · rw [if_pos ((product_window_iff hD hr hs hAX).mp hP),if_pos hP,Finset.card_singleton]
  · rw [if_neg (fun h => hP ((product_window_iff hD hr hs hAX).mpr h)),if_neg hP,Finset.card_empty]

/-- Exact finite separable expansion of the sharp product window. The
coefficient is common to all factors and each factor character has norm1. -/
theorem indicator_eq_sum_separated {X A D r s : ℕ}
    (hD : 0<D) (hr : 0<r) (hs : 0<s) (hDX : D≤X) (hrX : r≤X) (hsX : s≤X)
    (hAX : A≤X) :
    (if A<D*r*s ∧ D*r*s≤X then (1 : ℂ) else 0) =
      ∑ h : ZMod (modulus X), coefficient X A h *
        (character X h D * character X h r * character X h s) := by
  classical
  have hcard := card_residueClass_eq_indicator hD hr hs hDX hrX hsX hAX
  have hchar (h : ZMod (modulus X)) :
      ZMod.stdAddChar (-h*(totalLabel X D r s : ZMod (modulus X))) =
        character X h D*character X h r*character X h s := by
    unfold character totalLabel
    push_cast
    rw [← AddChar.map_add_eq_mul,← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    _ = ((ProgressionFourier.intResidueClass (modulus X)
        (Finset.Ioc (cut X A) (cut X X)) (totalLabel X D r s : ZMod (modulus X))).card : ℂ) := by
      rw [hcard]
      split <;> simp
    _ = (modulus X : ℂ)⁻¹ * ∑ h : ZMod (modulus X),
        ZMod.stdAddChar (-h*(totalLabel X D r s : ZMod (modulus X))) *
          ProgressionFourier.intCoefficient (modulus X) (Finset.Ioc (cut X A) (cut X X)) h :=
      ProgressionFourier.int_card_residueClass_eq_phase_sum _ _ _
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [hchar]
      unfold coefficient
      ring

theorem near_indicator_eq_sum_separated {B X D r s : ℕ} (hB : 0<B)
    (hD : 0<D) (hr : 0<r) (hs : 0<s) (hDX : D≤X) (hrX : r≤X) (hsX : s≤X) :
    (if X/2<B*(D*r*s) ∧ D*r*s≤X then (1 : ℂ) else 0) =
      ∑ h : ZMod (modulus X), coefficient X ((X/2)/B) h *
        (character X h D * character X h r * character X h s) := by
  have hA : (X/2)/B≤X := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  simpa only [Nat.div_lt_iff_lt_mul hB,mul_comm (D*r*s) B] using
    indicator_eq_sum_separated hD hr hs hDX hrX hsX hA

theorem modulus_le_square {X : ℕ} (hX : 0<X) : modulus X≤25*X^2 := by
  have hx : X≤X^2 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_le_of_lt hX) (by norm_num : 1≤2)
  unfold modulus grid
  nlinarith

theorem log_modulus_le {X : ℕ} (hX : 0<X) :
    Real.log (modulus X : ℝ)+1≤(Real.log (25 : ℝ)+3)*(1+Real.log (X : ℝ)) := by
  have hq : (0 : ℝ)<modulus X := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (modulus X))
  have hXR : (0 : ℝ)<X := by exact_mod_cast hX
  have hlog := Real.log_le_log hq (show (modulus X : ℝ)≤25*(X : ℝ)^2 by exact_mod_cast modulus_le_square hX)
  rw [Real.log_mul (by norm_num : (25 : ℝ)≠0) (pow_ne_zero _ hXR.ne'),Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hLX := Real.log_natCast_nonneg X
  have hL25 : 0≤Real.log (25 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg hLX hL25]

theorem sum_norm_coefficient_le_log {X A : ℕ} (hX : 0<X) (hAX : A≤X) :
    (∑ h : ZMod (modulus X), ‖coefficient X A h‖)≤
      (Real.log (25 : ℝ)+3)*(1+Real.log (X : ℝ)) :=
  (sum_norm_coefficient_le hAX).trans (log_modulus_le hX)

end Erdos387Proof.FiniteLogSeparator
