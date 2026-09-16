import Erdos387Proof.FourierVariation

/-! Polynomial mixed variation of the actual reciprocal-modulus weights.
The rectangle difference of the exponential is bounded algebraically,
without an exponential-in-frequency estimate. -/

set_option autoImplicit false

namespace Erdos387Proof.FourierMixedVariation

open FourierVariation FiniteAbel
open scoped BigOperators

theorem unitPhase_add (a b : ℝ) : unitPhase (a+b) = unitPhase a * unitPhase b := by
  simp only [unitPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem unitPhase_zero : unitPhase 0 = 1 := by simp [unitPhase]

theorem norm_unitPhase_sub_one_le (a : ℝ) : ‖unitPhase a - 1‖ ≤ |a| := by
  simpa only [unitPhase_zero, sub_zero] using norm_unitPhase_sub_le a 0

/-- The cross increment pays one bilinear phase increment and a product
of two linear increments. -/
theorem norm_phase_rectangle_le (a b c d : ℝ) :
    ‖unitPhase (a+b+c+d) - unitPhase (a+b) - unitPhase (a+c) + unitPhase a‖ ≤
      |d| + |b| * |c| := by
  have he : unitPhase (a+b+c+d) - unitPhase (a+b) - unitPhase (a+c) + unitPhase a =
      unitPhase (a+b+c)*(unitPhase d-1) +
        unitPhase a*(unitPhase b-1)*(unitPhase c-1) := by
    simp only [unitPhase_add]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_unitPhase, one_mul]
  exact add_le_add (norm_unitPhase_sub_one_le d)
    (mul_le_mul (norm_unitPhase_sub_one_le b) (norm_unitPhase_sub_one_le c)
      (norm_nonneg _) (abs_nonneg _))

theorem norm_phase_product_rectangle_le {c x v y w U : ℝ}
    (hv : 0 ≤ v) (hvx : v ≤ x) (hw : 0 ≤ w) (hwy : w ≤ y) (hU : x*y ≤ U) :
    ‖unitPhase (c*x*y) - unitPhase (c*x*w) - unitPhase (c*v*y) + unitPhase (c*v*w)‖ ≤
      (|c| + c^2*U)*(x-v)*(y-w) := by
  have hx := hv.trans hvx
  have hy := hw.trans hwy
  have hdx := sub_nonneg.mpr hvx
  have hdy := sub_nonneg.mpr hwy
  have hvw : v*w ≤ U := (mul_le_mul hvx hwy hw hx).trans hU
  have h := norm_phase_rectangle_le (c*v*w) (c*(x-v)*w) (c*v*(y-w)) (c*(x-v)*(y-w))
  have e1 : c*v*w+c*(x-v)*w+c*v*(y-w)+c*(x-v)*(y-w) = c*x*y := by ring
  have e2 : c*v*w+c*(x-v)*w = c*x*w := by ring
  have e3 : c*v*w+c*v*(y-w) = c*v*y := by ring
  rw [e1,e2,e3] at h
  apply h.trans
  simp only [abs_mul, abs_of_nonneg hv, abs_of_nonneg hw, abs_of_nonneg hdx, abs_of_nonneg hdy]
  have hc2 : |c| * |c| = c^2 := by rw [← sq_abs, pow_two]
  calc
    _ = (|c| + c^2*(v*w))*(x-v)*(y-w) := by rw [← hc2]; ring
    _ ≤ _ := by gcongr

theorem norm_elementaryWeight_rectangle_le {c x v y w U : ℝ}
    (hv : 0 ≤ v) (hvx : v ≤ x) (hw : 0 ≤ w) (hwy : w ≤ y) (hU : x*y ≤ U) :
    ‖elementaryWeight c (x*y) - elementaryWeight c (x*w) -
      elementaryWeight c (v*y) + elementaryWeight c (v*w)‖ ≤
      (1+3*|c| * U+c^2*U^2)*(x-v)*(y-w) := by
  have hx := hv.trans hvx
  have hy := hw.trans hwy
  have hdx := sub_nonneg.mpr hvx
  have hdy := sub_nonneg.mpr hwy
  have hU0 : 0 ≤ U := (mul_nonneg hx hy).trans hU
  have hxw : x*w ≤ U := (mul_le_mul_of_nonneg_left hwy hx).trans hU
  have hvy : v*y ≤ U := (mul_le_mul_of_nonneg_right hvx hy).trans hU
  have hvw : v*w ≤ U := (mul_le_mul hvx hwy hw hx).trans hU
  have he : elementaryWeight c (x*y) - elementaryWeight c (x*w) -
      elementaryWeight c (v*y) + elementaryWeight c (v*w) =
      (((x-v)*(y-w) : ℝ) : ℂ)*unitPhase (c*x*y) +
      (((x-v)*w : ℝ) : ℂ)*(unitPhase (c*x*y)-unitPhase (c*x*w)) +
      ((v*(y-w) : ℝ) : ℂ)*(unitPhase (c*x*y)-unitPhase (c*v*y)) +
      ((v*w : ℝ) : ℂ)*(unitPhase (c*x*y)-unitPhase (c*x*w)-
        unitPhase (c*v*y)+unitPhase (c*v*w)) := by
    unfold elementaryWeight
    simp only [mul_assoc, Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  have h1 : ‖unitPhase (c*x*y)-unitPhase (c*x*w)‖ ≤ |c| * x*(y-w) := by
    simpa only [← mul_sub, abs_mul, abs_of_nonneg hx, abs_of_nonneg hdy] using
      norm_unitPhase_sub_le (c*x*y) (c*x*w)
  have h2 : ‖unitPhase (c*x*y)-unitPhase (c*v*y)‖ ≤ |c| * y*(x-v) := by
    have e : c*x*y-c*v*y = c*y*(x-v) := by ring
    simpa only [e, abs_mul, abs_of_nonneg hy, abs_of_nonneg hdx] using
      norm_unitPhase_sub_le (c*x*y) (c*v*y)
  have h3 := norm_phase_product_rectangle_le hv hvx hw hwy hU (c := c)
  rw [he]
  calc
    _ ≤ ‖(((x-v)*(y-w) : ℝ) : ℂ)*unitPhase (c*x*y)‖ +
        ‖(((x-v)*w : ℝ) : ℂ)*(unitPhase (c*x*y)-unitPhase (c*x*w))‖ +
        ‖((v*(y-w) : ℝ) : ℂ)*(unitPhase (c*x*y)-unitPhase (c*v*y))‖ +
        ‖((v*w : ℝ) : ℂ)*(unitPhase (c*x*y)-unitPhase (c*x*w)-
          unitPhase (c*v*y)+unitPhase (c*v*w))‖ := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ = (x-v)*(y-w) + (x-v)*w*‖unitPhase (c*x*y)-unitPhase (c*x*w)‖ +
        v*(y-w)*‖unitPhase (c*x*y)-unitPhase (c*v*y)‖ +
        v*w*‖unitPhase (c*x*y)-unitPhase (c*x*w)-unitPhase (c*v*y)+unitPhase (c*v*w)‖ := by
      simp only [norm_mul, norm_unitPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hdx, abs_of_nonneg hdy, abs_of_nonneg hv, abs_of_nonneg hw]
    _ ≤ (x-v)*(y-w) + (x-v)*w*(|c| * x*(y-w)) +
        v*(y-w)*(|c| * y*(x-v)) + v*w*((|c|+c^2*U)*(x-v)*(y-w)) := by
      gcongr
    _ = (1+|c| * (x*w)+|c| * (v*y)+(v*w)*(|c|+c^2*U))*(x-v)*(y-w) := by ring
    _ ≤ (1+|c| * U+|c| * U+U*(|c|+c^2*U))*(x-v)*(y-w) := by gcongr
    _ = _ := by ring



theorem norm_finiteWeight_rectangle_le {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    {x v y z U C : ℝ} (hv : 0 ≤ v) (hvx : v ≤ x) (hz : 0 ≤ z) (hzy : z ≤ y)
    (hU : x*y ≤ U) (_hC : 0 ≤ C)
    (hw : ∀ n ∈ s, 0 ≤ w n) (hc : ∀ n ∈ s, |c n| ≤ C) :
    ‖finiteWeight s w c (x*y) - finiteWeight s w c (x*z) -
      finiteWeight s w c (v*y) + finiteWeight s w c (v*z)‖ ≤
      (∑ n ∈ s, w n) * (1+3*C*U+C^2*U^2)*(x-v)*(y-z) := by
  have hU0 : 0 ≤ U := (mul_nonneg (hv.trans hvx) (hz.trans hzy)).trans hU
  unfold finiteWeight
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ n ∈ s, ‖(w n : ℂ)*elementaryWeight (c n) (x*y) -
        (w n : ℂ)*elementaryWeight (c n) (x*z) -
        (w n : ℂ)*elementaryWeight (c n) (v*y) +
        (w n : ℂ)*elementaryWeight (c n) (v*z)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, w n*(1+3*C*U+C^2*U^2)*(x-v)*(y-z) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mul_sub, ← mul_sub, ← mul_add, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hw n hn)]
      calc
        _ ≤ w n*((1+3*|c n| * U+(c n)^2*U^2)*(x-v)*(y-z)) :=
          mul_le_mul_of_nonneg_left
            (norm_elementaryWeight_rectangle_le hv hvx hz hzy hU) (hw n hn)
        _ ≤ _ := by
          have hsq : (c n)^2 ≤ C^2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hc n hn) 2
          have hdx := sub_nonneg.mpr hvx
          have hdy := sub_nonneg.mpr hzy
          rw [← mul_assoc, ← mul_assoc]
          have hwn := hw n hn
          have hcn := hc n hn
          gcongr
    _ = _ := by simp only [Finset.sum_mul]

theorem sum_antitone_differences (u : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (u n-u (n+1))) = u 0-u N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

theorem mixedVariationMass_finiteWeight_le {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    (x y : ℕ → ℝ) (N M : ℕ) {U C : ℝ}
    (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hx : ∀ n, 0 ≤ x n) (hy : ∀ n, 0 ≤ y n)
    (hmx : Antitone x) (hmy : Antitone y) (hbound : x 0*y 0 ≤ U)
    (hw : ∀ n ∈ s, 0 ≤ w n) (hc : ∀ n ∈ s, |c n| ≤ C) :
    mixedVariationMass (fun i j => finiteWeight s w c (x i*y j)) N M ≤
      (∑ n ∈ s, w n)*(4*U+5*C*U^2+C^2*U^3) := by
  let A := ∑ n ∈ s, w n
  let K := 1+3*C*U+C^2*U^2
  have hA : 0 ≤ A := Finset.sum_nonneg hw
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb (i j : ℕ) : x i*y j ≤ U :=
    (mul_le_mul (hmx (Nat.zero_le i)) (hmy (Nat.zero_le j)) (hy _) (hx _)).trans hbound
  have hrow := variationMass_finiteWeight_le s w c (fun j => x (N-1)*y j) M hU hC
    (fun j => mul_nonneg (hx _) (hy _))
    (fun a b hab => mul_le_mul_of_nonneg_left (hmy hab) (hx _)) (hb _ _) hw hc
  have hdiff (i : ℕ) :
      variationMass (fun j => finiteWeight s w c (x (i+1)*y j) -
        finiteWeight s w c (x i*y j)) M ≤
      A*((1+C*U)+K)*(x i-x (i+1))*y 0 := by
    have hd : 0 ≤ x i-x (i+1) := sub_nonneg.mpr (hmx (by omega))
    have hend : ‖finiteWeight s w c (x (i+1)*y (M-1)) -
        finiteWeight s w c (x i*y (M-1))‖ ≤
        A*(1+C*U)*(x i-x (i+1))*y (M-1) := by
      rw [norm_sub_rev]
      have h := norm_finiteWeight_sub_le s w c
        (mul_nonneg (hx _) (hy _))
        (mul_le_mul_of_nonneg_right (hmx (show i ≤ i+1 by omega)) (hy _))
        (hb i (M-1)) hw hc
      convert h using 1
      dsimp [A]
      ring
    have hrect (j : ℕ) :
        ‖(finiteWeight s w c (x (i+1)*y (j+1)) - finiteWeight s w c (x i*y (j+1))) -
          (finiteWeight s w c (x (i+1)*y j) - finiteWeight s w c (x i*y j))‖ ≤
        A*K*(x i-x (i+1))*(y j-y (j+1)) := by
      have he : (finiteWeight s w c (x (i+1)*y (j+1)) - finiteWeight s w c (x i*y (j+1))) -
          (finiteWeight s w c (x (i+1)*y j) - finiteWeight s w c (x i*y j)) =
          finiteWeight s w c (x i*y j) - finiteWeight s w c (x i*y (j+1)) -
            finiteWeight s w c (x (i+1)*y j) + finiteWeight s w c (x (i+1)*y (j+1)) := by ring
      rw [he]
      exact norm_finiteWeight_rectangle_le s w c (hx _) (hmx (by omega))
        (hy _) (hmy (by omega)) (hb i j) hC hw hc
    unfold variationMass
    calc
      _ ≤ A*(1+C*U)*(x i-x (i+1))*y (M-1) +
          ∑ j ∈ Finset.range (M-1), A*K*(x i-x (i+1))*(y j-y (j+1)) :=
        add_le_add hend (Finset.sum_le_sum (fun j _ => hrect j))
      _ = A*(1+C*U)*(x i-x (i+1))*y (M-1) +
          A*K*(x i-x (i+1))*(y 0-y (M-1)) := by
        rw [← Finset.mul_sum, sum_antitone_differences]
      _ ≤ A*(1+C*U)*(x i-x (i+1))*y 0 + A*K*(x i-x (i+1))*y 0 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hmy (Nat.zero_le _)) (by positivity)
        · exact mul_le_mul_of_nonneg_left (by linarith [hy (M-1)]) (by positivity)
      _ = _ := by ring
  unfold mixedVariationMass
  calc
    _ ≤ A*(2*U+C*U^2) +
        ∑ i ∈ Finset.range (N-1), A*((1+C*U)+K)*(x i-x (i+1))*y 0 :=
      add_le_add hrow (Finset.sum_le_sum (fun i _ => hdiff i))
    _ = A*(2*U+C*U^2)+A*((1+C*U)+K)*(x 0-x (N-1))*y 0 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, sum_antitone_differences]
    _ ≤ A*(2*U+C*U^2)+A*((1+C*U)+K)*U := by
      apply add_le_add le_rfl
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (x 0-x (N-1))*y 0 ≤ x 0*y 0 :=
          mul_le_mul_of_nonneg_right (by linarith [hx (N-1)]) (hy _)
        _ ≤ U := hbound
    _ = _ := by dsimp [K, A]; ring



open Erdos387Proof.TentFourier

theorem mixedVariationMass_tentWeight_le (X : ℕ) (h i : ℤ)
    (x y : ℕ → ℝ) (N M : ℕ) {U H : ℝ}
    (hX : 0 < X) (hU : 0 ≤ U) (hH : 0 ≤ H)
    (hh : |(h : ℝ)| ≤ H) (hi : |i| ≤ (X : ℤ))
    (hx : ∀ n, 0 ≤ x n) (hy : ∀ n, 0 ≤ y n)
    (hmx : Antitone x) (hmy : Antitone y) (hbound : x 0*y 0 ≤ U) :
    mixedVariationMass (fun a b => tentWeight X h i (x a*y b)) N M ≤
      16*X*U+640*H*(X : ℝ)^2*U^2+4096*H^2*(X : ℝ)^3*U^3 := by
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
  have hv := mixedVariationMass_finiteWeight_le (supportInterval X) (tent X)
    (fun n => 2*Real.pi*(h : ℝ)*((n+i : ℤ) : ℝ)) x y N M hU
    (C := 32*H*X) (by positivity) hx hy hmx hmy hbound
    (fun n _ => tent_nonneg X n) hc
  apply hv.trans
  calc
    _ ≤ (4*X)*(4*U+5*(32*H*X)*U^2+(32*H*X)^2*U^3) :=
      mul_le_mul_of_nonneg_right (sum_tent_le_four_mul hX) (by positivity)
    _ = _ := by ring

theorem mixedVariationMass_tentWeight_reciprocal_le (X : ℕ) (h i : ℤ)
    (p q : ℕ → ℕ) (N M : ℕ) {R H : ℝ}
    (hX : 0 < X) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hh : |(h : ℝ)| ≤ H) (hi : |i| ≤ (X : ℤ))
    (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n)
    (hmp : Monotone p) (hmq : Monotone q)
    (hbound : (X : ℝ)/((p 0 : ℝ)*(q 0 : ℝ)) ≤ R) :
    mixedVariationMass (fun a b => tentWeight X h i ((p a : ℝ)*(q b : ℝ))⁻¹) N M ≤
      16*R+640*H*R^2+4096*H^2*R^3 := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hpi : Antitone (fun n => (p n : ℝ)⁻¹) := by
    intro a b hab
    apply inv_anti₀ (by exact_mod_cast hp a)
    exact_mod_cast hmp hab
  have hqi : Antitone (fun n => (q n : ℝ)⁻¹) := by
    intro a b hab
    apply inv_anti₀ (by exact_mod_cast hq a)
    exact_mod_cast hmq hab
  have hb : (p 0 : ℝ)⁻¹*(q 0 : ℝ)⁻¹ ≤ R/X := by
    apply (le_div_iff₀ hXR).mpr
    simpa [div_eq_mul_inv, mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbound
  have hv := mixedVariationMass_tentWeight_le X h i
    (fun n => (p n : ℝ)⁻¹) (fun n => (q n : ℝ)⁻¹) N M
    hX (U := R/X) (div_nonneg hR hXR.le) hH hh hi
    (fun n => inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun n => inv_nonneg.mpr (Nat.cast_nonneg _)) hpi hqi hb
  simp only [← mul_inv] at hv
  apply hv.trans_eq
  field_simp

end Erdos387Proof.FourierMixedVariation
