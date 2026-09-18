import MerLeanExperiment.TruncatedExponential
import MerLeanExperiment.OverconvergenceBounds

/-!
# Exact finite decomposition for exterior overconvergence

This file formalizes equation (10) of Luo--Yang--Zhu.  It reindexes the
coefficient convolution into the finite truncated-exponential decomposition
used by Proposition 3.3.
-/
open Finset Polynomial
open Filter Metric
open scoped Topology
namespace Erdos973

private theorem triangular_sum_swap {M : Type} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → ℕ → M) :
    (∑ m ∈ range (n + 1), ∑ ell ∈ range (m + 1), f ell (m - ell)) =
      ∑ ell ∈ range (n + 1), ∑ j ∈ range (n - ell + 1), f ell j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun a _ => ⟨a.2, a.1 - a.2⟩)
  · rintro ⟨m, ell⟩ ha
    rw [Finset.mem_sigma] at ha ⊢
    change m ∈ range (n + 1) ∧ ell ∈ range (m + 1) at ha
    change ell ∈ range (n + 1) ∧ (m - ell) ∈ range (n - ell + 1)
    constructor
    · rw [mem_range]
      have hm := mem_range.mp ha.1
      have hell := mem_range.mp ha.2
      omega
    · rw [mem_range]
      have hm := mem_range.mp ha.1
      have hell := mem_range.mp ha.2
      omega
  · rintro ⟨m₁, ell₁⟩ ha₁ ⟨m₂, ell₂⟩ ha₂ heq
    rw [Finset.mem_sigma] at ha₁ ha₂
    change m₁ ∈ range (n + 1) ∧ ell₁ ∈ range (m₁ + 1) at ha₁
    change m₂ ∈ range (n + 1) ∧ ell₂ ∈ range (m₂ + 1) at ha₂
    have hell : ell₁ = ell₂ := congrArg Sigma.fst heq
    have hsub : m₁ - ell₁ = m₂ - ell₂ := congrArg Sigma.snd heq
    have hle1 : ell₁ ≤ m₁ := Nat.le_of_lt_succ (mem_range.mp ha₁.2)
    have hle2 : ell₂ ≤ m₂ := Nat.le_of_lt_succ (mem_range.mp ha₂.2)
    subst ell₂
    have hm : m₁ = m₂ := by omega
    subst m₂
    rfl
  · rintro ⟨ell, j⟩ hb
    rw [Finset.mem_sigma] at hb
    change ell ∈ range (n + 1) ∧ j ∈ range (n - ell + 1) at hb
    refine ⟨⟨ell + j, ell⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      change ell + j ∈ range (n + 1) ∧ ell ∈ range (ell + j + 1)
      constructor <;> rw [mem_range]
      · have hell := mem_range.mp hb.1
        have hj := mem_range.mp hb.2
        omega
      · omega
    · apply Sigma.ext
      · simp
      · simp
  · rintro ⟨m, ell⟩ ha
    simp

private theorem sum_range_eq_zero_add_tail {M : Type} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → M) (h1 : f 1 = 0) :
    (∑ i ∈ range (n + 1), f i) =
      f 0 + ∑ i ∈ range (n + 1), if 2 ≤ i then f i else 0 := by
  calc
    (∑ i ∈ range (n + 1), f i) =
        ∑ i ∈ range (n + 1),
          ((if i = 0 then f i else 0) + (if 2 ≤ i then f i else 0)) := by
            apply sum_congr rfl
            intro i hi
            by_cases hi0 : i = 0
            · subst i
              simp
            · by_cases hi1' : i = 1
              · subst i
                simp [h1]
              · have hi2 : 2 ≤ i := by omega
                simp [hi0, hi2]
    _ = (∑ i ∈ range (n + 1), if i = 0 then f i else 0) +
        ∑ i ∈ range (n + 1), if 2 ≤ i then f i else 0 := by
          rw [sum_add_distrib]
    _ = f 0 + ∑ i ∈ range (n + 1), if 2 ≤ i then f i else 0 := by
          simp

theorem eval_rootProduct_eq_coeff_sum {n : ℕ} (z : Fin n → ℂ) (w : ℂ) :
    (rootProduct z).eval w =
      ∑ m ∈ range (n + 1), (rootProduct z).coeff m * w ^ m := by
  rw [Polynomial.eval_eq_sum_range]
  apply sum_subset ?_ ?_
  · exact range_subset_range.mpr (Nat.succ_le_succ
      (natDegree_le_iff_degree_le.mpr (degree_rootProduct_le z)))
  · intro m hm hmn
    have hlt : (rootProduct z).natDegree < m := by
      simpa [mem_range] using hmn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]

theorem rootProduct_eval_eq_truncatedExp_sum {n : ℕ} (z : Fin n → ℂ) (w : ℂ) :
    (rootProduct z).eval w =
      ∑ ell ∈ range (n + 1), perturbationCoeff z ell * w ^ ell *
        truncatedExp (n - ell) (-powerSum z 1 * w) := by
  rw [eval_rootProduct_eq_coeff_sum]
  have hcoeff : ∀ m ∈ range (n + 1), (rootProduct z).coeff m =
      ∑ ell ∈ range (m + 1), perturbationCoeff z ell *
        (-powerSum z 1) ^ (m - ell) / ((m - ell).factorial : ℂ) := by
    intro m hm
    apply rootProduct_coeff_eq_truncated_convolution
    rw [mem_range] at hm
    omega
  have hsum :
      (∑ m ∈ range (n + 1), (rootProduct z).coeff m * w ^ m) =
      ∑ m ∈ range (n + 1),
        (∑ ell ∈ range (m + 1), perturbationCoeff z ell *
          (-powerSum z 1) ^ (m - ell) / ((m - ell).factorial : ℂ)) * w ^ m := by
    apply sum_congr rfl
    intro m hm
    rw [hcoeff m hm]
  rw [hsum]
  simp_rw [sum_mul]
  have hreindex :
      (∑ m ∈ range (n + 1), ∑ ell ∈ range (m + 1),
        perturbationCoeff z ell * (-powerSum z 1) ^ (m - ell) /
          ((m - ell).factorial : ℂ) * w ^ m) =
      ∑ m ∈ range (n + 1), ∑ ell ∈ range (m + 1),
        perturbationCoeff z ell * w ^ ell *
          ((-powerSum z 1) ^ (m - ell) * w ^ (m - ell) /
            ((m - ell).factorial : ℂ)) := by
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro ell hell
    have hellm : ell ≤ m := Nat.le_of_lt_succ (mem_range.mp hell)
    rw [show m = ell + (m - ell) by omega, pow_add]
    simp only [Nat.add_sub_cancel_left]
    ring
  rw [hreindex]
  rw [triangular_sum_swap n (fun ell j =>
    perturbationCoeff z ell * w ^ ell *
      ((-powerSum z 1) ^ j * w ^ j / (j.factorial : ℂ)))]
  apply sum_congr rfl
  intro ell hell
  rw [truncatedExp]
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  ring_nf

/-- The finite perturbation remainder `G_n` from Proposition 3.3. -/
noncomputable def perturbationRemainder {n : ℕ} (z : Fin n → ℂ) (w : ℂ) : ℂ :=
  ∑ ell ∈ range (n + 1), if 2 ≤ ell then
    perturbationCoeff z ell * w ^ ell *
      truncatedExp (n - ell) (-powerSum z 1 * w)
  else 0

/-- Equation (10), split into its unperturbed truncated exponential and the
finite perturbation remainder. -/
theorem rootProduct_eval_eq_truncatedExp_add_remainder {n : ℕ}
    (z : Fin n → ℂ) (w : ℂ) :
    (rootProduct z).eval w =
      truncatedExp n (-powerSum z 1 * w) + perturbationRemainder z w := by
  rw [rootProduct_eval_eq_truncatedExp_sum]
  let f : ℕ → ℂ := fun ell =>
    perturbationCoeff z ell * w ^ ell *
      truncatedExp (n - ell) (-powerSum z 1 * w)
  have hf1 : f 1 = 0 := by
    simp [f, perturbationCoeff_one]
  rw [sum_range_eq_zero_add_tail n f hf1]
  simp [f, perturbationRemainder, perturbationCoeff_zero]

/-- Direct norm bound for the finite perturbation remainder.  The explicit
summability premise is supplied by the formal-series majorant in Lemma 2.1. -/
theorem norm_perturbationRemainder_le_tsum {n : ℕ} (z : Fin n → ℂ)
    {w : ℂ} {R : ℝ} (hR : 0 ≤ R) (hw : ‖w‖ ≤ R)
    (hsummable : Summable fun ell : ℕ =>
      if 2 ≤ ell then ‖perturbationCoeff z ell‖ * R ^ ell else 0) :
    ‖perturbationRemainder z w‖ ≤
      Real.exp ‖-powerSum z 1 * w‖ *
        ∑' ell : ℕ,
          if 2 ≤ ell then ‖perturbationCoeff z ell‖ * R ^ ell else 0 := by
  let b : ℕ → ℝ := fun ell =>
    if 2 ≤ ell then ‖perturbationCoeff z ell‖ * R ^ ell else 0
  have hb0 : ∀ ell, 0 ≤ b ell := by
    intro ell
    simp only [b]
    split_ifs <;> positivity
  calc
    ‖perturbationRemainder z w‖ ≤
        ∑ ell ∈ range (n + 1),
          ‖if 2 ≤ ell then perturbationCoeff z ell * w ^ ell *
            truncatedExp (n - ell) (-powerSum z 1 * w) else 0‖ := by
              rw [perturbationRemainder]
              exact norm_sum_le _ _
    _ ≤ ∑ ell ∈ range (n + 1),
        b ell * Real.exp ‖-powerSum z 1 * w‖ := by
          apply sum_le_sum
          intro ell hell
          by_cases h2 : 2 ≤ ell
          · have hbound :
                ‖perturbationCoeff z ell * w ^ ell *
                    truncatedExp (n - ell) (-powerSum z 1 * w)‖ ≤
                  b ell * Real.exp ‖-powerSum z 1 * w‖ := by
              rw [norm_mul, norm_mul, norm_pow]
              simp only [b, h2, ite_true]
              gcongr
              exact norm_truncatedExp_le_exp_norm _ _
            simpa only [h2, ite_true] using hbound
          · simp [h2, b]
    _ = Real.exp ‖-powerSum z 1 * w‖ *
        ∑ ell ∈ range (n + 1), b ell := by
          rw [mul_sum]
          apply sum_congr rfl
          intro ell hell
          ring
    _ ≤ Real.exp ‖-powerSum z 1 * w‖ * ∑' ell : ℕ, b ell := by
          gcongr
          exact hsummable.sum_le_tsum (range (n + 1))
            (fun ell hell => hb0 ell)
    _ = Real.exp ‖-powerSum z 1 * w‖ *
        ∑' ell : ℕ,
          if 2 ≤ ell then ‖perturbationCoeff z ell‖ * R ^ ell else 0 := by
          rfl

/-- Proposition 3.3's direct remainder estimate before inserting the eventual
exponential rates for `epsilon`, `R`, and the normalized first sum. -/
theorem norm_perturbationRemainder_le_majorant {n : ℕ} (z : Fin n → ℂ)
    {w : ℂ} {epsilon R : ℝ} (hepsilon : 0 ≤ epsilon) (hR : 0 ≤ R)
    (hw : ‖w‖ ≤ R)
    (hsmall : ∀ k ∈ Finset.Icc 2 (n + 1),
      ‖powerSum z k‖ ≤ epsilon) :
    ‖perturbationRemainder z w‖ ≤
      Real.exp ‖-powerSum z 1 * w‖ *
        (Real.exp (epsilon * perturbationMajorant n R) - 1) := by
  have hsummable : Summable fun ell : ℕ =>
      if 2 ≤ ell then ‖perturbationCoeff z ell‖ * R ^ ell else 0 := by
    have hs := (summable_perturbationCoeff_norm_mul_pow z R).indicator
      {ell : ℕ | 2 ≤ ell}
    apply hs.congr
    intro ell
    rw [Set.indicator_apply]
    by_cases h2 : 2 ≤ ell
    · simp [h2]
    · simp [h2]
  calc
    ‖perturbationRemainder z w‖ ≤
        Real.exp ‖-powerSum z 1 * w‖ *
          ∑' ell : ℕ,
            if 2 ≤ ell then ‖perturbationCoeff z ell‖ * R ^ ell else 0 :=
      norm_perturbationRemainder_le_tsum z hR hw hsummable
    _ ≤ Real.exp ‖-powerSum z 1 * w‖ *
        (Real.exp (epsilon * perturbationMajorant n R) - 1) := by
      exact mul_le_mul_of_nonneg_left
        (perturbationCoeff_majorant z hepsilon hR hsmall)
        (Real.exp_pos _).le

/-- The elementary finite majorant bound used in Proposition 3.3.  Its
polynomial prefactor is absorbed by the spare exponential margin. -/
theorem perturbationMajorant_le_nat_mul_pow (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    perturbationMajorant n R ≤ n * R ^ (n + 1) := by
  unfold perturbationMajorant
  calc
    (∑ k ∈ Icc 2 (n + 1), R ^ k / k) ≤
        ∑ _k ∈ Icc 2 (n + 1), R ^ (n + 1) := by
      gcongr with k hk
      have hk2 : 1 ≤ k := le_trans (by norm_num) (mem_Icc.mp hk).1
      have hkn : k ≤ n + 1 := (mem_Icc.mp hk).2
      calc
        R ^ k / (k : ℝ) ≤ R ^ k :=
          div_le_self (pow_nonneg (by positivity) k) (by exact_mod_cast hk2)
        _ ≤ R ^ (n + 1) := pow_le_pow_right₀ hR hkn
    _ = ((Icc 2 (n + 1)).card : ℝ) * R ^ (n + 1) := by simp
    _ ≤ n * R ^ (n + 1) := by
      gcongr
      norm_cast
      simp

/-- The derivative of the finite perturbation remainder, written term by
term. -/
noncomputable def perturbationRemainderDeriv {n : ℕ}
    (z : Fin n → ℂ) (w : ℂ) : ℂ :=
  ∑ ell ∈ range (n + 1), if 2 ≤ ell then
    perturbationCoeff z ell *
      ((ell : ℂ) * w ^ (ell - 1) *
          truncatedExp (n - ell) (-powerSum z 1 * w) +
        w ^ ell * truncatedExpPred (n - ell) (-powerSum z 1 * w) *
          (-powerSum z 1))
  else 0

theorem hasDerivAt_perturbationRemainder {n : ℕ}
    (z : Fin n → ℂ) (w : ℂ) :
    @HasDerivAt ℂ _ ℂ
      instCommCStarAlgebraComplex.toCStarAlgebra.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℂ).toModule _ _
      (perturbationRemainder z) (perturbationRemainderDeriv z w) w := by
  unfold perturbationRemainder perturbationRemainderDeriv
  have hterm : ∀ ell ∈ range (n + 1), @HasDerivAt ℂ _ ℂ
      instCommCStarAlgebraComplex.toCStarAlgebra.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℂ).toModule _ _
      (fun u : ℂ ↦ if 2 ≤ ell then
        perturbationCoeff z ell * u ^ ell *
          truncatedExp (n - ell) (-powerSum z 1 * u) else 0)
      (if 2 ≤ ell then
        perturbationCoeff z ell *
          ((ell : ℂ) * w ^ (ell - 1) *
              truncatedExp (n - ell) (-powerSum z 1 * w) +
            w ^ ell * truncatedExpPred (n - ell) (-powerSum z 1 * w) *
              (-powerSum z 1)) else 0) w := by
    intro ell hell
    by_cases h2 : 2 ≤ ell
    · simp only [h2, if_true]
      have ht := (hasDerivAt_const w (perturbationCoeff z ell)).mul
        ((hasDerivAt_pow ell w).mul
          ((hasDerivAt_truncatedExp (n - ell) (-powerSum z 1 * w)).comp w
            ((hasDerivAt_id w).const_mul (-powerSum z 1))))
      have hfun : (fun u : ℂ ↦ perturbationCoeff z ell * u ^ ell *
          truncatedExp (n - ell) (-powerSum z 1 * u)) =ᶠ[𝓝 w]
          ((fun x ↦ perturbationCoeff z ell) *
            ((fun x ↦ x ^ ell) * truncatedExp (n - ell) ∘
              HMul.hMul (-powerSum z 1))) :=
        Filter.Eventually.of_forall fun u ↦ by
          simp only [Pi.mul_apply, Function.comp_apply]
          ring
      have ht' := ht.congr_of_eventuallyEq hfun
      simpa only [Pi.mul_apply, Function.comp_apply, zero_mul, zero_add, mul_one,
        mul_assoc] using ht'
    · simpa [h2] using (hasDerivAt_const w (0 : ℂ))
  exact (HasDerivAt.sum hterm).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ by
      rw [Finset.sum_apply])

private theorem norm_truncatedExpPred_le_exp_norm (m : ℕ) (u : ℂ) :
    ‖truncatedExpPred m u‖ ≤ Real.exp ‖u‖ := by
  cases m with
  | zero => simp [truncatedExpPred, (Real.exp_pos _).le]
  | succ m => exact norm_truncatedExp_le_exp_norm m u

/-- Differentiating equation (10) gives the exact decomposition used for
estimate (16). -/
theorem rootProduct_derivative_eval_eq_truncatedExpPred_add_remainderDeriv
    {n : ℕ} (z : Fin n → ℂ) (w : ℂ) :
    (rootProduct z).derivative.eval w =
      (-powerSum z 1) * truncatedExpPred n (-powerSum z 1 * w) +
        perturbationRemainderDeriv z w := by
  have hp := (rootProduct z).hasDerivAt w
  have ht := (hasDerivAt_truncatedExp n (-powerSum z 1 * w)).comp w
    ((hasDerivAt_id w).const_mul (-powerSum z 1))
  have hr := hasDerivAt_perturbationRemainder z w
  have hsum := ht.add hr
  have heq : (fun u : ℂ ↦ (rootProduct z).eval u) =
      fun u ↦ truncatedExp n (-powerSum z 1 * u) + perturbationRemainder z u := by
    funext u
    exact rootProduct_eval_eq_truncatedExp_add_remainder z u
  rw [heq] at hp
  have := hsum.unique hp
  convert this.symm using 1 <;> ring

/-- The derivative counterpart of `norm_perturbationRemainder_le_majorant`.
The factor `n + ‖x‖` is harmless on the normalized exterior scale. -/
theorem norm_perturbationRemainderDeriv_le_majorant {n : ℕ} (z : Fin n → ℂ)
    {w : ℂ} {epsilon R : ℝ} (hepsilon : 0 ≤ epsilon) (hR : 1 ≤ R)
    (hw : ‖w‖ ≤ R)
    (hsmall : ∀ k ∈ Finset.Icc 2 (n + 1), ‖powerSum z k‖ ≤ epsilon) :
    ‖perturbationRemainderDeriv z w‖ ≤
      Real.exp ‖-powerSum z 1 * w‖ * ((n : ℝ) + ‖-powerSum z 1‖) *
        (Real.exp (epsilon * perturbationMajorant n R) - 1) := by
  let b : ℕ → ℝ := fun ell ↦
    if 2 ≤ ell then ‖perturbationCoeff z ell‖ * R ^ ell else 0
  let C : ℝ := Real.exp ‖-powerSum z 1 * w‖ *
    ((n : ℝ) + ‖-powerSum z 1‖)
  have hb0 : ∀ ell, 0 ≤ b ell := by
    intro ell
    simp only [b]
    split_ifs <;> positivity
  have hC0 : 0 ≤ C := by simp [C]; positivity
  have hsummable : Summable b := by
    have hs := (summable_perturbationCoeff_norm_mul_pow z R).indicator
      {ell : ℕ | 2 ≤ ell}
    apply hs.congr
    intro ell
    rw [Set.indicator_apply]
    by_cases h2 : 2 ≤ ell <;> simp [b, h2]
  have hterm : ∀ ell ∈ range (n + 1),
      ‖if 2 ≤ ell then
        perturbationCoeff z ell *
          ((ell : ℂ) * w ^ (ell - 1) *
              truncatedExp (n - ell) (-powerSum z 1 * w) +
            w ^ ell * truncatedExpPred (n - ell) (-powerSum z 1 * w) *
              (-powerSum z 1)) else 0‖ ≤ b ell * C := by
    intro ell hell
    by_cases h2 : 2 ≤ ell
    · simp only [h2, if_true, norm_mul, norm_add_le]
      have helln : ell ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hell)
      have hellR : ‖w‖ ^ (ell - 1) ≤ R ^ ell := by
        calc
          ‖w‖ ^ (ell - 1) ≤ R ^ (ell - 1) :=
            pow_le_pow_left₀ (norm_nonneg w) hw _
          _ ≤ R ^ ell := pow_le_pow_right₀ hR (Nat.sub_le ell 1)
      have hwpow : ‖w‖ ^ ell ≤ R ^ ell :=
        pow_le_pow_left₀ (norm_nonneg w) hw _
      have hellcast : (ell : ℝ) ≤ n := by exact_mod_cast helln
      have htrunc := norm_truncatedExp_le_exp_norm (n - ell) (-powerSum z 1 * w)
      have hpred := norm_truncatedExpPred_le_exp_norm
        (n - ell) (-powerSum z 1 * w)
      rw [show b ell = ‖perturbationCoeff z ell‖ * R ^ ell by simp [b, h2]]
      dsimp only [C]
      calc
        ‖perturbationCoeff z ell‖ *
            ‖(ell : ℂ) * w ^ (ell - 1) *
                truncatedExp (n - ell) (-powerSum z 1 * w) +
              w ^ ell * truncatedExpPred (n - ell) (-powerSum z 1 * w) *
                (-powerSum z 1)‖ ≤
            ‖perturbationCoeff z ell‖ *
              (‖(ell : ℂ) * w ^ (ell - 1) *
                  truncatedExp (n - ell) (-powerSum z 1 * w)‖ +
                ‖w ^ ell * truncatedExpPred (n - ell) (-powerSum z 1 * w) *
                  (-powerSum z 1)‖) := by gcongr; exact norm_add_le _ _
        _ =
        ‖perturbationCoeff z ell‖ *
            ((ell : ℝ) * ‖w‖ ^ (ell - 1) *
                ‖truncatedExp (n - ell) (-powerSum z 1 * w)‖ +
              ‖w‖ ^ ell *
                ‖truncatedExpPred (n - ell) (-powerSum z 1 * w)‖ *
                  ‖-powerSum z 1‖) := by simp
        _ ≤
            ‖perturbationCoeff z ell‖ *
              ((n : ℝ) * R ^ ell * Real.exp ‖-powerSum z 1 * w‖ +
                R ^ ell * Real.exp ‖-powerSum z 1 * w‖ *
                  ‖-powerSum z 1‖) := by gcongr
        _ = ‖perturbationCoeff z ell‖ * R ^ ell *
            (Real.exp ‖-powerSum z 1 * w‖ *
              ((n : ℝ) + ‖-powerSum z 1‖)) := by ring
    · simp [h2, b]
  calc
    ‖perturbationRemainderDeriv z w‖ ≤
        ∑ ell ∈ range (n + 1),
          ‖if 2 ≤ ell then
            perturbationCoeff z ell *
              ((ell : ℂ) * w ^ (ell - 1) *
                  truncatedExp (n - ell) (-powerSum z 1 * w) +
                w ^ ell * truncatedExpPred (n - ell) (-powerSum z 1 * w) *
                  (-powerSum z 1)) else 0‖ := by
      rw [perturbationRemainderDeriv]
      exact norm_sum_le _ _
    _ ≤ ∑ ell ∈ range (n + 1), b ell * C := by
      exact sum_le_sum hterm
    _ = C * ∑ ell ∈ range (n + 1), b ell := by
      rw [mul_sum]
      apply sum_congr rfl
      intro ell hell
      ring
    _ ≤ C * ∑' ell : ℕ, b ell := by
      gcongr
      exact hsummable.sum_le_tsum (range (n + 1)) (fun ell hell ↦ hb0 ell)
    _ ≤ C * (Real.exp (epsilon * perturbationMajorant n R) - 1) := by
      gcongr
      simpa [b] using perturbationCoeff_majorant z hepsilon (zero_le_one.trans hR) hsmall
    _ = _ := by rfl

private theorem compact_uniform_upper_gap {K : Set ℂ} {f : ℂ → ℝ} {b : ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hf : ContinuousOn f K)
    (hlt : ∀ w ∈ K, f w < b) :
    ∃ b₀ : ℝ, (∀ w ∈ K, f w ≤ b₀) ∧ b₀ < b := by
  obtain ⟨w₀, hw₀, hmax⟩ := hK.exists_isMaxOn hKne hf
  exact ⟨f w₀, fun w hw ↦ hmax hw, hlt w₀ hw₀⟩

private theorem compact_uniform_lower_gap {K : Set ℂ} {f : ℂ → ℝ} {a : ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hf : ContinuousOn f K)
    (hlt : ∀ w ∈ K, a < f w) :
    ∃ a₀ : ℝ, a < a₀ ∧ ∀ w ∈ K, a₀ ≤ f w := by
  have hneg : ContinuousOn (fun w ↦ -f w) K := hf.neg
  obtain ⟨b₀, hb₀, hb⟩ := compact_uniform_upper_gap (f := fun w ↦ -f w)
    (b := -a) hK hKne hneg (fun w hw ↦ neg_lt_neg (hlt w hw))
  exact ⟨-b₀, by linarith, fun w hw ↦ by
    have h := hb₀ w hw
    change -f w ≤ b₀ at h
    linarith⟩

private theorem real_pow_eq_exp_log_mul {R : ℝ} (hR : 0 < R) (n : ℕ) :
    R ^ n = Real.exp (Real.log R * n) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hR]

private theorem eventually_const_mul_nat_le_exp
    (N : ℕ → ℕ) (hN : Tendsto (fun m ↦ (N m : ℝ)) atTop atTop)
    {eta C : ℝ} (heta : 0 < eta) (hC : 0 ≤ C) :
    ∀ᶠ m in atTop, C * N m ≤ Real.exp (eta * N m) := by
  have hlin : Tendsto (fun m ↦ eta * (N m : ℝ)) atTop atTop :=
    hN.const_mul_atTop heta
  have ht0 : Tendsto
      (fun m ↦ C * (N m : ℝ) * Real.exp (-(eta * N m))) atTop (𝓝 0) := by
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
    have ht' := ht.mul_const (C / eta)
    convert ht' using 1 <;> simp [heta.ne']
    funext m
    field_simp
  have hev : ∀ᶠ m in atTop,
      C * (N m : ℝ) * Real.exp (-(eta * N m)) ≤ 1 :=
    ht0.eventually_le_const zero_lt_one
  filter_upwards [hev] with m hm
  have hexppos := Real.exp_pos (eta * N m)
  calc
    C * (N m : ℝ) =
        (C * (N m : ℝ) * Real.exp (-(eta * N m))) *
          Real.exp (eta * N m) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ 1 * Real.exp (eta * N m) := by gcongr
    _ = _ := one_mul _

/-- The normalized logarithmic derivative appearing in (17). -/
noncomputable def normalizedRootLogDeriv (size : ℕ → ℕ)
    (z : ∀ m, Fin (size m) → ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  (rootProduct (z m)).derivative.eval w /
    ((size m : ℂ) * (rootProduct (z m)).eval w)

set_option maxHeartbeats 800000 in
/-- Sequence form of Proposition 3.3 on the disk supplied by Lemma 3.2. -/
theorem exterior_overconvergence_sequence
    (lambda : ℝ) (size : ℕ → ℕ) (hsize : StrictMono size)
    (z : ∀ m, Fin (size m) → ℂ) (c center : ℂ)
    (radius a Q R eta : ℝ)
    (hlambda : 0 < lambda) (hradius : 0 < radius) (ha : 0 < a)
    (hQ0 : 0 < Q) (hR0 : 0 < R) (heta : 0 < eta)
    (hRdef : R = ‖center‖ + radius) (hRexp : R < Real.exp lambda)
    (hQ1 : Q < 1)
    (hexterior : ∀ w ∈ closedBall center radius, 1 < ‖w‖)
    (hreal : ∀ w ∈ closedBall center radius, a < (c * w).re)
    (hnorm : ∀ w ∈ closedBall center radius, ‖c * w‖ < Q)
    (hmarginTail : 1 + Real.log Q + 5 * eta < a)
    (hmarginPerturb : Q - lambda + Real.log R + 5 * eta < a)
    (hsmall : ∀ m, ∀ k ∈ Icc 2 (size m + 1),
      ‖powerSum (z m) k‖ ≤ Real.exp (-lambda * size m))
    (hx : Tendsto (fun m ↦ (-powerSum (z m) 1) / (size m : ℂ))
      atTop (𝓝 c)) :
    ∃ sigma : ℝ, 0 < sigma ∧
      (∀ᶠ m in atTop, ∀ w ∈ closedBall center radius,
        ‖(rootProduct (z m)).eval w -
            Complex.exp (-powerSum (z m) 1 * w)‖ ≤
          Real.exp (((-powerSum (z m) 1 * w).re) - sigma * size m) ∧
        ‖(rootProduct (z m)).derivative.eval w -
            (-powerSum (z m) 1) * Complex.exp (-powerSum (z m) 1 * w)‖ ≤
          size m * Real.exp (((-powerSum (z m) 1 * w).re) - sigma * size m) ∧
        (rootProduct (z m)).eval w ≠ 0) ∧
      TendstoUniformlyOn (normalizedRootLogDeriv size z) (fun _ ↦ c)
        atTop (closedBall center radius) := by
  let K : Set ℂ := closedBall center radius
  let x : ℕ → ℂ := fun m ↦ -powerSum (z m) 1
  let N : ℕ → ℕ := size
  have hK : IsCompact K := isCompact_closedBall center radius
  have hKne : K.Nonempty := by
    refine ⟨center, ?_⟩
    simp [K, hradius.le]
  obtain ⟨a₀, haa₀, ha₀⟩ := compact_uniform_lower_gap hK hKne
    (Complex.continuous_re.comp (continuous_const.mul continuous_id) |>.continuousOn)
    (by simpa [K] using hreal)
  obtain ⟨q₀, hq₀, hq₀Q⟩ := compact_uniform_upper_gap hK hKne
    ((continuous_const.mul continuous_id).norm.continuousOn)
    (by simpa [K] using hnorm)
  have hNtop : Tendsto (fun m ↦ (N m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize.tendsto_atTop
  have hNpos : ∀ᶠ m in atTop, 0 < N m :=
    (hsize.tendsto_atTop.eventually (eventually_gt_atTop 0))
  have hRone : 1 < R := by
    have hc_mem : center ∈ K := by simp [K, hradius.le]
    have hcnorm : 1 < ‖center‖ := by simpa [K] using hexterior center hc_mem
    rw [hRdef]
    linarith
  have hy : Tendsto (fun m ↦ x m / (N m : ℂ)) atTop (𝓝 c) := by
    simpa [x, N] using hx
  have hyerr : Tendsto (fun m ↦ ‖x m / (N m : ℂ) - c‖) atTop (𝓝 0) := by
    simpa using hy.sub_const c |>.norm
  let delta : ℝ := min ((a₀ - a) / R) ((Q - q₀) / R)
  have hdelta : 0 < delta := by
    dsimp [delta]
    apply lt_min
    · exact div_pos (sub_pos.mpr haa₀) hR0
    · exact div_pos (sub_pos.mpr hq₀Q) hR0
  have herr : ∀ᶠ m in atTop, ‖x m / (N m : ℂ) - c‖ < delta :=
    hyerr.eventually_lt_const hdelta
  have hscale : ∀ᶠ m in atTop, ∀ w ∈ K,
      a * N m < (x m * w).re ∧ ‖x m * w‖ < Q * N m := by
    filter_upwards [hNpos, herr] with m hNm hem w hw
    have hNR : (0 : ℝ) < N m := by exact_mod_cast hNm
    have hwR : ‖w‖ ≤ R := by
      have hd : ‖w - center‖ ≤ radius := by
        simpa only [← dist_eq_norm] using (mem_closedBall.mp hw)
      rw [hRdef]
      calc
        ‖w‖ = ‖(w - center) + center‖ := by ring_nf
        _ ≤ ‖w - center‖ + ‖center‖ := norm_add_le _ _
        _ ≤ ‖center‖ + radius := by linarith
    have herrR : ‖x m / (N m : ℂ) - c‖ * ‖w‖ <
        min (a₀ - a) (Q - q₀) := by
      have hmul : ‖x m / (N m : ℂ) - c‖ * ‖w‖ < delta * R := by
        exact mul_lt_mul hem hwR
          (lt_trans zero_lt_one (by simpa [K] using hexterior w hw)) hdelta.le
      have hdeltaR : delta * R = min (a₀ - a) (Q - q₀) := by
        dsimp [delta]
        rw [min_mul_of_nonneg _ _ hR0.le, div_mul_cancel₀ _ hR0.ne',
          div_mul_cancel₀ _ hR0.ne']
      rwa [hdeltaR] at hmul
    have herrA : ‖x m / (N m : ℂ) - c‖ * ‖w‖ < a₀ - a :=
      herrR.trans_le (min_le_left _ _)
    have herrQ : ‖x m / (N m : ℂ) - c‖ * ‖w‖ < Q - q₀ :=
      herrR.trans_le (min_le_right _ _)
    have hxdiv : x m = (N m : ℂ) * (x m / (N m : ℂ)) := by
      exact (mul_div_cancel₀ (x m) (by exact_mod_cast hNm.ne')).symm
    have hreerr : |((x m / (N m : ℂ) - c) * w).re| ≤
        ‖x m / (N m : ℂ) - c‖ * ‖w‖ := by
      exact (Complex.abs_re_le_norm _).trans_eq (norm_mul _ _)
    have hrealnorm : a < ((x m / (N m : ℂ)) * w).re := by
      have hcw : a₀ ≤ (c * w).re := by simpa using ha₀ w hw
      have hadd : ((x m / (N m : ℂ)) * w).re =
          (c * w).re + ((x m / (N m : ℂ) - c) * w).re := by
        rw [show (x m / (N m : ℂ)) * w =
          c * w + (x m / (N m : ℂ) - c) * w by ring]
        exact Complex.add_re _ _
      rw [hadd]
      have hneg : -(a₀ - a) < ((x m / (N m : ℂ) - c) * w).re :=
        lt_of_lt_of_le (by linarith) (neg_abs_le _)
      linarith
    have hnormdiv : ‖(x m / (N m : ℂ)) * w‖ < Q := by
      calc
        ‖(x m / (N m : ℂ)) * w‖ ≤
            ‖c * w‖ + ‖(x m / (N m : ℂ) - c) * w‖ := by
          rw [show (x m / (N m : ℂ)) * w =
            c * w + (x m / (N m : ℂ) - c) * w by ring]
          exact norm_add_le _ _
        _ ≤ q₀ + ‖x m / (N m : ℂ) - c‖ * ‖w‖ := by
          gcongr
          · simpa using hq₀ w hw
          · rw [norm_mul]
        _ < Q := by linarith
    have hre : (x m * w).re = (N m : ℝ) * ((x m / (N m : ℂ)) * w).re := by
      calc
        (x m * w).re = (((N m : ℂ) * (x m / (N m : ℂ))) * w).re := by rw [← hxdiv]
        _ = (N m : ℝ) * ((x m / (N m : ℂ)) * w).re := by
          rw [mul_assoc, Complex.mul_re]
          simp
    have hnrm : ‖x m * w‖ = (N m : ℝ) * ‖(x m / (N m : ℂ)) * w‖ := by
      calc
        ‖x m * w‖ = ‖((N m : ℂ) * (x m / (N m : ℂ))) * w‖ := by rw [← hxdiv]
        _ = (N m : ℝ) * ‖(x m / (N m : ℂ)) * w‖ := by
          rw [mul_assoc, norm_mul, Complex.norm_natCast]
    constructor
    · rw [hre]
      nlinarith
    · rw [hnrm]
      nlinarith
  have haQ : a < Q := by
    have hc : center ∈ K := by simp [K, hradius.le]
    exact (hreal center (by simpa [K] using hc)).trans_le
      ((Complex.re_le_norm (c * center)).trans_lt (hnorm center (by simpa [K] using hc))).le
  have hlogR : Real.log R < lambda :=
    (Real.log_lt_iff_lt_exp hR0).2 hRexp
  have hrate : Real.log R - lambda + 5 * eta < 0 := by
    linarith
  have habsorbRN : ∀ᶠ m in atTop,
      R * N m ≤ Real.exp (eta * N m) :=
    eventually_const_mul_nat_le_exp N hNtop heta hR0.le
  have habsorbTwoN : ∀ᶠ m in atTop,
      2 * N m ≤ Real.exp (eta * N m) :=
    eventually_const_mul_nat_le_exp N hNtop heta (by norm_num)
  have habsorbQN : ∀ᶠ m in atTop,
      (1 + Q) * N m ≤ Real.exp (eta * N m) :=
    eventually_const_mul_nat_le_exp N hNtop heta (by linarith)
  have hmajorRate : ∀ᶠ m in atTop,
      Real.exp (Real.exp (-lambda * N m) * perturbationMajorant (N m) R) - 1 ≤
        Real.exp ((Real.log R - lambda + 2 * eta) * N m) := by
    have hdecayOne : ∀ᶠ m in atTop,
        Real.exp ((Real.log R - lambda + eta) * N m) ≤ 1 := by
      filter_upwards with m
      rw [Real.exp_le_one_iff]
      have hN0 : 0 ≤ (N m : ℝ) := by positivity
      nlinarith
    filter_upwards [habsorbRN, habsorbTwoN, hdecayOne, hNpos] with m hRN htwo hdec hNm
    let t : ℝ := Real.exp (-lambda * N m) * perturbationMajorant (N m) R
    have ht0 : 0 ≤ t := by
      dsimp [t]
      apply mul_nonneg (Real.exp_pos _).le
      unfold perturbationMajorant
      positivity
    have htRate : t ≤ Real.exp ((Real.log R - lambda + eta) * N m) := by
      dsimp [t]
      calc
        Real.exp (-lambda * N m) * perturbationMajorant (N m) R ≤
            Real.exp (-lambda * N m) * ((N m : ℝ) * R ^ (N m + 1)) := by
          gcongr
          exact perturbationMajorant_le_nat_mul_pow (N m) hRone.le
        _ = Real.exp (-lambda * N m) *
            ((R * N m) * R ^ N m) := by rw [pow_succ]; ring
        _ ≤ Real.exp (-lambda * N m) *
            (Real.exp (eta * N m) * R ^ N m) := by gcongr
        _ = Real.exp ((Real.log R - lambda + eta) * N m) := by
          rw [real_pow_eq_exp_log_mul hR0]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact htRate.trans hdec
    have hexp := Real.abs_exp_sub_one_le ht1
    have hexp0 : 0 ≤ Real.exp t - 1 := by linarith [Real.one_le_exp ht0]
    calc
      Real.exp (Real.exp (-lambda * N m) * perturbationMajorant (N m) R) - 1 =
          Real.exp t - 1 := by rfl
      _ ≤ 2 * t := by simpa [abs_of_nonneg ht0, abs_of_nonneg hexp0] using hexp
      _ ≤ 2 * Real.exp ((Real.log R - lambda + eta) * N m) := by gcongr
      _ ≤ Real.exp (eta * N m) *
          Real.exp ((Real.log R - lambda + eta) * N m) := by
        exact mul_le_mul_of_nonneg_right
          (le_trans (by
            have hNone : (1 : ℝ) ≤ N m := by exact_mod_cast hNm
            nlinarith) htwo)
          (Real.exp_pos _).le
      _ = Real.exp ((Real.log R - lambda + 2 * eta) * N m) := by
        rw [← Real.exp_add]
        congr 1
        ring
  obtain ⟨n₀, htail⟩ := exponential_tail_bound hQ0 hQ1 heta
  have hn₀ : ∀ᶠ m in atTop, n₀ ≤ N m :=
    hsize.tendsto_atTop.eventually (eventually_ge_atTop n₀)
  have hestimates : ∀ᶠ m in atTop, ∀ w ∈ K,
      ‖(rootProduct (z m)).eval w - Complex.exp (x m * w)‖ ≤
          Real.exp ((x m * w).re - eta * N m) ∧
      ‖(rootProduct (z m)).derivative.eval w -
          x m * Complex.exp (x m * w)‖ ≤
          N m * Real.exp ((x m * w).re - eta * N m) := by
    filter_upwards [hscale, hmajorRate, habsorbTwoN, habsorbQN, hNpos, hn₀]
      with m hsc hmaj htwo hQN hNm hn₀m w hw
    have hNR : (0 : ℝ) < N m := by exact_mod_cast hNm
    have hwR : ‖w‖ ≤ R := by
      have hd : ‖w - center‖ ≤ radius := by
        simpa only [← dist_eq_norm] using (mem_closedBall.mp hw)
      rw [hRdef]
      calc
        ‖w‖ = ‖(w - center) + center‖ := by ring_nf
        _ ≤ ‖w - center‖ + ‖center‖ := norm_add_le _ _
        _ ≤ ‖center‖ + radius := by linarith
    obtain ⟨hre, hnormu⟩ := hsc w hw
    have htail' := htail (N m) hn₀m (x m * w) hnormu.le
    have htailFun : ‖Complex.exp (x m * w) - truncatedExp (N m) (x m * w)‖ ≤
        Real.exp ((x m * w).re - 4 * eta * N m) := by
      calc
        ‖Complex.exp (x m * w) - truncatedExp (N m) (x m * w)‖ ≤
            ‖Complex.exp (x m * w) - truncatedExp (N m) (x m * w)‖ +
              ‖Complex.exp (x m * w) - truncatedExpPred (N m) (x m * w)‖ := by
          exact le_add_of_nonneg_right (norm_nonneg _)
        _ ≤ Real.exp ((1 + Real.log Q + eta) * N m) := htail'
        _ ≤ Real.exp ((x m * w).re - 4 * eta * N m) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hmarginTail]
    have htailDeriv :
        ‖Complex.exp (x m * w) - truncatedExpPred (N m) (x m * w)‖ ≤
          Real.exp ((x m * w).re - 4 * eta * N m) := by
      calc
        ‖Complex.exp (x m * w) - truncatedExpPred (N m) (x m * w)‖ ≤
            ‖Complex.exp (x m * w) - truncatedExp (N m) (x m * w)‖ +
              ‖Complex.exp (x m * w) - truncatedExpPred (N m) (x m * w)‖ := by
          exact le_add_of_nonneg_left (norm_nonneg _)
        _ ≤ Real.exp ((1 + Real.log Q + eta) * N m) := htail'
        _ ≤ Real.exp ((x m * w).re - 4 * eta * N m) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hmarginTail]
    have hrem0 := norm_perturbationRemainder_le_majorant (z m)
      (epsilon := Real.exp (-lambda * N m)) (R := R) (by positivity) hR0.le hwR
      (by simpa [N] using hsmall m)
    have hrem : ‖perturbationRemainder (z m) w‖ ≤
        Real.exp ((x m * w).re - 3 * eta * N m) := by
      calc
        ‖perturbationRemainder (z m) w‖ ≤
            Real.exp ‖x m * w‖ *
              (Real.exp (Real.exp (-lambda * N m) *
                perturbationMajorant (N m) R) - 1) := by simpa [x, N] using hrem0
        _ ≤ Real.exp (Q * N m) *
              Real.exp ((Real.log R - lambda + 2 * eta) * N m) := by
          exact mul_le_mul (Real.exp_le_exp.mpr hnormu.le) hmaj
            (by
              have harg : 0 ≤ Real.exp (-lambda * N m) *
                  perturbationMajorant (N m) R := by
                apply mul_nonneg (Real.exp_pos _).le
                unfold perturbationMajorant
                positivity
              linarith [Real.one_le_exp harg])
            (Real.exp_pos _).le
        _ = Real.exp ((Q - lambda + Real.log R + 2 * eta) * N m) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp ((x m * w).re - 3 * eta * N m) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hmarginPerturb]
    have hxnorm : ‖x m‖ < Q * N m := by
      have hwone : 1 < ‖w‖ := by simpa [K] using hexterior w hw
      have hxle : ‖x m‖ ≤ ‖x m‖ * ‖w‖ := by
        nlinarith [norm_nonneg (x m)]
      exact hxle.trans_lt (by simpa [norm_mul] using hnormu)
    have hfactor : (N m : ℝ) + ‖x m‖ ≤ Real.exp (eta * N m) := by
      have hf : (N m : ℝ) + ‖x m‖ ≤ (1 + Q) * N m := by nlinarith
      exact hf.trans hQN
    have hremD0 := norm_perturbationRemainderDeriv_le_majorant (z m)
      (epsilon := Real.exp (-lambda * N m)) (R := R) (by positivity) hRone.le hwR
      (by simpa [N] using hsmall m)
    have hremD : ‖perturbationRemainderDeriv (z m) w‖ ≤
        Real.exp ((x m * w).re - 2 * eta * N m) := by
      have hS0 : 0 ≤ Real.exp (Real.exp (-lambda * N m) *
          perturbationMajorant (N m) R) - 1 := by
        have harg : 0 ≤ Real.exp (-lambda * N m) *
            perturbationMajorant (N m) R := by
          apply mul_nonneg (Real.exp_pos _).le
          unfold perturbationMajorant
          positivity
        linarith [Real.one_le_exp harg]
      calc
        ‖perturbationRemainderDeriv (z m) w‖ ≤
            Real.exp ‖x m * w‖ * ((N m : ℝ) + ‖x m‖) *
              (Real.exp (Real.exp (-lambda * N m) *
                perturbationMajorant (N m) R) - 1) := by simpa [x, N] using hremD0
        _ ≤ Real.exp (Q * N m) * Real.exp (eta * N m) *
              Real.exp ((Real.log R - lambda + 2 * eta) * N m) := by
          exact mul_le_mul
            (mul_le_mul (Real.exp_le_exp.mpr hnormu.le) hfactor
              (by positivity) (Real.exp_pos _).le)
            hmaj hS0 (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
        _ = Real.exp ((Q - lambda + Real.log R + 3 * eta) * N m) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp ((x m * w).re - 2 * eta * N m) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hmarginPerturb]
    have htwo' : (2 : ℝ) ≤ Real.exp (eta * N m) := by
      have hNone : (1 : ℝ) ≤ N m := by exact_mod_cast hNm
      have h2N : (2 : ℝ) ≤ 2 * N m := by nlinarith
      exact h2N.trans htwo
    constructor
    · rw [rootProduct_eval_eq_truncatedExp_add_remainder]
      calc
        ‖truncatedExp (N m) (x m * w) + perturbationRemainder (z m) w -
            Complex.exp (x m * w)‖ ≤
            ‖Complex.exp (x m * w) - truncatedExp (N m) (x m * w)‖ +
              ‖perturbationRemainder (z m) w‖ := by
          rw [show truncatedExp (N m) (x m * w) + perturbationRemainder (z m) w -
              Complex.exp (x m * w) =
            -(Complex.exp (x m * w) - truncatedExp (N m) (x m * w)) +
              perturbationRemainder (z m) w by ring]
          simpa [norm_neg, add_comm, norm_sub_rev] using norm_add_le
            (-(Complex.exp (x m * w) - truncatedExp (N m) (x m * w)))
            (perturbationRemainder (z m) w)
        _ ≤ 2 * Real.exp ((x m * w).re - 3 * eta * N m) := by
          have htmono : Real.exp ((x m * w).re - 4 * eta * N m) ≤
              Real.exp ((x m * w).re - 3 * eta * N m) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          nlinarith [htailFun, hrem, Real.exp_pos ((x m * w).re - 3 * eta * N m)]
        _ ≤ Real.exp ((x m * w).re - 2 * eta * N m) := by
          calc
            2 * Real.exp ((x m * w).re - 3 * eta * N m) ≤
                Real.exp (eta * N m) *
                  Real.exp ((x m * w).re - 3 * eta * N m) := by gcongr
            _ = Real.exp ((x m * w).re - 2 * eta * N m) := by
              rw [← Real.exp_add]
              congr 1
              ring
        _ ≤ Real.exp ((x m * w).re - eta * N m) := by
          apply Real.exp_le_exp.mpr
          nlinarith
    · rw [rootProduct_derivative_eval_eq_truncatedExpPred_add_remainderDeriv]
      calc
        ‖x m * truncatedExpPred (N m) (x m * w) +
            perturbationRemainderDeriv (z m) w - x m * Complex.exp (x m * w)‖ ≤
            ‖x m‖ * ‖Complex.exp (x m * w) -
              truncatedExpPred (N m) (x m * w)‖ +
              ‖perturbationRemainderDeriv (z m) w‖ := by
          rw [show x m * truncatedExpPred (N m) (x m * w) +
              perturbationRemainderDeriv (z m) w - x m * Complex.exp (x m * w) =
            -(x m * (Complex.exp (x m * w) -
              truncatedExpPred (N m) (x m * w))) +
              perturbationRemainderDeriv (z m) w by ring]
          calc
            ‖-(x m * (Complex.exp (x m * w) -
                truncatedExpPred (N m) (x m * w))) +
                perturbationRemainderDeriv (z m) w‖ ≤
                ‖-(x m * (Complex.exp (x m * w) -
                  truncatedExpPred (N m) (x m * w)))‖ +
                  ‖perturbationRemainderDeriv (z m) w‖ := norm_add_le _ _
            _ = _ := by simp [norm_mul]
        _ ≤ (N m : ℝ) * Real.exp ((x m * w).re - 3 * eta * N m) +
              Real.exp ((x m * w).re - 2 * eta * N m) := by
          have hp : ‖x m‖ * ‖Complex.exp (x m * w) -
                truncatedExpPred (N m) (x m * w)‖ ≤
              (N m : ℝ) * Real.exp ((x m * w).re - 3 * eta * N m) := by
            calc
            ‖x m‖ * ‖Complex.exp (x m * w) -
                truncatedExpPred (N m) (x m * w)‖ ≤
                (Q * N m) * Real.exp ((x m * w).re - 4 * eta * N m) := by
                  exact mul_le_mul hxnorm.le htailDeriv (norm_nonneg _) (by positivity)
            _ ≤ (N m : ℝ) * Real.exp ((x m * w).re - 3 * eta * N m) := by
              have hQexp : Q ≤ Real.exp (eta * N m) :=
                hQ1.le.trans (Real.one_le_exp (mul_nonneg heta.le hNR.le))
              calc
                (Q * N m) * Real.exp ((x m * w).re - 4 * eta * N m) ≤
                    (Real.exp (eta * N m) * N m) *
                      Real.exp ((x m * w).re - 4 * eta * N m) := by gcongr
                _ = (N m : ℝ) * Real.exp ((x m * w).re - 3 * eta * N m) := by
                  rw [show Real.exp (eta * N m) * (N m : ℝ) *
                    Real.exp ((x m * w).re - 4 * eta * N m) =
                    (N m : ℝ) * (Real.exp (eta * N m) *
                      Real.exp ((x m * w).re - 4 * eta * N m)) by ring,
                    ← Real.exp_add]
                  congr 2
                  ring
          exact add_le_add hp hremD
        _ ≤ 2 * (N m : ℝ) * Real.exp ((x m * w).re - 2 * eta * N m) := by
          have hNone : (1 : ℝ) ≤ N m := by exact_mod_cast hNm
          have hemono : Real.exp ((x m * w).re - 3 * eta * N m) ≤
              Real.exp ((x m * w).re - 2 * eta * N m) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          nlinarith [hremD, Real.exp_pos ((x m * w).re - 2 * eta * N m)]
        _ ≤ (N m : ℝ) * Real.exp ((x m * w).re - eta * N m) := by
          calc
            2 * (N m : ℝ) * Real.exp ((x m * w).re - 2 * eta * N m) ≤
                Real.exp (eta * N m) * (N m : ℝ) *
                  Real.exp ((x m * w).re - 2 * eta * N m) := by gcongr
            _ = (N m : ℝ) * Real.exp ((x m * w).re - eta * N m) := by
              rw [show Real.exp (eta * N m) * (N m : ℝ) *
                Real.exp ((x m * w).re - 2 * eta * N m) =
                (N m : ℝ) * (Real.exp (eta * N m) *
                  Real.exp ((x m * w).re - 2 * eta * N m)) by ring,
                ← Real.exp_add]
              congr 2
              ring
  have hnonzero : ∀ᶠ m in atTop, ∀ w ∈ K,
      (rootProduct (z m)).eval w ≠ 0 := by
    filter_upwards [hestimates, hNpos] with m hest hNm w hw
    intro hzero
    obtain ⟨hp, hd⟩ := hest w hw
    have hnormexp : ‖Complex.exp (x m * w)‖ = Real.exp (x m * w).re :=
      Complex.norm_exp _
    have hle : Real.exp (x m * w).re ≤
        Real.exp ((x m * w).re - eta * N m) := by
      rw [hzero, zero_sub, norm_neg, hnormexp] at hp
      exact hp
    have hlt : Real.exp ((x m * w).re - eta * N m) <
        Real.exp (x m * w).re := by
      apply Real.exp_lt_exp.mpr
      have hNR : (0 : ℝ) < N m := by exact_mod_cast hNm
      nlinarith
    exact (not_lt_of_ge hle) hlt
  have hlinEta : Tendsto (fun m ↦ eta * (N m : ℝ)) atTop atTop :=
    hNtop.const_mul_atTop heta
  have hqzero : Tendsto (fun m ↦ Real.exp (-eta * N m)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinEta
  have huniform : TendstoUniformlyOn (normalizedRootLogDeriv size z) (fun _ ↦ c)
      atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    have hqhalf : ∀ᶠ m in atTop, Real.exp (-eta * N m) ≤ 1 / 2 :=
      hqzero.eventually_le_const (by norm_num)
    have hqeps : ∀ᶠ m in atTop,
        2 * (1 + Q) * Real.exp (-eta * N m) < eps / 2 := by
      have ht : Tendsto (fun m ↦ 2 * (1 + Q) * Real.exp (-eta * N m))
          atTop (𝓝 0) := by simpa using hqzero.const_mul (2 * (1 + Q))
      exact ht.eventually_lt_const (half_pos heps)
    have hyhalf : ∀ᶠ m in atTop, ‖x m / (N m : ℂ) - c‖ < eps / 2 :=
      hyerr.eventually_lt_const (half_pos heps)
    filter_upwards [hestimates, hnonzero, hscale, hNpos, hqhalf, hqeps, hyhalf]
      with m hest hnz hsc hNm hhalf hqe hyh w hw
    obtain ⟨hp, hd⟩ := hest w hw
    obtain ⟨hre, hnormu⟩ := hsc w hw
    have hz := hnz w hw
    let F : ℂ := (rootProduct (z m)).eval w
    let D : ℂ := (rootProduct (z m)).derivative.eval w
    let E : ℂ := Complex.exp (x m * w)
    have hNR : (0 : ℝ) < N m := by exact_mod_cast hNm
    have hxnorm : ‖x m‖ < Q * N m := by
      have hwone : 1 < ‖w‖ := by simpa [K] using hexterior w hw
      have hxle : ‖x m‖ ≤ ‖x m‖ * ‖w‖ := by
        nlinarith [norm_nonneg (x m)]
      exact hxle.trans_lt (by simpa [norm_mul] using hnormu)
    have hE : ‖E‖ = Real.exp (x m * w).re := by
      simp [E, Complex.norm_exp]
    have hqrewrite : Real.exp ((x m * w).re - eta * N m) =
        ‖E‖ * Real.exp (-eta * N m) := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring
    have hFlower : Real.exp (x m * w).re / 2 ≤ ‖F‖ := by
      have hrev : ‖E‖ ≤ ‖F - E‖ + ‖F‖ := by
        calc
          ‖E‖ = ‖(F - E) - F‖ := by
            rw [show (F - E) - F = -E by ring, norm_neg]
          _ ≤ ‖F - E‖ + ‖F‖ := norm_sub_le _ _
      have hp' : ‖F - E‖ ≤ ‖E‖ / 2 := by
        calc
          ‖F - E‖ ≤ Real.exp ((x m * w).re - eta * N m) := by simpa [F, E] using hp
          _ = ‖E‖ * Real.exp (-eta * N m) := hqrewrite
          _ ≤ ‖E‖ * (1 / 2) := by gcongr
          _ = ‖E‖ / 2 := by ring
      rw [hE] at hrev hp'
      linarith
    have hnum : ‖D - x m * F‖ ≤
        (1 + Q) * N m * Real.exp ((x m * w).re - eta * N m) := by
      calc
        ‖D - x m * F‖ =
            ‖(D - x m * E) - x m * (F - E)‖ := by
          congr 1
          ring
        _ ≤ ‖D - x m * E‖ + ‖x m * (F - E)‖ := norm_sub_le _ _
        _ ≤ (N m : ℝ) * Real.exp ((x m * w).re - eta * N m) +
            ‖x m‖ * Real.exp ((x m * w).re - eta * N m) := by
          rw [norm_mul]
          exact add_le_add (by simpa [D, E] using hd)
            (mul_le_mul_of_nonneg_left (by simpa [F, E] using hp) (norm_nonneg _))
        _ ≤ (1 + Q) * N m *
            Real.exp ((x m * w).re - eta * N m) := by
          have he := Real.exp_pos ((x m * w).re - eta * N m)
          nlinarith
    have hden : (N m : ℝ) * Real.exp (x m * w).re / 2 ≤
        ‖(N m : ℂ) * F‖ := by
      rw [norm_mul, Complex.norm_natCast]
      nlinarith [hFlower]
    have hdenpos : 0 < ‖(N m : ℂ) * F‖ := by
      rw [norm_pos_iff]
      exact mul_ne_zero (by exact_mod_cast hNm.ne') (by simpa [F] using hz)
    have hquot : ‖D / ((N m : ℂ) * F) - x m / (N m : ℂ)‖ ≤
        2 * (1 + Q) * Real.exp (-eta * N m) := by
      have halg : D / ((N m : ℂ) * F) - x m / (N m : ℂ) =
          (D - x m * F) / ((N m : ℂ) * F) := by
        have hFne : F ≠ 0 := by simpa [F] using hz
        field_simp [hFne, hNm.ne']
      rw [halg, norm_div]
      apply (div_le_iff₀ hdenpos).2
      calc
        ‖D - x m * F‖ ≤
            (1 + Q) * N m * Real.exp ((x m * w).re - eta * N m) := hnum
        _ = 2 * (1 + Q) * Real.exp (-eta * N m) *
            ((N m : ℝ) * Real.exp (x m * w).re / 2) := by
          calc
            (1 + Q) * (N m : ℝ) *
                Real.exp ((x m * w).re - eta * N m) =
                (1 + Q) * (N m : ℝ) *
                  (Real.exp (-eta * N m) * Real.exp (x m * w).re) := by
              rw [← Real.exp_add]
              congr 2
              ring
            _ = _ := by ring
        _ ≤ 2 * (1 + Q) * Real.exp (-eta * N m) *
            ‖(N m : ℂ) * F‖ := by
          gcongr
    have htotal : ‖D / ((N m : ℂ) * F) - c‖ < eps := by
      calc
        ‖D / ((N m : ℂ) * F) - c‖ ≤
            ‖D / ((N m : ℂ) * F) - x m / (N m : ℂ)‖ +
              ‖x m / (N m : ℂ) - c‖ := by
          rw [show D / ((N m : ℂ) * F) - c =
            (D / ((N m : ℂ) * F) - x m / (N m : ℂ)) +
              (x m / (N m : ℂ) - c) by ring]
          exact norm_add_le _ _
        _ < eps := by linarith
    simpa [normalizedRootLogDeriv, F, D, x, N, K, dist_eq_norm,
      norm_sub_rev] using htotal
  refine ⟨eta, heta, ?_, ?_⟩
  · filter_upwards [hestimates, hnonzero] with m hest hnz w hw
    have hwK : w ∈ K := by simpa [K] using hw
    change
      ‖(rootProduct (z m)).eval w - Complex.exp (x m * w)‖ ≤
          Real.exp ((x m * w).re - eta * N m) ∧
      ‖(rootProduct (z m)).derivative.eval w - x m * Complex.exp (x m * w)‖ ≤
          N m * Real.exp ((x m * w).re - eta * N m) ∧
      (rootProduct (z m)).eval w ≠ 0
    exact ⟨(hest w hwK).1, (hest w hwK).2, hnz w hwK⟩
  · simpa [K] using huniform

end Erdos973
