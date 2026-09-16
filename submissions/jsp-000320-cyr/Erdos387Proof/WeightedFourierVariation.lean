import Erdos387Proof.FourierVariation
import ErdosProblems.Erdos387.ProgressionFourier

/-! Finite Fourier coefficient mass from variation, retaining the original
whole interval for character-uniform cancellation estimates. -/

set_option autoImplicit false
namespace Erdos387Proof.WeightedFourierVariation
open FiniteAbel Erdos387
open scoped BigOperators

/-- Abel summation followed by summation over frequencies. The hypothesis
is an L1 bound on unweighted prefix kernels, not cancellation on shorter
intervals of the target oscillatory sequence. -/
theorem sum_norm_weighted_sums_le {ι : Type*} (H : Finset ι)
    (w : ℕ → ℂ) (f : ι → ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hprefix : ∀ m≤N, (∑ h ∈ H, ‖∑ n ∈ Finset.range m, f h n‖)≤B) :
    (∑ h ∈ H, ‖∑ n ∈ Finset.range N, w n*f h n‖)≤variationMass w N*B := by
  have hpoint (h : ι) :
      ‖∑ n ∈ Finset.range N, w n*f h n‖ ≤
        ‖w (N-1)‖*‖∑ n ∈ Finset.range N, f h n‖ +
        ∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖*‖∑ n ∈ Finset.range (i+1), f h n‖ := by
    have he := Finset.sum_range_by_parts w (f h) N
    simp only [smul_eq_mul] at he
    rw [he]
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    exact add_le_add le_rfl ((norm_sum_le _ _).trans_eq (by simp only [norm_mul]))
  calc
    _ ≤ ∑ h ∈ H, (‖w (N-1)‖*‖∑ n ∈ Finset.range N, f h n‖ +
        ∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖*‖∑ n ∈ Finset.range (i+1), f h n‖) :=
      Finset.sum_le_sum (fun h _ => hpoint h)
    _ = ‖w (N-1)‖*(∑ h ∈ H, ‖∑ n ∈ Finset.range N, f h n‖) +
        ∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖*
          (∑ h ∈ H, ‖∑ n ∈ Finset.range (i+1), f h n‖) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ ‖w (N-1)‖*B + ∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖*B := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hprefix N le_rfl) (norm_nonneg _)
      · apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (hprefix (i+1) (by have := Finset.mem_range.mp hi; omega)) (norm_nonneg _)
    _ = _ := by rw [variationMass,add_mul,Finset.sum_mul]

theorem sum_Ioc_eq_sum_range (A : ℤ) (N : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Ioc A (A+N), f n)=∑ j ∈ Finset.range N, f (A+1+j) := by
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => A+1+(j : ℤ))
  · intro j hj
    have := Finset.mem_range.mp hj
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro a ha b hb he
    omega
  · intro n hn
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hn
    refine ⟨(n-A-1).toNat,Finset.mem_range.mpr (by omega),?_⟩
    omega
  · intro j hj
    rfl

noncomputable def coefficient (q : ℕ) [NeZero q] (A : ℤ) (N : ℕ)
    (w : ℕ → ℂ) (h : ZMod q) : ℂ :=
  (∑ j ∈ Finset.range N, w j*ZMod.stdAddChar (h*((A+1+j : ℤ) : ZMod q)))/(q : ℂ)

/-- Normalized coefficient L1 is logarithmic times actual weight variation.
No norm bound on each coefficient is multiplied by the number of frequencies. -/
theorem sum_norm_coefficient_le (q : ℕ) [NeZero q] (A : ℤ) (N : ℕ)
    (w : ℕ → ℂ) (hN : N≤q) :
    (∑ h : ZMod q, ‖coefficient q A N w h‖)≤variationMass w N*(Real.log q+1) := by
  have hp : ∀ m≤N, (∑ h : ZMod q,
      ‖∑ j ∈ Finset.range m, ZMod.stdAddChar (h*((A+1+j : ℤ) : ZMod q))‖) ≤
      (q : ℝ)*(Real.log q+1) := by
    intro m hm
    have he (h : ZMod q) : (∑ j ∈ Finset.range m,
        ZMod.stdAddChar (h*((A+1+j : ℤ) : ZMod q))) =
        ProgressionFourier.intCoefficient q (Finset.Ioc A (A+m)) h := by
      exact (sum_Ioc_eq_sum_range A m (fun n => ZMod.stdAddChar (h*(n : ZMod q)))).symm
    simp_rw [he]
    exact ProgressionFourier.sum_norm_intCoefficient_Ioc_le q A m (hm.trans hN)
  have hb := sum_norm_weighted_sums_le Finset.univ w
    (fun (h : ZMod q) j => ZMod.stdAddChar (h*((A+1+j : ℤ) : ZMod q))) N hp
  simp only [coefficient,norm_div,Complex.norm_natCast]
  rw [← Finset.sum_div]
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply (div_le_iff₀ hq).mpr
  exact hb.trans_eq (by ring)



/-- Exact weighted inversion, retaining possible residue multiplicity. -/
theorem phase_sum_eq_fibre (q : ℕ) [NeZero q] (A : ℤ) (N : ℕ)
    (w : ℕ → ℂ) (a : ZMod q) :
    (∑ h : ZMod q, coefficient q A N w h*ZMod.stdAddChar (-h*a)) =
      ∑ j ∈ Finset.range N, if ((A+1+j : ℤ) : ZMod q)=a then w j else 0 := by
  classical
  have hq : (q : ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have hterm (h : ZMod q) (j : ℕ) :
      ZMod.stdAddChar (h*((A+1+j : ℤ) : ZMod q))*ZMod.stdAddChar (-h*a) =
        ZMod.stdAddChar (h*(((A+1+j : ℤ) : ZMod q)-a)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    _ = ∑ h : ZMod q, ∑ j ∈ Finset.range N,
        (w j*ZMod.stdAddChar (h*(((A+1+j : ℤ) : ZMod q)-a)))/(q : ℂ) := by
      apply Finset.sum_congr rfl
      intro h hh
      unfold coefficient
      rw [Finset.sum_div,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_mul_eq_mul_div,mul_assoc,hterm]
    _ = ∑ j ∈ Finset.range N, w j*
        (∑ h : ZMod q, ZMod.stdAddChar (h*(((A+1+j : ℤ) : ZMod q)-a)))/(q : ℂ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum,Finset.sum_div]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [AdditiveOrthogonality.sum_stdAddChar_mul]
      by_cases he : ((A+1+j : ℤ) : ZMod q)=a
      · simp [he,hq]
      · push_cast at he ⊢
        simp [he,sub_ne_zero.mpr he]

theorem inversion (q : ℕ) [NeZero q] (A : ℤ) (N : ℕ)
    (w : ℕ → ℂ) (hN : N≤q) {j : ℕ} (hj : j<N) :
    (∑ h : ZMod q, coefficient q A N w h*
      ZMod.stdAddChar (-h*((A+1+j : ℤ) : ZMod q)))=w j := by
  rw [phase_sum_eq_fibre]
  have he (n : ℕ) (hn : n∈Finset.range N) :
      (((A+1+n : ℤ) : ZMod q)=((A+1+j : ℤ) : ZMod q)) ↔ n=j := by
    push_cast
    rw [add_right_inj]
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ((Finset.mem_range.mp hn).trans_le hN),
        Nat.mod_eq_of_lt (hj.trans_le hN)] using hv
    · intro h
      rw [h]
  calc
    _ = ∑ n ∈ Finset.range N, if n=j then w n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [he n hn]
    _ = w j := by simp [Finset.mem_range.mpr hj]

/-- The target sequence stays on its whole original interval in every
Fourier twist; no estimate on shorter intervals is assumed. -/
theorem weighted_sum_eq_twists (q : ℕ) [NeZero q] (A : ℤ) (N : ℕ)
    (w f : ℕ → ℂ) (hN : N≤q) :
    (∑ j ∈ Finset.range N, w j*f j) =
      ∑ h : ZMod q, coefficient q A N w h*
        (∑ j ∈ Finset.range N, ZMod.stdAddChar (-h*((A+1+j : ℤ) : ZMod q))*f j) := by
  calc
    _ = ∑ j ∈ Finset.range N, (∑ h : ZMod q, coefficient q A N w h*
        ZMod.stdAddChar (-h*((A+1+j : ℤ) : ZMod q)))*f j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [inversion q A N w hN (Finset.mem_range.mp hj)]
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem norm_weighted_sum_le_of_twists (q : ℕ) [NeZero q] (A : ℤ) (N : ℕ)
    (w f : ℕ → ℂ) (hN : N≤q) {B : ℝ}
    (htwist : ∀ h : ZMod q,
      ‖∑ j ∈ Finset.range N, ZMod.stdAddChar (-h*((A+1+j : ℤ) : ZMod q))*f j‖≤B) :
    ‖∑ j ∈ Finset.range N, w j*f j‖ ≤ variationMass w N*(Real.log q+1)*B := by
  have hB : 0≤B := (norm_nonneg _).trans (htwist 0)
  rw [weighted_sum_eq_twists q A N w f hN]
  calc
    _ ≤ ∑ h : ZMod q, ‖coefficient q A N w h*
        (∑ j ∈ Finset.range N, ZMod.stdAddChar (-h*((A+1+j : ℤ) : ZMod q))*f j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h : ZMod q, ‖coefficient q A N w h‖*B := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (htwist h) (norm_nonneg _)
    _ = (∑ h : ZMod q, ‖coefficient q A N w h‖)*B := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_norm_coefficient_le q A N w hN) hB

end Erdos387Proof.WeightedFourierVariation
