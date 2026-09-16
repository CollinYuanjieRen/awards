import Erdos387Proof.WeightedCharacterInterval
import Erdos387Proof.IntervalWeightVariation

/-! Exact sharp interval restrictions inside a weighted whole-interval
character estimate. The cost of both endpoints is explicit. -/

set_option autoImplicit false
namespace Erdos387Proof.WeightedIntervalCut
open FiniteAbel FourierVariation WeightedCharacterInterval IntervalWeightVariation
open scoped BigOperators

theorem norm_weighted_cut_Ioc_le (A N lo hi : ℕ) (w f : ℕ → ℂ) {B : ℝ}
    (hlo : lo≤hi)
    (htwist : ∀ χ : AddChar ℤ ℂ, (∀ n, ‖χ n‖=1) →
      ‖∑ n ∈ Finset.Ioc A (A+N), χ (n : ℤ)*f n‖≤B) :
    ‖∑ n ∈ Finset.Ioc A (A+N), if lo<n ∧ n≤hi then w n*f n else 0‖ ≤
      (4*variationMass (fun j => w (A+1+j)) N)*(Real.log (N+1 : ℕ)+1)*B := by
  have hB : 0≤B := (norm_nonneg _).trans (htwist 1 (by simp))
  have hlog : 0≤Real.log (N+1 : ℕ)+1 := by
    have : (1 : ℝ)≤(N+1 : ℕ) := by exact_mod_cast (show 1≤N+1 by omega)
    linarith [Real.log_nonneg this]
  have he (n : ℕ) : (if lo<n ∧ n≤hi then w n*f n else 0)=
      (if lo<n ∧ n≤hi then w n else 0)*f n := by split_ifs <;> simp
  simp_rw [he]
  apply (norm_weighted_Ioc_le A N _ f htwist).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (variationMass_intervalCut_le (fun j => w (A+1+j)) N A lo hi hlo) hlog) hB

theorem norm_tent_cut_Ioc_le (X M A N lo hi : ℕ) (h i : ℤ) (f : ℕ → ℂ)
    {R H B : ℝ} (hX : 0<X) (hM : 0<M) (hR : 0≤R) (hH : 0≤H)
    (hh : |(h : ℝ)|≤H) (hiX : |i|≤(X : ℤ)) (hlo : lo≤hi)
    (hbound : (X : ℝ)/(M*(A+1) : ℕ)≤R)
    (htwist : ∀ χ : AddChar ℤ ℂ, (∀ n, ‖χ n‖=1) →
      ‖∑ n ∈ Finset.Ioc A (A+N), χ (n : ℤ)*f n‖≤B) :
    ‖∑ n ∈ Finset.Ioc A (A+N), if lo<n ∧ n≤hi then
      tentWeight X h i (M*n : ℕ)⁻¹*f n else 0‖ ≤
      (4*(8*R+128*H*R^2))*(Real.log (N+1 : ℕ)+1)*B := by
  have hB : 0≤B := (norm_nonneg _).trans (htwist 1 (by simp))
  have hlog : 0≤Real.log (N+1 : ℕ)+1 := by
    have : (1 : ℝ)≤(N+1 : ℕ) := by exact_mod_cast (show 1≤N+1 by omega)
    linarith [Real.log_nonneg this]
  apply (norm_weighted_cut_Ioc_le A N lo hi _ f hlo htwist).trans
  apply mul_le_mul_of_nonneg_right _ hB
  apply mul_le_mul_of_nonneg_right _ hlog
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ)≤4)
  apply variationMass_tentWeight_reciprocal_le X h i (fun j => M*(A+1+j)) N
    hX hR hH hh hiX
  · intro j
    exact Nat.mul_pos hM (by omega)
  · intro a b hab
    exact Nat.mul_le_mul_left M (by omega)
  · simpa only [Nat.add_zero] using hbound

end Erdos387Proof.WeightedIntervalCut
