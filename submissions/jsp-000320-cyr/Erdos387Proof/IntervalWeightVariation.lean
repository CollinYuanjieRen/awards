import Erdos387Proof.FiniteAbel

/-! Cutting a weight to one interval costs only a fixed factor in its total
variation. This permits original geometric masks inside whole-interval DFT. -/

set_option autoImplicit false
namespace Erdos387Proof.IntervalWeightVariation
open FiniteAbel
open scoped BigOperators

theorem norm_le_endpoint_variation (w : ℕ → ℂ) {j n : ℕ} (hj : j≤n) :
    ‖w j‖≤‖w n‖+∑ i ∈ Finset.range n, ‖w (i+1)-w i‖ := by
  induction n with
  | zero =>
    have : j=0 := by omega
    simp [this]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases he : j=n+1
    · rw [he]
      have hs : 0≤∑ i ∈ Finset.range n, ‖w (i+1)-w i‖ := Finset.sum_nonneg (by intros; positivity)
      linarith [norm_nonneg (w (n+1)-w n)]
    · have hjn : j≤n := by omega
      have hn : ‖w n‖≤‖w (n+1)‖+‖w (n+1)-w n‖ := by
        simpa only [sub_sub_cancel] using norm_sub_le (w (n+1)) (w (n+1)-w n)
      linarith [ih hjn]

theorem norm_le_variationMass (w : ℕ → ℂ) (N j : ℕ) (hj : j≤N-1) :
    ‖w j‖≤variationMass w N := norm_le_endpoint_variation w hj

theorem variationMass_nonneg (w : ℕ → ℂ) (N : ℕ) : 0≤variationMass w N := by
  unfold variationMass
  positivity

theorem variationMass_sub_le (w v : ℕ → ℂ) (N : ℕ) :
    variationMass (fun j => w j-v j) N≤variationMass w N+variationMass v N := by
  unfold variationMass
  have hstep (j : ℕ) : ‖w (j+1)-v (j+1)-(w j-v j)‖ ≤
      ‖w (j+1)-w j‖+‖v (j+1)-v j‖ := by
    rw [show w (j+1)-v (j+1)-(w j-v j)=(w (j+1)-w j)-(v (j+1)-v j) by ring]
    exact norm_sub_le _ _
  have hs := Finset.sum_le_sum (fun j (_ : j∈Finset.range (N-1)) => hstep j)
  rw [Finset.sum_add_distrib] at hs
  linarith [norm_sub_le (w (N-1)) (v (N-1))]

theorem variationMass_mul_monotone_le (w : ℕ → ℂ) (v : ℕ → ℝ) (N : ℕ)
    (hv : ∀ j, 0≤v j ∧ v j≤1) (hmono : Monotone v) :
    variationMass (fun j => w j*(v j : ℂ)) N≤2*variationMass w N := by
  have hV := variationMass_nonneg w N
  have hend : ‖w (N-1)*(v (N-1) : ℂ)‖≤‖w (N-1)‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hv _).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hv _).2
  have hstep (j : ℕ) (hj : j∈Finset.range (N-1)) :
      ‖w (j+1)*(v (j+1) : ℂ)-w j*(v j : ℂ)‖≤
        ‖w (j+1)-w j‖+variationMass w N*(v (j+1)-v j) := by
    have hdiff : 0≤v (j+1)-v j := sub_nonneg.mpr (hmono (by omega))
    have hid : w (j+1)*(v (j+1) : ℂ)-w j*(v j : ℂ)=
        (w (j+1)-w j)*(v j : ℂ)+w (j+1)*((v (j+1)-v j : ℝ) : ℂ) := by push_cast; ring
    rw [hid]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (hv j).1,abs_of_nonneg hdiff]
    apply add_le_add
    · exact mul_le_of_le_one_right (norm_nonneg _) (hv j).2
    · exact mul_le_mul_of_nonneg_right
        (norm_le_variationMass w N (j+1) (by have := Finset.mem_range.mp hj; omega)) hdiff
  have htel : (∑ j ∈ Finset.range (N-1), (v (j+1)-v j))=v (N-1)-v 0 := by
    induction N-1 with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih]; ring
  have hs := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib,← Finset.mul_sum,htel] at hs
  change ‖w (N-1)*(v (N-1) : ℂ)‖+_≤_
  have hbound : variationMass w N*(v (N-1)-v 0)≤variationMass w N :=
    mul_le_of_le_one_right hV (by linarith [(hv (N-1)).2,(hv 0).1])
  dsimp [variationMass] at hbound hs ⊢
  linarith

noncomputable def upperStep (a j : ℕ) : ℝ := if a<j then 1 else 0

theorem upperStep_bounds (a j : ℕ) : 0≤upperStep a j ∧ upperStep a j≤1 := by
  unfold upperStep
  split_ifs <;> norm_num

theorem upperStep_monotone (a : ℕ) : Monotone (upperStep a) := by
  intro i j hij
  unfold upperStep
  split_ifs <;> norm_num; omega

/-- The interval mask is exact, including both endpoints. -/
theorem variationMass_intervalCut_le (w : ℕ → ℂ) (N A lo hi : ℕ) (hlo : lo≤hi) :
    variationMass (fun j => if lo<A+1+j ∧ A+1+j≤hi then w j else 0) N ≤
      4*variationMass w N := by
  have hid (j : ℕ) : (if lo<A+1+j ∧ A+1+j≤hi then w j else 0)=
      w j*(upperStep lo (A+1+j) : ℂ)-w j*(upperStep hi (A+1+j) : ℂ) := by
    unfold upperStep
    split_ifs <;> simp_all <;> omega
  simp_rw [hid]
  apply (variationMass_sub_le _ _ N).trans
  have h1 := variationMass_mul_monotone_le w (fun j => upperStep lo (A+1+j)) N
    (fun j => upperStep_bounds _ _) (fun i j hij => upperStep_monotone lo (by omega))
  have h2 := variationMass_mul_monotone_le w (fun j => upperStep hi (A+1+j)) N
    (fun j => upperStep_bounds _ _) (fun i j hij => upperStep_monotone hi (by omega))
  linarith

end Erdos387Proof.IntervalWeightVariation
