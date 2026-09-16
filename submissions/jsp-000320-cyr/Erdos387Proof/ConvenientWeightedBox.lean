import Erdos387Proof.ConvenientWeightedPrefix

/-! The two exact product separators and the actual weighted dyadic box. -/
set_option autoImplicit false
namespace Erdos387Proof.ConvenientWeightedBox
open Erdos387 Erdos387.CoverBPZ
open ConvenientMomentBoxes ConvenientMomentBound ConvenientWeightedMoment ConvenientWeightedPrefix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def boxSum {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (r s a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) : ℂ :=
  ∑ u ∈ variableBox g r (SubpowerScale.medium N S.k) c,
  ∑ v ∈ variableBox g s (SubpowerScale.medium N S.k) c,
    sharpMask B (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k) (product c) u v *
      (FourierVariation.tentWeight (SubpowerScale.X N S.k) h (-(i.val : ℤ))
        ((modulus S g (product c) : ℝ)*u*v)⁻¹ *momentKernel S i a h hg hsupport c u v)

noncomputable def twistedBoxSum {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (r s a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (c : ActualIndex S N i)
    (alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)))
    (beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k))) : ℂ :=
  ∑ u ∈ variableBox g r (SubpowerScale.medium N S.k) c,
  ∑ v ∈ variableBox g s (SubpowerScale.medium N S.k) c,
    FourierVariation.tentWeight (SubpowerScale.X N S.k) h (-(i.val : ℤ))
      ((modulus S g (product c) : ℝ)*u*v)⁻¹ *
      (separatorTwist (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k) alpha beta u*
        separatorTwist (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k) alpha beta v*
        momentKernel S i a h hg hsupport c u v)

private theorem sum_four_swap {U V A B : Type*} (u : Finset U) (v : Finset V)
    (a : Finset A) (b : Finset B) (F : U → V → A → B → ℂ) :
    (∑ x ∈ u, ∑ y ∈ v, ∑ z ∈ a, ∑ t ∈ b, F x y z t) =
      ∑ z ∈ a, ∑ t ∈ b, ∑ x ∈ u, ∑ y ∈ v, F x y z t := by
  calc
    _ = ∑ x ∈ u, ∑ z ∈ a, ∑ y ∈ v, ∑ t ∈ b, F x y z t := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ z ∈ a, ∑ x ∈ u, ∑ y ∈ v, ∑ t ∈ b, F x y z t := Finset.sum_comm
    _ = ∑ z ∈ a, ∑ x ∈ u, ∑ t ∈ b, ∑ y ∈ v, F x y z t := by
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      exact Finset.sum_comm

theorem boxSum_eq_separated {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (r s a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) (hB : 0 < B)
    (hmX : SubpowerScale.medium N S.k ≤ SubpowerScale.X N S.k) :
    boxSum S i r s a h hg hsupport c =
      ∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
      ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
        separatorCoefficient B (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k)
          (product c) alpha beta * twistedBoxSum S i r s a h hg hsupport c alpha beta := by
  classical
  unfold boxSum twistedBoxSum
  conv_lhs =>
    arg 2
    ext u
    arg 2
    ext v
  have heach (u : ℕ) (hu : u ∈ variableBox g r (SubpowerScale.medium N S.k) c)
      (v : ℕ) (hv : v ∈ variableBox g s (SubpowerScale.medium N S.k) c) :=
    sharpMask_eq_sum_separated hB (product_data c).1
      (ambientBox_data (variableBox_subset_ambient g r _ c hu)).1
      (ambientBox_data (variableBox_subset_ambient g s _ c hv)).1
      (product_data c).2.1
      ((ambientBox_data (variableBox_subset_ambient g r _ c hu)).2.1.trans (min_le_left _ _))
      ((ambientBox_data (variableBox_subset_ambient g s _ c hv)).2.1.trans (min_le_left _ _)) hmX
  trans ∑ u ∈ variableBox g r (SubpowerScale.medium N S.k) c,
    ∑ v ∈ variableBox g s (SubpowerScale.medium N S.k) c,
    ∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
    ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
      separatorCoefficient B (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k)
        (product c) alpha beta *
      (FourierVariation.tentWeight (SubpowerScale.X N S.k) h (-(i.val : ℤ))
        ((modulus S g (product c) : ℝ)*u*v)⁻¹ *
        (separatorTwist (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k) alpha beta u*
          separatorTwist (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k) alpha beta v*
          momentKernel S i a h hg hsupport c u v))
  · apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    rw [heach u hu v hv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro alpha _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro beta _
    ring
  · rw [sum_four_swap]
    apply Finset.sum_congr rfl
    intro alpha _
    apply Finset.sum_congr rfl
    intro beta _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    exact (Finset.mul_sum _ _ _).symm

end Erdos387Proof.ConvenientWeightedBox
