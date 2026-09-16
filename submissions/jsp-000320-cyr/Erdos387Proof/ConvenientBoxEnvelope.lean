import Erdos387Proof.ConvenientWeightedBox

/-! The norm envelope for one dyadic weighted box.

The sharp nonseparable product window is removed exactly by the finite log
separator, and the remaining mixed tent weight is removed by the weighted
Abel prefix bound, one maximizing rectangular prefix per complementary index
and per separator frequency pair.  The result is a double sum over separator
frequencies of the separator L1 weight times an explicit mixed-variation
constant times an honest `firstMoment` with an admissible unimodular column
twist. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientBoxEnvelope
open Erdos387 Erdos387.CoverBPZ
open ConvenientMomentBoxes ConvenientMomentBound ConvenientWeightedMoment
open ConvenientWeightedPrefix ConvenientWeightedBox
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The separator coefficient's modulus does not see the complementary
product: the product only enters through a unimodular character.  This is
what lets the coefficient leave the complement sum. -/
theorem norm_separatorCoefficient_eq (B X medium D : ℕ)
    (alpha : ZMod (FiniteLogSeparator.modulus X))
    (beta : ZMod (FiniteLogSeparator.modulus medium)) :
    ‖separatorCoefficient B X medium D alpha beta‖ =
      ‖separatorCoefficient B X medium 0 alpha beta‖ := by
  simp only [separatorCoefficient,norm_mul,FiniteLogSeparator.norm_character,mul_one]

/-- One dyadic box, summed over the active complementary indices, is
controlled by the separator L1 mass times the tent mixed variation times a
first moment with per-frequency rectangular prefixes. -/
theorem exists_cuts_sum_norm_boxSum_le {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (e r s a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (hB : 0 < B) (hindex : i.val ≤ SubpowerScale.X N S.k)
    (hmX : SubpowerScale.medium N S.k ≤ SubpowerScale.X N S.k)
    (H : ℕ) (hh : h.natAbs ≤ H) :
    ∃ rCut sCut : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)) →
        ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)) →
        ActualIndex S N i → ℕ,
      (∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
            (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
         ‖ConvenientWeightedBox.boxSum S i r s a h hg hsupport c‖) ≤
        ∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
        ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
          ‖separatorCoefficient B (SubpowerScale.X N S.k)
              (SubpowerScale.medium N S.k) 0 alpha beta‖*
          ((128*(B : ℝ)+40960*H*B^2+2097152*(H : ℝ)^2*B^3)*
            firstMoment S N i e r s a h hg hsupport (rCut alpha beta) (sCut alpha beta)
              (fun _ v => separatorTwist (SubpowerScale.X N S.k)
                (SubpowerScale.medium N S.k) alpha beta v)) := by
  classical
  set I := activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
    (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s with hI
  -- One weighted Abel prefix bound per separator frequency pair.
  have hchoice : ∀ (alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)))
      (beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k))),
      ∃ rc sc : ActualIndex S N i → ℕ,
        (∑ c ∈ I, ‖twistedBoxSum S i r s a h hg hsupport c alpha beta‖) ≤
          (128*(B : ℝ)+40960*H*B^2+2097152*(H : ℝ)^2*B^3)*
            firstMoment S N i e r s a h hg hsupport rc sc
              (fun _ v => separatorTwist (SubpowerScale.X N S.k)
                (SubpowerScale.medium N S.k) alpha beta v) := by
    intro alpha beta
    have := exists_weighted_prefix_bound S i e r s a h hg hsupport hindex H hh
      (fun _ u => separatorTwist (SubpowerScale.X N S.k)
        (SubpowerScale.medium N S.k) alpha beta u)
      (fun _ v => separatorTwist (SubpowerScale.X N S.k)
        (SubpowerScale.medium N S.k) alpha beta v)
      (fun c _ u _ => le_of_eq (norm_separatorTwist _ _ _ _ _))
    simpa only [twistedBoxSum,hI] using this
  choose rCut sCut hcut using hchoice
  refine ⟨rCut,sCut,?_⟩
  have hswap : (∑ c ∈ I,
      ∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
      ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
        ‖separatorCoefficient B (SubpowerScale.X N S.k)
            (SubpowerScale.medium N S.k) 0 alpha beta‖*
          ‖twistedBoxSum S i r s a h hg hsupport c alpha beta‖) =
      ∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
      ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
        ‖separatorCoefficient B (SubpowerScale.X N S.k)
            (SubpowerScale.medium N S.k) 0 alpha beta‖*
          ∑ c ∈ I, ‖twistedBoxSum S i r s a h hg hsupport c alpha beta‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro alpha _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro beta _
    exact (Finset.mul_sum _ _ _).symm
  calc
    (∑ c ∈ I, ‖ConvenientWeightedBox.boxSum S i r s a h hg hsupport c‖)
        ≤ ∑ c ∈ I,
          ∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
          ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
            ‖separatorCoefficient B (SubpowerScale.X N S.k)
                (SubpowerScale.medium N S.k) 0 alpha beta‖*
              ‖twistedBoxSum S i r s a h hg hsupport c alpha beta‖ := by
          apply Finset.sum_le_sum
          intro c _
          rw [boxSum_eq_separated S i r s a h hg hsupport c hB hmX]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun alpha _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun beta _ => ?_)
          rw [norm_mul,norm_separatorCoefficient_eq]
    _ = ∑ alpha : ZMod (FiniteLogSeparator.modulus (SubpowerScale.X N S.k)),
        ∑ beta : ZMod (FiniteLogSeparator.modulus (SubpowerScale.medium N S.k)),
          ‖separatorCoefficient B (SubpowerScale.X N S.k)
              (SubpowerScale.medium N S.k) 0 alpha beta‖*
            ∑ c ∈ I, ‖twistedBoxSum S i r s a h hg hsupport c alpha beta‖ := hswap
    _ ≤ _ := by
          apply Finset.sum_le_sum
          intro alpha _
          apply Finset.sum_le_sum
          intro beta _
          exact mul_le_mul_of_nonneg_left (hcut alpha beta) (norm_nonneg _)

end Erdos387Proof.ConvenientBoxEnvelope
