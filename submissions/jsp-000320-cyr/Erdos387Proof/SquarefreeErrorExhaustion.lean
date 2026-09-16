import ErdosProblems.Erdos387.AlmostPrimeExhaustion
import ErdosProblems.Erdos387.SquarefreeCandidates

/-! The finite five-error cover restricted to the actual squarefree
candidate set used by the analytic estimates. No error bound is assumed. -/

set_option autoImplicit false

namespace Erdos387Proof.SquarefreeErrorExhaustion

open Erdos387 Erdos387.CoverBPZ

theorem bad_squarefree_subset_five {B K X z y medium large secondMin gap : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) (hy : 2 ≤ y)
    (hsecond : 1 ≤ secondMin)
    (hscaleSecond : B * y^(3 * S.k) * medium * secondMin^(S.k - 1) ≤ X / 2)
    (hscaleGap : B * y^(3 * S.k) * (gap * secondMin)^S.k ≤ X / 2) :
    RefinedSquarefreeCandidates S X z ∩ RefinedBadCandidates S X z ⊆
      (RefinedSquarefreeCandidates S X z ∩ RefinedLargeErrors S X z large) ∪
      (RefinedSquarefreeCandidates S X z ∩ RefinedMediumErrors S X z medium large) ∪
      (RefinedSquarefreeCandidates S X z ∩ RefinedConvenientErrors S X z y medium) ∪
      (RefinedSquarefreeCandidates S X z ∩ RefinedComparablePrimeErrors S X z secondMin gap medium) ∪
      (RefinedSquarefreeCandidates S X z ∩ RefinedSeparatedAlmostPrimeErrors S X z y medium secondMin gap) := by
  classical
  intro n hn
  obtain ⟨hnSF, hnBad⟩ := Finset.mem_inter.mp hn
  have hclass := refinedBadCandidates_subset_errorClasses (medium := medium) (large := large) S hB hy hnBad
  have halmost := refinedAlmostPrimeErrors_subset_comparable_union_separated
    (z := z) S hsecond hscaleSecond hscaleGap
  simp only [Finset.mem_union] at hclass
  simp only [Finset.mem_union, Finset.mem_inter]
  rcases hclass with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hnSF,h⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hnSF,h⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨hnSF,h⟩))
  · rcases Finset.mem_union.mp (halmost h) with hc | hs
    · exact Or.inl (Or.inr ⟨hnSF,hc⟩)
    · exact Or.inr ⟨hnSF,hs⟩

/-- The exact counting interface needed downstream only asks for errors
inside the same squarefree candidate family. -/
theorem bad_squarefree_card_le_five {B K X z y medium large secondMin gap : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) (hy : 2 ≤ y)
    (hsecond : 1 ≤ secondMin)
    (hscaleSecond : B * y^(3 * S.k) * medium * secondMin^(S.k - 1) ≤ X / 2)
    (hscaleGap : B * y^(3 * S.k) * (gap * secondMin)^S.k ≤ X / 2) :
    (RefinedSquarefreeCandidates S X z ∩ RefinedBadCandidates S X z).card ≤
      (RefinedSquarefreeCandidates S X z ∩ RefinedLargeErrors S X z large).card +
      (RefinedSquarefreeCandidates S X z ∩ RefinedMediumErrors S X z medium large).card +
      (RefinedSquarefreeCandidates S X z ∩ RefinedConvenientErrors S X z y medium).card +
      (RefinedSquarefreeCandidates S X z ∩ RefinedComparablePrimeErrors S X z secondMin gap medium).card +
      (RefinedSquarefreeCandidates S X z ∩ RefinedSeparatedAlmostPrimeErrors S X z y medium secondMin gap).card := by
  apply (Finset.card_le_card (bad_squarefree_subset_five S hB hy hsecond hscaleSecond hscaleGap)).trans
  apply (Finset.card_union_le _ _).trans
  refine Nat.add_le_add ?_ le_rfl
  apply (Finset.card_union_le _ _).trans
  refine Nat.add_le_add ?_ le_rfl
  apply (Finset.card_union_le _ _).trans
  refine Nat.add_le_add ?_ le_rfl
  exact Finset.card_union_le _ _

/-- Select an actual natural counterexample from a strict finite counting
inequality. This is a finite combinatorial helper, not the unconditional
root theorem: its cardinality premise must be supplied by the estimates. -/
theorem exists_counterexample_of_bad_squarefree_card_lt {B K X z : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B)
    (hcard : (RefinedSquarefreeCandidates S X z ∩ RefinedBadCandidates S X z).card <
      (RefinedSquarefreeCandidates S X z).card) :
    ∃ n : ℕ, n ∈ Finset.Ioc (X / 2) X ∧ S.k < n ∧
      (refinementModulus S : ℤ) ∣ (n : ℤ) - refinementResidue S ∧
      IsZRough z (n.choose S.k) ∧
      ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n → ¬ d ∣ n.choose S.k := by
  classical
  have hnot : ¬ RefinedSquarefreeCandidates S X z ⊆ RefinedBadCandidates S X z := by
    intro hsub
    have heq : RefinedSquarefreeCandidates S X z ∩ RefinedBadCandidates S X z =
        RefinedSquarefreeCandidates S X z := Finset.inter_eq_left.mpr hsub
    rw [heq] at hcard
    omega
  obtain ⟨n,hnSF,hnBad⟩ := Finset.not_subset.mp hnot
  have hnS := (Finset.mem_filter.mp hnSF).1
  have hnData := hnS
  rw [RefinedSiftedCandidates, Finset.mem_filter, mem_RefinedBaseCandidates] at hnData
  refine ⟨n,hnData.1.1,hnData.1.2.1,hnData.1.2.2,hnData.2,?_⟩
  intro d hdI hdvd
  apply hnBad
  rw [RefinedBadCandidates, Finset.mem_filter]
  exact ⟨hnS,d,(mem_Ioc_natCast_div_iff hB).mp hdI |>.1,
    (mem_Ioc_natCast_div_iff hB).mp hdI |>.2,hdvd⟩

end Erdos387Proof.SquarefreeErrorExhaustion
