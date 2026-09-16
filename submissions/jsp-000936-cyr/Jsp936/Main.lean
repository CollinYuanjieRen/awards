import Jsp936.CanonicalBounds
import Jsp936.Singleton

/-! Complete characterization of all optimal free interpolation node families. -/
namespace Jsp936
open Randy1153 Randy1153.DeBoorPinkus
noncomputable section

/-- Complete characterization for every number of distinct nodes at least two. -/
theorem minimizer_iff_equioscillating_and_controlled_tails
    (d : ℕ) (nodes : NodeFamily (d + 2)) :
    IsOptimal nodes ↔ EquioscillatingWithControlledTails nodes := by
  obtain ⟨opt, hopt, hunique⟩ := existsUniqueEquioscillatingStatement d (-1) 1
    (by norm_num [AdmissibleInterval])
  constructor
  · intro hmin
    have hmax : lebesgueOn nodes (-1) 1 ≤ opt.height 0 := by
      rw [← canonical_lebesgueOn_eq opt hopt]
      exact hmin opt.toNodeFamily
    have hnormalized : normalizedNodes nodes.sorted = opt := by
      apply canonical_upper_threshold opt hopt
      intro i
      change gapHeight (normalizedNodes nodes.sorted).toOrderedNodes i ≤ _
      rw [gapHeight_normalized]
      exact (gapHeight_le_lebesgueOn nodes.sorted i).trans
        (by simpa only [NodeFamily.lebesgueOn_sorted] using hmax)
    have hpeak (i : Fin (d + 1)) : gapHeight nodes.sorted i = opt.height 0 := by
      rw [← gapHeight_normalized nodes.sorted i]
      change (normalizedNodes nodes.sorted).height i = opt.height 0
      rw [hnormalized, hopt i 0]
    refine ⟨fun i j ↦ (hpeak i).trans (hpeak j).symm, ?_, ?_⟩
    · rw [hpeak 0]
      exact (lebesgueFunction_le_on nodes (by norm_num) (by simp)).trans hmax
    · rw [hpeak 0]
      exact (lebesgueFunction_le_on nodes (by norm_num) (by simp)).trans hmax
  · rintro ⟨hequal, hleft, hright⟩
    have hnormalized : normalizedNodes nodes.sorted = opt := by
      apply hunique
      intro i j
      change gapHeight (normalizedNodes nodes.sorted).toOrderedNodes i =
        gapHeight (normalizedNodes nodes.sorted).toOrderedNodes j
      rw [gapHeight_normalized, gapHeight_normalized]
      exact hequal i j
    have hpeak : gapHeight nodes.sorted (0 : Fin (d + 1)) = opt.height 0 := by
      rw [← gapHeight_normalized nodes.sorted (0 : Fin (d + 1))]
      change (normalizedNodes nodes.sorted).height 0 = opt.height 0
      rw [hnormalized]
    have hmax : lebesgueOn nodes (-1) 1 ≤ opt.height 0 := by
      rw [← nodes.lebesgueOn_sorted (-1) 1, ← hpeak]
      apply lebesgueOn_le_of_gapHeight_le nodes.sorted
      · intro i
        exact (hequal i 0).le
      · simpa only [NodeFamily.lebesgueFunction_sorted] using hleft
      · simpa only [NodeFamily.lebesgueFunction_sorted] using hright
    intro other
    exact hmax.trans (canonical_peak_le_free_maximum opt hopt other)

end
end Jsp936
