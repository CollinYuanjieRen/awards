import Jsp936.AffineNormalization
import Jsp936.GapCover
import Randy1153.DeBoorPinkus.Package

/-!
Canonical optimal values and their lower bound for all free-node competitors.
The first two comparison consequences follow the canonical JSP000936 adapter by
randyxian08 (MIT, upstream commit e1df51e950876056d8951f4a93fa7fef6863b422).
The de Boor–Pinkus theory itself is imported from the credited upstream core.
-/
namespace Jsp936
open Randy1153 Randy1153.DeBoorPinkus
noncomputable section

/-- A canonical equioscillator is rigid under coordinatewise upper bounds on its peaks. -/
theorem canonical_upper_threshold {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (s : EndpointArray d (-1) 1)
    (h : ∀ i, s.height i ≤ opt.height 0) : s = opt := by
  apply (comparisonPackage d (-1) 1).gapHeight_le_rigidity s opt
  intro i
  rw [hopt i 0]
  exact h i

/-- The canonical optimal peak bounds every simultaneous upper bound on another array. -/
theorem canonical_peak_le_upper_bound {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (s : EndpointArray d (-1) 1) (U : ℝ)
    (hU : ∀ i, s.height i ≤ U) : opt.height 0 ≤ U := by
  by_contra h
  have hlt : U < opt.height 0 := lt_of_not_ge h
  have heq : s = opt := canonical_upper_threshold opt hopt s
    (fun i ↦ (hU i).trans hlt.le)
  have hbad := hU 0
  rw [heq] at hbad
  exact (not_le_of_gt hlt) hbad

/-- Each gap contains a node, where the Lebesgue function is one. -/
theorem one_le_gapHeight {d : ℕ} (nodes : OrderedNodes (d + 2))
    (g : Fin (d + 1)) : 1 ≤ gapHeight nodes g := by
  have h := lebesgueFunction_le_on nodes.toNodeFamily (gap_left_lt_right nodes g).le
    (show nodes.point (gapLeftIndex g) ∈
      Set.Icc (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g)) from
      ⟨le_rfl, (gap_left_lt_right nodes g).le⟩)
  simpa only [lebesgueFunction_at_node] using h

/-- The common canonical gap peak is exactly the full interval maximum. -/
theorem canonical_lebesgueOn_eq {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt) :
    lebesgueOn opt.toNodeFamily (-1) 1 = opt.height 0 := by
  apply le_antisymm
  · apply lebesgueOn_le_of_gapHeight_le opt.toOrderedNodes
    · intro g
      exact (hopt g 0).le
    · calc
        lebesgueFunction opt.toNodeFamily (-1) =
            lebesgueFunction opt.toNodeFamily (opt.point (endpointLeftIndex d)) :=
          congrArg (lebesgueFunction opt.toNodeFamily) opt.left_endpoint.symm
        _ = 1 := lebesgueFunction_at_node opt.toNodeFamily (endpointLeftIndex d)
        _ ≤ opt.height 0 := one_le_gapHeight opt.toOrderedNodes 0
    · calc
        lebesgueFunction opt.toNodeFamily 1 =
            lebesgueFunction opt.toNodeFamily (opt.point (endpointRightIndex d)) :=
          congrArg (lebesgueFunction opt.toNodeFamily) opt.right_endpoint.symm
        _ = 1 := lebesgueFunction_at_node opt.toNodeFamily (endpointRightIndex d)
        _ ≤ opt.height 0 := one_le_gapHeight opt.toOrderedNodes 0
  · exact gapHeight_le_lebesgueOn opt.toOrderedNodes 0

/-- The canonical optimum is a lower bound for every free-node configuration. -/
theorem canonical_peak_le_free_maximum {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    opt.height 0 ≤ lebesgueOn nodes (-1) 1 := by
  apply canonical_peak_le_upper_bound opt hopt (normalizedNodes nodes.sorted)
  intro i
  change gapHeight (normalizedNodes nodes.sorted).toOrderedNodes i ≤ _
  rw [gapHeight_normalized]
  calc
    gapHeight nodes.sorted i ≤ lebesgueOn nodes.sorted.toNodeFamily (-1) 1 :=
      gapHeight_le_lebesgueOn nodes.sorted i
    _ = lebesgueOn nodes (-1) 1 := nodes.lebesgueOn_sorted (-1) 1

end
end Jsp936
