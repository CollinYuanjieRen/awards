import Jsp937.Attainment
import Jsp937.Canonical
import Jsp937.GapObjective
import Jsp937.SmallCases

/-! Classification and existence of maximizers for the augmented-gap objective. -/
namespace Jsp937
open Randy1153
open Randy1153.DeBoorPinkus
noncomputable section

/-- A normalized equioscillating endpoint array exists for every number of interior nodes. -/
private theorem exists_canonical (d : ℕ) :
    ∃ opt : EndpointArray d (-1) 1, Equioscillates opt := by
  obtain ⟨opt, hopt, _⟩ := existsUniqueEquioscillatingStatement d (-1) 1
    (by norm_num [AdmissibleInterval])
  exact ⟨opt, hopt⟩

/-- The canonical internal height bounds the augmented objective of every free array. -/
private theorem upsilon_le_canonical {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : OrderedNodes (d + 2)) :
    upsilon nodes ≤ opt.height 0 := by
  obtain ⟨g, hg⟩ := exists_gapHeight_le_canonical opt hopt nodes
  exact (upsilon_le_gapHeight nodes g).trans hg

/-- The augmented-gap maximizers are exactly the internally equioscillating arrays whose two
exterior values are no smaller than their common internal height. -/
theorem maximizer_iff_equioscillating_and_large_tails (d : ℕ)
    (nodes : OrderedNodes (d + 2)) :
    IsUpsilonMaximizer nodes ↔ EquioscillatingWithLargeTails nodes := by
  obtain ⟨opt, hopt⟩ := exists_canonical d
  let H : ℝ := opt.height 0
  obtain ⟨witness, hwgap, hwleft, hwright⟩ :=
    exists_nodes_preserving_heights_with_large_tails opt H
  have hwlower : H ≤ upsilon witness := (le_upsilon_iff witness H).mpr
    ⟨fun g ↦ by rw [hwgap g, hopt g 0], hwleft, hwright⟩
  constructor
  · intro hmax
    have hlower : H ≤ upsilon nodes := hwlower.trans (hmax witness)
    obtain ⟨hgapLower, hleft, hright⟩ := (le_upsilon_iff nodes H).mp hlower
    have hgap := (normalizedNodes_eq_canonical_of_height_le opt hopt nodes hgapLower).2
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      rw [hgap i, hgap j]
    · rw [hgap 0]
      exact hleft
    · rw [hgap 0]
      exact hright
  · rintro ⟨hgapEqual, hleft, hright⟩
    have hgap := gapHeight_eq_canonical_of_equioscillates opt hopt nodes hgapEqual
    have hlower : H ≤ upsilon nodes := (le_upsilon_iff nodes H).mpr
      ⟨fun g ↦ (hgap g).ge, by
        change opt.height 0 ≤ lebesgueFunction nodes.toNodeFamily (-1)
        rw [← hgap 0]
        exact hleft, by
        change opt.height 0 ≤ lebesgueFunction nodes.toNodeFamily 1
        rw [← hgap 0]
        exact hright⟩
    intro other
    exact (upsilon_le_canonical opt hopt other).trans hlower

/-- For every number of interior nodes, the augmented-gap objective has a global maximizer. -/
theorem exists_upsilon_maximizer (d : ℕ) :
    ∃ nodes : OrderedNodes (d + 2), IsUpsilonMaximizer nodes := by
  obtain ⟨opt, hopt⟩ := exists_canonical d
  let H : ℝ := opt.height 0
  obtain ⟨nodes, hgap, hleft, hright⟩ :=
    exists_nodes_preserving_heights_with_large_tails opt H
  have hlower : H ≤ upsilon nodes := (le_upsilon_iff nodes H).mpr
    ⟨fun g ↦ by rw [hgap g, hopt g 0], hleft, hright⟩
  refine ⟨nodes, fun other ↦ ?_⟩
  exact (upsilon_le_canonical opt hopt other).trans hlower

end
end Jsp937
