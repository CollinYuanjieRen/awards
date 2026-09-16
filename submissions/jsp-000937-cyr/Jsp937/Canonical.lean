import Jsp937.AffineNormalization
import Randy1153.DeBoorPinkus.Package

/-! Canonical comparison with an equioscillating normalized endpoint array. -/
namespace Jsp937
open Randy1153
open Randy1153.DeBoorPinkus
noncomputable section

/-- Every free node array has a gap no higher than the canonical equioscillating height. -/
theorem exists_gapHeight_le_canonical {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : OrderedNodes (d + 2)) :
    ∃ g : Fin (d + 1), gapHeight nodes g ≤ opt.height 0 := by
  let normalized : EndpointArray d (-1) 1 := normalizedNodes nodes
  by_contra h
  push_neg at h
  have hle : ∀ g : Fin (d + 1), opt.height g ≤ normalized.height g := by
    intro g
    rw [hopt g 0]
    change opt.height 0 ≤ gapHeight (normalizedNodes nodes).toOrderedNodes g
    rw [gapHeight_normalized]
    exact (h g).le
  have heq : opt = normalized :=
    (comparisonPackage d (-1) 1).gapHeight_le_rigidity opt normalized hle
  let g₀ : Fin (d + 1) := 0
  have hstrict : opt.height g₀ < normalized.height g₀ := by
    change opt.height g₀ < gapHeight (normalizedNodes nodes).toOrderedNodes g₀
    rw [gapHeight_normalized]
    exact (hopt g₀ 0).symm.le.trans_lt (h g₀)
  rw [← heq] at hstrict
  exact lt_irrefl _ hstrict

/-- If every free gap reaches the canonical height, normalization gives the canonical array and
all gaps have exactly that height. -/
theorem normalizedNodes_eq_canonical_of_height_le {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : OrderedNodes (d + 2))
    (hge : ∀ g : Fin (d + 1), opt.height 0 ≤ gapHeight nodes g) :
    normalizedNodes nodes = opt ∧
      ∀ g : Fin (d + 1), gapHeight nodes g = opt.height 0 := by
  let normalized : EndpointArray d (-1) 1 := normalizedNodes nodes
  have hle : ∀ g : Fin (d + 1), opt.height g ≤ normalized.height g := by
    intro g
    rw [hopt g 0]
    change opt.height 0 ≤ gapHeight (normalizedNodes nodes).toOrderedNodes g
    rw [gapHeight_normalized]
    exact hge g
  have heq : opt = normalized :=
    (comparisonPackage d (-1) 1).gapHeight_le_rigidity opt normalized hle
  constructor
  · exact heq.symm
  · intro g
    rw [← gapHeight_normalized nodes g]
    change normalized.height g = opt.height 0
    rw [← heq]
    exact hopt g 0

/-- Equal free gap heights necessarily equal the canonical equioscillating height. -/
theorem gapHeight_eq_canonical_of_equioscillates {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : OrderedNodes (d + 2))
    (hnodes : ∀ i j : Fin (d + 1), gapHeight nodes i = gapHeight nodes j) :
    ∀ g : Fin (d + 1), gapHeight nodes g = opt.height 0 := by
  let normalized : EndpointArray d (-1) 1 := normalizedNodes nodes
  have hnorm : ∀ i j : Fin (d + 1), normalized.height i = normalized.height j := by
    intro i j
    change gapHeight (normalizedNodes nodes).toOrderedNodes i =
      gapHeight (normalizedNodes nodes).toOrderedNodes j
    rw [gapHeight_normalized, gapHeight_normalized]
    exact hnodes i j
  rcases le_total (opt.height 0) (normalized.height 0) with hle | hle
  · have hall : ∀ g : Fin (d + 1), opt.height 0 ≤ gapHeight nodes g := by
      intro g
      rw [← gapHeight_normalized nodes g]
      change opt.height 0 ≤ normalized.height g
      rw [hnorm g 0]
      exact hle
    exact (normalizedNodes_eq_canonical_of_height_le opt hopt nodes hall).2
  · have hcoord : ∀ g : Fin (d + 1), normalized.height g ≤ opt.height g := by
      intro g
      rw [hnorm g 0, hopt g 0]
      exact hle
    have heq : normalized = opt :=
      (comparisonPackage d (-1) 1).gapHeight_le_rigidity normalized opt hcoord
    intro g
    rw [← gapHeight_normalized nodes g]
    change normalized.height g = opt.height 0
    rw [heq]
    exact hopt g 0

end
end Jsp937
