import Randy1153.DeBoorPinkus.NodeSpace
import Mathlib.Data.Finset.Lattice.Fold

/-! The actual free-node maximin problem, including the two exterior gaps. -/
namespace Jsp937
open Randy1153
noncomputable section

/-- Adjoin the ambient endpoints to the strictly ordered interpolation nodes. -/
def augmentedNodes {n : ℕ} (nodes : OrderedNodes n) : Fin (n + 2) → ℝ :=
  Fin.cases (-1) (Fin.lastCases 1 nodes.point)

/-- Maximum of the actual Lebesgue function on an augmented nodal gap. -/
def localPeak {n : ℕ} (nodes : OrderedNodes n) (i : Fin (n + 1)) : ℝ :=
  lebesgueOn nodes.toNodeFamily (augmentedNodes nodes i.castSucc)
    (augmentedNodes nodes i.succ)

/-- Minimum of all `n+1` local peaks, including both exterior gaps. -/
def upsilon {n : ℕ} (nodes : OrderedNodes n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (localPeak nodes)

/-- Global maximality among all free ordered node configurations of the same size. -/
def IsUpsilonMaximizer {n : ℕ} (nodes : OrderedNodes n) : Prop :=
  ∀ other : OrderedNodes n, upsilon other ≤ upsilon nodes

/-- Internal peaks agree, and neither exterior peak is smaller than them. -/
def EquioscillatingWithLargeTails {d : ℕ} (nodes : OrderedNodes (d + 2)) : Prop :=
  (∀ i j : Fin (d + 1), gapHeight nodes i = gapHeight nodes j) ∧
    gapHeight nodes (0 : Fin (d + 1)) ≤ lebesgueFunction nodes.toNodeFamily (-1) ∧
    gapHeight nodes (0 : Fin (d + 1)) ≤ lebesgueFunction nodes.toNodeFamily 1

end
end Jsp937
