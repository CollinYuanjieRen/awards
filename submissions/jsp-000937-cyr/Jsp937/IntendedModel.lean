import Jsp937.Definitions

/-! A literal coordinate model for ordered nodes and the augmented-gap objective. -/
namespace Jsp937
open Randy1153
noncomputable section

/-- Ordered node families are exactly strictly increasing coordinate vectors in `[-1, 1]`. -/
def orderedNodesEquivCoordinates (n : ℕ) :
    OrderedNodes n ≃
      {x : Fin n → ℝ // StrictMono x ∧ ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1} where
  toFun nodes := ⟨nodes.point, nodes.strictMono, nodes.mem_Icc⟩
  invFun x := {
    point := x.1
    injective := x.2.1.injective
    mem_Icc := x.2.2
    strictMono := x.2.1
  }
  left_inv nodes := by
    cases nodes
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- The coordinate adapter preserves every ordered-node coordinate definitionally. -/
@[simp]
theorem orderedNodesEquivCoordinates_apply {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    (orderedNodesEquivCoordinates n nodes).1 i = nodes.point i :=
  rfl

/-- Reconstructing ordered nodes preserves every supplied coordinate definitionally. -/
@[simp]
theorem orderedNodesEquivCoordinates_symm_point {n : ℕ}
    (x : {f : Fin n → ℝ // StrictMono f ∧ ∀ i, f i ∈ Set.Icc (-1 : ℝ) 1})
    (i : Fin n) :
    ((orderedNodesEquivCoordinates n).symm x).point i = x.1 i :=
  rfl

/-- The literal Lagrange fundamental function of an arbitrary coordinate vector. -/
def rawLagrangeFundamental {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k, (t - x i) / (x k - x i)

/-- The literal finite-product Lebesgue function of an arbitrary coordinate vector. -/
def rawLebesgueFunction {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k : Fin n, |rawLagrangeFundamental x k t|

/-- Adjoin the ambient endpoints to an arbitrary coordinate vector. -/
def rawAugmentedNodes {n : ℕ} (x : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  Fin.cases (-1) (Fin.lastCases 1 x)

/-- Supremum of the raw Lebesgue function on one augmented coordinate gap. -/
def rawLocalPeak {n : ℕ} (x : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  sSup (rawLebesgueFunction x ''
    Set.Icc (rawAugmentedNodes x i.castSucc) (rawAugmentedNodes x i.succ))

/-- Minimum of all raw augmented-gap suprema. -/
def rawUpsilon {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (rawLocalPeak x)

/-- The project fundamental function is the literal raw finite product on node coordinates. -/
theorem lagrangeFundamental_eq_raw {n : ℕ} (nodes : OrderedNodes n) (k : Fin n) (t : ℝ) :
    lagrangeFundamental nodes.toNodeFamily k t =
      rawLagrangeFundamental nodes.point k t :=
  rfl

/-- The project Lebesgue function is the literal raw finite sum on node coordinates. -/
theorem lebesgueFunction_eq_raw {n : ℕ} (nodes : OrderedNodes n) (t : ℝ) :
    lebesgueFunction nodes.toNodeFamily t = rawLebesgueFunction nodes.point t :=
  rfl

/-- The project augmented coordinates are the literal endpoint-extended coordinates. -/
theorem augmentedNodes_eq_raw {n : ℕ} (nodes : OrderedNodes n) :
    augmentedNodes nodes = rawAugmentedNodes nodes.point :=
  rfl

/-- Each project local peak is the corresponding raw coordinate supremum. -/
theorem localPeak_eq_raw {n : ℕ} (nodes : OrderedNodes n) (i : Fin (n + 1)) :
    localPeak nodes i = rawLocalPeak nodes.point i :=
  rfl

/-- The frozen augmented-gap objective is exactly the independent raw coordinate objective. -/
theorem upsilon_eq_raw {n : ℕ} (nodes : OrderedNodes n) :
    upsilon nodes = rawUpsilon nodes.point :=
  rfl

end
end Jsp937
