import Jsp936.Definitions

/-! A literal coordinate model for the project's finite node families. -/
namespace Jsp936
open Randy1153
noncomputable section

/-- Node families are exactly injective real coordinate vectors contained in `[-1, 1]`. -/
def nodeFamilyEquivCoordinates (n : ℕ) :
    NodeFamily n ≃
      {x : Fin n → ℝ // Function.Injective x ∧ ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1} where
  toFun nodes := ⟨nodes.point, nodes.injective, nodes.mem_Icc⟩
  invFun x := {
    point := x.1
    injective := x.2.1
    mem_Icc := x.2.2
  }
  left_inv nodes := by
    cases nodes
    rfl
  right_inv x := by
    cases x
    rfl

/-- The coordinate adapter preserves every node coordinate definitionally. -/
@[simp]
lemma nodeFamilyEquivCoordinates_apply {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    (nodeFamilyEquivCoordinates n nodes).1 i = nodes.point i :=
  rfl

/-- Reconstructing a node family preserves every supplied coordinate definitionally. -/
@[simp]
lemma nodeFamilyEquivCoordinates_symm_point {n : ℕ}
    (x : {f : Fin n → ℝ // Function.Injective f ∧ ∀ i, f i ∈ Set.Icc (-1 : ℝ) 1})
    (i : Fin n) :
    ((nodeFamilyEquivCoordinates n).symm x).point i = x.1 i :=
  rfl

end
end Jsp936
