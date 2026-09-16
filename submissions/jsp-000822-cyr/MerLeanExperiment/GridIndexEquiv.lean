import MerLeanExperiment.GridQuadrature
import MerLeanExperiment.CellRandom
import Mathlib.Logic.Equiv.Fin.Basic

namespace DiskDiscrepancy

noncomputable section

def gridIndex (q : ℕ) (z : ℤ × ℤ) (v : Fin q × Fin q) : ℤ × ℤ :=
  (z.1 * q + v.1, z.2 * q + v.2)

/-- Euclidean division in each coordinate identifies integer cells plus their
`q × q` subcell residues with the global `q⁻¹` midpoint grid. -/
def gridIndexEquiv (q : ℕ) (hq : 0 < q) :
    ((ℤ × ℤ) × (Fin q × Fin q)) ≃ (ℤ × ℤ) := by
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let e := Int.divModEquiv q
  exact
    { toFun := fun p ↦ (e.symm (p.1.1, p.2.1), e.symm (p.1.2, p.2.2))
      invFun := fun m ↦ (((e m.1).1, (e m.2).1), ((e m.1).2, (e m.2).2))
      left_inv := by
        rintro ⟨⟨z₁, z₂⟩, ⟨v₁, v₂⟩⟩
        change (((e (e.symm (z₁, v₁))).1, (e (e.symm (z₂, v₂))).1),
          ((e (e.symm (z₁, v₁))).2, (e (e.symm (z₂, v₂))).2)) = _
        simp
      right_inv := by
        rintro ⟨m₁, m₂⟩
        change (e.symm (e m₁), e.symm (e m₂)) = _
        simp }

@[simp] theorem gridIndexEquiv_apply (q : ℕ) (hq : 0 < q)
    (p : (ℤ × ℤ) × (Fin q × Fin q)) :
    gridIndexEquiv q hq p = gridIndex q p.1 p.2 := by
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  rcases p with ⟨⟨z₁,z₂⟩,⟨v₁,v₂⟩⟩
  simp [gridIndexEquiv, gridIndex, Int.divModEquiv_symm_apply]

/-- A candidate in integer cell `z` with residue `v` is literally the global
midpoint indexed by `q*z+v`. -/
theorem cellCandidate_eq_gridMidpoint (q : ℕ) (hq : 0 < q)
    (z : ℤ × ℤ) (v : Fin q × Fin q) :
    cellCandidate q hq z v = gridMidpoint q (gridIndex q z v) := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;>
    simp [cellCandidate, periodicGridPoint, jitterPoint, midpointOffset,
      gridMidpoint, gridIndex] <;> field_simp <;> ring

end
end DiskDiscrepancy
