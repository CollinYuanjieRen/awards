import MerLeanExperiment.CapSemantics
import MerLeanExperiment.FivePointWidth
import MerLeanExperiment.GeometricDirections
import MerLeanExperiment.ThreeCenterUpper
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
The five-point ordered-direction obstruction gives the actual lower bound for
every configuration with at least five points, and hence the exact five-point
minimax angle. This closes only the first `m = 2` face of the classification.
-/

namespace PlanarMinimax

private structure FiveOrderedIndex {N : ℕ} (ord : LinearOrder (Fin N)) where
  val : Fin N

private noncomputable instance {N : ℕ} {ord : LinearOrder (Fin N)} :
    Fintype (FiveOrderedIndex ord) :=
  Fintype.ofEquiv (Fin N)
    { toFun := fun i ↦ ⟨i⟩
      invFun := fun i ↦ i.val
      left_inv := fun _ ↦ rfl
      right_inv := by intro i; cases i; rfl }

private theorem fiveOrderedIndex_val_injective {N : ℕ} {ord : LinearOrder (Fin N)} :
    Function.Injective (fun i : FiveOrderedIndex ord ↦ i.val) := by
  intro i j hij
  cases i
  cases j
  congr

set_option linter.style.haveILetI false in
private noncomputable instance {N : ℕ} {ord : LinearOrder (Fin N)} :
    LinearOrder (FiveOrderedIndex ord) := by
  letI : LinearOrder (Fin N) := ord
  exact LinearOrder.lift' (fun i : FiveOrderedIndex ord ↦ i.val)
    fiveOrderedIndex_val_injective

set_option linter.style.haveILetI false in
private noncomputable def fiveOrderedData {N : ℕ} (ord : LinearOrder (Fin N))
    {width : ℝ} (D : @OrderedDirections.Data (Fin N) ord width) :
    OrderedDirections.Data (FiveOrderedIndex ord) width := by
  letI : LinearOrder (Fin N) := ord
  refine
    { value := fun i j ↦ D.value i.val j.val
      nonnegative := ?_
      below_width := ?_
      between := ?_
      separated := ?_
      first_gap := ?_
      last_gap := ?_ }
  · intro i j hij
    exact D.nonnegative hij
  · intro i j hij
    exact D.below_width hij
  · intro i j k hij hjk
    exact D.between hij hjk
  · intro i j k hij hjk
    exact D.separated hij hjk
  · intro i j k hij hjk
    exact D.first_gap hij hjk
  · intro i j k hij hjk
    exact D.last_gap hij hjk

/-- Every configuration of at least five points has minimax angle at least `3π / 5`. -/
theorem fivePoint_minimax_lower {N : ℕ} (hN : 5 ≤ N) :
    3 * Real.pi / 5 ≤ minimaxAngle N := by
  unfold minimaxAngle
  refine le_csInf ⟨Real.pi, realizableCap_pi N⟩ ?_
  intro bound hbound
  have hNthree : 3 ≤ N := by omega
  have hbound_nonneg : 0 ≤ bound := realizableCap_nonnegative hNthree hbound
  by_contra hnot
  have hbound_lt : bound < 3 * Real.pi / 5 := lt_of_not_ge hnot
  rcases hbound with ⟨points, hpoints, hcap⟩
  let h : ℝ := Real.pi - bound
  have hh : 0 < h := by
    dsimp [h]
    nlinarith [Real.pi_pos]
  have hhpi : h ≤ Real.pi := by
    dsimp [h]
    linarith
  have hangle : ∀ i j k : Fin N, i ≠ j → j ≠ k → i ≠ k →
      EuclideanGeometry.angle (points i) (points j) (points k) ≤ Real.pi - h := by
    intro i j k hij hjk hik
    simpa [h] using hcap i j k hij hjk hik
  obtain ⟨ord, ⟨D⟩⟩ :=
    exists_geometricOrderedDirections points hpoints hh hhpi hangle
  let D' := fiveOrderedData ord D
  have hcard : Fintype.card (FiveOrderedIndex ord) = N := by
    let e : FiveOrderedIndex ord ≃ Fin N :=
      { toFun := fun i ↦ i.val
        invFun := fun i ↦ ⟨i⟩
        left_inv := by intro i; cases i; rfl
        right_inv := fun _ ↦ rfl }
    simpa using Fintype.card_congr e
  let enumerate :=
    (Finset.univ : Finset (FiveOrderedIndex ord)).orderEmbOfFin hcard
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  let i2 : Fin N := ⟨2, by omega⟩
  let i3 : Fin N := ⟨3, by omega⟩
  let i4 : Fin N := ⟨4, by omega⟩
  have h01 := enumerate.strictMono (show i0 < i1 by simp [i0, i1])
  have h12 := enumerate.strictMono (show i1 < i2 by simp [i1, i2])
  have h23 := enumerate.strictMono (show i2 < i3 by simp [i2, i3])
  have h34 := enumerate.strictMono (show i3 < i4 by simp [i3, i4])
  have hwidth : (5 : ℝ) / 2 ≤ Real.pi / h :=
    OrderedDirections.fivePoint_width D' h01 h12 h23 h34
  have hwidth_lt : Real.pi / h < (5 : ℝ) / 2 := by
    rw [div_lt_iff₀ hh]
    dsimp [h]
    nlinarith [Real.pi_pos]
  exact (not_lt_of_ge hwidth) hwidth_lt

/-- The minimax angle of five points is exactly `3π / 5`. -/
theorem minimaxAngle_five : minimaxAngle 5 = 3 * Real.pi / 5 := by
  apply le_antisymm
  · calc
      minimaxAngle 5 ≤ Real.pi * (1 - 2 / (2 * (2 : ℝ) + 1)) :=
        minimaxAngle_le_threeCenter (m := 2) (N := 5) (by omega) (by omega) (by norm_num)
      _ = 3 * Real.pi / 5 := by ring
  · exact fivePoint_minimax_lower (N := 5) (by omega)

#print axioms fivePoint_minimax_lower
#print axioms minimaxAngle_five

end PlanarMinimax
