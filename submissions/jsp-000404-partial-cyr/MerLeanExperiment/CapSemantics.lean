import MerLeanExperiment.Problem
import Mathlib.Tactic

/-!
Well-posedness and elementary semantics of the ordinary minimax-angle cap.
These results do not establish the sharp value of the minimax angle.
-/

namespace PlanarMinimax

/-- The cap set is nonempty: every angle is at most `π`. -/
theorem realizableCap_pi (n : ℕ) : RealizableCap n Real.pi := by
  let points : Fin n → Plane := fun i ↦ !₂[(i : ℝ), 0]
  refine ⟨points, ?_, ?_⟩
  · intro i j hij
    have hcoord := congrArg (fun p : Plane ↦ p 0) hij
    simp [points] at hcoord
    exact Fin.ext <| by exact_mod_cast hcoord
  · intro i j k _ _ _
    exact EuclideanGeometry.angle_le_pi (points i) (points j) (points k)

/-- For at least three vertices, every realizable angle cap is nonnegative. -/
theorem realizableCap_nonnegative {n : ℕ} (hn : 3 ≤ n) {bound : ℝ}
    (hbound : RealizableCap n bound) : 0 ≤ bound := by
  rcases hbound with ⟨points, _, hcap⟩
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have hjk : j ≠ k := by simp [j, k]
  have hik : i ≠ k := by simp [i, k]
  exact (EuclideanGeometry.angle_nonneg (points i) (points j) (points k)).trans
    (hcap i j k hij hjk hik)

/-- For at least three vertices, the set of realizable caps is bounded below. -/
theorem realizableCap_bddBelow {n : ℕ} (hn : 3 ≤ n) :
    BddBelow {bound : ℝ | RealizableCap n bound} := by
  exact ⟨0, fun _ hbound ↦ realizableCap_nonnegative hn hbound⟩

/-- For at least three vertices, the minimax angle lies between `0` and `π`. -/
theorem minimaxAngle_bounds {n : ℕ} (hn : 3 ≤ n) :
    0 ≤ minimaxAngle n ∧ minimaxAngle n ≤ Real.pi := by
  constructor
  · unfold minimaxAngle
    exact le_csInf ⟨Real.pi, realizableCap_pi n⟩ fun _ hbound ↦
      realizableCap_nonnegative hn hbound
  · unfold minimaxAngle
    exact csInf_le (realizableCap_bddBelow hn) (realizableCap_pi n)

/-- Every injective configuration has a pairwise-distinct angle at least `a`. -/
def Guaranteed (n : ℕ) (a : ℝ) : Prop :=
  ∀ points : Fin n → Plane, Function.Injective points →
    ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      a ≤ EuclideanGeometry.angle (points i) (points j) (points k)

/-- The infimum cap equals the ordinary guaranteed-angle semantics. -/
theorem le_minimaxAngle_iff_guaranteed {n : ℕ} (hn : 3 ≤ n) (a : ℝ) :
    a ≤ minimaxAngle n ↔ Guaranteed n a := by
  constructor
  · intro hmin points hinjective
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    let k : Fin n := ⟨2, by omega⟩
    have hij : i ≠ j := by simp [i, j]
    have hjk : j ≠ k := by simp [j, k]
    have hik : i ≠ k := by simp [i, k]
    by_cases ha : a ≤ 0
    · exact ⟨i, j, k, hij, hjk, hik,
        ha.trans (EuclideanGeometry.angle_nonneg (points i) (points j) (points k))⟩
    · have ha_pos : 0 < a := lt_of_not_ge ha
      by_contra hguaranteed
      let _ : Nonempty (Fin n) := ⟨i⟩
      let score : (Fin 3 → Fin n) → ℝ := fun q ↦
        if q 0 ≠ q 1 ∧ q 1 ≠ q 2 ∧ q 0 ≠ q 2 then
          EuclideanGeometry.angle (points (q 0)) (points (q 1)) (points (q 2))
        else 0
      obtain ⟨q, hq⟩ := Finite.exists_max score
      have hscore_lt : score q < a := by
        dsimp [score]
        split
        · rename_i hdistinct
          exact lt_of_not_ge fun hangle ↦ hguaranteed
            ⟨q 0, q 1, q 2, hdistinct.1, hdistinct.2.1, hdistinct.2.2, hangle⟩
        · exact ha_pos
      have hrealizable : RealizableCap n (score q) := by
        refine ⟨points, hinjective, ?_⟩
        intro x y z hxy hyz hxz
        simpa [score, hxy, hyz, hxz] using hq ![x, y, z]
      have hinf_le : minimaxAngle n ≤ score q := by
        unfold minimaxAngle
        exact csInf_le (realizableCap_bddBelow hn) hrealizable
      exact (not_lt_of_ge hmin) (hinf_le.trans_lt hscore_lt)
  · intro hguaranteed
    unfold minimaxAngle
    refine le_csInf ⟨Real.pi, realizableCap_pi n⟩ ?_
    intro bound hbound
    rcases hbound with ⟨points, hinjective, hcap⟩
    rcases hguaranteed points hinjective with ⟨i, j, k, hij, hjk, hik, hangle⟩
    exact hangle.trans (hcap i j k hij hjk hik)

#print axioms realizableCap_pi
#print axioms realizableCap_nonnegative
#print axioms realizableCap_bddBelow
#print axioms minimaxAngle_bounds
#print axioms le_minimaxAngle_iff_guaranteed

end PlanarMinimax
