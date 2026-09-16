import MerLeanExperiment.CapSemantics
import MerLeanExperiment.DyadicUpper
import MerLeanExperiment.GeometricDirections
import MerLeanExperiment.SixPointWidth
import Mathlib.Data.Finset.Sort

/-!
The six-point ordered-direction obstruction gives the lower half of the second
small sharp face, and the dyadic construction supplies the matching upper bound.
-/

namespace PlanarMinimax

/-- Every configuration of at least six points has minimax angle at least `2π/3`. -/
theorem minimaxAngle_ge_six {N : ℕ} (hN : 6 ≤ N) :
    2 * Real.pi / 3 ≤ minimaxAngle N := by
  unfold minimaxAngle
  apply le_csInf ⟨Real.pi, realizableCap_pi N⟩
  intro b hb
  have hN3 : 3 ≤ N := by omega
  have hb0 : 0 ≤ b := realizableCap_nonnegative hN3 hb
  by_contra hn
  have hbsmall : b < 2 * Real.pi / 3 := lt_of_not_ge hn
  let h : ℝ := Real.pi - b
  have hh : 0 < h := by
    dsimp [h]
    nlinarith [Real.pi_pos]
  have hhpi : h ≤ Real.pi := by
    dsimp [h]
    linarith
  rcases hb with ⟨points, hpoints, hcap⟩
  have hcap' : ∀ i j k : Fin N, i ≠ j → j ≠ k → i ≠ k →
      EuclideanGeometry.angle (points i) (points j) (points k) ≤ Real.pi - h := by
    simpa [h] using hcap
  obtain ⟨ord, ⟨D⟩⟩ :=
    exists_geometricOrderedDirections points hpoints hh hhpi hcap'
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  let enumerate := @Finset.orderEmbOfFin (Fin N) ord Finset.univ N hcard
  let firstSix := (Fin.castLEOrderEmb hN).trans enumerate
  have hstrict {i j : Fin 6} (hij : i < j) :
      @LT.lt (Fin N) ord.toLT (firstSix i) (firstSix j) :=
    @lt_of_le_of_ne (Fin N) ord.toPartialOrder _ _
      (firstSix.map_rel_iff.2 hij.le) (firstSix.injective.ne hij.ne)
  have h01 := hstrict (show (0 : Fin 6) < 1 by decide)
  have h12 := hstrict (show (1 : Fin 6) < 2 by decide)
  have h23 := hstrict (show (2 : Fin 6) < 3 by decide)
  have h34 := hstrict (show (3 : Fin 6) < 4 by decide)
  have h45 := hstrict (show (4 : Fin 6) < 5 by decide)
  have hwidth : (3 : ℝ) ≤ Real.pi / h :=
    @OrderedDirections.sixPoint_width (Fin N) ord (Real.pi / h) D
      (firstSix 0) (firstSix 1) (firstSix 2) (firstSix 3) (firstSix 4) (firstSix 5)
      h01 h12 h23 h34 h45
  have hwidthlt : Real.pi / h < 3 := by
    rw [div_lt_iff₀ hh]
    dsimp [h]
    nlinarith [Real.pi_pos]
  exact (not_lt_of_ge hwidth) hwidthlt

/-- For six, seven, or eight points the minimax angle is exactly `2π/3`. -/
theorem minimaxAngle_six_to_eight {N : ℕ} (hN6 : 6 ≤ N) (hN8 : N ≤ 8) :
    minimaxAngle N = 2 * Real.pi / 3 := by
  apply le_antisymm
  · have hu := minimaxAngle_le_dyadic (N := N) (k := 3) (by omega)
      (by omega) (by norm_num at hN8 ⊢; exact hN8)
    calc
      minimaxAngle N ≤ Real.pi * (1 - 1 / (3 : ℝ)) := hu
      _ = 2 * Real.pi / 3 := by ring
  · exact minimaxAngle_ge_six hN6

#print axioms minimaxAngle_ge_six
#print axioms minimaxAngle_six_to_eight

end PlanarMinimax
