import MerLeanExperiment.BinaryLimits
import MerLeanExperiment.DirectionFrame

/-!
The unconditional dyadic upper construction for ordinary planar minimax angles.
-/

namespace PlanarMinimax

open Filter Set
open scoped Topology

/-- A bit change times a unit vector is the signed direction selected by the new bit. -/
theorem bitCoeff_smul_unitDirection {b c : Bool} (hbc : b ≠ c) (θ : ℝ) :
    (bitCoeff c - bitCoeff b) • unitDirection θ = signedDirection c θ := by
  cases b <;> cases c <;> simp_all [bitCoeff, signedDirection]

/-- The regular half-circle frame used in the binary power-sum construction. -/
noncomputable def dyadicFrame (k : ℕ) (r : Fin k) : Plane :=
  unitDirection (frameAngle k r)

/-- A chosen injection of indices into binary words. -/
noncomputable def indexBinaryWord {N k : ℕ} (hNk : N ≤ 2 ^ k) :
    Fin N → BinaryWord k :=
  (Fintype.equivFinOfCardEq (by simp)).symm ∘ Fin.castLE hNk

/-- The chosen indexed binary words are distinct. -/
theorem indexBinaryWord_injective {N k : ℕ} (hNk : N ≤ 2 ^ k) :
    Function.Injective (indexBinaryWord hNk) := by
  exact (Fintype.equivFinOfCardEq (by simp)).symm.injective.comp
    (Fin.castLEEmb hNk).injective

/-- Binary power-sum points for an indexed family of words. -/
noncomputable def dyadicPoint {N k : ℕ} (words : Fin N → BinaryWord k)
    (ε : ℝ) (i : Fin N) : Plane :=
  binaryPoint (dyadicFrame k) ε (words i)

/-- Total inverse-power scales, with a harmless diagonal value. -/
noncomputable def dyadicScale {N k : ℕ} (words : Fin N → BinaryWord k)
    (hwords : Function.Injective words) (i j : Fin N) (ε : ℝ) : ℝ :=
  if hij : i = j then 1
  else (ε ^ (firstDiff (words i) (words j) (hwords.ne hij)).val)⁻¹

/-- Total limiting directions, with zero on the unused diagonal. -/
noncomputable def dyadicDirection {N k : ℕ} (words : Fin N → BinaryWord k)
    (hwords : Function.Injective words) (i j : Fin N) : Plane :=
  if hij : i = j then 0
  else
    let r := firstDiff (words i) (words j) (hwords.ne hij)
    signedDirection (words j r) (frameAngle k r)

/-- The off-diagonal dyadic scale is eventually positive. -/
theorem dyadicScale_eventually_pos {N k : ℕ} (words : Fin N → BinaryWord k)
    (hwords : Function.Injective words) (i j : Fin N) (hij : i ≠ j) :
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), 0 < dyadicScale words hwords i j ε := by
  simpa [dyadicScale, hij] using
    eventually_invPow_pos (firstDiff (words i) (words j) (hwords.ne hij)).val

/-- Rescaled dyadic displacements converge to their total limiting directions. -/
theorem dyadicDisplacement_tendsto {N k : ℕ} (words : Fin N → BinaryWord k)
    (hwords : Function.Injective words) (i j : Fin N) (hij : i ≠ j) :
    Tendsto (rescaledDisplacement (dyadicPoint words) (dyadicScale words hwords) i j)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (dyadicDirection words hwords i j)) := by
  let r := firstDiff (words i) (words j) (hwords.ne hij)
  have hlimit := tendsto_invPow_binaryPoint_sub (dyadicFrame k) (words i) (words j) r
    (firstDiff_spec (words i) (words j) (hwords.ne hij))
  have hlead := bitCoeff_smul_unitDirection
    (firstDiff_ne (words i) (words j) (hwords.ne hij)) (frameAngle k r)
  rw [show dyadicDirection words hwords i j =
      signedDirection (words j r) (frameAngle k r) by
    simp [dyadicDirection, hij, r]]
  rw [← hlead]
  apply hlimit.congr'
  filter_upwards [] with ε
  simp [rescaledDisplacement, dyadicPoint, dyadicScale, hij, r]

/-- Every off-diagonal limiting direction is nonzero. -/
theorem dyadicDirection_ne_zero {N k : ℕ} (words : Fin N → BinaryWord k)
    (hwords : Function.Injective words) (i j : Fin N) (hij : i ≠ j) :
    dyadicDirection words hwords i j ≠ 0 := by
  simp [dyadicDirection, hij, signedDirection_ne_zero]

/-- At each vertex, two dyadic limiting directions obey the regular-frame angle bound. -/
theorem dyadicDirection_angle_le {N k : ℕ} (hk : 2 ≤ k)
    (words : Fin N → BinaryWord k) (hwords : Function.Injective words)
    (i j l : Fin N) (hij : i ≠ j) (hjl : j ≠ l) (_hil : i ≠ l) :
    InnerProductGeometry.angle (dyadicDirection words hwords j i)
        (dyadicDirection words hwords j l) ≤ Real.pi - Real.pi / k := by
  have hji : j ≠ i := hij.symm
  let r := firstDiff (words j) (words i) (hwords.ne hji)
  let s := firstDiff (words j) (words l) (hwords.ne hjl)
  simp only [dyadicDirection, hji, hjl]
  change InnerProductGeometry.angle
      (signedDirection (words i r) (frameAngle k r))
      (signedDirection (words l s) (frameAngle k s)) ≤ Real.pi - Real.pi / k
  by_cases hrs : r = s
  · have hri : words j r ≠ words i r := by
      exact firstDiff_ne (words j) (words i) (hwords.ne hji)
    have hrl : words j s ≠ words l s := by
      exact firstDiff_ne (words j) (words l) (hwords.ne hjl)
    have hbits : words i r = words l s := by
      rw [← hrs] at hrl ⊢
      cases hjbit : words j r <;> cases hibit : words i r <;>
        cases hlbit : words l r <;> simp_all
    rw [hbits, hrs]
    rw [InnerProductGeometry.angle_self (signedDirection_ne_zero _ _)]
    have hkpos : (0 : ℝ) < k := by positivity
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hdiv : Real.pi / (k : ℝ) ≤ Real.pi := by
      apply (div_le_iff₀ hkpos).mpr
      nlinarith [Real.pi_pos]
    linarith
  · exact angle_signed_frame_le hk hrs (words i r) (words l s)

/-- The regular binary construction gives the dyadic minimax upper bound. -/
theorem minimaxAngle_le_dyadic {N k : ℕ} (hk : 2 ≤ k) (hN : 3 ≤ N)
    (hNk : N ≤ 2 ^ k) :
    minimaxAngle N ≤ Real.pi * (1 - 1 / (k : ℝ)) := by
  let words := indexBinaryWord hNk
  have hwords : Function.Injective words := indexBinaryWord_injective hNk
  have hbound := minimaxAngle_le_of_angleLimit hN (dyadicPoint words)
    (dyadicScale words hwords) (dyadicDirection words hwords)
    (dyadicScale_eventually_pos words hwords)
    (dyadicDisplacement_tendsto words hwords)
    (dyadicDirection_ne_zero words hwords)
    (dyadicDirection_angle_le hk words hwords)
  calc
    minimaxAngle N ≤ Real.pi - Real.pi / k := hbound
    _ = Real.pi * (1 - 1 / (k : ℝ)) := by ring

#print axioms minimaxAngle_le_dyadic

end PlanarMinimax
