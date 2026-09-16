import MerLeanExperiment.ClassicalLower
import MerLeanExperiment.DyadicUpper
import MerLeanExperiment.MissingBandCapacity
import MerLeanExperiment.PlaneRotation
import Mathlib.Order.PiLex
import Mathlib.Tactic

/-!
The strict missing-band capacity bound and the exact dyadic endpoint values.
This module does not assert the full sharp classification.
-/

namespace PlanarMinimax

private noncomputable def dyadicLexKey {N : ℕ} (p : Fin N → Plane) (i : Fin N) :
    Lex (Fin 2 → ℝ) := toLex ![p i 1, p i 0]

private theorem dyadicLexKey_injective {N : ℕ} {p : Fin N → Plane}
    (hp : Function.Injective p) : Function.Injective (dyadicLexKey p) := by
  intro i j h
  apply hp
  ext q
  fin_cases q
  · exact congrFun (congrArg ofLex h) 1
  · exact congrFun (congrArg ofLex h) 0

private structure DyadicOrderedVertex {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) where val : Fin N

private noncomputable instance {N : ℕ} {p : Fin N → Plane}
    {hp : Function.Injective p} : Fintype (DyadicOrderedVertex p hp) :=
  Fintype.ofEquiv (Fin N)
    { toFun := fun i ↦ ⟨i⟩
      invFun := fun i ↦ i.val
      left_inv := fun _ ↦ rfl
      right_inv := by intro i; cases i; rfl }

private theorem dyadicOrderedVertex_val_injective {N : ℕ} {p : Fin N → Plane}
    {hp : Function.Injective p} :
    Function.Injective (fun i : DyadicOrderedVertex p hp ↦ i.val) := by
  intro i j h
  cases i
  cases j
  congr

private noncomputable instance {N : ℕ} {p : Fin N → Plane}
    {hp : Function.Injective p} : LinearOrder (DyadicOrderedVertex p hp) :=
  LinearOrder.lift' (fun i ↦ dyadicLexKey p i.val)
    ((dyadicLexKey_injective hp).comp dyadicOrderedVertex_val_injective)

private theorem dyadic_forward_shape {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) (i j : DyadicOrderedVertex p hp) (hij : i < j) :
    0 < (p j.val - p i.val) 1 ∨
      ((p j.val - p i.val) 1 = 0 ∧ 0 < (p j.val - p i.val) 0) := by
  change dyadicLexKey p i.val < dyadicLexKey p j.val at hij
  change Pi.Lex (· < ·) (· < ·) (![p i.val 1, p i.val 0])
    (![p j.val 1, p j.val 0]) at hij
  rcases hij with ⟨a, hprev, hlt⟩
  fin_cases a
  · exact Or.inl (by simpa using sub_pos.mpr hlt)
  · have heq := hprev (0 : Fin 2) (by simp)
    exact Or.inr ⟨by simpa using sub_eq_zero.mpr heq.symm,
      by simpa using sub_pos.mpr hlt⟩

private theorem dyadic_lt_of_forward_shape {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) (i j : DyadicOrderedVertex p hp)
    (hshape : 0 < (p j.val - p i.val) 1 ∨
      ((p j.val - p i.val) 1 = 0 ∧ 0 < (p j.val - p i.val) 0)) : i < j := by
  change dyadicLexKey p i.val < dyadicLexKey p j.val
  change Pi.Lex (· < ·) (· < ·) (![p i.val 1, p i.val 0])
    (![p j.val 1, p j.val 0])
  rcases hshape with hy | ⟨hy, hx⟩
  · refine ⟨0, ?_, by simpa using sub_pos.mp hy⟩
    intro b hb
    simp at hb
  · refine ⟨1, ?_, by simpa using sub_pos.mp hx⟩
    intro b hb
    fin_cases b
    · simpa using (sub_eq_zero.mp hy).symm
    · simp at hb

private noncomputable def dyadicForwardAngle {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) (i j : DyadicOrderedVertex p hp) : ℝ :=
  if 0 < (p j.val - p i.val) 1 then upperDirectionAngle (p j.val - p i.val) else 0

private noncomputable def dyadicForwardScale {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) (i j : DyadicOrderedVertex p hp) : ℝ :=
  ‖p j.val - p i.val‖

private theorem dyadicForwardAngle_range {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) {i j : DyadicOrderedVertex p hp} (hij : i < j) :
    0 ≤ dyadicForwardAngle p hp i j ∧ dyadicForwardAngle p hp i j < Real.pi := by
  rcases dyadic_forward_shape p hp i j hij with hy | ⟨hy, _⟩
  · have hcond : p i.val 1 < p j.val 1 := by simpa using hy
    simp only [dyadicForwardAngle, ite_eq_left hy]
    exact ⟨(upperDirectionAngle_pos hy).le, upperDirectionAngle_lt_pi hy⟩
  · have hy' : p j.val 1 - p i.val 1 = 0 := by simpa using hy
    have hcond : ¬p i.val 1 < p j.val 1 := by linarith
    simp [dyadicForwardAngle, hcond, Real.pi_pos]

private theorem dyadicForwardScale_pos {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) {i j : DyadicOrderedVertex p hp} (hij : i < j) :
    0 < dyadicForwardScale p hp i j := by
  rw [dyadicForwardScale, norm_pos_iff]
  exact sub_ne_zero.mpr
    (hp.ne (dyadicOrderedVertex_val_injective.ne (ne_of_lt hij))).symm

private theorem dyadicForward_edge {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) {i j : DyadicOrderedVertex p hp} (hij : i < j) :
    p j.val - p i.val = dyadicForwardScale p hp i j •
      unitDirection (dyadicForwardAngle p hp i j) := by
  rcases dyadic_forward_shape p hp i j hij with hy | ⟨hy, hx⟩
  · have hcond : p i.val 1 < p j.val 1 := by simpa using hy
    simpa [dyadicForwardAngle, dyadicForwardScale, hcond] using
      upperDirectionAngle_reconstruct hy
  · have hn : ‖p j.val - p i.val‖ = (p j.val - p i.val) 0 := by
      have hx' : 0 < p j.val 0 - p i.val 0 := by simpa using hx
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, hy]
      simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hx'.le]
    have hy' : p j.val 1 - p i.val 1 = 0 := by simpa using hy
    have hcond : ¬p i.val 1 < p j.val 1 := by linarith
    ext a
    fin_cases a <;>
      simp [dyadicForwardAngle, dyadicForwardScale, hy, unitDirection, hn]

private theorem upperDirectionAngle_pos_smul_unit {r a : ℝ} (hr : 0 < r)
    (ha : 0 < a) (hapi : a < Real.pi) :
    upperDirectionAngle (r • unitDirection a) = a := by
  have hn : ‖r • unitDirection a‖ = r := by
    simp [norm_smul, norm_unitDirection, abs_of_pos hr]
  rw [upperDirectionAngle, hn]
  change Real.arccos (r * Real.cos a / r) = a
  rw [mul_div_cancel_left₀ _ hr.ne']
  exact Real.arccos_cos ha.le hapi.le

private theorem card_dyadicOrderedVertex {N : ℕ} (p : Fin N → Plane)
    (hp : Function.Injective p) : Fintype.card (DyadicOrderedVertex p hp) = N := by
  let e : DyadicOrderedVertex p hp ≃ Fin N :=
    { toFun := fun i ↦ i.val
      invFun := fun i ↦ ⟨i⟩
      left_inv := by intro i; cases i; rfl
      right_inv := by intro i; rfl }
  simpa using Fintype.card_congr e

set_option linter.style.haveILetI false in
/-- A strict cap below the dyadic endpoint leaves one Boolean band word unused. -/
theorem strict_dyadic_capacity {N k : ℕ} (hk : 2 ≤ k) (hN : 3 ≤ N)
    (p : Fin N → Plane) (hp : Function.Injective p)
    (hcap : ∀ i j l : Fin N, i ≠ j → j ≠ l → i ≠ l →
      EuclideanGeometry.angle (p i) (p j) (p l) < Real.pi - Real.pi / k) :
    N + 1 ≤ 2 ^ k := by
  classical
  let q : DyadicOrderedVertex p hp → Plane := fun i ↦ p i.val
  letI : Nonempty (DyadicOrderedVertex p hp) :=
    ⟨⟨⟨0, by omega⟩⟩⟩
  obtain ⟨a, ha⟩ := Finite.exists_min (fun x : DyadicOrderedVertex p hp ↦ x)
  have halt : ∀ {x : DyadicOrderedVertex p hp}, x ≠ a → a < x := by
    intro x hxa
    exact (ha x).lt_of_ne (Ne.symm hxa)
  have hcard : Fintype.card (DyadicOrderedVertex p hp) = N :=
    card_dyadicOrderedVertex p hp
  have hone : 1 < Fintype.card (DyadicOrderedVertex p hp) := by omega
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card hone a
  let Other := {x : DyadicOrderedVertex p hp // x ≠ a}
  letI : Nonempty Other := ⟨⟨b, hba⟩⟩
  let theta : DyadicOrderedVertex p hp → ℝ :=
    fun x ↦ dyadicForwardAngle p hp a x
  let rho : DyadicOrderedVertex p hp → ℝ :=
    fun x ↦ dyadicForwardScale p hp a x
  obtain ⟨q0, hq0⟩ := Finite.exists_min (fun x : Other ↦ theta x.1)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by positivity
  have hh : 0 < Real.pi / (k : ℝ) := div_pos Real.pi_pos hkpos
  have hBpos : 0 < Real.pi - Real.pi / (k : ℝ) := by
    rw [sub_pos, div_lt_iff₀ hkpos]
    nlinarith [Real.pi_pos]
  have hBpi : Real.pi - Real.pi / (k : ℝ) < Real.pi := by linarith
  have hthetaRange : ∀ x, x ≠ a → 0 ≤ theta x ∧ theta x < Real.pi := by
    intro x hxa
    exact dyadicForwardAngle_range p hp (halt hxa)
  have hrhoPos : ∀ x, x ≠ a → 0 < rho x := by
    intro x hxa
    exact dyadicForwardScale_pos p hp (halt hxa)
  have hedge : ∀ x, x ≠ a →
      q x - q a = rho x • unitDirection (theta x) := by
    intro x hxa
    exact dyadicForward_edge p hp (halt hxa)
  have hdiff : ∀ x, x ≠ a →
      0 ≤ theta x - theta q0.1 ∧
        theta x - theta q0.1 < Real.pi - Real.pi / (k : ℝ) := by
    intro x hxa
    have hmin : theta q0.1 ≤ theta x := hq0 ⟨x, hxa⟩
    constructor
    · linarith
    · by_cases hxq : x = q0.1
      · subst x
        simpa using hBpos
      · have ha0 := halt q0.2
        have hax := halt hxa
        have hs0 := hrhoPos q0.1 q0.2
        have hsx := hrhoPos x hxa
        have he0 := hedge q0.1 q0.2
        have hex := hedge x hxa
        have hr0 := hthetaRange q0.1 q0.2
        have hrx := hthetaRange x hxa
        have habs : |theta q0.1 - theta x| = theta x - theta q0.1 := by
          rw [abs_of_nonpos]
          · ring
          · linarith
        have hpi : |theta q0.1 - theta x| ≤ Real.pi := by
          rw [habs]
          linarith
        have hang := hcap q0.1.val a.val x.val
          (dyadicOrderedVertex_val_injective.ne q0.2)
          (dyadicOrderedVertex_val_injective.ne hxa.symm)
          (dyadicOrderedVertex_val_injective.ne (fun h ↦ hxq h.symm))
        unfold EuclideanGeometry.angle at hang
        simp only [vsub_eq_sub] at hang
        change InnerProductGeometry.angle (q q0.1 - q a) (q x - q a) < _ at hang
        rw [he0, hex] at hang
        rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hs0,
          InnerProductGeometry.angle_smul_right_of_pos _ _ hsx,
          angle_unitDirection _ _ hpi, habs] at hang
        exact hang
  let alpha := theta q0.1
  let pRot : Fin N → Plane := fun i ↦ rotatePlane alpha (p i - p a.val)
  have hpRot : Function.Injective pRot := by
    intro i j hij
    have hsub : p i - p a.val = p j - p a.val :=
      rotatePlane_injective alpha hij
    apply hp
    have hadd := congrArg (fun z : Plane ↦ z + p a.val) hsub
    simpa using hadd
  have hpRotAnchor : pRot a.val = 0 := by
    simp [pRot, rotatePlane]
  have hrotEdge : ∀ x, x ≠ a →
      pRot x.val - pRot a.val = rho x • unitDirection (theta x - alpha) := by
    intro x hxa
    rw [hpRotAnchor, sub_zero, show pRot x.val = rotatePlane alpha (q x - q a) by
      simp [pRot, q]]
    rw [hedge x hxa, rotatePlane_smul, rotatePlane_unitDirection]
  have hrotShape : ∀ x, x ≠ a →
      0 < (pRot x.val - pRot a.val) 1 ∨
        ((pRot x.val - pRot a.val) 1 = 0 ∧
          0 < (pRot x.val - pRot a.val) 0) := by
    intro x hxa
    have hd := hdiff x hxa
    have hs := hrhoPos x hxa
    have he := hrotEdge x hxa
    by_cases hz : theta x - alpha = 0
    · right
      constructor
      · rw [he, hz]
        simp [unitDirection]
      · rw [he, hz]
        simpa [unitDirection] using hs
    · left
      have hdpos : 0 < theta x - alpha := lt_of_le_of_ne hd.1 (Ne.symm hz)
      have hsin : 0 < Real.sin (theta x - alpha) :=
        Real.sin_pos_of_pos_of_lt_pi hdpos (hd.2.trans hBpi)
      rw [he]
      simpa [unitDirection] using mul_pos hs hsin
  let aRot : DyadicOrderedVertex pRot hpRot := ⟨a.val⟩
  have haRot : ∀ x : DyadicOrderedVertex pRot hpRot, aRot ≤ x := by
    intro x
    by_cases hxa : x.val = a.val
    · have : x = aRot := dyadicOrderedVertex_val_injective hxa
      subst x
      exact le_rfl
    · apply (dyadic_lt_of_forward_shape pRot hpRot aRot x ?_).le
      let xo : DyadicOrderedVertex p hp := ⟨x.val⟩
      have hxoa : xo ≠ a := by
        intro h
        exact hxa (congrArg DyadicOrderedVertex.val h)
      simpa [aRot, xo] using hrotShape xo hxoa
  have hanchorAngle : ∀ x : DyadicOrderedVertex pRot hpRot, x ≠ aRot →
      dyadicForwardAngle pRot hpRot aRot x = theta ⟨x.val⟩ - alpha := by
    intro x hxa
    let xo : DyadicOrderedVertex p hp := ⟨x.val⟩
    have hxoa : xo ≠ a := by
      intro h
      apply hxa
      apply dyadicOrderedVertex_val_injective
      simpa [xo, aRot] using congrArg DyadicOrderedVertex.val h
    have hd := hdiff xo hxoa
    have hs := hrhoPos xo hxoa
    have he : pRot x.val - pRot aRot.val =
        rho xo • unitDirection (theta xo - alpha) := by
      simpa [aRot, xo] using hrotEdge xo hxoa
    by_cases hz : theta xo - alpha = 0
    · have hy : (pRot x.val - pRot aRot.val) 1 = 0 := by
        rw [he, hz]
        simp [unitDirection]
      have hchart : dyadicForwardAngle pRot hpRot aRot x = 0 := by
        simp [dyadicForwardAngle, hy]
      rw [hchart]
      simpa [xo] using hz.symm
    · have hdpos : 0 < theta xo - alpha := lt_of_le_of_ne hd.1 (Ne.symm hz)
      have hdpi : theta xo - alpha < Real.pi := hd.2.trans hBpi
      have hy : 0 < (pRot x.val - pRot aRot.val) 1 := by
        rw [he]
        simpa [unitDirection] using
          mul_pos hs (Real.sin_pos_of_pos_of_lt_pi hdpos hdpi)
      simp only [dyadicForwardAngle, ite_eq_left hy]
      rw [he]
      exact upperDirectionAngle_pos_smul_unit hs hdpos hdpi
  let thetaRot : DyadicOrderedVertex pRot hpRot → DyadicOrderedVertex pRot hpRot → ℝ :=
    dyadicForwardAngle pRot hpRot
  let scaleRot : DyadicOrderedVertex pRot hpRot → DyadicOrderedVertex pRot hpRot → ℝ :=
    dyadicForwardScale pRot hpRot
  have hrange : ∀ ⦃i j : DyadicOrderedVertex pRot hpRot⦄, i < j →
      0 ≤ thetaRot i j ∧ thetaRot i j < (k : ℝ) * (Real.pi / k) := by
    intro i j hij
    have hr := dyadicForwardAngle_range pRot hpRot hij
    have heq : (k : ℝ) * (Real.pi / k) = Real.pi := by field_simp
    rwa [heq]
  have hscaleRot : ∀ ⦃i j : DyadicOrderedVertex pRot hpRot⦄, i < j →
      0 < scaleRot i j := by
    intro i j hij
    exact dyadicForwardScale_pos pRot hpRot hij
  have hedgeRot : ∀ ⦃i j : DyadicOrderedVertex pRot hpRot⦄, i < j →
      pRot j.val - pRot i.val = scaleRot i j • unitDirection (thetaRot i j) := by
    intro i j hij
    exact dyadicForward_edge pRot hpRot hij
  have hcapRot : ∀ i j l : DyadicOrderedVertex pRot hpRot,
      i ≠ j → j ≠ l → i ≠ l →
      EuclideanGeometry.angle (pRot i.val) (pRot j.val) (pRot l.val) ≤
        Real.pi - Real.pi / k := by
    intro i j l hij hjl hil
    have horig := hcap i.val j.val l.val
      (dyadicOrderedVertex_val_injective.ne hij)
      (dyadicOrderedVertex_val_injective.ne hjl)
      (dyadicOrderedVertex_val_injective.ne hil)
    apply le_of_lt
    rw [show EuclideanGeometry.angle (pRot i.val) (pRot j.val) (pRot l.val) =
        EuclideanGeometry.angle (p i.val) (p j.val) (p l.val) by
      unfold EuclideanGeometry.angle
      simp only [vsub_eq_sub]
      rw [show pRot i.val - pRot j.val = rotatePlane alpha (p i.val - p j.val) by
        rw [← rotatePlane_sub]; simp [pRot],
        show pRot l.val - pRot j.val = rotatePlane alpha (p l.val - p j.val) by
        rw [← rotatePlane_sub]; simp [pRot],
        angle_rotatePlane]]
    exact horig
  have hsep : ∀ ⦃i j l : DyadicOrderedVertex pRot hpRot⦄, i < j → j < l →
      Real.pi / k ≤ |thetaRot i j - thetaRot j l| := by
    apply middle_separation_of_angle_cap
      (fun x : DyadicOrderedVertex pRot hpRot ↦ pRot x.val)
      thetaRot scaleRot 0 (Real.pi / k) k
      (hpRot.comp dyadicOrderedVertex_val_injective) hh
    · intro i j hij
      simpa using hrange hij
    · exact le_of_eq (by field_simp)
    · exact hscaleRot
    · exact hedgeRot
    · exact hcapRot
  let last : Fin k := ⟨k - 1, by omega⟩
  have hmissing : last ∉ incidentBand thetaRot (Real.pi / k) k aRot := by
    intro hm
    simp only [incidentBand, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    rcases hm with ⟨w, hin | hout⟩
    · exact (not_lt_of_ge (haRot w)) hin.1
    · rcases hout with ⟨haw, hlo, _⟩
      have hwa : w ≠ aRot := ne_of_gt haw
      have hang := hanchorAngle w hwa
      have hlt := (hdiff (⟨w.val⟩ : DyadicOrderedVertex p hp) (by
        intro h
        apply hwa
        apply dyadicOrderedVertex_val_injective
        simpa [aRot] using congrArg DyadicOrderedVertex.val h)).2
      change theta (⟨w.val⟩ : DyadicOrderedVertex p hp) - alpha < _ at hlt
      have hmcast : (last : ℝ) = (k : ℝ) - 1 := by
        simp [last, Nat.cast_sub (show 1 ≤ k by omega)]
      have hlower := (le_div_iff₀ hh).mp hlo
      dsimp [thetaRot] at hlower
      rw [hang, hmcast] at hlower
      have hformula : ((k : ℝ) - 1) * (Real.pi / k) =
          Real.pi - Real.pi / k := by field_simp
      rw [hformula] at hlower
      linarith
  have hmiss := missingBand_capacity thetaRot (Real.pi / k) k hh hrange hsep
    aRot last hmissing
  rw [card_dyadicOrderedVertex pRot hpRot] at hmiss
  exact hmiss

/-- At and beyond a dyadic cardinality, every configuration has an angle at
least the dyadic endpoint value. -/
theorem minimaxAngle_ge_dyadic {N k : ℕ} (hk : 2 ≤ k) (hNk : 2 ^ k ≤ N) :
    Real.pi * (1 - 1 / (k : ℝ)) ≤ minimaxAngle N := by
  have hpow : 4 ≤ 2 ^ k := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hN : 3 ≤ N := by omega
  rw [le_minimaxAngle_iff_guaranteed hN]
  intro p hp
  by_contra hnot
  push Not at hnot
  have hstrict : ∀ i j l : Fin N, i ≠ j → j ≠ l → i ≠ l →
      EuclideanGeometry.angle (p i) (p j) (p l) < Real.pi - Real.pi / k := by
    intro i j l hij hjl hil
    have h := hnot i j l hij hjl hil
    rw [show Real.pi - Real.pi / (k : ℝ) =
      Real.pi * (1 - 1 / (k : ℝ)) by ring]
    exact h
  have hcapacity := strict_dyadic_capacity hk hN p hp hstrict
  omega

/-- The exact minimax value at every dyadic endpoint. -/
theorem minimaxAngle_dyadic {k : ℕ} (hk : 2 ≤ k) :
    minimaxAngle (2 ^ k) = Real.pi * (1 - 1 / (k : ℝ)) := by
  have hN : 3 ≤ 2 ^ k := by
    have hpow : 4 ≤ 2 ^ k := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  exact le_antisymm (minimaxAngle_le_dyadic hk hN le_rfl)
    (minimaxAngle_ge_dyadic hk le_rfl)

#print axioms strict_dyadic_capacity
#print axioms minimaxAngle_ge_dyadic
#print axioms minimaxAngle_dyadic

end PlanarMinimax
