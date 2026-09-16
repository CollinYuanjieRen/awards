import MerLeanExperiment.DirectionFrame
import Mathlib.Tactic

/-!
A Boolean band-code bound and an intermediate geometric interface producing
its separation hypothesis. This file does not assert the sharp Sendov bound.
-/

namespace PlanarMinimax

private def incomingNormalizedBand {V : Type*} [LinearOrder V]
    (theta : V → V → ℝ) (h : ℝ) (u : ℝ) (j : V) : Prop :=
  ∃ i, i < j ∧ u ≤ theta i j / h ∧ theta i j / h < u + 1

private theorem normalizedBand_separates {V : Type*} [LinearOrder V]
    (theta : V → V → ℝ) {h u : ℝ} (hh : 0 < h)
    (hmiddle : ∀ ⦃i j l : V⦄, i < j → j < l → h ≤ |theta i j - theta j l|)
    {i j : V} (hij : i < j) (hlo : u ≤ theta i j / h)
    (hhi : theta i j / h < u + 1) :
    ¬ incomingNormalizedBand theta h u i ∧ incomingNormalizedBand theta h u j := by
  constructor
  · rintro ⟨l, hli, hlo', hhi'⟩
    have hgap := hmiddle hli hij
    have hsmallNorm : |theta l i / h - theta i j / h| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have hsmall : |theta l i - theta i j| < h := by
      rw [← div_lt_one hh]
      calc
        |theta l i - theta i j| / h = |(theta l i - theta i j) / h| := by
          rw [abs_div, abs_of_pos hh]
        _ = |theta l i / h - theta i j / h| := by rw [sub_div]
        _ < 1 := hsmallNorm
    exact (not_lt_of_ge hgap) hsmall
  · exact ⟨i, hij, hlo, hhi⟩

/-- Values in `k` half-open bands, with unit `h` separation at every ordered
middle vertex, encode the vertices by `k` Boolean bits. -/
theorem angularBand_capacity {V : Type*} [LinearOrder V] [Fintype V]
    (theta : V → V → ℝ) (h : ℝ) (k : ℕ) (hh : 0 < h)
    (hrange : ∀ ⦃i j : V⦄, i < j → 0 ≤ theta i j ∧ theta i j < (k : ℝ) * h)
    (hmiddle : ∀ ⦃i j l : V⦄, i < j → j < l → h ≤ |theta i j - theta j l|) :
    Fintype.card V ≤ 2 ^ k := by
  classical
  let code : V → Fin k → Bool := fun j m ↦
    decide (incomingNormalizedBand theta h (m : ℝ) j)
  have hsep : ∀ {i j : V}, i < j → code i ≠ code j := by
    intro i j hij hcode
    have hnonneg : 0 ≤ theta i j / h := div_nonneg (hrange hij).1 hh.le
    have hvalue_k : theta i j / h < (k : ℝ) := by
      rw [div_lt_iff₀ hh]
      exact (hrange hij).2
    have hm_lt : Nat.floor (theta i j / h) < k :=
      (Nat.floor_lt hnonneg).2 hvalue_k
    let m : Fin k := ⟨Nat.floor (theta i j / h), hm_lt⟩
    have hmlo : (m : ℝ) ≤ theta i j / h := by
      simpa [m] using Nat.floor_le hnonneg
    have hmhi : theta i j / h < (m : ℝ) + 1 := by
      simpa [m] using Nat.lt_floor_add_one (theta i j / h)
    have hband := normalizedBand_separates theta hh hmiddle hij hmlo hmhi
    have hbit := congrFun hcode m
    simp [code, hband.1, hband.2] at hbit
  have hcode : Function.Injective code := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hsep hlt hij
    · exact hsep hgt hij.symm
  simpa using Fintype.card_le_of_injective code hcode

/-- An angle cap turns positive unit-direction edge coordinates into the
middle-vertex parameter separation needed by `angularBand_capacity`. -/
theorem middle_separation_of_angle_cap {V : Type*} [LinearOrder V]
    (points : V → Plane) (theta scale : V → V → ℝ) (A h : ℝ) (k : ℕ)
    (_hpoints : Function.Injective points)
    (_hh : 0 < h)
    (hrange : ∀ ⦃i j : V⦄, i < j →
      0 ≤ theta i j - A ∧ theta i j - A < (k : ℝ) * h)
    (hwidth : (k : ℝ) * h ≤ Real.pi)
    (hscale : ∀ ⦃i j : V⦄, i < j → 0 < scale i j)
    (hedge : ∀ ⦃i j : V⦄, i < j →
      points j - points i = scale i j • unitDirection (theta i j))
    (hcap : ∀ i j l : V, i ≠ j → j ≠ l → i ≠ l →
      EuclideanGeometry.angle (points i) (points j) (points l) ≤ Real.pi - h) :
    ∀ ⦃i j l : V⦄, i < j → j < l → h ≤ |theta i j - theta j l| := by
  intro i j l hij hjl
  have hil : i ≠ l := ne_of_lt (hij.trans hjl)
  have hdiff : |theta i j - theta j l| ≤ Real.pi := by
    have hi := hrange hij
    have hj := hrange hjl
    have habs : |theta i j - theta j l| < (k : ℝ) * h := by
      rw [abs_lt]
      constructor <;> linarith
    exact habs.le.trans hwidth
  have hleft : points i - points j =
      scale i j • (-unitDirection (theta i j)) := by
    rw [← neg_sub, hedge hij]
    simp
  have hright : points l - points j =
      scale j l • unitDirection (theta j l) := hedge hjl
  have hangle := hcap i j l (ne_of_lt hij) (ne_of_lt hjl) hil
  unfold EuclideanGeometry.angle at hangle
  simp only [vsub_eq_sub, hleft, hright] at hangle
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (hscale hij),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (hscale hjl),
    InnerProductGeometry.angle_neg_left,
    angle_unitDirection (theta i j) (theta j l) hdiff] at hangle
  linarith

/-- Geometric angular-band data therefore has at most `2^k` vertices. -/
theorem geometricAngularBand_capacity {V : Type*} [LinearOrder V] [Fintype V]
    (points : V → Plane) (theta scale : V → V → ℝ) (A h : ℝ) (k : ℕ)
    (hpoints : Function.Injective points)
    (hh : 0 < h)
    (hrange : ∀ ⦃i j : V⦄, i < j →
      0 ≤ theta i j - A ∧ theta i j - A < (k : ℝ) * h)
    (hwidth : (k : ℝ) * h ≤ Real.pi)
    (hscale : ∀ ⦃i j : V⦄, i < j → 0 < scale i j)
    (hedge : ∀ ⦃i j : V⦄, i < j →
      points j - points i = scale i j • unitDirection (theta i j))
    (hcap : ∀ i j l : V, i ≠ j → j ≠ l → i ≠ l →
      EuclideanGeometry.angle (points i) (points j) (points l) ≤ Real.pi - h) :
    Fintype.card V ≤ 2 ^ k := by
  apply angularBand_capacity (fun i j ↦ theta i j - A) h k hh hrange
  intro i j l hij hjl
  simpa only [sub_sub_sub_cancel_right] using
    middle_separation_of_angle_cap points theta scale A h k hpoints hh hrange hwidth
      hscale hedge hcap hij hjl

#print axioms angularBand_capacity
#print axioms middle_separation_of_angle_cap
#print axioms geometricAngularBand_capacity

end PlanarMinimax
