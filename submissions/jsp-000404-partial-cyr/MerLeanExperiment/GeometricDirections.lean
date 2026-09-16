import MerLeanExperiment.AngularBandCapacity
import MerLeanExperiment.DirectionBetween
import MerLeanExperiment.DirectionalData
import MerLeanExperiment.UpperHalfPlaneDirection
import Mathlib.Order.PiLex
import Mathlib.Tactic

/-!
Conversion of ordinary planar configurations into the ordered-direction model.
This is a model bridge and does not assert a capacity or classification theorem.
-/

namespace PlanarMinimax

/-- Positive unit-direction coordinates for every forward edge produce the full
ordered-direction constraint structure after normalization by the angle deficit. -/
noncomputable def orderedDirectionsData_of_unit_edges {V : Type*} [LinearOrder V] [Fintype V]
    (points : V → Plane) (theta scale : V → V → ℝ) (h : ℝ)
    (_hpoints : Function.Injective points) (hh : 0 < h) (_hhpi : h ≤ Real.pi)
    (hrange : ∀ ⦃i j : V⦄, i < j → 0 ≤ theta i j ∧ theta i j < Real.pi)
    (hscale : ∀ ⦃i j : V⦄, i < j → 0 < scale i j)
    (hedge : ∀ ⦃i j : V⦄, i < j →
      points j - points i = scale i j • unitDirection (theta i j))
    (hcap : ∀ i j k : V, i ≠ j → j ≠ k → i ≠ k →
      EuclideanGeometry.angle (points i) (points j) (points k) ≤ Real.pi - h) :
    OrderedDirections.Data V (Real.pi / h) := by
  let value : V → V → ℝ := fun i j ↦ theta i j / h
  refine
    { value := value
      nonnegative := ?_
      below_width := ?_
      between := ?_
      separated := ?_
      first_gap := ?_
      last_gap := ?_ }
  · intro i j hij
    exact div_nonneg (hrange hij).1 hh.le
  · intro i j hij
    exact (div_lt_div_iff_of_pos_right hh).2 (hrange hij).2
  · intro i j k hij hjk
    have hik : i < k := hij.trans hjk
    have heq : scale i k • unitDirection (theta i k) =
        scale i j • unitDirection (theta i j) +
          scale j k • unitDirection (theta j k) := by
      rw [← hedge hik, ← hedge hij, ← hedge hjk]
      module
    have hb := direction_between (hrange hij).1 (hrange hij).2
      (hrange hjk).1 (hrange hjk).2 (hrange hik).1 (hrange hik).2
      (hscale hij) (hscale hjk) (hscale hik) heq
    rcases hb with hb | hb
    · exact Or.inl ⟨(div_le_div_iff_of_pos_right hh).2 hb.1,
        (div_le_div_iff_of_pos_right hh).2 hb.2⟩
    · exact Or.inr ⟨(div_le_div_iff_of_pos_right hh).2 hb.1,
        (div_le_div_iff_of_pos_right hh).2 hb.2⟩
  · intro i j k hij hjk
    have hik : i ≠ k := ne_of_lt (hij.trans hjk)
    have hdiff : |theta i j - theta j k| ≤ Real.pi := by
      rw [abs_le]
      constructor <;> linarith [(hrange hij).1, (hrange hij).2,
        (hrange hjk).1, (hrange hjk).2]
    have hleft : points i - points j =
        scale i j • (-unitDirection (theta i j)) := by
      rw [← neg_sub, hedge hij]
      simp
    have hright : points k - points j =
        scale j k • unitDirection (theta j k) := hedge hjk
    have hc := hcap i j k (ne_of_lt hij) (ne_of_lt hjk) hik
    unfold EuclideanGeometry.angle at hc
    simp only [vsub_eq_sub, hleft, hright] at hc
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (hscale hij),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (hscale hjk),
      InnerProductGeometry.angle_neg_left,
      angle_unitDirection _ _ hdiff] at hc
    rw [← sub_div, abs_div, abs_of_pos hh, le_div_iff₀ hh]
    linarith
  · intro i j k hij hjk
    have hik : i < k := hij.trans hjk
    have hdiff : |theta i j - theta i k| ≤ Real.pi := by
      rw [abs_le]
      constructor <;> linarith [(hrange hij).1, (hrange hij).2,
        (hrange hik).1, (hrange hik).2]
    have hc := hcap j i k (ne_of_gt hij) (ne_of_lt hik) (ne_of_lt hjk)
    unfold EuclideanGeometry.angle at hc
    simp only [vsub_eq_sub, hedge hij, hedge hik] at hc
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (hscale hij),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (hscale hik),
      angle_unitDirection _ _ hdiff] at hc
    rw [← sub_div, abs_div, abs_of_pos hh]
    calc
      |theta i j - theta i k| / h ≤ (Real.pi - h) / h :=
        (div_le_div_iff_of_pos_right hh).2 hc
      _ = Real.pi / h - 1 := by field_simp
  · intro i j k hij hjk
    have hik : i < k := hij.trans hjk
    have hdiff : |theta i k - theta j k| ≤ Real.pi := by
      rw [abs_le]
      constructor <;> linarith [(hrange hik).1, (hrange hik).2,
        (hrange hjk).1, (hrange hjk).2]
    have hleft : points i - points k =
        scale i k • (-unitDirection (theta i k)) := by
      rw [← neg_sub, hedge hik]
      simp
    have hright : points j - points k =
        scale j k • (-unitDirection (theta j k)) := by
      rw [← neg_sub, hedge hjk]
      simp
    have hc := hcap i k j (ne_of_lt hik) (ne_of_gt hjk) (ne_of_lt hij)
    unfold EuclideanGeometry.angle at hc
    simp only [vsub_eq_sub, hleft, hright] at hc
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (hscale hik),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (hscale hjk),
      InnerProductGeometry.angle_neg_neg,
      angle_unitDirection _ _ hdiff] at hc
    rw [← sub_div, abs_div, abs_of_pos hh]
    calc
      |theta i k - theta j k| / h ≤ (Real.pi - h) / h :=
        (div_le_div_iff_of_pos_right hh).2 hc
      _ = Real.pi / h - 1 := by field_simp

private noncomputable def geometricLexKey {N : ℕ} (points : Fin N → Plane)
    (i : Fin N) : Lex (Fin 2 → ℝ) :=
  toLex ![points i 1, points i 0]

private theorem geometricLexKey_injective {N : ℕ} {points : Fin N → Plane}
    (hpoints : Function.Injective points) : Function.Injective (geometricLexKey points) := by
  intro i j h
  apply hpoints
  ext q
  fin_cases q
  · exact congrFun (congrArg ofLex h) 1
  · exact congrFun (congrArg ofLex h) 0

/-- The lexicographic `(y,x)` order of an injective configuration. -/
@[instance_reducible]
noncomputable def geometricConfigurationOrder {N : ℕ} (points : Fin N → Plane)
    (hpoints : Function.Injective points) : LinearOrder (Fin N) :=
  LinearOrder.lift' (geometricLexKey points) (geometricLexKey_injective hpoints)

private theorem geometric_forward_shape {N : ℕ} (points : Fin N → Plane)
    (hpoints : Function.Injective points) {i j : Fin N}
    (hij : @LT.lt (Fin N) (geometricConfigurationOrder points hpoints).toLT i j) :
    0 < (points j - points i) 1 ∨
      ((points j - points i) 1 = 0 ∧ 0 < (points j - points i) 0) := by
  change geometricLexKey points i < geometricLexKey points j at hij
  change Pi.Lex (· < ·) (· < ·) (![points i 1, points i 0])
    (![points j 1, points j 0]) at hij
  rcases hij with ⟨a, hprev, hlt⟩
  fin_cases a
  · exact Or.inl (by simpa using sub_pos.mpr hlt)
  · have heq := hprev (0 : Fin 2) (by simp)
    exact Or.inr ⟨by simpa using sub_eq_zero.mpr heq.symm,
      by simpa using sub_pos.mpr hlt⟩

private noncomputable def geometricForwardAngle {N : ℕ} (points : Fin N → Plane)
    (i j : Fin N) : ℝ :=
  if 0 < (points j - points i) 1 then
    upperDirectionAngle (points j - points i) else 0

private noncomputable def geometricForwardScale {N : ℕ} (points : Fin N → Plane)
    (i j : Fin N) : ℝ :=
  ‖points j - points i‖

private theorem geometricForwardAngle_range {N : ℕ} (points : Fin N → Plane)
    (hpoints : Function.Injective points) {i j : Fin N}
    (hij : @LT.lt (Fin N) (geometricConfigurationOrder points hpoints).toLT i j) :
    0 ≤ geometricForwardAngle points i j ∧ geometricForwardAngle points i j < Real.pi := by
  rcases geometric_forward_shape points hpoints hij with hy | ⟨hy, _⟩
  · simp only [geometricForwardAngle, ite_eq_left hy]
    exact ⟨(upperDirectionAngle_pos hy).le, upperDirectionAngle_lt_pi hy⟩
  · have hcond : ¬points i 1 < points j 1 := by
      have : points j 1 - points i 1 = 0 := by simpa using hy
      linarith
    simp [geometricForwardAngle, hcond, Real.pi_pos]

private theorem geometricForwardScale_pos {N : ℕ} (points : Fin N → Plane)
    (hpoints : Function.Injective points) {i j : Fin N}
    (hij : @LT.lt (Fin N) (geometricConfigurationOrder points hpoints).toLT i j) :
    0 < geometricForwardScale points i j := by
  rw [geometricForwardScale, norm_pos_iff]
  have hijne : i ≠ j := by
    intro heq
    subst j
    change geometricLexKey points i < geometricLexKey points i at hij
    exact (lt_irrefl _ hij)
  exact sub_ne_zero.mpr (hpoints.ne hijne).symm

private theorem geometricForward_edge {N : ℕ} (points : Fin N → Plane)
    (hpoints : Function.Injective points) {i j : Fin N}
    (hij : @LT.lt (Fin N) (geometricConfigurationOrder points hpoints).toLT i j) :
    points j - points i = geometricForwardScale points i j •
      unitDirection (geometricForwardAngle points i j) := by
  rcases geometric_forward_shape points hpoints hij with hy | ⟨hy, hx⟩
  · have hcond : points i 1 < points j 1 := by simpa using hy
    simpa [geometricForwardAngle, geometricForwardScale, hcond] using
      upperDirectionAngle_reconstruct hy
  · have hn : ‖points j - points i‖ = (points j - points i) 0 := by
      have hx' : 0 < points j 0 - points i 0 := by simpa using hx
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, hy]
      simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hx'.le]
    ext a
    fin_cases a <;>
      simp [geometricForwardAngle, geometricForwardScale, hy, unitDirection, hn]

/-- Every injective configuration with angle cap `π-h` yields ordered-direction
data for some explicit linear order on its indices. -/
theorem exists_geometricOrderedDirections {N : ℕ} (points : Fin N → Plane)
    (hpoints : Function.Injective points) {h : ℝ} (hh : 0 < h) (hhpi : h ≤ Real.pi)
    (hcap : ∀ i j k : Fin N, i ≠ j → j ≠ k → i ≠ k →
      EuclideanGeometry.angle (points i) (points j) (points k) ≤ Real.pi - h) :
    ∃ ord : LinearOrder (Fin N),
      Nonempty (@OrderedDirections.Data (Fin N) ord (Real.pi / h)) := by
  let ord := geometricConfigurationOrder points hpoints
  have hrange : ∀ ⦃i j : Fin N⦄, @LT.lt (Fin N) ord.toLT i j →
      0 ≤ geometricForwardAngle points i j ∧
        geometricForwardAngle points i j < Real.pi := by
    intro i j hij
    simpa [ord] using geometricForwardAngle_range points hpoints hij
  have hscale : ∀ ⦃i j : Fin N⦄, @LT.lt (Fin N) ord.toLT i j →
      0 < geometricForwardScale points i j := by
    intro i j hij
    simpa [ord] using geometricForwardScale_pos points hpoints hij
  have hedge : ∀ ⦃i j : Fin N⦄, @LT.lt (Fin N) ord.toLT i j →
      points j - points i = geometricForwardScale points i j •
        unitDirection (geometricForwardAngle points i j) := by
    intro i j hij
    simpa [ord] using geometricForward_edge points hpoints hij
  refine ⟨ord, ⟨?_⟩⟩
  exact @orderedDirectionsData_of_unit_edges (Fin N) ord inferInstance points
    (geometricForwardAngle points) (geometricForwardScale points) h hpoints hh hhpi
    hrange hscale hedge hcap

/-- Every injective configuration has positive unit-direction coordinates for
all forward edges in its explicit lexicographic configuration order. -/
theorem exists_geometricUnitEdges {N : ℕ} (points : Fin N → Plane)
    (hpoints : Function.Injective points) :
    ∃ ord : LinearOrder (Fin N), ∃ theta scale : Fin N → Fin N → ℝ,
      (∀ ⦃i j : Fin N⦄, @LT.lt (Fin N) ord.toLT i j →
        0 ≤ theta i j ∧ theta i j < Real.pi) ∧
      (∀ ⦃i j : Fin N⦄, @LT.lt (Fin N) ord.toLT i j → 0 < scale i j) ∧
      (∀ ⦃i j : Fin N⦄, @LT.lt (Fin N) ord.toLT i j →
        points j - points i = scale i j • unitDirection (theta i j)) := by
  let ord := geometricConfigurationOrder points hpoints
  refine ⟨ord, geometricForwardAngle points, geometricForwardScale points, ?_, ?_, ?_⟩
  · intro i j hij
    simpa [ord] using geometricForwardAngle_range points hpoints hij
  · intro i j hij
    simpa [ord] using geometricForwardScale_pos points hpoints hij
  · intro i j hij
    simpa [ord] using geometricForward_edge points hpoints hij

#print axioms orderedDirectionsData_of_unit_edges
#print axioms exists_geometricOrderedDirections
#print axioms exists_geometricUnitEdges

end PlanarMinimax
