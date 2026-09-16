import MerLeanExperiment.CapSemantics
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Tactic

/-!
An interface turning rescaled limiting directions into ordinary finite configurations.
This is supporting infrastructure and does not provide a sharp upper construction.
-/

namespace PlanarMinimax

open Filter Set
open scoped Topology

/-- The positively rescaled displacement from `i` to `j`. -/
def rescaledDisplacement {N : ℕ} (P : ℝ → Fin N → Plane)
    (scale : Fin N → Fin N → ℝ → ℝ) (i j : Fin N) (ε : ℝ) : Plane :=
  scale i j ε • (P ε j - P ε i)

/-- Angles of two convergent nonzero vector families converge to the limiting angle. -/
theorem tendsto_inner_angle {α V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {l : Filter α} {f g : α → V} {a b : V}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (ha : a ≠ 0) (hb : b ≠ 0) :
    Tendsto (fun x ↦ InnerProductGeometry.angle (f x) (g x)) l
      (𝓝 (InnerProductGeometry.angle a b)) := by
  unfold InnerProductGeometry.angle
  have hinner : Tendsto (fun x ↦ inner ℝ (f x) (g x)) l (𝓝 (inner ℝ a b)) :=
    hf.inner hg
  have hdenominator : Tendsto (fun x ↦ ‖f x‖ * ‖g x‖) l (𝓝 (‖a‖ * ‖b‖)) :=
    hf.norm.mul hg.norm
  have hquotient := hinner.div hdenominator
    (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))
  exact hquotient.arccos

/-- Limiting nonzero outgoing directions give simultaneous strict angle bounds for small
positive parameters. -/
theorem angleLimit_eventually {N : ℕ} {B : ℝ} (P : ℝ → Fin N → Plane)
    (scale : Fin N → Fin N → ℝ → ℝ) (direction : Fin N → Fin N → Plane)
    (hscale : ∀ i j, i ≠ j →
      ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < scale i j ε)
    (hlimit : ∀ i j, i ≠ j →
      Tendsto (rescaledDisplacement P scale i j) (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 (direction i j)))
    (hnonzero : ∀ i j, i ≠ j → direction i j ≠ 0)
    (hangle : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      InnerProductGeometry.angle (direction j i) (direction j k) ≤ B)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < ε ∧ Function.Injective (P ε) ∧
      ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
        EuclideanGeometry.angle (P ε i) (P ε j) (P ε k) < B + η := by
  have hpairs : ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0,
      ∀ i j, i ≠ j → P ε i ≠ P ε j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i = j
    · filter_upwards [] with ε
      exact fun hne ↦ (hne hij).elim
    · filter_upwards [(hlimit i j hij).eventually_ne (hnonzero i j hij)] with ε hne
      intro _ heq
      apply hne
      simp [rescaledDisplacement, heq]
  have hinjective : ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0, Function.Injective (P ε) := by
    filter_upwards [hpairs] with ε hpairsε
    intro i j heq
    by_contra hij
    exact hpairsε i j hij heq
  have hangles : ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0,
      ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
        EuclideanGeometry.angle (P ε i) (P ε j) (P ε k) < B + η := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro k
    by_cases hij : i = j
    · filter_upwards [] with ε
      exact fun hne ↦ (hne hij).elim
    by_cases hjk : j = k
    · filter_upwards [] with ε
      exact fun _ hne ↦ (hne hjk).elim
    by_cases hik : i = k
    · filter_upwards [] with ε
      exact fun _ _ hne ↦ (hne hik).elim
    have hji0 : direction j i ≠ (0 : Plane) := hnonzero j i (Ne.symm hij)
    have hjk0 : direction j k ≠ (0 : Plane) := hnonzero j k hjk
    have hangleLimit : Tendsto (fun ε ↦ InnerProductGeometry.angle
        (rescaledDisplacement P scale j i ε) (rescaledDisplacement P scale j k ε))
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 (InnerProductGeometry.angle (direction j i) (direction j k))) := by
      exact tendsto_inner_angle (hlimit j i (Ne.symm hij)) (hlimit j k hjk) hji0 hjk0
    have hstrict : InnerProductGeometry.angle (direction j i) (direction j k) < B + η :=
      lt_of_le_of_lt (hangle i j k hij hjk hik) (lt_add_of_pos_right B hη)
    have heventual : ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0,
        InnerProductGeometry.angle (rescaledDisplacement P scale j i ε)
          (rescaledDisplacement P scale j k ε) < B + η :=
      hangleLimit.eventually_lt tendsto_const_nhds hstrict
    filter_upwards [heventual, hscale j i (Ne.symm hij), hscale j k hjk] with ε hε hsji hsjk
    unfold rescaledDisplacement at hε
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hsji,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hsjk] at hε
    intro _ _ _
    exact hε
  have hpositive : ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < ε :=
    self_mem_nhdsWithin
  filter_upwards [hpositive, hinjective, hangles] with ε hε hinjε hangleε
  exact ⟨hε, hinjε, hangleε⟩

/-- Every positive error admits an ordinary configuration with cap `B + η`. -/
theorem realizableCap_of_angleLimit {N : ℕ} {B : ℝ} (P : ℝ → Fin N → Plane)
    (scale : Fin N → Fin N → ℝ → ℝ) (direction : Fin N → Fin N → Plane)
    (hscale : ∀ i j, i ≠ j →
      ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < scale i j ε)
    (hlimit : ∀ i j, i ≠ j →
      Tendsto (rescaledDisplacement P scale i j) (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 (direction i j)))
    (hnonzero : ∀ i j, i ≠ j → direction i j ≠ 0)
    (hangle : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      InnerProductGeometry.angle (direction j i) (direction j k) ≤ B)
    {η : ℝ} (hη : 0 < η) : RealizableCap N (B + η) := by
  obtain ⟨ε, _, hinjective, hangles⟩ :=
    (angleLimit_eventually P scale direction hscale hlimit hnonzero hangle hη).exists
  exact ⟨P ε, hinjective, fun i j k hij hjk hik ↦ (hangles i j k hij hjk hik).le⟩

/-- Limiting angle bounds give the corresponding minimax upper bound for `N ≥ 3`. -/
theorem minimaxAngle_le_of_angleLimit {N : ℕ} {B : ℝ} (hN : 3 ≤ N)
    (P : ℝ → Fin N → Plane) (scale : Fin N → Fin N → ℝ → ℝ)
    (direction : Fin N → Fin N → Plane)
    (hscale : ∀ i j, i ≠ j →
      ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < scale i j ε)
    (hlimit : ∀ i j, i ≠ j →
      Tendsto (rescaledDisplacement P scale i j) (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 (direction i j)))
    (hnonzero : ∀ i j, i ≠ j → direction i j ≠ 0)
    (hangle : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      InnerProductGeometry.angle (direction j i) (direction j k) ≤ B) :
    minimaxAngle N ≤ B := by
  by_contra hle
  have hlt : B < minimaxAngle N := lt_of_not_ge hle
  let η := (minimaxAngle N - B) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hrealizable :=
    realizableCap_of_angleLimit P scale direction hscale hlimit hnonzero hangle hη
  have hinf : minimaxAngle N ≤ B + η := by
    unfold minimaxAngle
    exact csInf_le (realizableCap_bddBelow hN) hrealizable
  dsimp [η] at hinf
  linarith

#print axioms angleLimit_eventually
#print axioms realizableCap_of_angleLimit
#print axioms minimaxAngle_le_of_angleLimit

end PlanarMinimax
