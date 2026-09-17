import Mathlib

/-!
# Erdős Problem #655: every point determines at least `(n − 1)/2` distinct distances

Erdős and Pach asked: if `x₁, …, xₙ ∈ ℝ²` are such that no circle centred at one of the `xᵢ`
contains three other points, are there at least `(1 + c)·n/2` distinct distances for some
`c > 0` and all large `n`?  (As stated, Zach Hunter's regular `n`-gon disproves it; the
general-position variant is open; neither is addressed here.)  The problem page records:
"It is easy to see that this assumption implies that there are at least `(n − 1)/2` distinct
distances determined by every point."

This file proves that remark, with the formal-conjectures definitions `IsValid`
(`FormalConjectures/ErdosProblems/655.lean`, where `ℝ²` is `EuclideanSpace ℝ (Fin 2)`) and
`distinctDistancesFrom` (`FormalConjecturesForMathlib/Geometry/Metric.lean`) copied verbatim:
for a valid `X` and `x ∈ X`, `#X − 1 ≤ 2 · distinctDistancesFrom X x`.

Proof.  The map `y ↦ dist y x` sends `X.erase x` onto the distances from `x`; the fibre over a
distance `r > 0` is `X ∩ sphere x r`, which has at most two points by validity.  Hence
`#X − 1 = #(X.erase x) ≤ 2 · #(image)`.
-/

open scoped Finset

variable {X : Type*} [MetricSpace X]

open Classical in
/-- Given a finite set of points in a metric space, we define the number of distinct distances
from a point `pt` to the other points. -/
noncomputable def distinctDistancesFrom (points : Finset X) (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

namespace Erdos655

/-- A collection $x_1, \dots, x_n\in\mathbb{R}^2$ is _valid_ if
no circle whose centre is one of the $x_i$ contains three other points. -/
def IsValid (X : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ᵉ (x ∈ X) (r > 0), ¬3 ≤ (Metric.sphere x r ∩ X).ncard

end Erdos655

open Erdos655

/-- **Validity, restated as an upper bound.**  In a valid configuration a circle of positive
radius centred at a point of `X` contains at most two points of `X`. -/
theorem erdos_655_ncard_sphere_inter_le_two {X : Finset (EuclideanSpace ℝ (Fin 2))}
    (hX : IsValid X) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ X) {r : ℝ} (hr : 0 < r) :
    (Metric.sphere x r ∩ (X : Set (EuclideanSpace ℝ (Fin 2)))).ncard ≤ 2 := by
  have h := hX x hx r hr
  omega

/-- **The fibre bound.**  Any subset `s` of a valid `X` all of whose points are at the same
positive distance `r` from `x ∈ X` lies on the circle of radius `r` about `x`, hence `#s ≤ 2`. -/
private lemma card_le_two_of_dist_eq {X : Finset (EuclideanSpace ℝ (Fin 2))} (hX : IsValid X)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ X) {r : ℝ} (hr : 0 < r)
    {s : Finset (EuclideanSpace ℝ (Fin 2))} (hsX : ∀ y ∈ s, y ∈ X)
    (hsr : ∀ y ∈ s, dist y x = r) : #s ≤ 2 := by
  have hsub : (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      Metric.sphere x r ∩ (X : Set (EuclideanSpace ℝ (Fin 2))) := fun z hz =>
    ⟨Metric.mem_sphere.mpr (hsr z (Finset.mem_coe.mp hz)),
      Finset.mem_coe.mpr (hsX z (Finset.mem_coe.mp hz))⟩
  have hfin : (Metric.sphere x r ∩ (X : Set (EuclideanSpace ℝ (Fin 2)))).Finite :=
    X.finite_toSet.subset Set.inter_subset_right
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset] at hle
  exact hle.trans (erdos_655_ncard_sphere_inter_le_two hX hx hr)

/-- **Erdős #655, the page's easy remark**: in a valid configuration every point determines at
least `(n − 1)/2` distinct distances, i.e. `n − 1 ≤ 2 · (number of distinct distances from it)`. -/
theorem erdos_655_distinctDistancesFrom (X : Finset (EuclideanSpace ℝ (Fin 2))) (hX : IsValid X)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ X) : #X - 1 ≤ 2 * distinctDistancesFrom X x := by
  classical
  have key : #X - 1 ≤ 2 * #((X.erase x).image fun y => dist y x) := by
    refine le_trans (le_of_eq (Finset.card_erase_of_mem hx).symm)
      (Finset.card_le_mul_card_image _ 2 ?_)
    intro b hb
    obtain ⟨y₀, hy₀, hb₀⟩ := Finset.mem_image.mp hb
    refine card_le_two_of_dist_eq hX hx (r := b) ?_ ?_ ?_
    · rw [← hb₀]
      exact dist_pos.mpr (Finset.mem_erase.mp hy₀).1
    · exact fun y hy => Finset.mem_of_mem_erase (Finset.mem_filter.mp hy).1
    · exact fun y hy => (Finset.mem_filter.mp hy).2
  simp only [distinctDistancesFrom]
  convert key using 4
  ext a
  simp [Finset.mem_erase]

/-- The same as a closed statement (no binders), used as the graded root. -/
theorem erdos_655_distinctDistancesFrom_closed :
    ¬ ∃ (X : Finset (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2)),
      IsValid X ∧ x ∈ X ∧ 2 * distinctDistancesFrom X x < #X - 1 := by
  rintro ⟨X, x, hX, hx, hlt⟩
  exact absurd (erdos_655_distinctDistancesFrom X hX hx) (not_le.mpr hlt)
