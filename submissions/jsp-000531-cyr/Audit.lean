import Erdos655PerPoint

open scoped Finset
open Erdos655

#print axioms erdos_655_distinctDistancesFrom
#print axioms erdos_655_distinctDistancesFrom_closed

/-- Erdős #655: every point of a valid configuration determines at least `(n − 1)/2` distances. -/
example (X : Finset (EuclideanSpace ℝ (Fin 2))) (hX : IsValid X) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ X) : #X - 1 ≤ 2 * distinctDistancesFrom X x := erdos_655_distinctDistancesFrom X hX hx

/-- The definitions are the formal-conjectures ones. -/
example (X : Finset (EuclideanSpace ℝ (Fin 2))) :
    IsValid X ↔ ∀ᵉ (x ∈ X) (r > 0), ¬3 ≤ (Metric.sphere x r ∩ X).ncard := Iff.rfl
open Classical in
example {Y : Type*} [MetricSpace Y] (points : Finset Y) (pt : Y) :
    distinctDistancesFrom points pt = #((points.erase pt).image fun x => dist x pt) := rfl
