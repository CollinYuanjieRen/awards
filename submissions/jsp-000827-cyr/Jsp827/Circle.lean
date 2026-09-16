import Mathlib
import Jsp827.Tower.Basic

/-!
# The multiplicative action on the unit circle

For primes `p : Fin d → ℕ`, the maps `x ↦ (∏ p i ^ e i) • x` on `UnitAddCircle` form a
free measure-preserving `ℕ^d`-action (`RokhlinTower.NatAction`).  The hypothesis
`HasCountableSeparatingOn UnitAddCircle MeasurableSet univ` needed by the tower theorem
is already available from Mathlib, since the circle is a second-countable T₀ Borel space.
-/

open MeasureTheory Set

namespace Erdos994

/-- The smooth number with exponent vector `e` (duplicated here to keep this file
independent of `Arith.lean`; the two definitions are definitionally equal). -/
def gvalC {d : ℕ} (p : Fin d → ℕ) (e : Fin d → ℕ) : ℕ := ∏ i, p i ^ e i

/-- The multiplier attached to the zero exponent vector is `1`. -/
@[simp] lemma gvalC_zero {d : ℕ} (p : Fin d → ℕ) : gvalC p 0 = 1 := by
  simp [gvalC]

/-- The multipliers are multiplicative in the exponent vector. -/
lemma gvalC_add {d : ℕ} (p : Fin d → ℕ) (m n : Fin d → ℕ) :
    gvalC p (m + n) = gvalC p m * gvalC p n := by
  simp [gvalC, pow_add, Finset.prod_mul_distrib]

/-- Positive primes give positive multipliers. -/
lemma gvalC_pos {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, 0 < p i) (e : Fin d → ℕ) :
    0 < gvalC p e :=
  Finset.prod_pos fun i _ ↦ pow_pos (hp i) _

/-- For distinct primes the exponent vector is recovered from the multiplier, so the
multiplier map is injective. -/
lemma gvalC_injective {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) : Function.Injective (gvalC p) := by
  have key : ∀ e : Fin d → ℕ, ∀ j : Fin d, (gvalC p e).factorization (p j) = e j := by
    intro e j
    rw [gvalC, Nat.factorization_prod fun i _ ↦ (pow_ne_zero _ (hp i).ne_zero)]
    simp only [Nat.factorization_pow, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, (hp _).factorization, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hinj.ne hij]
    · simp
  intro k l h
  funext j
  rw [← key k j, ← key l j, h]

/-- Distinct multipliers agree only on a torsion set, which is null. -/
lemma measure_setOf_nsmul_eq_nsmul {a b : ℕ} (hab : a ≠ b) :
    volume {x : UnitAddCircle | a • x = b • x} = 0 := by
  have : NullSingletonClass (volume : Measure UnitAddCircle) :=
    ⟨fun x ↦ by rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]; simp⟩
  wlog h : b < a generalizing a b
  · simpa only [eq_comm] using this hab.symm (lt_of_le_of_ne (not_lt.mp h) hab)
  obtain ⟨c, hc, rfl⟩ : ∃ c, 0 < c ∧ a = b + c := ⟨a - b, by omega, by omega⟩
  have hset : {x : UnitAddCircle | (b + c) • x = b • x}
      = {x : UnitAddCircle | c • x = 0} := by
    ext x
    simp [add_nsmul, add_eq_left]
  rw [hset]
  exact (AddCircle.finite_torsion (1 : ℝ) hc).measure_zero _

/-- Multiplication by `gvalC p e` on the unit circle. -/
noncomputable def smoothAction {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, 0 < p i) :
    RokhlinTower.NatAction (volume : Measure UnitAddCircle) d where
  f e x := gvalC p e • x
  f_zero := by
    funext x
    simp
  f_add := by
    intro m n
    funext x
    simp [gvalC_add, mul_nsmul']
  measurePreserving := by
    intro n
    have h : ((gvalC p n : ℤ)) ≠ 0 := by
      exact_mod_cast (gvalC_pos hp n).ne'
    simpa only [natCast_zsmul] using
      MeasureTheory.Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) h

/-- Distinct exponent vectors give distinct multipliers, hence agree only on the finite
(torsion) set `{x | (g - g') • x = 0}`, which is null. -/
theorem smoothAction_free {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    (smoothAction p fun i => (hp i).pos).Free := by
  intro k l hkl
  exact measure_setOf_nsmul_eq_nsmul fun h ↦ hkl (gvalC_injective hp hinj h)

end Erdos994
