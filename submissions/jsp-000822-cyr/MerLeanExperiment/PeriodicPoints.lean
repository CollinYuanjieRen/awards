import MerLeanExperiment.DiskModel

open Set

namespace DiskDiscrepancy

noncomputable section

/-- An integer lattice point with a cell-dependent offset. -/
def jitterPoint (offset : (ℤ × ℤ) → Plane) (z : ℤ × ℤ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i ↦
    if i = 0 then (z.1 : ℝ) + offset z 0 else (z.2 : ℝ) + offset z 1

@[simp] theorem jitterPoint_apply_zero (offset : (ℤ × ℤ) → Plane) (z : ℤ × ℤ) :
    jitterPoint offset z 0 = (z.1 : ℝ) + offset z 0 := by simp [jitterPoint]

@[simp] theorem jitterPoint_apply_one (offset : (ℤ × ℤ) → Plane) (z : ℤ × ℤ) :
    jitterPoint offset z 1 = (z.2 : ℝ) + offset z 1 := by simp [jitterPoint]

/-- Offsets lying in the half-open unit cell make the integer-indexed point
map injective. -/
theorem jitterPoint_injective {offset : (ℤ × ℤ) → Plane}
    (hoff : ∀ z i, 0 ≤ offset z i ∧ offset z i < 1) :
    Function.Injective (jitterPoint offset) := by
  intro z w h
  have hcoord (i : Fin 2) : jitterPoint offset z i = jitterPoint offset w i :=
    congrFun (congrArg (EuclideanSpace.equiv (Fin 2) ℝ) h) i
  have hz : z.1 = w.1 := by
    have hfz : ⌊(jitterPoint offset z 0 : ℝ)⌋ = z.1 := by
      rw [jitterPoint_apply_zero, Int.floor_eq_iff]
      exact ⟨by linarith [(hoff z 0).1], by linarith [(hoff z 0).2]⟩
    have hfw : ⌊(jitterPoint offset w 0 : ℝ)⌋ = w.1 := by
      rw [jitterPoint_apply_zero, Int.floor_eq_iff]
      exact ⟨by linarith [(hoff w 0).1], by linarith [(hoff w 0).2]⟩
    rw [← hfz, ← hfw, hcoord 0]
  have hw : z.2 = w.2 := by
    have hfz : ⌊(jitterPoint offset z 1 : ℝ)⌋ = z.2 := by
      rw [jitterPoint_apply_one, Int.floor_eq_iff]
      exact ⟨by linarith [(hoff z 1).1], by linarith [(hoff z 1).2]⟩
    have hfw : ⌊(jitterPoint offset w 1 : ℝ)⌋ = w.2 := by
      rw [jitterPoint_apply_one, Int.floor_eq_iff]
      exact ⟨by linarith [(hoff w 1).1], by linarith [(hoff w 1).2]⟩
    rw [← hfz, ← hfw, hcoord 1]
  exact Prod.ext hz hw

/-- The range of any half-open-unit-cell jitter of the integer lattice is
locally finite. -/
theorem locallyFinitePoints_range_jitterPoint {offset : (ℤ × ℤ) → Plane}
    (hoff : ∀ z i, 0 ≤ offset z i ∧ offset z i < 1) :
    LocallyFinitePoints (Set.range (jitterPoint offset)) := by
  intro center radius
  let I₀ : Set ℤ := Set.Icc ⌊center 0 - radius - 1⌋ ⌈center 0 + radius⌉
  let I₁ : Set ℤ := Set.Icc ⌊center 1 - radius - 1⌋ ⌈center 1 + radius⌉
  have hindices : {z : ℤ × ℤ | jitterPoint offset z ∈ Metric.closedBall center radius} ⊆
      I₀ ×ˢ I₁ := by
    intro z hz
    have hdist : dist (jitterPoint offset z) center ≤ radius := hz
    have h₀ := PiLp.dist_apply_le (jitterPoint offset z) center (0 : Fin 2)
    have h₁ := PiLp.dist_apply_le (jitterPoint offset z) center (1 : Fin 2)
    rw [Real.dist_eq] at h₀ h₁
    have hb₀ : |jitterPoint offset z 0 - center 0| ≤ radius := h₀.trans hdist
    have hb₁ : |jitterPoint offset z 1 - center 1| ≤ radius := h₁.trans hdist
    constructor
    · constructor
      · have hzreal : (center 0 - radius - 1) ≤ (z.1 : ℝ) := by
          rw [jitterPoint_apply_zero] at hb₀
          have := (hoff z 0).2
          have := neg_le_of_abs_le hb₀
          linarith
        have hf := Int.floor_le (center 0 - radius - 1)
        exact Int.cast_le.mp (hf.trans hzreal)
      · have hzreal : (z.1 : ℝ) ≤ center 0 + radius := by
          rw [jitterPoint_apply_zero] at hb₀
          have := (hoff z 0).1
          have := le_of_abs_le hb₀
          linarith
        have hc := Int.le_ceil (center 0 + radius)
        exact_mod_cast hzreal.trans hc
    · constructor
      · have hzreal : (center 1 - radius - 1) ≤ (z.2 : ℝ) := by
          rw [jitterPoint_apply_one] at hb₁
          have := (hoff z 1).2
          have := neg_le_of_abs_le hb₁
          linarith
        have hf := Int.floor_le (center 1 - radius - 1)
        exact Int.cast_le.mp (hf.trans hzreal)
      · have hzreal : (z.2 : ℝ) ≤ center 1 + radius := by
          rw [jitterPoint_apply_one] at hb₁
          have := (hoff z 1).1
          have := le_of_abs_le hb₁
          linarith
        have hc := Int.le_ceil (center 1 + radius)
        exact_mod_cast hzreal.trans hc
  have hfinidx : {z : ℤ × ℤ | jitterPoint offset z ∈ Metric.closedBall center radius}.Finite :=
    ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).subset hindices
  have himage : (jitterPoint offset) ''
      {z : ℤ × ℤ | jitterPoint offset z ∈ Metric.closedBall center radius} =
      diskPoints (Set.range (jitterPoint offset)) center radius := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, rfl⟩, hz⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      exact ⟨z, hz, rfl⟩
  rw [← himage]
  exact hfinidx.image _

end

end DiskDiscrepancy
