import MerLeanExperiment.PeriodicPoints

open Set

namespace DiskDiscrepancy

noncomputable section

def intResidue (L : ℕ) (hL : 0 < L) (z : ℤ) : Fin L :=
  ⟨(z % (L : ℤ)).toNat, by
    have hp : (0 : ℤ) < L := by exact_mod_cast hL
    have hn := Int.emod_nonneg z hp.ne'
    have ht := Int.emod_lt_of_pos z hp
    omega⟩

@[simp] theorem intResidue_add_mul (L : ℕ) (hL : 0 < L) (z k : ℤ) :
    intResidue L hL (z + (L : ℤ) * k) = intResidue L hL z := by
  apply Fin.ext
  simp [intResidue, Int.add_emod]

def midpointOffset (L q : ℕ) (hL : 0 < L) (_hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) (z : ℤ × ℤ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i ↦
    let v := omega (intResidue L hL z.1, intResidue L hL z.2)
    if i = 0 then ((v.1.val : ℝ) + 1 / 2) / q
    else ((v.2.val : ℝ) + 1 / 2) / q

theorem midpointOffset_mem_Ico (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) (z : ℤ × ℤ) (i : Fin 2) :
    0 ≤ midpointOffset L q hL hq omega z i ∧
      midpointOffset L q hL hq omega z i < 1 := by
  fin_cases i <;> simp [midpointOffset]
  · have hv := (omega (intResidue L hL z.1, intResidue L hL z.2)).1.isLt
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    constructor
    · positivity
    · apply (div_lt_one hqR).2
      have hvR : ((omega (intResidue L hL z.1, intResidue L hL z.2)).1.val : ℝ) + 1 ≤ q := by
        exact_mod_cast hv
      linarith
  · have hv := (omega (intResidue L hL z.1, intResidue L hL z.2)).2.isLt
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    constructor
    · positivity
    · apply (div_lt_one hqR).2
      have hvR : ((omega (intResidue L hL z.1, intResidue L hL z.2)).2.val : ℝ) + 1 ≤ q := by
        exact_mod_cast hv
      linarith

def periodicGridPoint (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) : ℤ × ℤ → Plane :=
  jitterPoint (midpointOffset L q hL hq omega)

def periodicGridSet (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) : Set Plane :=
  Set.range (periodicGridPoint L q hL hq omega)

theorem admissible_periodicGridSet (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) :
    Admissible (periodicGridSet L q hL hq omega) := by
  have hoff := midpointOffset_mem_Ico L q hL hq omega
  have hinj : Function.Injective (periodicGridPoint L q hL hq omega) :=
    jitterPoint_injective hoff
  constructor
  · exact Set.infinite_range_of_injective hinj
  · exact locallyFinitePoints_range_jitterPoint hoff

def periodVector (L : ℕ) (k : ℤ × ℤ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i ↦
    if i = 0 then (L : ℝ) * k.1 else (L : ℝ) * k.2

theorem midpointOffset_add_period (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) (z k : ℤ × ℤ) :
    midpointOffset L q hL hq omega
        (z.1 + (L : ℤ) * k.1, z.2 + (L : ℤ) * k.2) =
      midpointOffset L q hL hq omega z := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [midpointOffset, intResidue_add_mul]

theorem periodicGridPoint_add_period (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) (z k : ℤ × ℤ) :
    periodicGridPoint L q hL hq omega
        (z.1 + (L : ℤ) * k.1, z.2 + (L : ℤ) * k.2) =
      periodicGridPoint L q hL hq omega z + periodVector L k := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i
  · simp [periodicGridPoint, jitterPoint, periodVector, midpointOffset,
      intResidue_add_mul]
    ring
  · simp [periodicGridPoint, jitterPoint, periodVector, midpointOffset,
      intResidue_add_mul]
    ring

theorem periodicGridSet_add_period (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) (k : ℤ × ℤ) :
    (fun x ↦ x + periodVector L k) '' periodicGridSet L q hL hq omega =
      periodicGridSet L q hL hq omega := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(z.1 + (L : ℤ) * k.1, z.2 + (L : ℤ) * k.2), ?_⟩
    exact periodicGridPoint_add_period L q hL hq omega z k
  · rintro ⟨z, rfl⟩
    let w : ℤ × ℤ := (z.1 - (L : ℤ) * k.1, z.2 - (L : ℤ) * k.2)
    refine ⟨periodicGridPoint L q hL hq omega w, ⟨w, rfl⟩, ?_⟩
    have hp := periodicGridPoint_add_period L q hL hq omega w k
    have hw : (w.1 + (L : ℤ) * k.1, w.2 + (L : ℤ) * k.2) = z := by
      apply Prod.ext <;> dsimp [w] <;> ring
    rw [hw] at hp
    exact hp.symm

end

end DiskDiscrepancy
