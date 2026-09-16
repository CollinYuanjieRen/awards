import Mathlib

/-!
# Towers for commuting endomorphisms: basic definitions

Avila–Candela, Ann. Inst. Fourier 66 (2016) 1529–1544, Section 1.  A measure-preserving
action of `ℕ^d` by commuting endomorphisms, boxes of multi-indices, admissible sets
(pairwise disjoint preimages over a box) and towers.
-/

open MeasureTheory Set
open scoped ENNReal

namespace RokhlinTower

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- A measure-preserving action of `ℕ^d` (as `Fin d → ℕ`) by commuting endomorphisms. -/
structure NatAction (d : ℕ) where
  /-- the endomorphism attached to a multi-index -/
  f : (Fin d → ℕ) → X → X
  f_zero : f 0 = id
  f_add : ∀ m n, f (m + n) = f m ∘ f n
  measurePreserving : ∀ n, MeasurePreserving (f n) μ μ

variable {μ}

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

lemma f_apply_add (m n : Fin d → ℕ) (x : X) : A.f (m + n) x = A.f m (A.f n x) :=
  congrFun (A.f_add m n) x

lemma f_comm (m n : Fin d → ℕ) (x : X) : A.f m (A.f n x) = A.f n (A.f m x) := by
  rw [← A.f_apply_add, ← A.f_apply_add, add_comm]

lemma measurable (n : Fin d → ℕ) : Measurable (A.f n) :=
  (A.measurePreserving n).measurable

/-- Preimages compose additively. -/
lemma preimage_preimage (m n : Fin d → ℕ) (B : Set X) :
    A.f m ⁻¹' (A.f n ⁻¹' B) = A.f (n + m) ⁻¹' B := by
  ext x
  simp only [Set.mem_preimage, A.f_apply_add]

lemma measure_preimage (n : Fin d → ℕ) {B : Set X} (hB : MeasurableSet B) :
    μ (A.f n ⁻¹' B) = μ B :=
  (A.measurePreserving n).measure_preimage hB.nullMeasurableSet

/-- Freeness: distinct multi-indices agree only on a null set. -/
def Free : Prop :=
  ∀ k l : Fin d → ℕ, k ≠ l → μ {x | A.f k x = A.f l x} = 0

end NatAction

/-- The box `[0, n)` of multi-indices. -/
def box {d : ℕ} (n : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => Finset.range (n i)

lemma mem_box {d : ℕ} {n k : Fin d → ℕ} : k ∈ box n ↔ ∀ i, k i < n i := by
  simp [box, Fintype.mem_piFinset, Finset.mem_range]

lemma card_box {d : ℕ} (n : Fin d → ℕ) : (box n).card = ∏ i, n i := by
  simp [box, Fintype.card_piFinset, Finset.card_range]

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

/-- `B` is `n`-admissible: its preimages over the box are pairwise disjoint. -/
def Admissible (n : Fin d → ℕ) (B : Set X) : Prop :=
  MeasurableSet B ∧
    ∀ k ∈ box n, ∀ l ∈ box n, k ≠ l → Disjoint (A.f k ⁻¹' B) (A.f l ⁻¹' B)

/-- The tower over `B`. -/
def tower (n : Fin d → ℕ) (B : Set X) : Set X :=
  ⋃ k ∈ box n, A.f k ⁻¹' B

lemma measurableSet_tower {n : Fin d → ℕ} {B : Set X} (hB : MeasurableSet B) :
    MeasurableSet (A.tower n B) :=
  Finset.measurableSet_biUnion _ fun k _ ↦ A.measurable k hB

/-- The measure of an admissible tower is the number of levels times the base measure. -/
lemma measure_tower {n : Fin d → ℕ} {B : Set X} (hB : A.Admissible n B) :
    μ (A.tower n B) = (box n).card * μ B := by
  have hd : (↑(box n) : Set (Fin d → ℕ)).PairwiseDisjoint fun k ↦ A.f k ⁻¹' B :=
    fun k hk l hl hkl ↦ hB.2 k (by simpa using hk) l (by simpa using hl) hkl
  have hm : ∀ k ∈ box n, MeasurableSet (A.f k ⁻¹' B) := fun k _ ↦ A.measurable k hB.1
  rw [tower, measure_biUnion_finset hd hm]
  simp only [A.measure_preimage _ hB.1, Finset.sum_const, nsmul_eq_mul]

/-- Every level of an admissible tower has the measure of the base; in particular the
base measure is at most `μ univ / card (box n)`. -/
lemma card_mul_measure_le {n : Fin d → ℕ} {B : Set X} (hB : A.Admissible n B) :
    (box n).card * μ B ≤ μ univ := by
  rw [← A.measure_tower hB]
  exact measure_mono (subset_univ _)

/-- Admissibility is inherited by measurable subsets. -/
lemma Admissible.mono {n : Fin d → ℕ} {B C : Set X} (hB : A.Admissible n B)
    (hC : MeasurableSet C) (hCB : C ⊆ B) : A.Admissible n C :=
  ⟨hC, fun k hk l hl hkl ↦
    (hB.2 k hk l hl hkl).mono (preimage_mono hCB) (preimage_mono hCB)⟩

/-- A preimage of an admissible set is admissible. -/
lemma Admissible.preimage {n : Fin d → ℕ} {B : Set X} (hB : A.Admissible n B)
    (m : Fin d → ℕ) : A.Admissible n (A.f m ⁻¹' B) := by
  have h : ∀ j : Fin d → ℕ,
      A.f j ⁻¹' (A.f m ⁻¹' B) = A.f m ⁻¹' (A.f j ⁻¹' B) := fun j ↦ by
    rw [A.preimage_preimage, A.preimage_preimage, add_comm]
  refine ⟨A.measurable m hB.1, fun k hk l hl hkl ↦ ?_⟩
  rw [h k, h l]
  exact Disjoint.preimage _ (hB.2 k hk l hl hkl)

end NatAction

end RokhlinTower
