import MerLeanExperiment.AngleLimit
import Mathlib.Tactic

/-!
Finite binary power-sum configurations and their exact leading limits.
-/

namespace PlanarMinimax

open Filter Set
open scoped Topology

/-- A binary word with `k` entries. -/
abbrev BinaryWord (k : ℕ) := Fin k → Bool

/-- The real coefficient represented by a Boolean bit. -/
def bitCoeff (b : Bool) : ℝ :=
  if b then 1 else 0

/-- The indices at which two binary words differ. -/
def differingIndices {k : ℕ} (b c : BinaryWord k) : Finset (Fin k) :=
  Finset.univ.filter fun j ↦ b j ≠ c j

/-- Distinct binary words have a differing index. -/
theorem differingIndices_nonempty {k : ℕ} {b c : BinaryWord k} (hbc : b ≠ c) :
    (differingIndices b c).Nonempty := by
  by_contra hempty
  apply hbc
  funext j
  by_contra hj
  have hjmem : j ∈ differingIndices b c := by
    simp [differingIndices, hj]
  exact hempty ⟨j, hjmem⟩

/-- The least index at which two distinct binary words differ. -/
noncomputable def firstDiff {k : ℕ} (b c : BinaryWord k) (hbc : b ≠ c) : Fin k :=
  (differingIndices b c).min' (differingIndices_nonempty hbc)

/-- The selected first-difference index really differs. -/
theorem firstDiff_ne {k : ℕ} (b c : BinaryWord k) (hbc : b ≠ c) :
    b (firstDiff b c hbc) ≠ c (firstDiff b c hbc) := by
  have hmem := Finset.min'_mem (differingIndices b c) (differingIndices_nonempty hbc)
  simpa [differingIndices, firstDiff] using hmem

/-- The first difference is no later than any other differing index. -/
theorem firstDiff_le {k : ℕ} (b c : BinaryWord k) (hbc : b ≠ c) (j : Fin k)
    (hj : b j ≠ c j) : firstDiff b c hbc ≤ j := by
  apply Finset.min'_le
  simp [differingIndices, hj]

/-- All entries before the first difference coincide. -/
theorem before_firstDiff {k : ℕ} (b c : BinaryWord k) (hbc : b ≠ c) (j : Fin k)
    (hj : j < firstDiff b c hbc) : b j = c j := by
  by_contra hne
  exact (not_le_of_gt hj) (firstDiff_le b c hbc j hne)

/-- A supplied index is the first difference of two words. -/
def IsFirstDiff {k : ℕ} (b c : BinaryWord k) (r : Fin k) : Prop :=
  b r ≠ c r ∧ ∀ j, j < r → b j = c j

/-- The selected least differing index satisfies the proof-facing specification. -/
theorem firstDiff_spec {k : ℕ} (b c : BinaryWord k) (hbc : b ≠ c) :
    IsFirstDiff b c (firstDiff b c hbc) := by
  exact ⟨firstDiff_ne b c hbc, before_firstDiff b c hbc⟩

/-- The binary power-sum point associated to a word. -/
def binaryPoint {k : ℕ} (u : Fin k → Plane) (ε : ℝ) (b : BinaryWord k) : Plane :=
  ∑ j, (ε ^ j.val * bitCoeff (b j)) • u j

/-- The polynomial tail after extracting the power at an index `r`. -/
def binaryTail {k : ℕ} (u : Fin k → Plane) (b c : BinaryWord k) (r : Fin k)
    (ε : ℝ) : Plane :=
  ∑ j, (ε ^ (j.val - r.val) * (bitCoeff (c j) - bitCoeff (b j))) • u j

/-- The difference of two binary power sums factors exactly at their first differing power. -/
theorem binaryPoint_sub_factor {k : ℕ} (u : Fin k → Plane) (b c : BinaryWord k)
    (r : Fin k) (hr : IsFirstDiff b c r) (ε : ℝ) :
    binaryPoint u ε c - binaryPoint u ε b = (ε ^ r.val) • binaryTail u b c r ε := by
  unfold binaryPoint binaryTail
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < r
  · have hbit : b j = c j := hr.2 j hj
    simp [hbit]
  · have hrj : r.val ≤ j.val := by omega
    rw [← sub_smul, smul_smul]
    congr 1
    have hexp : r.val + (j.val - r.val) = j.val := Nat.add_sub_of_le hrj
    have hpow : ε ^ j.val = ε ^ r.val * ε ^ (j.val - r.val) := by
      rw [← pow_add, hexp]
    rw [hpow]
    ring

/-- At zero, the tail is exactly its signed leading vector. -/
theorem binaryTail_zero {k : ℕ} (u : Fin k → Plane) (b c : BinaryWord k) (r : Fin k)
    (hr : IsFirstDiff b c r) :
    binaryTail u b c r 0 = (bitCoeff (c r) - bitCoeff (b r)) • u r := by
  unfold binaryTail
  rw [Finset.sum_eq_single r]
  · simp
  · intro j _ hjr
    by_cases hj : j < r
    · simp [hr.2 j hj]
    · have hrj : r < j := by omega
      have hpos : 0 < j.val - r.val := Nat.sub_pos_of_lt hrj
      simp [zero_pow hpos.ne']
  · simp

/-- The finite polynomial tail is continuous. -/
theorem continuous_binaryTail {k : ℕ} (u : Fin k → Plane) (b c : BinaryWord k)
    (r : Fin k) : Continuous (binaryTail u b c r) := by
  unfold binaryTail
  fun_prop

/-- Positive nonzero parameters cancel the extracted power under inverse rescaling. -/
theorem invPow_smul_binaryPoint_sub {k : ℕ} (u : Fin k → Plane)
    (b c : BinaryWord k) (r : Fin k) (hr : IsFirstDiff b c r) {ε : ℝ} (hε : ε ≠ 0) :
    (ε ^ r.val)⁻¹ • (binaryPoint u ε c - binaryPoint u ε b) = binaryTail u b c r ε := by
  rw [binaryPoint_sub_factor u b c r hr ε, smul_smul]
  simp [hε]

/-- The inverse extracted power is positive at every positive parameter. -/
theorem invPow_pos {r : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 < (ε ^ r)⁻¹ := by
  exact inv_pos.mpr (pow_pos hε r)

/-- The inverse extracted power is eventually positive along positive parameters near zero. -/
theorem eventually_invPow_pos (r : ℕ) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < (ε ^ r)⁻¹ := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact invPow_pos hε

/-- Inverse-power rescaled displacements converge to the signed leading vector. -/
theorem tendsto_invPow_binaryPoint_sub {k : ℕ} (u : Fin k → Plane)
    (b c : BinaryWord k) (r : Fin k) (hr : IsFirstDiff b c r) :
    Tendsto (fun ε : ℝ ↦ (ε ^ r.val)⁻¹ • (binaryPoint u ε c - binaryPoint u ε b))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds ((bitCoeff (c r) - bitCoeff (b r)) • u r)) := by
  rw [← binaryTail_zero u b c r hr]
  apply ((continuous_binaryTail u b c r).continuousAt.mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (invPow_smul_binaryPoint_sub u b c r hr hε.ne').symm

/-- The signed leading vector is nonzero when its frame vector is nonzero. -/
theorem signedLeading_ne_zero {k : ℕ} (u : Fin k → Plane) (b c : BinaryWord k)
    (r : Fin k) (hr : b r ≠ c r) (hu : u r ≠ 0) :
    (bitCoeff (c r) - bitCoeff (b r)) • u r ≠ 0 := by
  cases hbr : b r <;> cases hcr : c r <;> simp_all [bitCoeff]

/-- Two Boolean bits different from the same bit give the same signed real difference. -/
theorem bitCoeff_sub_eq_of_ne {x y z : Bool} (hxy : x ≠ y) (hxz : x ≠ z) :
    bitCoeff y - bitCoeff x = bitCoeff z - bitCoeff x := by
  cases x <;> cases y <;> cases z <;> simp_all [bitCoeff]

/-- At a common first index, two outgoing words have identical signed leading vectors. -/
theorem same_signedLeading {k : ℕ} (u : Fin k → Plane) (b c d : BinaryWord k)
    (r : Fin k) (hbc : b r ≠ c r) (hbd : b r ≠ d r) :
    (bitCoeff (c r) - bitCoeff (b r)) • u r =
      (bitCoeff (d r) - bitCoeff (b r)) • u r := by
  rw [bitCoeff_sub_eq_of_ne hbc hbd]

/-- Equal first-difference indices from one base word give identical leading vectors. -/
theorem same_signedLeading_firstDiff {k : ℕ} (u : Fin k → Plane)
    (b c d : BinaryWord k) (hbc : b ≠ c) (hbd : b ≠ d)
    (hfirst : firstDiff b c hbc = firstDiff b d hbd) :
    (bitCoeff (c (firstDiff b c hbc)) - bitCoeff (b (firstDiff b c hbc))) •
        u (firstDiff b c hbc) =
      (bitCoeff (d (firstDiff b d hbd)) - bitCoeff (b (firstDiff b d hbd))) •
        u (firstDiff b d hbd) := by
  rw [hfirst]
  exact same_signedLeading u b c d (firstDiff b d hbd)
    (hfirst ▸ firstDiff_ne b c hbc) (firstDiff_ne b d hbd)

#print axioms binaryPoint_sub_factor
#print axioms binaryTail_zero
#print axioms tendsto_invPow_binaryPoint_sub
#print axioms signedLeading_ne_zero
#print axioms same_signedLeading
#print axioms same_signedLeading_firstDiff

end PlanarMinimax
