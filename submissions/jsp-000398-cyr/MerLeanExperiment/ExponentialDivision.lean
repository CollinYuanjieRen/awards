import MerLeanExperiment.Subdivision
import MerLeanExperiment.SimultaneousApproximation

open Set

namespace Erdos492Real

noncomputable section

/-- The exponential endpoint with index `j` in Schmidt's finite grid. -/
def exponentialGridPoint (q j : ℕ) : ℝ :=
  Real.exp (-(q : ℝ) + (j : ℝ) / q)

/-- Schmidt's truncated exponential grid, together with the endpoint zero. -/
def exponentialPoints (q : ℕ) : Finset ℝ :=
  {0} ∪ (Finset.range (q ^ 2 + 1)).image (exponentialGridPoint q)

/-- The truncated exponential grid is a finite division of the unit interval. -/
def exponentialDivision (q : ℕ) (hq : 0 < q) : FiniteDivision where
  points := exponentialPoints q
  zero_mem := by simp [exponentialPoints]
  one_mem := by
    rw [exponentialPoints, Finset.mem_union]
    right
    rw [Finset.mem_image]
    refine ⟨q ^ 2, by simp, ?_⟩
    simp only [exponentialGridPoint, Real.exp_eq_one_iff]
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    push_cast
    field_simp
    ring
  mem_unit := by
    intro x hx
    rw [exponentialPoints, Finset.mem_union] at hx
    rcases hx with hx | hx
    · simp_all
    · rw [Finset.mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      refine ⟨Real.exp_pos _ |>.le, ?_⟩
      unfold exponentialGridPoint
      rw [Real.exp_le_one_iff]
      have hjlt := Finset.mem_range.mp hj
      have hjle : j ≤ q ^ 2 := by omega
      have hqr : (0 : ℝ) < q := by exact_mod_cast hq
      have hjler : (j : ℝ) ≤ q ^ 2 := by exact_mod_cast hjle
      have hdiv : (j : ℝ) / q ≤ q := by
        apply (div_le_iff₀ hqr).2
        nlinarith
      linarith

/-- The positive exponential grid points are strictly increasing with their indices. -/
theorem exponentialGridPoint_strictMono (q : ℕ) (hq : 0 < q) :
    StrictMono (exponentialGridPoint q) := by
  intro i j hij
  rw [exponentialGridPoint, exponentialGridPoint, Real.exp_lt_exp]
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hijr : (i : ℝ) < j := by exact_mod_cast hij
  have hdiv := (div_lt_div_iff_of_pos_right hqr).2 hijr
  linarith

/-- Consecutive positive grid points differ by the common exponential ratio. -/
theorem exponentialGridPoint_succ (q j : ℕ) (hq : 0 < q) :
    exponentialGridPoint q (j + 1) =
      exponentialGridPoint q j * Real.exp (1 / (q : ℝ)) := by
  rw [exponentialGridPoint, exponentialGridPoint, ← Real.exp_add]
  congr 1
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  push_cast
  field_simp
  ring

/-- A sufficiently deep and fine exponential grid is fine as a real subdivision. -/
theorem exponentialDivision_fine (q : ℕ) (hq : 0 < q) (ε : ℝ)
    (hbottom : exponentialGridPoint q 0 < ε)
    (hratio : Real.exp (1 / (q : ℝ)) - 1 < ε) :
    (exponentialDivision q hq).Fine ε := by
  intro a b hab
  have ha := hab.1
  have hb := hab.2.1
  have hunit_a := (exponentialDivision q hq).mem_unit a ha
  have hunit_b := (exponentialDivision q hq).mem_unit b hb
  have hgrid_mem (j : ℕ) (hj : j < q ^ 2 + 1) :
      exponentialGridPoint q j ∈ (exponentialDivision q hq).points := by
    change exponentialGridPoint q j ∈ exponentialPoints q
    rw [exponentialPoints, Finset.mem_union]
    right
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  have ha' : a ∈ exponentialPoints q := ha
  rw [exponentialPoints, Finset.mem_union] at ha'
  rcases ha' with ha' | ha'
  · simp only [Finset.mem_singleton] at ha'
    subst a
    have hc : exponentialGridPoint q 0 ∈
        (exponentialDivision q hq).points := hgrid_mem 0 (by positivity)
    have hcpos : 0 < exponentialGridPoint q 0 := Real.exp_pos _
    have hbc := hab.2.2.2 _ hc hcpos
    linarith
  · rw [Finset.mem_image] at ha'
    obtain ⟨j, hj, rfl⟩ := ha'
    have hjlt : j < q ^ 2 + 1 := Finset.mem_range.mp hj
    by_cases hjtop : j = q ^ 2
    · subst j
      have haone : exponentialGridPoint q (q ^ 2) = 1 := by
        change Real.exp (-q + (q ^ 2 : ℕ) / (q : ℝ)) = 1
        rw [Real.exp_eq_one_iff]
        have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
        push_cast
        field_simp
        ring
      rw [haone] at hab
      have hablt := hab.2.2.1
      linarith [hunit_b.2]
    · have hjsucc : j + 1 < q ^ 2 + 1 := by omega
      have hc : exponentialGridPoint q (j + 1) ∈
          (exponentialDivision q hq).points := hgrid_mem (j + 1) hjsucc
      have hac : exponentialGridPoint q j < exponentialGridPoint q (j + 1) :=
        exponentialGridPoint_strictMono q hq (Nat.lt_succ_self j)
      have hbc := hab.2.2.2 _ hc hac
      have hratio_nonneg : 0 ≤ Real.exp (1 / (q : ℝ)) - 1 := by
        have hqr : (0 : ℝ) ≤ 1 / q := by positivity
        exact sub_nonneg.mpr (Real.one_le_exp hqr)
      have hgap : exponentialGridPoint q (j + 1) - exponentialGridPoint q j ≤
          Real.exp (1 / (q : ℝ)) - 1 := by
        rw [exponentialGridPoint_succ q j hq]
        have haj : exponentialGridPoint q j ≤ 1 := hunit_a.2
        nlinarith [Real.exp_pos (-(q : ℝ) + (j : ℝ) / q)]
      linarith

end

end Erdos492Real
