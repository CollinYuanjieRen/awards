import MerLeanExperiment.ExponentialDivision

open Set

namespace Erdos492Real

noncomputable section

/-- The logarithmic position of the arithmetic midpoint of one exponential cell,
scaled so that a whole cell has length one. -/
def phaseThreshold (q : ℕ) : ℝ :=
  (q : ℝ) * Real.log ((1 + Real.exp (1 / (q : ℝ))) / 2)

/-- The periodic sign pattern determined by the arithmetic halves of exponential cells. -/
def phaseSign (q : ℕ) (x : ℝ) : ℝ :=
  if Int.fract ((q : ℝ) * Real.log x) < phaseThreshold q then 1 else -1

/-- The scaled midpoint threshold lies strictly inside one logarithmic cell. -/
theorem phaseThreshold_mem_Ioo (q : ℕ) (hq : 0 < q) :
    phaseThreshold q ∈ Ioo (0 : ℝ) 1 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hinv : (0 : ℝ) < 1 / q := by positivity
  have hexp : 1 < Real.exp (1 / (q : ℝ)) := by
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr hinv)
  have hmid_pos : 0 < (1 + Real.exp (1 / (q : ℝ))) / 2 := by positivity
  have hone_mid : 1 < (1 + Real.exp (1 / (q : ℝ))) / 2 := by linarith
  have hmid_exp : (1 + Real.exp (1 / (q : ℝ))) / 2 <
      Real.exp (1 / (q : ℝ)) := by linarith
  constructor
  · exact mul_pos hqr (Real.log_pos hone_mid)
  · have hlog : Real.log ((1 + Real.exp (1 / (q : ℝ))) / 2) < 1 / q := by
      calc
        Real.log ((1 + Real.exp (1 / (q : ℝ))) / 2) <
            Real.log (Real.exp (1 / (q : ℝ))) :=
          Real.strictMonoOn_log hmid_pos (Real.exp_pos _) hmid_exp
        _ = 1 / q := Real.log_exp _
    rw [phaseThreshold]
    calc
      (q : ℝ) * Real.log ((1 + Real.exp (1 / (q : ℝ))) / 2) <
          (q : ℝ) * (1 / q) := mul_lt_mul_of_pos_left hlog hqr
      _ = 1 := by field_simp

/-- Adjacent indices below the top of the exponential grid are consecutive endpoints. -/
theorem exponentialGridPoint_consecutive (q j : ℕ) (hq : 0 < q) (hj : j < q ^ 2) :
    Consecutive (exponentialPoints q : Set ℝ) (exponentialGridPoint q j)
      (exponentialGridPoint q (j + 1)) := by
  have hmem (k : ℕ) (hk : k < q ^ 2 + 1) :
      exponentialGridPoint q k ∈ exponentialPoints q := by
    rw [exponentialPoints, Finset.mem_union]
    right
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  refine ⟨hmem j (by omega), hmem (j + 1) (by omega),
    exponentialGridPoint_strictMono q hq (Nat.lt_succ_self j), ?_⟩
  intro c hc hjc
  have hc' : c ∈ exponentialPoints q := hc
  rw [exponentialPoints, Finset.mem_union] at hc'
  rcases hc' with hc | hc
  · simp only [Finset.mem_singleton] at hc
    subst c
    exact False.elim <| (not_lt_of_ge (Real.exp_pos _).le) hjc
  · rw [Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    have hjk : j < k := by
      by_contra h
      have hkj : k ≤ j := Nat.le_of_not_gt h
      exact (not_lt_of_ge (exponentialGridPoint_strictMono q hq |>.monotone hkj)) hjc
    exact exponentialGridPoint_strictMono q hq |>.monotone (by omega)

/-- Every point above the truncation lies in one of the finite exponential cells. -/
theorem exists_exponential_cell (q : ℕ) (hq : 0 < q) {x : ℝ}
    (hlo : exponentialGridPoint q 0 ≤ x) (hhi : x < 1) :
    ∃ j < q ^ 2, exponentialGridPoint q j ≤ x ∧
      x < exponentialGridPoint q (j + 1) := by
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hlo
  let y : ℝ := (q : ℝ) * (Real.log x + q)
  have hloglo : -(q : ℝ) ≤ Real.log x := by
    have := Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hxpos hlo
    simpa [exponentialGridPoint, Real.log_exp] using this
  have hy0 : 0 ≤ y := by
    dsimp [y]
    have hqr : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have hloghi : Real.log x < 0 := Real.log_neg hxpos hhi
  have hylt : y < (q ^ 2 : ℕ) := by
    dsimp [y]
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    push_cast
    nlinarith
  let j := ⌊y⌋₊
  have hjle : (j : ℝ) ≤ y := Nat.floor_le hy0
  have hyj : y < (j : ℝ) + 1 := Nat.lt_floor_add_one y
  have hj : j < q ^ 2 := by exact_mod_cast lt_of_le_of_lt hjle hylt
  refine ⟨j, hj, ?_, ?_⟩
  · rw [exponentialGridPoint]
    dsimp [y] at hjle
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    rw [← Real.exp_log hxpos]
    apply Real.exp_le_exp.mpr
    have hdiv : (j : ℝ) / q ≤ Real.log x + q := by
      apply (div_le_iff₀ hqr).2
      nlinarith
    linarith
  · rw [exponentialGridPoint]
    dsimp [y] at hyj
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    rw [← Real.exp_log hxpos]
    apply Real.exp_lt_exp.mpr
    have hdiv : Real.log x + q < ((j + 1 : ℕ) : ℝ) / q := by
      apply (lt_div_iff₀ hqr).2
      push_cast
      nlinarith
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using hdiv

/-- The scaled logarithm takes integral values at the exponential grid points. -/
theorem scaledLog_exponentialGridPoint (q j : ℕ) (hq : 0 < q) :
    (q : ℝ) * Real.log (exponentialGridPoint q j) = (j : ℝ) - q ^ 2 := by
  rw [exponentialGridPoint, Real.log_exp]
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp
  ring

/-- The arithmetic midpoint of the exponential cell with left index `j`. -/
def exponentialCellMidpoint (q j : ℕ) : ℝ :=
  exponentialGridPoint q j +
    (1 / 2 : ℝ) * (exponentialGridPoint q (j + 1) - exponentialGridPoint q j)

/-- The scaled logarithm of a cell midpoint is its left integral phase plus
the common midpoint threshold. -/
theorem scaledLog_exponentialCellMidpoint (q j : ℕ) (hq : 0 < q) :
    (q : ℝ) * Real.log (exponentialCellMidpoint q j) =
      (j : ℝ) - q ^ 2 + phaseThreshold q := by
  have hgrid : 0 < exponentialGridPoint q j := Real.exp_pos _
  have hfactor : 0 < (1 + Real.exp (1 / (q : ℝ))) / 2 := by positivity
  have hmid : exponentialCellMidpoint q j =
      exponentialGridPoint q j * ((1 + Real.exp (1 / (q : ℝ))) / 2) := by
    rw [exponentialCellMidpoint, exponentialGridPoint_succ q j hq]
    ring
  rw [hmid, Real.log_mul hgrid.ne' hfactor.ne', phaseThreshold]
  have hgridlog := scaledLog_exponentialGridPoint q j hq
  nlinarith

/-- Within a fixed exponential cell, the fractional logarithmic phase records
the displacement from the left endpoint. -/
theorem fract_scaledLog_of_mem_exponentialCell (q j : ℕ) (hq : 0 < q) {x : ℝ}
    (hlo : exponentialGridPoint q j ≤ x)
    (hhi : x < exponentialGridPoint q (j + 1)) :
    Int.fract ((q : ℝ) * Real.log x) =
      (q : ℝ) * Real.log x - ((j : ℝ) - q ^ 2) := by
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hlo
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hloglo : (j : ℝ) - q ^ 2 ≤ (q : ℝ) * Real.log x := by
    rw [← scaledLog_exponentialGridPoint q j hq]
    exact mul_le_mul_of_nonneg_left
      (Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hxpos hlo) hqpos.le
  have hloghi : (q : ℝ) * Real.log x < ((j : ℝ) - q ^ 2) + 1 := by
    have hlog := Real.strictMonoOn_log hxpos (Real.exp_pos _) hhi
    have hs := scaledLog_exponentialGridPoint q (j + 1) hq
    push_cast at hs
    calc
      (q : ℝ) * Real.log x <
          (q : ℝ) * Real.log (exponentialGridPoint q (j + 1)) :=
        mul_lt_mul_of_pos_left hlog hqpos
      _ = ((j : ℝ) + 1) - q ^ 2 := hs
      _ = ((j : ℝ) - q ^ 2) + 1 := by ring
  let z : ℤ := (j : ℤ) - (q ^ 2 : ℕ)
  let t : ℝ := (q : ℝ) * Real.log x - (z : ℝ)
  have hz : (z : ℝ) = (j : ℝ) - q ^ 2 := by
    dsimp [z]
    push_cast
    rfl
  have ht : t ∈ Ico (0 : ℝ) 1 := by
    rw [mem_Ico]
    dsimp [t]
    rw [hz]
    constructor <;> linarith
  have hxrepr : (q : ℝ) * Real.log x = t + (z : ℝ) := by
    dsimp [t]
    ring
  rw [hxrepr, Int.fract_add_intCast, Int.fract_eq_self.2 ht]
  dsimp [t]
  rw [hz]
  ring

/-- In a cell, lying below its arithmetic midpoint is equivalent to lying
below the common fractional logarithmic threshold. -/
theorem lt_exponentialCellMidpoint_iff_fract (q j : ℕ) (hq : 0 < q) {x : ℝ}
    (hlo : exponentialGridPoint q j ≤ x)
    (hhi : x < exponentialGridPoint q (j + 1)) :
    x < exponentialCellMidpoint q j ↔
      Int.fract ((q : ℝ) * Real.log x) < phaseThreshold q := by
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hlo
  have hmidpos : 0 < exponentialCellMidpoint q j := by
    have hgrid : 0 < exponentialGridPoint q j := Real.exp_pos _
    have hfactor : 0 < (1 + Real.exp (1 / (q : ℝ))) / 2 := by positivity
    rw [exponentialCellMidpoint, exponentialGridPoint_succ q j hq]
    rw [show exponentialGridPoint q j +
        1 / 2 * (exponentialGridPoint q j * Real.exp (1 / (q : ℝ)) -
          exponentialGridPoint q j) =
        exponentialGridPoint q j * ((1 + Real.exp (1 / (q : ℝ))) / 2) by ring]
    exact mul_pos hgrid hfactor
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  rw [fract_scaledLog_of_mem_exponentialCell q j hq hlo hhi]
  have hlogiff : x < exponentialCellMidpoint q j ↔
      (q : ℝ) * Real.log x <
        (q : ℝ) * Real.log (exponentialCellMidpoint q j) := by
    constructor
    · intro h
      exact mul_lt_mul_of_pos_left (Real.strictMonoOn_log hxpos hmidpos h) hqpos
    · intro h
      have hlog : Real.log x < Real.log (exponentialCellMidpoint q j) := by
        nlinarith
      exact (Real.strictMonoOn_log.lt_iff_lt hxpos hmidpos).mp hlog
  rw [hlogiff, scaledLog_exponentialCellMidpoint q j hq]
  constructor <;> intro h <;> linarith

/-- On a known cell, membership in the actual lower-half region is exactly
the arithmetic midpoint inequality. -/
theorem mem_lowerRegion_exponentialPoints_iff (q j : ℕ) (hq : 0 < q)
    (hj : j < q ^ 2) {x : ℝ}
    (hlo : exponentialGridPoint q j ≤ x)
    (hhi : x < exponentialGridPoint q (j + 1)) :
    x ∈ lowerRegion (exponentialPoints q : Set ℝ) (1 / 2) ↔
      x < exponentialCellMidpoint q j := by
  let a := exponentialGridPoint q j
  let b := exponentialGridPoint q (j + 1)
  have hab : Consecutive (exponentialPoints q : Set ℝ) a b :=
    exponentialGridPoint_consecutive q j hq hj
  constructor
  · rintro ⟨u, v, huv, hux, hxmid⟩
    have huvlt : u < v := huv.2.2.1
    have hxv : x < v := by nlinarith
    have hua : u = a := by
      apply le_antisymm
      · by_contra h
        have hau : a < u := lt_of_not_ge h
        have hbu : b ≤ u := hab.2.2.2 u huv.1 hau
        nlinarith
      · by_contra h
        have hua' : u < a := lt_of_not_ge h
        have hva : v ≤ a := huv.2.2.2 a hab.1 hua'
        nlinarith
    have hvb : v = b := by
      apply le_antisymm
      · exact huv.2.2.2 b hab.2.1 (by simpa [hua] using hab.2.2.1)
      · exact hab.2.2.2 v huv.2.1 (by simpa [hua] using huvlt)
    simpa [exponentialCellMidpoint, a, b, hua, hvb] using hxmid
  · intro hxmid
    exact ⟨a, b, hab, hlo, by simpa [exponentialCellMidpoint, a, b] using hxmid⟩

/-- Above the truncated bottom endpoint and below one, the actual exponential
division sign is precisely its periodic logarithmic phase sign. -/
theorem divisionSign_exponentialPoints_eq_phaseSign (q : ℕ) (hq : 0 < q) {x : ℝ}
    (hlo : exponentialGridPoint q 0 ≤ x) (hhi : x < 1) :
    divisionSign (exponentialPoints q : Set ℝ) x = phaseSign q x := by
  obtain ⟨j, hj, hxlo, hxhi⟩ := exists_exponential_cell q hq hlo hhi
  rw [divisionSign, phaseSign]
  rw [mem_lowerRegion_exponentialPoints_iff q j hq hj hxlo hxhi,
    lt_exponentialCellMidpoint_iff_fract q j hq hxlo hxhi]

end

end Erdos492Real
