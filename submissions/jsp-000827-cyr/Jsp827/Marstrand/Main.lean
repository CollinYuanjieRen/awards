import Mathlib
import Jsp827.Statement
import Jsp827.Tower.Main
import Jsp827.Marstrand.Scale

/-!
# Assembly of Marstrand's counterexample

Scales `s = 0, 1, …`: `blockLen s := 2^(s+5)`, `primeList s` = all primes `≤ 2^(blockLen s)`,
threshold `j₀ := s + 1`, `towerErr s := 2^{-(s+1)}`, `boxSide s` a multiple of `blockLen s`
with `numPrimes s * blockLen s / boxSide s ≤ 2^{-s}`, and a tower base `base s` from
`RokhlinTower.NatAction.exists_tower`.  Put `bigE := ⋃ s, badScale s`, so
`volume bigE ≤ ∑ 2 / blockLen s = 1/8`.  The complements of `goodScale s` have summable
measure, so (Borel–Cantelli) almost every `x` lies in `goodScale s` for all large `s`; for
such `s` the scale `j_s(x) ≥ s + 1` satisfies `visitAverage bigE x (2^{j_s(x)}) ≥ 1/2`.
Hence `limsup ≥ 1/2 > 1/8 ≥ volume bigE`, so the averages do not converge to `volume bigE`.
Finally transfer from the circle to `ℝ` (`Int.fract (k * α)` is the class of `k • α`).
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Erdos994

open RokhlinTower

attribute [local instance] Classical.propDecidable

/-- The block length at scale `s`. -/
def blockLen (s : ℕ) : ℕ := 2 ^ (s + 5)

/-- The primes up to `2 ^ blockLen s`, as a finset. -/
def primeFinset (s : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ blockLen s + 1)).filter Nat.Prime

/-- The number of primes up to `2 ^ blockLen s`. -/
def numPrimes (s : ℕ) : ℕ := (primeFinset s).card

/-- The increasing enumeration of the primes up to `2 ^ blockLen s`. -/
def primeList (s : ℕ) : Fin (numPrimes s) → ℕ := (primeFinset s).orderEmbOfFin rfl

/-- The box side at scale `s`. -/
def boxSide (s : ℕ) : ℕ := blockLen s * (numPrimes s * 2 ^ s + 1)

/-- The tower error at scale `s`. -/
noncomputable def towerErr (s : ℕ) : ℝ := (1 / 2) ^ (s + 1)

/-- The block length is at least `3`, as required by the counting lemmas. -/
lemma three_le_blockLen (s : ℕ) : 3 ≤ blockLen s := by
  have : (2:ℕ) ^ 5 ≤ 2 ^ (s + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa [blockLen] using le_trans (by norm_num) this

/-- Membership in `primeFinset s` means being a prime at most `2 ^ blockLen s`. -/
lemma mem_primeFinset {s q : ℕ} : q ∈ primeFinset s ↔ q.Prime ∧ q ≤ 2 ^ blockLen s := by
  simp [primeFinset, Finset.mem_filter, Finset.mem_range, and_comm]

/-- The enumeration takes values in `primeFinset s`. -/
lemma primeList_mem (s : ℕ) (i : Fin (numPrimes s)) : primeList s i ∈ primeFinset s :=
  (primeFinset s).orderEmbOfFin_mem rfl i

/-- Every entry of `primeList s` is prime. -/
lemma primeList_prime (s : ℕ) : ∀ i, (primeList s i).Prime :=
  fun i ↦ (mem_primeFinset.mp (primeList_mem s i)).1

/-- The enumeration `primeList s` is injective. -/
lemma primeList_injective (s : ℕ) : Function.Injective (primeList s) :=
  ((primeFinset s).orderEmbOfFin rfl).injective

/-- `primeList s` enumerates exactly the primes `≤ 2 ^ blockLen s`. -/
lemma primeList_primesUpTo (s : ℕ) : PrimesUpTo (primeList s) (blockLen s) := by
  refine ⟨primeList_injective s, fun q hq hle ↦ ?_⟩
  have hmem : q ∈ primeFinset s := mem_primeFinset.mpr ⟨hq, hle⟩
  have hr : Set.range (primeList s) = ↑(primeFinset s) :=
    Finset.range_orderEmbOfFin (primeFinset s) rfl
  have hq' : q ∈ Set.range (primeList s) := by
    rw [hr]
    exact_mod_cast hmem
  obtain ⟨i, hi⟩ := hq'
  exact ⟨i, hi⟩

/-- The prime `2` occurs in `primeList s`. -/
lemma primeList_two (s : ℕ) : ∃ i, primeList s i = 2 := by
  have hb : 0 < blockLen s := by have := three_le_blockLen s; omega
  have h2 : (2:ℕ) ≤ 2 ^ blockLen s := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ blockLen s := Nat.pow_le_pow_right (by norm_num) hb
  exact (primeList_primesUpTo s).2 2 Nat.prime_two h2

/-- There is at least one prime below `2 ^ blockLen s`. -/
lemma one_le_numPrimes (s : ℕ) : 1 ≤ numPrimes s := by
  obtain ⟨i, _⟩ := primeList_two s
  have : 0 < numPrimes s := i.pos
  omega

/-- The block length divides the box side. -/
lemma blockLen_dvd_boxSide (s : ℕ) : blockLen s ∣ boxSide s := ⟨_, rfl⟩

/-- The block length is at most the box side. -/
lemma blockLen_le_boxSide (s : ℕ) : blockLen s ≤ boxSide s := by
  have h : 1 ≤ numPrimes s * 2 ^ s + 1 := by omega
  simpa [boxSide] using Nat.le_mul_of_pos_right (blockLen s) (by omega)

/-- The box side is positive. -/
lemma boxSide_pos (s : ℕ) : 0 < boxSide s :=
  lt_of_lt_of_le (by have := three_le_blockLen s; omega) (blockLen_le_boxSide s)

/-- The tower error is positive. -/
lemma towerErr_pos (s : ℕ) : 0 < towerErr s := by
  unfold towerErr
  positivity

/-- The tower error is at most `1`. -/
lemma towerErr_le_one (s : ℕ) : towerErr s ≤ 1 := by
  unfold towerErr
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The `ℕ^{numPrimes s}`-action at scale `s`. -/
noncomputable abbrev scaleAct (s : ℕ) :
    NatAction (volume : Measure UnitAddCircle) (numPrimes s) :=
  act (primeList s) (primeList_prime s)

/-- Existence of a tower base at scale `s`, from the Avila–Candela tower theorem. -/
lemma exists_base (s : ℕ) : ∃ W : Set UnitAddCircle,
    (scaleAct s).Admissible (fun _ ↦ boxSide s) W ∧
      1 - towerErr s ≤ (volume ((scaleAct s).tower (fun _ ↦ boxSide s) W)).toReal := by
  have : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  exact RokhlinTower.NatAction.exists_tower _
    (smoothAction_free (primeList s) (primeList_prime s) (primeList_injective s)) _
    (fun _ ↦ boxSide_pos s) (towerErr_pos s)

/-- The tower base at scale `s`. -/
noncomputable def base (s : ℕ) : Set UnitAddCircle := (exists_base s).choose

/-- The chosen base is admissible for the box of side `boxSide s`. -/
lemma base_admissible (s : ℕ) : (scaleAct s).Admissible (fun _ ↦ boxSide s) (base s) :=
  (exists_base s).choose_spec.1

/-- The chosen base is measurable. -/
lemma measurableSet_base (s : ℕ) : MeasurableSet (base s) := (base_admissible s).1

/-- The tower over the chosen base has measure at least `1 - towerErr s`. -/
lemma base_tower (s : ℕ) :
    1 - towerErr s ≤ (volume ((scaleAct s).tower (fun _ ↦ boxSide s) (base s))).toReal :=
  (exists_base s).choose_spec.2

/-- The bad set at scale `s`. -/
noncomputable def badScale (s : ℕ) : Set UnitAddCircle :=
  badSet (primeList s) (primeList_prime s) (blockLen s) (boxSide s) (base s)

/-- The good set at scale `s`. -/
noncomputable def goodScale (s : ℕ) : Set UnitAddCircle :=
  goodSet (primeList s) (primeList_prime s) (blockLen s) (boxSide s) (s + 1) (base s)

/-- The counterexample on the circle. -/
noncomputable def bigE : Set UnitAddCircle := ⋃ s, badScale s

/-- The bad set at scale `s` is measurable. -/
lemma measurableSet_badScale (s : ℕ) : MeasurableSet (badScale s) :=
  measurableSet_badSet _ _ (measurableSet_base s)

/-- The good set at scale `s` is measurable. -/
lemma measurableSet_goodScale (s : ℕ) : MeasurableSet (goodScale s) :=
  measurableSet_goodSet _ _ (measurableSet_base s)

/-- The circle counterexample is measurable. -/
lemma measurableSet_bigE : MeasurableSet bigE :=
  MeasurableSet.iUnion fun s ↦ measurableSet_badScale s

/-- The block length is positive. -/
lemma blockLen_pos (s : ℕ) : 0 < blockLen s := by
  have := three_le_blockLen s
  omega

/-- The unit circle has total volume one. -/
lemma isProbabilityMeasure_circle : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The circle has finite volume. -/
lemma volume_circle_ne_top (A : Set UnitAddCircle) : volume A ≠ ∞ := by
  have := isProbabilityMeasure_circle
  exact measure_ne_top _ _

/-- The bad set at scale `s` has measure at most `2 / blockLen s`. -/
lemma measure_badScale_le (s : ℕ) :
    (volume (badScale s)).toReal ≤ 2 / (blockLen s : ℝ) :=
  measure_badSet_le (primeList s) (primeList_prime s) (blockLen_pos s)
    (blockLen_dvd_boxSide s) (primeList_two s) (base_admissible s)

/-- Explicit form of the scale-`s` measure bound as a geometric term. -/
lemma two_div_blockLen (s : ℕ) : 2 / (blockLen s : ℝ) = (1 / 16) * (1 / 2) ^ s := by
  have h : ((blockLen s : ℕ) : ℝ) = 2 ^ (s + 5) := by
    simp [blockLen]
  rw [h, pow_add]
  rw [div_pow, one_pow]
  field_simp
  ring

/-- Geometric bound for the measure of the bad set at scale `s`. -/
lemma volume_badScale_le (s : ℕ) :
    volume (badScale s) ≤ ENNReal.ofReal ((1 / 16) * (1 / 2) ^ s) := by
  rw [ENNReal.le_ofReal_iff_toReal_le (volume_circle_ne_top _) (by positivity)]
  rw [← two_div_blockLen]
  exact measure_badScale_le s

/-- The circle counterexample has volume at most `1/8`. -/
lemma volume_bigE_le : volume bigE ≤ ENNReal.ofReal (1 / 8) := by
  have hsum : ∑' s : ℕ, ((1 : ℝ) / 16) * (1 / 2) ^ s = 1 / 8 := by
    rw [tsum_mul_left, tsum_geometric_two]
    norm_num
  calc volume bigE ≤ ∑' s : ℕ, volume (badScale s) := measure_iUnion_le _
    _ ≤ ∑' s : ℕ, ENNReal.ofReal ((1 / 16) * (1 / 2) ^ s) :=
        ENNReal.tsum_le_tsum fun s ↦ volume_badScale_le s
    _ = ENNReal.ofReal (1 / 8) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun s ↦ by positivity)
          (summable_geometric_two.mul_left _), hsum]

/-- Real form of the volume bound for `bigE`. -/
lemma toReal_volume_bigE_le : (volume bigE).toReal ≤ 1 / 8 :=
  ENNReal.toReal_le_of_le_ofReal (by norm_num) volume_bigE_le

/-- The real value of the block length. -/
lemma blockLen_cast (s : ℕ) : ((blockLen s : ℕ) : ℝ) = 32 * 2 ^ s := by
  have : ((2:ℝ) ^ (s + 5)) = 2 ^ s * 32 := by
    rw [pow_add]
    norm_num
  simp [blockLen, this]
  ring

/-- The real value of the box side. -/
lemma boxSide_cast (s : ℕ) :
    ((boxSide s : ℕ) : ℝ) = (blockLen s : ℝ) * ((numPrimes s : ℝ) * 2 ^ s + 1) := by
  simp only [boxSide, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]

/-- The threshold `s + 1` is at most the block length. -/
lemma succ_le_blockLen (s : ℕ) : s + 1 ≤ blockLen s := by
  have h : s + 5 < 2 ^ (s + 5) := Nat.lt_two_pow_self
  simp only [blockLen]
  omega

/-- Bernoulli bound for the `(3/2)^s` growth used below. -/
lemma bernoulli_three_halves (s : ℕ) : 1 + (s : ℝ) / 2 ≤ (3 / 2) ^ s := by
  have h := one_add_mul_le_pow (a := (1/2 : ℝ)) (by norm_num) s
  have h2 : (1 : ℝ) + (1 / 2) = 3 / 2 := by norm_num
  rw [h2] at h
  calc 1 + (s : ℝ) / 2 = 1 + (s : ℝ) * (1 / 2) := by ring
    _ ≤ (3 / 2) ^ s := h

/-- Comparison of the two geometric rates used below. -/
lemma half_pow_le (s : ℕ) : ((1 : ℝ) / 2) ^ s ≤ (3 / 4) ^ s :=
  pow_le_pow_left₀ (by norm_num) (by norm_num) s

/-- The tower error is dominated by `(3/4)^s`. -/
lemma towerErr_le (s : ℕ) : towerErr s ≤ (3 / 4) ^ s := by
  have h : towerErr s ≤ (1 / 2 : ℝ) ^ s := by
    unfold towerErr
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) s]
  exact h.trans (half_pow_le s)

/-- The threshold term is dominated by `(3/4)^s`. -/
lemma thresholdTerm_le (s : ℕ) : ((s : ℝ) + 1) / (blockLen s : ℝ) ≤ (3 / 4) ^ s := by
  have hpos : (0 : ℝ) < 32 * 2 ^ s := by positivity
  rw [blockLen_cast, div_le_iff₀ hpos]
  have hb := bernoulli_three_halves s
  have h32 : (3 / 4 : ℝ) ^ s * (32 * 2 ^ s) = 32 * (3 / 2) ^ s := by
    rw [show (32:ℝ) * 2 ^ s = 2 ^ s * 32 by ring, ← mul_assoc, ← mul_pow]
    norm_num
    ring
  rw [h32]
  nlinarith [Nat.cast_nonneg (α := ℝ) s]

/-- The tower-shape term is dominated by `2^{-s}`. -/
lemma primeTerm_le (s : ℕ) :
    (numPrimes s : ℝ) * ((blockLen s : ℝ) / (boxSide s : ℝ)) ≤ (1 / 2 : ℝ) ^ s := by
  have hB : (0 : ℝ) < (blockLen s : ℝ) := by
    exact_mod_cast blockLen_pos s
  have hD : (1 : ℝ) ≤ (numPrimes s : ℝ) := by
    exact_mod_cast one_le_numPrimes s
  have hden : (0 : ℝ) < (numPrimes s : ℝ) * 2 ^ s + 1 := by positivity
  rw [boxSide_cast]
  have hrw : (numPrimes s : ℝ) * ((blockLen s : ℝ) /
      ((blockLen s : ℝ) * ((numPrimes s : ℝ) * 2 ^ s + 1)))
      = (numPrimes s : ℝ) / ((numPrimes s : ℝ) * 2 ^ s + 1) := by
    field_simp
  rw [hrw, div_le_iff₀ hden]
  have hp : ((1:ℝ) / 2) ^ s * 2 ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) s]

/-- `(1-x)(1-y)(1-z) ≥ 1-x-y-z` for `x, y ≥ 0` and `z ∈ [0,1]`. -/
lemma three_factor_bound {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - x - y - z ≤ (1 - x) * (1 - y) * (1 - z) := by
  nlinarith [mul_nonneg (mul_nonneg hx hy) (sub_nonneg.mpr hz1), mul_nonneg hx hz,
    mul_nonneg hy hz]

/-- A linear lower bound for the measure of the good set at scale `s`. -/
lemma measure_goodScale_ge (s : ℕ) :
    1 - towerErr s - (numPrimes s : ℝ) * ((blockLen s : ℝ) / (boxSide s : ℝ))
        - ((s : ℝ) + 1) / (blockLen s : ℝ) ≤ (volume (goodScale s)).toReal := by
  have hmain := measure_goodSet_ge (primeList s) (primeList_prime s) (blockLen_pos s)
    (blockLen_dvd_boxSide s) (blockLen_le_boxSide s) (succ_le_blockLen s) (primeList_two s)
    (base_admissible s) (base_tower s)
  set a : ℝ := (blockLen s : ℝ) / (boxSide s : ℝ) with ha
  set x : ℝ := towerErr s with hxdef
  set y : ℝ := (numPrimes s : ℝ) * a with hy
  set z : ℝ := ((s : ℝ) + 1) / (blockLen s : ℝ) with hz
  have hcast : ((s + 1 : ℕ) : ℝ) / (blockLen s : ℝ) = z := by
    rw [hz]
    push_cast
    ring
  rw [hcast] at hmain
  have hx0 : 0 ≤ x := (towerErr_pos s).le
  have hx1 : x ≤ 1 := towerErr_le_one s
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by exact_mod_cast boxSide_pos s)]
    exact_mod_cast blockLen_le_boxSide s
  have hy0 : 0 ≤ y := by positivity
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z ≤ 1 := by
    rw [hz, div_le_one (by exact_mod_cast blockLen_pos s)]
    have := succ_le_blockLen s
    have : ((s : ℝ) + 1) ≤ ((blockLen s : ℕ) : ℝ) := by exact_mod_cast this
    exact this
  have hber : 1 - y ≤ (1 - a) ^ (numPrimes s) := by
    have h := one_add_mul_le_pow (a := -a) (by linarith) (numPrimes s)
    calc 1 - y = 1 + (numPrimes s : ℝ) * (-a) := by rw [hy]; ring
      _ ≤ (1 + -a) ^ (numPrimes s) := h
      _ = (1 - a) ^ (numPrimes s) := by ring_nf
  have step1 : (1 - x) * (1 - y) ≤ (1 - x) * (1 - a) ^ (numPrimes s) :=
    mul_le_mul_of_nonneg_left hber (by linarith)
  have step2 : (1 - x) * (1 - y) * (1 - z) ≤ (1 - x) * (1 - a) ^ (numPrimes s) * (1 - z) :=
    mul_le_mul_of_nonneg_right step1 (by linarith)
  have step3 : 1 - x - y - z ≤ (1 - x) * (1 - y) * (1 - z) :=
    three_factor_bound hx0 hy0 hz0 hz1
  rw [goodScale]
  linarith [hmain]

/-- The complement of the good set at scale `s` is small. -/
lemma toReal_volume_compl_goodScale_le (s : ℕ) :
    (volume (goodScale s)ᶜ).toReal ≤ 3 * (3 / 4) ^ s := by
  have hle : volume (goodScale s) ≤ 1 := by
    calc volume (goodScale s) ≤ volume (univ : Set UnitAddCircle) := measure_mono (subset_univ _)
      _ = 1 := UnitAddCircle.measure_univ
  have hcompl : volume (goodScale s)ᶜ = 1 - volume (goodScale s) := by
    rw [measure_compl (measurableSet_goodScale s) (volume_circle_ne_top _),
      UnitAddCircle.measure_univ]
  have htoReal : (volume (goodScale s)ᶜ).toReal = 1 - (volume (goodScale s)).toReal := by
    rw [hcompl, ENNReal.toReal_sub_of_le hle (by simp)]
    simp
  rw [htoReal]
  have h1 := measure_goodScale_ge s
  have h2 := towerErr_le s
  have h3 := (primeTerm_le s).trans (half_pow_le s)
  have h4 := thresholdTerm_le s
  linarith

/-- Geometric bound for the measure of the complement of the good set. -/
lemma volume_compl_goodScale_le (s : ℕ) :
    volume (goodScale s)ᶜ ≤ ENNReal.ofReal (3 * (3 / 4) ^ s) := by
  rw [ENNReal.le_ofReal_iff_toReal_le (volume_circle_ne_top _) (by positivity)]
  exact toReal_volume_compl_goodScale_le s

/-- The complements of the good sets have summable measure. -/
lemma tsum_volume_compl_goodScale_ne_top : ∑' s : ℕ, volume (goodScale s)ᶜ ≠ ∞ := by
  have hsummable : Summable fun s : ℕ ↦ 3 * (3 / 4 : ℝ) ^ s :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3
  have hle : ∑' s : ℕ, volume (goodScale s)ᶜ ≤ ∑' s : ℕ, ENNReal.ofReal (3 * (3 / 4 : ℝ) ^ s) :=
    ENNReal.tsum_le_tsum fun s ↦ volume_compl_goodScale_le s
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun s ↦ by positivity) hsummable] at hle
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- Borel–Cantelli: almost every point is eventually good. -/
lemma ae_eventually_mem_goodScale :
    ∀ᵐ x : UnitAddCircle, ∀ᶠ s in atTop, x ∈ goodScale s := by
  filter_upwards [MeasureTheory.ae_eventually_notMem tsum_volume_compl_goodScale_ne_top]
    with x hx
  filter_upwards [hx] with s hs
  simpa using hs

/-- A good point at scale `s` has a dyadic scale `j ≥ s + 1` at which at
least half of its multiples visit `bigE`. -/
lemma visits_of_mem_goodScale {x : UnitAddCircle} {s : ℕ} (hx : x ∈ goodScale s) :
    ∃ j : ℕ, s + 1 ≤ j ∧
      2 ^ (j - 1) ≤ ((Finset.Icc 1 (2 ^ j)).filter fun n ↦ n • x ∈ bigE).card := by
  rw [goodScale, goodSet] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨e, he, hxe⟩ := hx
  have he' := he
  rw [goodIdx, Finset.mem_filter] at he'
  refine ⟨L (primeList s) e % blockLen s, he'.2.2, ?_⟩
  have hhalf := half_visits (primeList s) (primeList_prime s) (three_le_blockLen s)
    (primeList_primesUpTo s) he (by omega) hxe
  refine le_trans hhalf (Finset.card_le_card ?_)
  refine Finset.monotone_filter_right _ fun n _ hn ↦ ?_
  simp only [bigE, Set.mem_iUnion]
  exact ⟨s, hn⟩

/-- Almost every point of the circle sees dyadic scales at which at least half of its
multiples land in `bigE`. -/
lemma ae_visits_bigE : ∀ᵐ x : UnitAddCircle, ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
    2 ^ (j - 1) ≤ ((Finset.Icc 1 (2 ^ j)).filter fun n ↦ n • x ∈ bigE).card := by
  filter_upwards [ae_eventually_mem_goodScale] with x hx j₀
  obtain ⟨s, hs, hsj⟩ := (hx.and (eventually_ge_atTop j₀)).exists
  obtain ⟨j, hj, hcard⟩ := visits_of_mem_goodScale hs
  exact ⟨j, by omega, hcard⟩

/-- Circle version of the counterexample: a measurable `E ⊆ UnitAddCircle` with
`volume E ≤ 1/8` such that for almost every `x`, infinitely many dyadic scales `2^j` have at
least half of the multiples `1 ≤ n ≤ 2^j` of `x` in `E`. -/
theorem exists_circle_counterexample :
    ∃ E : Set UnitAddCircle, MeasurableSet E ∧ (volume E).toReal ≤ 1 / 8 ∧
      ∀ᵐ x : UnitAddCircle, ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
        2 ^ (j - 1) ≤ ((Finset.Icc 1 (2 ^ j)).filter fun n => n • x ∈ E).card :=
  ⟨bigE, measurableSet_bigE, toReal_volume_bigE_le, ae_visits_bigE⟩

/-- Integers vanish in the unit circle. -/
lemma intCast_circle_eq_zero (m : ℤ) : ((m : ℝ) : UnitAddCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m, by simp⟩

/-- The class of `Int.fract (k * α)` in the circle is `k • α`. -/
lemma coe_fract (α : ℝ) (k : ℕ) :
    ((Int.fract ((k : ℝ) * α) : ℝ) : UnitAddCircle) = k • ((α : ℝ) : UnitAddCircle) := by
  have h1 : Int.fract ((k : ℝ) * α) = (k : ℝ) * α + ((-⌊(k : ℝ) * α⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h1, show ((((k : ℝ) * α + ((-⌊(k : ℝ) * α⌋ : ℤ) : ℝ) : ℝ)) : UnitAddCircle)
      = (((k : ℝ) * α : ℝ) : UnitAddCircle) + ((((-⌊(k : ℝ) * α⌋ : ℤ)) : ℝ) : UnitAddCircle) from
      rfl, intCast_circle_eq_zero, add_zero, ← nsmul_eq_mul, AddCircle.coe_nsmul]

/-- The counterexample on the line. -/
noncomputable def bigE' : Set ℝ := Ioo (0 : ℝ) 1 ∩ ((↑) : ℝ → UnitAddCircle) ⁻¹' bigE

/-- The real counterexample is measurable. -/
lemma measurableSet_bigE' : MeasurableSet bigE' :=
  measurableSet_Ioo.inter ((AddCircle.measurable_mk' (a := (1 : ℝ))) measurableSet_bigE)

/-- The real counterexample has measure at most `1/8`. -/
lemma volume_bigE'_le : (volume bigE').toReal ≤ 1 / 8 := by
  have hproj := AddCircle.add_projection_respects_measure (T := 1) (t := 0) measurableSet_bigE
  have hsub : bigE' ⊆ (QuotientAddGroup.mk ⁻¹' bigE ∩ Ioc (0 : ℝ) (0 + 1)) := by
    intro y hy
    exact ⟨hy.2, ⟨hy.1.1, by simpa using hy.1.2.le⟩⟩
  have hle : volume bigE' ≤ volume bigE := by
    rw [hproj]
    exact measure_mono hsub
  exact le_trans (ENNReal.toReal_mono (volume_circle_ne_top _) hle) toReal_volume_bigE_le

/-- The preimage of a circle null set under the covering map is null. -/
lemma preimage_null {Z : Set UnitAddCircle} (hZ : MeasurableSet Z) (h0 : volume Z = 0) :
    volume ((QuotientAddGroup.mk : ℝ → UnitAddCircle) ⁻¹' Z) = 0 := by
  have hcover : (QuotientAddGroup.mk : ℝ → UnitAddCircle) ⁻¹' Z
      = ⋃ m : ℤ, ((QuotientAddGroup.mk : ℝ → UnitAddCircle) ⁻¹' Z ∩
        Ioc ((m : ℝ)) ((m : ℝ) + 1)) := by
    refine Set.eq_of_subset_of_subset (fun y hy ↦ ?_)
      (Set.iUnion_subset fun m ↦ Set.inter_subset_left)
    refine Set.mem_iUnion.mpr ⟨⌈y⌉ - 1, hy, ?_, ?_⟩
    · push_cast
      linarith [Int.ceil_lt_add_one y]
    · push_cast
      linarith [Int.le_ceil y]
  rw [hcover]
  refine measure_iUnion_null fun m ↦ ?_
  rw [← AddCircle.add_projection_respects_measure (T := 1) (t := (m : ℝ)) hZ]
  exact h0

/-- An almost-everywhere property on the circle pulls back to `ℝ`. -/
lemma ae_pullback {P : UnitAddCircle → Prop} (h : ∀ᵐ x : UnitAddCircle, P x) :
    ∀ᵐ α : ℝ, P ((α : ℝ) : UnitAddCircle) := by
  rw [ae_iff] at h ⊢
  obtain ⟨Z, hsub, hmeas, h0⟩ := exists_measurable_superset_of_null h
  exact measure_mono_null (fun α hα ↦ hsub hα) (preimage_null hmeas h0)

/-- Almost every real number is irrational. -/
lemma ae_irrational : ∀ᵐ α : ℝ, Irrational α := by
  rw [ae_iff]
  have hset : {α : ℝ | ¬ Irrational α} = Set.range ((↑) : ℚ → ℝ) := by
    ext α
    simp [Irrational]
  rw [hset]
  exact (Set.countable_range _).measure_zero _

/-- For irrational `α` and `k ≥ 1`, `Int.fract (k * α)` lies in `bigE'`
exactly when `k • α` lies in `bigE`. -/
lemma fract_mem_bigE'_iff {α : ℝ} (hα : Irrational α) {k : ℕ} (hk : 1 ≤ k) :
    Int.fract ((k : ℝ) * α) ∈ bigE' ↔ k • ((α : ℝ) : UnitAddCircle) ∈ bigE := by
  have hpos : 0 < Int.fract ((k : ℝ) * α) := by
    rcases (Int.fract_nonneg ((k : ℝ) * α)).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hirr : Irrational ((k : ℝ) * α) := hα.natCast_mul (by omega)
      have h2 : (k : ℝ) * α - (⌊(k : ℝ) * α⌋ : ℤ) = 0 := by
        rw [← Int.fract]
        exact h1.symm
      exact hirr.ne_int _ (sub_eq_zero.mp h2)
  constructor
  · intro h
    rw [← coe_fract]
    exact h.2
  · intro h
    refine ⟨⟨hpos, Int.fract_lt_one _⟩, ?_⟩
    show ((Int.fract ((k : ℝ) * α) : ℝ) : UnitAddCircle) ∈ bigE
    rw [coe_fract]
    exact h

/-- The visit averages of `bigE'` count the circle multiples landing in `bigE`. -/
lemma visitAverage_eq {α : ℝ} (hα : Irrational α) (n : ℕ) :
    visitAverage bigE' α n
      = (((Finset.Icc 1 n).filter fun k ↦ k • ((α : ℝ) : UnitAddCircle) ∈ bigE).card : ℝ) / n := by
  have hfilter : ((Finset.Icc 1 n).filter fun k : ℕ ↦ Int.fract ((k : ℝ) * α) ∈ bigE')
      = ((Finset.Icc 1 n).filter fun k : ℕ ↦ k • ((α : ℝ) : UnitAddCircle) ∈ bigE) :=
    Finset.filter_congr fun k hk ↦ fract_mem_bigE'_iff hα (Finset.mem_Icc.mp hk).1
  rw [visitAverage, Finset.sum_boole, hfilter]

/-- At a good dyadic scale the visit average is at least `1/2`. -/
lemma half_le_visitAverage {α : ℝ} (hα : Irrational α) {j : ℕ} (hj : 1 ≤ j)
    (hcard : 2 ^ (j - 1) ≤ ((Finset.Icc 1 (2 ^ j)).filter
      fun n ↦ n • ((α : ℝ) : UnitAddCircle) ∈ bigE).card) :
    1 / 2 ≤ visitAverage bigE' α (2 ^ j) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [visitAverage_eq hα, le_div_iff₀ (by positivity)]
  have h0 : (2 : ℕ) ^ m ≤ ((Finset.Icc 1 (2 ^ (m + 1))).filter
      fun n : ℕ ↦ n • ((α : ℝ) : UnitAddCircle) ∈ bigE).card := by simpa using hcard
  have h1 : ((2 : ℝ) ^ m) ≤
      (((Finset.Icc 1 (2 ^ (m + 1))).filter
        fun n : ℕ ↦ n • ((α : ℝ) : UnitAddCircle) ∈ bigE).card : ℝ) := by
    exact_mod_cast h0
  have h2 : (1 / 2 : ℝ) * (((2 ^ (m + 1) : ℕ) : ℝ)) = 2 ^ m := by
    push_cast
    rw [pow_succ]
    ring
  rw [h2]
  exact h1

/-- Transfer: the fractional parts `Int.fract (k * α)` are the representatives in `[0,1)` of
`k • (α : UnitAddCircle)`; the set `E' := {x ∈ Ioo 0 1 | (x : UnitAddCircle) ∈ E}` has the
same measure as `E` and, for irrational `α`, the same visit counts. -/
theorem exists_counterexample_ae' :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ α : ℝ, ¬ HasExpectedLimit E α := by
  refine ⟨bigE', measurableSet_bigE', Set.inter_subset_left, ?_⟩
  filter_upwards [ae_irrational, ae_pullback ae_visits_bigE] with α hα hvis
  intro hlim
  have hc : (volume bigE').toReal < 1 / 4 := lt_of_le_of_lt volume_bigE'_le (by norm_num)
  have hev : ∀ᶠ n in atTop, visitAverage bigE' α n < 1 / 4 :=
    Filter.Tendsto.eventually_lt_const hc hlim
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  obtain ⟨j, hj, hcard⟩ := hvis (max M 1)
  have hj1 : 1 ≤ j := le_trans (le_max_right M 1) hj
  have hjM : M ≤ j := le_trans (le_max_left M 1) hj
  have h2j : M ≤ 2 ^ j := le_trans hjM (le_of_lt Nat.lt_two_pow_self)
  have hlt := hM (2 ^ j) h2j
  have hge := half_le_visitAverage hα hj1 hcard
  linarith

/-- The explicit witness form of the target, closing `Erdos994.exists_counterexample_ae`. -/
theorem exists_counterexample_ae_final :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ α : ℝ, ¬ HasExpectedLimit E α := exists_counterexample_ae'

/-- **Marstrand 1970.**  Khintchine's fixed-set conjecture is false. -/
theorem not_khintchineFixedSet_final : ¬ KhintchineFixedSet :=
  not_khintchineFixedSet_of_exists exists_counterexample_ae'

end Erdos994
