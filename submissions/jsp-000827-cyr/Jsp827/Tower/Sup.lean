import Mathlib
import Jsp827.Tower.Basic
import Jsp827.Tower.Iterate

/-!
# Towers of measure `> 2^{-d} μ Y − ε` (Avila–Candela Lemma 2.4)

A supremum argument: if the best admissible base inside preimages of `Y` had measure
`ρ < μ Y / (2^d ∏ n i)`, one could enlarge a near-optimal base by an admissible set found
(Lemma 2.3) inside `f_{N₀+n}⁻¹ Y` minus the `2n`-tower of the near-optimal base.
-/

open MeasureTheory Set
open scoped ENNReal

namespace RokhlinTower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Doubling every side of a box multiplies its cardinality by `2 ^ d`. -/
lemma card_box_two_mul {d : ℕ} (n : Fin d → ℕ) :
    (box fun i ↦ 2 * n i).card = 2 ^ d * (box n).card := by
  simp [card_box, Finset.prod_mul_distrib]

/-- A box with positive sides contains its own corner inside its double. -/
lemma self_mem_box_two_mul {d : ℕ} {n : Fin d → ℕ} (hn : ∀ i, 0 < n i) :
    n ∈ box fun i ↦ 2 * n i :=
  mem_box.2 fun i ↦ by have := hn i; omega

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

/-- Each level of a tower is contained in the tower. -/
lemma preimage_subset_tower {m k : Fin d → ℕ} (hk : k ∈ box m) (B : Set X) :
    A.f k ⁻¹' B ⊆ A.tower m B := fun _ hx ↦ Set.mem_biUnion hk hx

/-- The union bound for a tower: no admissibility is needed. -/
lemma measure_tower_le (m : Fin d → ℕ) {B : Set X} (hB : MeasurableSet B) :
    μ (A.tower m B) ≤ (box m).card * μ B :=
  calc μ (A.tower m B) ≤ ∑ _k ∈ box m, μ B := by
        refine (measure_biUnion_finset_le _ _).trans ?_
        exact Finset.sum_le_sum fun k _ ↦ (A.measure_preimage k hB).le
    _ = (box m).card * μ B := by simp [mul_comm]

/-- Splicing an `n`-admissible set living outside the `2n`-tower of `D` onto a preimage of
`f n ⁻¹' D` preserves `n`-admissibility. -/
lemma Admissible.union_preimage {n : Fin d → ℕ} {D C : Set X}
    (hD : A.Admissible n D) (hC : A.Admissible n C) (N : Fin d → ℕ)
    (hCT : ∀ x ∈ C, A.f N x ∉ A.tower (fun i ↦ 2 * n i) D) :
    A.Admissible n (A.f N ⁻¹' (A.f n ⁻¹' D) ∪ C) := by
  have hP : A.Admissible n (A.f N ⁻¹' (A.f n ⁻¹' D)) := (hD.preimage A n).preimage A N
  have cross : ∀ k ∈ box n, ∀ l ∈ box n,
      Disjoint (A.f k ⁻¹' C) (A.f l ⁻¹' (A.f N ⁻¹' (A.f n ⁻¹' D))) := by
    intro k hk l hl
    rw [Set.disjoint_left]
    intro x hxk hxl
    obtain ⟨m, hm⟩ : ∃ m : Fin d → ℕ, ∀ i, m i = l i + n i - k i := ⟨_, fun _ ↦ rfl⟩
    have hmbox : m ∈ box fun i ↦ 2 * n i := mem_box.2 fun i ↦ by
      have h1 := mem_box.1 hk i
      have h2 := mem_box.1 hl i
      have h3 := hm i
      omega
    refine hCT _ hxk (A.preimage_subset_tower hmbox D ?_)
    show A.f m (A.f N (A.f k x)) ∈ D
    have key : A.f m (A.f N (A.f k x)) = A.f n (A.f N (A.f l x)) := by
      simp only [← A.f_apply_add]
      congr 1
      funext i
      have h1 := mem_box.1 hk i
      have h3 := hm i
      simp only [Pi.add_apply]
      omega
    rw [key]
    exact hxl
  refine ⟨(A.measurable N (A.measurable n hD.1)).union hC.1, fun k hk l hl hkl ↦ ?_⟩
  rw [Set.preimage_union, Set.preimage_union, Set.disjoint_union_left,
    Set.disjoint_union_right, Set.disjoint_union_right]
  exact ⟨⟨hP.2 k hk l hl hkl, (cross l hl k hk).symm⟩,
    ⟨cross k hk l hl, hC.2 k hk l hl hkl⟩⟩

/-- The set of measures of `n`-admissible sets sitting inside some preimage of `Y`. -/
def baseMeasures (n : Fin d → ℕ) (Y : Set X) : Set ℝ :=
  {r : ℝ | ∃ (N : Fin d → ℕ) (B : Set X), A.Admissible n B ∧ B ⊆ A.f N ⁻¹' Y ∧
    r = (μ B).toReal}

/-- The empty base shows that `0` belongs to `baseMeasures`. -/
lemma zero_mem_baseMeasures (n : Fin d → ℕ) (Y : Set X) : (0 : ℝ) ∈ A.baseMeasures n Y :=
  ⟨0, ∅, ⟨MeasurableSet.empty, fun k _ l _ _ ↦ by simp⟩, Set.empty_subset _, by simp⟩

/-- `baseMeasures` is nonempty. -/
lemma baseMeasures_nonempty (n : Fin d → ℕ) (Y : Set X) : (A.baseMeasures n Y).Nonempty :=
  ⟨0, A.zero_mem_baseMeasures n Y⟩

/-- `baseMeasures` is bounded above by `1`. -/
lemma baseMeasures_bddAbove [IsProbabilityMeasure μ] (n : Fin d → ℕ) (Y : Set X) :
    BddAbove (A.baseMeasures n Y) := by
  refine ⟨1, ?_⟩
  rintro r ⟨N, B, -, -, rfl⟩
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- The supremum of the base measures is at least `μ Y / (2 ^ d * card (box n))`. -/
lemma measure_le_sSup_baseMeasures [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) {n : Fin d → ℕ}
    (hn : ∀ i, 0 < n i) {Y : Set X} (hY : MeasurableSet Y) :
    (μ Y).toReal ≤ 2 ^ d * (box n).card * sSup (A.baseMeasures n Y) := by
  have hSne : (A.baseMeasures n Y).Nonempty := A.baseMeasures_nonempty n Y
  have hSbdd : BddAbove (A.baseMeasures n Y) := A.baseMeasures_bddAbove n Y
  set ρ : ℝ := sSup (A.baseMeasures n Y) with hρdef
  have hπnn : (0 : ℝ) ≤ 2 ^ d * (box n).card := by positivity
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc, hLem⟩ := A.exists_admissible_subset hfree n
  have hδpos : 0 < (μ Y).toReal - 2 ^ d * (box n).card * ρ := by linarith
  obtain ⟨-, ⟨N₀, D, hD, hDY, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hSne
    (show ρ - ((μ Y).toReal - 2 ^ d * (box n).card * ρ) * c < ρ from
      sub_lt_self _ (mul_pos hδpos hc))
  have hDρ : (μ D).toReal ≤ ρ := le_csSup hSbdd ⟨N₀, D, hD, hDY, rfl⟩
  have hTmeas : MeasurableSet (A.tower (fun i ↦ 2 * n i) D) :=
    A.measurableSet_tower hD.1
  have hTle : (μ (A.tower (fun i ↦ 2 * n i) D)).toReal ≤
      2 ^ d * (box n).card * (μ D).toReal := by
    calc (μ (A.tower (fun i ↦ 2 * n i) D)).toReal
        ≤ (((box fun i ↦ 2 * n i).card : ℝ≥0∞) * μ D).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
            (measure_ne_top μ D)) (A.measure_tower_le _ hD.1)
      _ = ((box fun i ↦ 2 * n i).card : ℝ) * (μ D).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      _ = 2 ^ d * (box n).card * (μ D).toReal := by
          rw [card_box_two_mul]; push_cast; ring
  -- the set `Y' \ T` has measure at least `δ`
  have hY' : μ (A.f (N₀ + n) ⁻¹' Y) = μ Y := A.measure_preimage _ hY
  have hreal : (μ Y).toReal ≤
      (μ (A.f (N₀ + n) ⁻¹' Y \ A.tower (fun i ↦ 2 * n i) D)).toReal +
        (μ (A.tower (fun i ↦ 2 * n i) D)).toReal := by
    rw [← hY', ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) ?_
    refine (measure_mono (fun x hx ↦ ?_)).trans (measure_union_le _ _)
    by_cases hxT : x ∈ A.tower (fun i ↦ 2 * n i) D
    · exact Or.inr hxT
    · exact Or.inl ⟨hx, hxT⟩
  have hstep : 2 ^ d * (box n).card * (μ D).toReal ≤ 2 ^ d * (box n).card * ρ :=
    mul_le_mul_of_nonneg_left hDρ hπnn
  have hδle : (μ Y).toReal - 2 ^ d * (box n).card * ρ ≤
      (μ (A.f (N₀ + n) ⁻¹' Y \ A.tower (fun i ↦ 2 * n i) D)).toReal := by linarith
  obtain ⟨N₁, C, hC, hCsub, hCmeas⟩ :=
    hLem _ ((A.measurable _ hY).diff hTmeas)
  have hCδ : c * ((μ Y).toReal - 2 ^ d * (box n).card * ρ) ≤ (μ C).toReal :=
    le_trans (mul_le_mul_of_nonneg_left hδle hc.le) hCmeas
  -- the enlarged base
  have hCT : ∀ x ∈ C, A.f N₁ x ∉ A.tower (fun i ↦ 2 * n i) D := fun x hx ↦ (hCsub hx).2
  have hadm : A.Admissible n (A.f N₁ ⁻¹' (A.f n ⁻¹' D) ∪ C) :=
    Admissible.union_preimage A hD hC N₁ hCT
  have hnD : A.f n ⁻¹' (A.f N₀ ⁻¹' Y) = A.f (N₀ + n) ⁻¹' Y := A.preimage_preimage _ _ _
  have hN₁ : A.f N₁ ⁻¹' (A.f (N₀ + n) ⁻¹' Y) = A.f (N₀ + n + N₁) ⁻¹' Y :=
    A.preimage_preimage _ _ _
  have hsub : A.f N₁ ⁻¹' (A.f n ⁻¹' D) ∪ C ⊆ A.f (N₀ + n + N₁) ⁻¹' Y := by
    rw [← hN₁]
    refine Set.union_subset (Set.preimage_mono ?_) (fun x hx ↦ (hCsub hx).1)
    rw [← hnD]
    exact Set.preimage_mono hDY
  -- the measure of the enlarged base exceeds `ρ`
  have hdisj : Disjoint (A.f N₁ ⁻¹' (A.f n ⁻¹' D)) C := by
    rw [Set.disjoint_right]
    intro x hx hx'
    exact hCT x hx (A.preimage_subset_tower (self_mem_box_two_mul hn) D hx')
  have hmeas : μ (A.f N₁ ⁻¹' (A.f n ⁻¹' D) ∪ C) = μ D + μ C := by
    rw [measure_union hdisj hC.1, A.measure_preimage _ (A.measurable n hD.1),
      A.measure_preimage _ hD.1]
  have hBρ : (μ (A.f N₁ ⁻¹' (A.f n ⁻¹' D) ∪ C)).toReal ≤ ρ :=
    le_csSup hSbdd ⟨N₀ + n + N₁, _, hadm, hsub, rfl⟩
  rw [hmeas, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hBρ
  nlinarith [hr, hCδ, hBρ]

/-- **AC Lemma 2.4.**  Inside some preimage of `Y` there is an `n`-admissible set whose tower
has measure `> 2^{-d} μ Y − ε`. -/
theorem exists_admissible_tower_ge [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) (n : Fin d → ℕ)
    (hn : ∀ i, 0 < n i) {Y : Set X} (hY : MeasurableSet Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : Fin d → ℕ) (B : Set X), A.Admissible n B ∧ B ⊆ A.f N ⁻¹' Y ∧
      (μ Y).toReal / 2 ^ d - ε ≤ (μ (A.tower n B)).toReal := by
  have hcard : 0 < (box n).card := by
    rw [card_box]
    exact Finset.prod_pos fun i _ ↦ hn i
  have hcardR : (0 : ℝ) < (box n).card := by exact_mod_cast hcard
  have hSne : (A.baseMeasures n Y).Nonempty := A.baseMeasures_nonempty n Y
  have hkey := A.measure_le_sSup_baseMeasures hfree hn hY
  obtain ⟨-, ⟨N, B, hB, hBY, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hSne
    (show sSup (A.baseMeasures n Y) - ε / (box n).card < sSup (A.baseMeasures n Y) from
      sub_lt_self _ (by positivity))
  refine ⟨N, B, hB, hBY, ?_⟩
  rw [A.measure_tower hB, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hdiv : (μ Y).toReal / 2 ^ d ≤ (box n).card * sSup (A.baseMeasures n Y) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ d)]
    have h : 2 ^ d * ((box n).card : ℝ) * sSup (A.baseMeasures n Y)
        = (box n).card * sSup (A.baseMeasures n Y) * 2 ^ d := by ring
    linarith [hkey]
  have hmul : (box n).card * (sSup (A.baseMeasures n Y) - ε / (box n).card) ≤
      (box n).card * (μ B).toReal := mul_le_mul_of_nonneg_left hr.le hcardR.le
  have hexp : ((box n).card : ℝ) * (sSup (A.baseMeasures n Y) - ε / (box n).card) =
      (box n).card * sSup (A.baseMeasures n Y) - ε := by
    field_simp
  linarith

end NatAction

end RokhlinTower
