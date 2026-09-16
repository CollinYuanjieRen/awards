import MerLeanExperiment.IntervalRegionDefinitions
import MerLeanExperiment.IntTelescoping
import Mathlib.Tactic

namespace Erdos441

open scoped BigOperators

/-- A positive-natural prefix has no extra endpoint error: its size is at
most the real upper endpoint itself. -/
theorem positive_prefix_card_le (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n)
    (H : ℝ) (hH : 0 ≤ H) :
    ((A.filter fun n : ℕ => (n : ℝ) ≤ H).card : ℝ) ≤ H := by
  let S := A.filter fun n : ℕ => (n : ℝ) ≤ H
  have hsub : S ⊆ Finset.Icc 1 ⌊H⌋₊ := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨hA n hn'.1, Nat.le_floor hn'.2⟩
  have hc : S.card ≤ (Finset.Icc 1 ⌊H⌋₊).card := Finset.card_le_card hsub
  have hfloor : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH
  have hIcc : (Finset.Icc 1 ⌊H⌋₊).card ≤ ⌊H⌋₊ := by
    rw [Nat.card_Icc]
    omega
  have hcard : (S.card : ℝ) ≤ (⌊H⌋₊ : ℝ) := by
    exact_mod_cast hc.trans hIcc
  exact hcard.trans hfloor

/-- Counts of the actual contiguous geometric regions telescope exactly. -/
theorem grid_middle_card_sum (A : Finset ℕ) (q : ℝ) (hq : 1 < q)
    (T : ℤ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 ≤ R) :
    (∑ i ∈ Finset.Icc (-T) T,
      ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ)) =
        (intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card := by
  let F : ℤ → Finset ℕ := fun i ↦ A.filter fun n : ℕ =>
    (n : ℝ) ≤ q ^ (i + 1) * R
  have hqpos : 0 < q := by linarith
  have hmono (i : ℤ) : F (i - 1) ⊆ F i := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨hn'.1, hn'.2.trans ?_⟩
    have hp : q ^ i ≤ q ^ (i + 1) := zpow_le_zpow_right₀ hq.le (by omega)
    rw [show i - 1 + 1 = i by omega]
    exact mul_le_mul_of_nonneg_right hp hR
  have hdiff (i : ℤ) : F i \ F (i - 1) =
      intervalRegion A (q ^ i) (q ^ (i + 1)) R := by
    ext n
    simp only [F, Finset.mem_sdiff, Finset.mem_filter, intervalRegion]
    have he : i - 1 + 1 = i := by omega
    rw [he]
    constructor
    · rintro ⟨⟨hnA, hnhi⟩, hnnot⟩
      exact ⟨hnA, lt_of_not_ge (fun hnle ↦ hnnot ⟨hnA, hnle⟩), hnhi⟩
    · rintro ⟨hnA, hnlo, hnhi⟩
      exact ⟨⟨hnA, hnhi⟩, fun hnprev ↦ (not_le_of_gt hnlo) hnprev.2⟩
  have htel := sum_Icc_backward_sub
    (fun i : ℤ ↦ ((F i).card : ℝ)) (-T) T (by omega)
  have hterms :
      (∑ i ∈ Finset.Icc (-T) T, ((F i \ F (i - 1)).card : ℝ)) =
        ∑ i ∈ Finset.Icc (-T) T,
          (((F i).card : ℝ) - ((F (i - 1)).card : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hc := Finset.card_sdiff_add_card_eq_card (hmono i)
    have hcR : (((F i \ F (i - 1)).card : ℝ) + ((F (i - 1)).card : ℝ)) =
        ((F i).card : ℝ) := by exact_mod_cast hc
    linarith
  have houterMono : F (-T - 1) ⊆ F T := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨hn'.1, hn'.2.trans ?_⟩
    have hp : q ^ (-T) ≤ q ^ (T + 1) :=
      zpow_le_zpow_right₀ hq.le (by omega)
    rw [show -T - 1 + 1 = -T by omega]
    exact mul_le_mul_of_nonneg_right hp hR
  have houter : F T \ F (-T - 1) =
      intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R := by
    ext n
    simp only [F, Finset.mem_sdiff, Finset.mem_filter, intervalRegion]
    rw [show -T - 1 + 1 = -T by omega]
    constructor
    · rintro ⟨⟨hnA, hnhi⟩, hnnot⟩
      exact ⟨hnA, lt_of_not_ge (fun hnle ↦ hnnot ⟨hnA, hnle⟩), hnhi⟩
    · rintro ⟨hnA, hnlo, hnhi⟩
      exact ⟨⟨hnA, hnhi⟩, fun hnprev ↦ (not_le_of_gt hnlo) hnprev.2⟩
  have houterCard :
      (((F T).card : ℝ) - ((F (-T - 1)).card : ℝ)) =
        ((F T \ F (-T - 1)).card : ℝ) := by
    have hc := Finset.card_sdiff_add_card_eq_card houterMono
    have hcR : (((F T \ F (-T - 1)).card : ℝ) + ((F (-T - 1)).card : ℝ)) =
        ((F T).card : ℝ) := by exact_mod_cast hc
    linarith
  calc
    (∑ i ∈ Finset.Icc (-T) T,
        ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ)) =
      ∑ i ∈ Finset.Icc (-T) T, ((F i \ F (i - 1)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hdiff]
    _ = ∑ i ∈ Finset.Icc (-T) T,
        (((F i).card : ℝ) - ((F (i - 1)).card : ℝ)) := hterms
    _ = ((F T).card : ℝ) - ((F (-T - 1)).card : ℝ) := by
      simpa using htel
    _ = ((F T \ F (-T - 1)).card : ℝ) := houterCard
    _ = ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) := by
      rw [houter]

/-- The small prefix, middle interval, and strict tail form an exact
partition of the original finite set. -/
theorem three_region_card_partition (A : Finset ℕ) (H J : ℝ) (hHJ : H ≤ J) :
    A.card = (A.filter fun n : ℕ => (n : ℝ) ≤ H).card +
      (A.filter fun n : ℕ => H < (n : ℝ) ∧ (n : ℝ) ≤ J).card +
      (A.filter fun n : ℕ => J < (n : ℝ)).card := by
  let S := A.filter fun n : ℕ => (n : ℝ) ≤ H
  let M := A.filter fun n : ℕ => H < (n : ℝ) ∧ (n : ℝ) ≤ J
  let U := A.filter fun n : ℕ => J < (n : ℝ)
  have hunion : A = (S ∪ M) ∪ U := by
    ext n
    simp only [S, M, U, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hnA
      by_cases hnH : (n : ℝ) ≤ H
      · exact Or.inl (Or.inl ⟨hnA, hnH⟩)
      · by_cases hnJ : (n : ℝ) ≤ J
        · exact Or.inl (Or.inr ⟨hnA, lt_of_not_ge hnH, hnJ⟩)
        · exact Or.inr ⟨hnA, lt_of_not_ge hnJ⟩
    · rintro (hnSM | hnU)
      · rcases hnSM with hnS | hnM
        · exact hnS.1
        · exact hnM.1
      · exact hnU.1
  have hSM : Disjoint S M := by
    rw [Finset.disjoint_left]
    intro n hnS hnM
    simp only [S, M, Finset.mem_filter] at hnS hnM
    linarith
  have hSU : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro n hnS hnU
    simp only [S, U, Finset.mem_filter] at hnS hnU
    linarith [hHJ]
  have hMU : Disjoint M U := by
    rw [Finset.disjoint_left]
    intro n hnM hnU
    simp only [M, U, Finset.mem_filter] at hnM hnU
    linarith
  have hSMU : Disjoint (S ∪ M) U := Finset.disjoint_union_left.mpr ⟨hSU, hMU⟩
  change A.card = S.card + M.card + U.card
  rw [hunion, Finset.card_union_of_disjoint hSMU,
    Finset.card_union_of_disjoint hSM]

end Erdos441
