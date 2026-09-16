import Mathlib
import Jsp827.Tower.Basic
import Jsp827.Tower.Separation

/-!
# Iterating the separation step (Avila–Candela Lemma 2.3)

Applying Proposition 2.1 (`RokhlinTower.exists_separated_subset`) once for every ordered pair
of distinct box elements produces, inside some preimage of `Y`, an `n`-admissible set of
measure at least `c · μ Y` with `c = 5 ^ (-(number of pairs))`.

The induction is carried out over an arbitrary finite set `L` of ordered pairs of
multi-indices in `exists_subset_pairwise_disjoint`; Lemma 2.3 is the special case where `L`
is the set of pairs of distinct elements of the box.
-/

open MeasureTheory Set
open scoped ENNReal

namespace RokhlinTower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

namespace NatAction

variable {d : ℕ} (A : NatAction μ d)

/-- Iterating Proposition 2.1 over a finite set `L` of ordered pairs of multi-indices: inside
some preimage of `Y` there is a measurable set `B` of measure at least `5 ^ (-L.card) · μ Y`
whose preimages under the two entries of every pair of distinct multi-indices in `L` are
disjoint. -/
lemma exists_subset_pairwise_disjoint [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free)
    (L : Finset ((Fin d → ℕ) × (Fin d → ℕ))) {Y : Set X} (hY : MeasurableSet Y) :
    ∃ (N : Fin d → ℕ) (B : Set X), MeasurableSet B ∧ B ⊆ A.f N ⁻¹' Y ∧
      (∀ q ∈ L, q.1 ≠ q.2 → Disjoint (A.f q.1 ⁻¹' B) (A.f q.2 ⁻¹' B)) ∧
      (1 / 5 : ℝ) ^ L.card * (μ Y).toReal ≤ (μ B).toReal := by
  classical
  induction L using Finset.induction_on with
  | empty =>
    refine ⟨0, Y, hY, ?_, by simp, by simp⟩
    simp [A.f_zero]
  | insert a L ha ih =>
    obtain ⟨N₀, B₀, hB₀meas, hB₀sub, hB₀disj, hB₀le⟩ := ih
    obtain ⟨k, l⟩ := a
    have hcard : (insert (k, l) L).card = L.card + 1 := Finset.card_insert_of_notMem ha
    have hYpos : (0 : ℝ) ≤ (μ Y).toReal := ENNReal.toReal_nonneg
    by_cases hkl : k = l
    · refine ⟨N₀, B₀, hB₀meas, hB₀sub, ?_, ?_⟩
      · intro q hq hq2
        rcases Finset.mem_insert.1 hq with h | h
        · subst h
          exact absurd hkl hq2
        · exact hB₀disj q h hq2
      · have h2 : (1 / 5 : ℝ) ^ (L.card + 1) ≤ (1 / 5 : ℝ) ^ L.card := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 5) L.card]
        rw [hcard]
        nlinarith [mul_le_mul_of_nonneg_right h2 hYpos]
    · by_cases hpos : 0 < (μ B₀).toReal
      · obtain ⟨B₁, hB₁meas, hB₁sub, hB₁ge, hB₁disj⟩ :=
          exists_separated_subset (μ := μ) (A.measurePreserving k) (A.measurePreserving l)
            (fun x ↦ A.f_comm k l x) (hfree k l hkl) hB₀meas
            (show (0 : ℝ) < (μ B₀).toReal / 5 by linarith)
        have hstep : ∀ m : Fin d → ℕ, A.f m ⁻¹' B₁ ⊆ A.f (m + k) ⁻¹' B₀ := by
          intro m
          have h := preimage_mono (f := A.f m) hB₁sub
          rwa [A.preimage_preimage, add_comm] at h
        refine ⟨N₀ + k, B₁, hB₁meas, ?_, ?_, ?_⟩
        · have h : A.f k ⁻¹' B₀ ⊆ A.f k ⁻¹' (A.f N₀ ⁻¹' Y) := preimage_mono hB₀sub
          rw [A.preimage_preimage] at h
          exact hB₁sub.trans h
        · intro q hq hq2
          rcases Finset.mem_insert.1 hq with h | h
          · subst h
            exact hB₁disj
          · have hd2 : Disjoint (A.f (q.1 + k) ⁻¹' B₀) (A.f (q.2 + k) ⁻¹' B₀) := by
              have h3 := (hB₀disj q h hq2).preimage (A.f k)
              rwa [A.preimage_preimage, A.preimage_preimage] at h3
            exact Disjoint.mono (hstep q.1) (hstep q.2) hd2
        · have hb : (μ B₀).toReal / 5 ≤ (μ B₁).toReal := by linarith
          have hsplit : (1 / 5 : ℝ) ^ (L.card + 1) * (μ Y).toReal
              = ((1 / 5 : ℝ) ^ L.card * (μ Y).toReal) / 5 := by
            rw [pow_succ]
            ring
          rw [hcard, hsplit]
          linarith
      · have hY0 : (μ Y).toReal = 0 := by
          have h2 : (μ B₀).toReal ≤ 0 := not_lt.1 hpos
          have h3 : (0 : ℝ) < (1 / 5 : ℝ) ^ L.card := pow_pos (by norm_num) _
          have h5 : (μ Y).toReal ≤ 0 := by
            by_contra h6
            have h7 : 0 < (1 / 5 : ℝ) ^ L.card * (μ Y).toReal := mul_pos h3 (not_le.1 h6)
            linarith
          linarith
        refine ⟨0, ∅, MeasurableSet.empty, empty_subset _, fun q _ _ ↦ by simp, ?_⟩
        rw [hcard, hY0]
        simp

/-- **AC Lemma 2.3.**  There is a constant `c > 0` (depending only on `n` and `d`) such that
inside some preimage of any measurable `Y` there is an `n`-admissible set of measure at least
`c · μ Y`. -/
theorem exists_admissible_subset [IsProbabilityMeasure μ]
    [HasCountableSeparatingOn X MeasurableSet univ] (hfree : A.Free) (n : Fin d → ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ Y : Set X, MeasurableSet Y →
      ∃ (N : Fin d → ℕ) (B : Set X), A.Admissible n B ∧ B ⊆ A.f N ⁻¹' Y ∧
        c * (μ Y).toReal ≤ (μ B).toReal := by
  classical
  set pairs : Finset ((Fin d → ℕ) × (Fin d → ℕ)) :=
    (box n ×ˢ box n).filter fun q ↦ q.1 ≠ q.2 with hpairs
  refine ⟨(1 / 5 : ℝ) ^ pairs.card, pow_pos (by norm_num) _, fun Y hY ↦ ?_⟩
  obtain ⟨N, B, hBmeas, hBsub, hBdisj, hBle⟩ := A.exists_subset_pairwise_disjoint hfree pairs hY
  refine ⟨N, B, ⟨hBmeas, fun k hk l hl hkl ↦ ?_⟩, hBsub, hBle⟩
  refine hBdisj (k, l) ?_ hkl
  simp only [hpairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hk, hl⟩, hkl⟩

end NatAction

end RokhlinTower
