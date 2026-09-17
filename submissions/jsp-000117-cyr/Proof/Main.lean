import Proof.Defs

/-!
# The double-counting upper bound for unit circles through three points (Erdős #104, scoped)

For `n` points in the plane, the number `C` of distinct unit circles containing at least three
of the points satisfies `3 * C ≤ n * (n - 1)`.  The argument is the elementary double count of
the incidences `(circle, ordered pair of its points)`: each rich circle carries at least
`3 * 2 = 6` ordered pairs of points, each ordered pair of distinct points lies on at most `2`
unit circles, and there are `n * (n - 1)` ordered pairs, so `6 * C ≤ 2 * n * (n - 1)`.

The Erdős problems page attributes the corrected constant `n(n-1)/3` to Harborth and Mengerson
[HaMe86] (Erdős stated the weaker `n(n-1)` in several places).  This package proves the
multiplied, division-free form `3 * unitCircleCount P ≤ P.card * (P.card - 1)`.

Not claimed here: the `o(n²)` question of Erdős problem #104, Erdős's `≫ n` and Elekes's
`≫ n^{3/2}` constructions, and the general-position questions.
-/

namespace Erdos104

open Finset

/-- Each rich circle carries at least `6` ordered pairs of distinct points of `P`:
if `k ≥ 3` points of `P` lie on the circle centred at `c`, the off-diagonal of that set of
points has `k * k - k ≥ 6` elements. -/
theorem card_pairs_on_center (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (c : EuclideanSpace ℝ (Fin 2)) (h : IsRichCenter P c) :
    6 ≤ ((P.filter (fun p => dist p c = 1)).offDiag).card := by
  classical
  have h3 : 3 ≤ (P.filter (fun p => dist p c = 1)).card := h
  rw [Finset.offDiag_card]
  have hk : 6 + (P.filter (fun p => dist p c = 1)).card
      ≤ (P.filter (fun p => dist p c = 1)).card * (P.filter (fun p => dist p c = 1)).card := by
    nlinarith [h3]
  exact Nat.le_sub_of_add_le hk

/-- Each ordered pair of distinct points lies on at most `2` unit circles with centre in `S`:
the centres at distance `1` from both `p` and `q` are confined to the two centres supplied by
`Erdos104.exists_two_centers`. -/
theorem card_centers_on_pair_le (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (p q : EuclideanSpace ℝ (Fin 2)) (hpq : p ≠ q) :
    (S.filter (fun c => dist p c = 1 ∧ dist q c = 1)).card ≤ 2 := by
  classical
  obtain ⟨c₁, c₂, hc⟩ := exists_two_centers p q hpq
  have hsub : S.filter (fun c => dist p c = 1 ∧ dist q c = 1) ⊆ ({c₁, c₂} : Finset _) := by
    intro c hcmem
    simp only [Finset.mem_filter] at hcmem
    rcases hc c hcmem.2.1 hcmem.2.2 with rfl | rfl <;> simp
  have hpair : ({c₁, c₂} : Finset (EuclideanSpace ℝ (Fin 2))).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  exact le_trans (Finset.card_le_card hsub) hpair

/-- (T5) The double-counting core: any finite set `S` of centres of unit circles, each carrying
at least three points of `P`, satisfies `3 * |S| ≤ |P| * (|P| - 1)`. -/
theorem three_mul_card_le_of_rich (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : ∀ c ∈ S, IsRichCenter P c) :
    3 * S.card ≤ P.card * (P.card - 1) := by
  classical
  -- `f c pq` is the indicator of the incidence "both points of `pq` lie on the circle at `c`".
  let f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℕ :=
    fun c pq => if dist pq.1 c = 1 ∧ dist pq.2 c = 1 then 1 else 0
  -- Count by circles: at least `6` ordered pairs each.
  have hlow : 6 * S.card ≤ ∑ c ∈ S, ∑ pq ∈ P.offDiag, f c pq := by
    have h6 : ∀ c ∈ S, 6 ≤ ∑ pq ∈ P.offDiag, f c pq := by
      intro c hc
      have hfib : ∑ pq ∈ P.offDiag, f c pq
          = (P.offDiag.filter (fun pq => dist pq.1 c = 1 ∧ dist pq.2 c = 1)).card := by
        rw [Finset.card_filter]
      rw [hfib]
      refine le_trans (card_pairs_on_center P c (hS c hc)) (Finset.card_le_card ?_)
      intro pq hpq
      simp only [Finset.mem_offDiag, Finset.mem_filter] at hpq ⊢
      exact ⟨⟨hpq.1.1, hpq.2.1.1, hpq.2.2⟩, hpq.1.2, hpq.2.1.2⟩
    calc 6 * S.card = ∑ _c ∈ S, 6 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum h6
  -- Count by ordered pairs: at most `2` circles each.
  have hupp : ∑ pq ∈ P.offDiag, ∑ c ∈ S, f c pq ≤ 2 * P.offDiag.card := by
    have h2 : ∀ pq ∈ P.offDiag, ∑ c ∈ S, f c pq ≤ 2 := by
      intro pq hpq
      have hfib : ∑ c ∈ S, f c pq
          = (S.filter (fun c => dist pq.1 c = 1 ∧ dist pq.2 c = 1)).card := by
        rw [Finset.card_filter]
      rw [hfib]
      exact card_centers_on_pair_le S pq.1 pq.2 (Finset.mem_offDiag.mp hpq).2.2
    calc ∑ pq ∈ P.offDiag, ∑ c ∈ S, f c pq ≤ ∑ _pq ∈ P.offDiag, 2 := Finset.sum_le_sum h2
      _ = 2 * P.offDiag.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [Finset.sum_comm] at hlow
  have hcard : P.offDiag.card = P.card * (P.card - 1) := by
    rw [Finset.offDiag_card, Nat.mul_sub_one, mul_comm]
  have harith : ∀ a b : ℕ, 6 * a ≤ 2 * b → 3 * a ≤ b := by
    intro a b hab; omega
  exact harith _ _ (le_trans hlow (by rw [← hcard]; exact hupp))

/-- (T3) The set of rich centres is finite: every rich centre carries two distinct points of `P`,
hence is one of the two centres attached by `Erdos104.exists_two_centers` to that pair, and there
are finitely many pairs. -/
theorem richCenters_finite (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    {c : EuclideanSpace ℝ (Fin 2) | IsRichCenter P c}.Finite := by
  classical
  have hF : ∀ pq : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      ∃ t : Finset (EuclideanSpace ℝ (Fin 2)), ∀ c : EuclideanSpace ℝ (Fin 2),
        pq.1 ≠ pq.2 → dist pq.1 c = 1 → dist pq.2 c = 1 → c ∈ t := by
    intro pq
    by_cases hne : pq.1 = pq.2
    · exact ⟨∅, fun c hc _ _ => absurd hne hc⟩
    · obtain ⟨c₁, c₂, hc⟩ := exists_two_centers pq.1 pq.2 hne
      refine ⟨{c₁, c₂}, fun c _ h1 h2 => ?_⟩
      rcases hc c h1 h2 with rfl | rfl <;> simp
  choose F hFmem using hF
  refine Set.Finite.subset (P.offDiag.biUnion F).finite_toSet ?_
  intro c hc
  have hc' : 3 ≤ (P.filter (fun p => dist p c = 1)).card := hc
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num) hc')
  simp only [Finset.mem_filter] at hp hq
  refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨(p, q), ?_, ?_⟩)
  · exact Finset.mem_offDiag.mpr ⟨hp.1, hq.1, hpq⟩
  · exact hFmem (p, q) c hpq hp.2 hq.2

/-- (T2) The bound in direct form: `3 * unitCircleCount P ≤ |P| * (|P| - 1)`. -/
theorem three_mul_unitCircleCount_le (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    3 * unitCircleCount P ≤ P.card * (P.card - 1) := by
  classical
  have hfin := richCenters_finite P
  rw [unitCircleCount, Set.ncard_eq_toFinset_card _ hfin]
  refine three_mul_card_le_of_rich P hfin.toFinset ?_
  intro c hcs
  exact (Set.Finite.mem_toFinset hfin).mp hcs

/-- (T1) The audited root: no `n`-point set has more than `n * (n - 1) / 3` unit circles through
three of its points, stated in the division-free negation form. -/
theorem not_exists_unitCircleCount_gt (n : ℕ) :
    ¬ ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧ n * (n - 1) < 3 * unitCircleCount P := by
  rintro ⟨P, rfl, h⟩
  exact absurd (three_mul_unitCircleCount_le P) (not_le.2 h)

end Erdos104
