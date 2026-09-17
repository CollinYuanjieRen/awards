import Erdos210Ordinary.Witness
import Erdos210Ordinary.Config

/-!
# Erdős Problem 210 — the trivial upper bound `f n ≤ n`

The near-pencil `witness n` of `Witness.lean` — the `n - 1` points `(i, 0)`, `i < n - 1`, together
with the apex `(0, 1)` — determines at most `n` ordinary lines.

* For `n = 3` there are at most `C(3, 2) = 3` ordinary pairs at all.
* For `n ≥ 4` the `n - 1 ≥ 3` axis points are collinear, so a pair of two axis points is never
  ordinary: a third axis point lies on the line it spans.  Hence every ordinary pair contains the
  apex, and `e ↦ e.erase (0, 1)` injects `ordinaryPairs` into the singletons of the `n - 1`
  remaining points.

Combining with `le_f_linear` this gives `f n = Θ(n)`.
-/

namespace Erdos210

/-- Membership in the near-pencil `witness n`. -/
private lemma mem_witness_iff {n : ℕ} {x : ℝ × ℝ} :
    x ∈ witness n ↔ (∃ i : ℕ, i < n - 1 ∧ x = ((i : ℝ), (0 : ℝ))) ∨ x = ((0 : ℝ), (1 : ℝ)) := by
  rw [witness, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
      exact Or.inl ⟨i, Finset.mem_range.1 hi, rfl⟩
    · exact Or.inr h
  · rintro (⟨i, hi, rfl⟩ | h)
    · exact Or.inl (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩)
    · exact Or.inr h

/-- The apex belongs to the near-pencil. -/
private lemma apex_mem_witness (n : ℕ) : ((0 : ℝ), (1 : ℝ)) ∈ witness n :=
  mem_witness_iff.2 (Or.inr rfl)

/-- Three axis points are collinear. -/
private lemma onLine_axis (i j k : ℕ) :
    OnLine ((i : ℝ), (0 : ℝ)) ((j : ℝ), (0 : ℝ)) ((k : ℝ), (0 : ℝ)) := by
  simp [OnLine, D]

/-- For `n ≥ 4`, every ordinary pair of the near-pencil contains the apex. -/
private lemma apex_mem_of_mem_ordinaryPairs {n : ℕ} (hn : 4 ≤ n) {e : Finset (ℝ × ℝ)}
    (he : e ∈ ordinaryPairs (witness n)) : ((0 : ℝ), (1 : ℝ)) ∈ e := by
  by_contra hape
  obtain ⟨a, b, hab, haP, hbP, rfl⟩ := exists_pair_of_mem_ordinaryPairs he
  have ha' : a ≠ ((0 : ℝ), (1 : ℝ)) := by
    rintro rfl
    exact hape (Finset.mem_insert_self _ _)
  have hb' : b ≠ ((0 : ℝ), (1 : ℝ)) := by
    rintro rfl
    exact hape (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rcases mem_witness_iff.1 haP with ⟨i, hi, rfl⟩ | h
  · rcases mem_witness_iff.1 hbP with ⟨j, hj, rfl⟩ | h
    · have hij : i ≠ j := by
        rintro rfl
        exact hab rfl
      -- a third axis point, distinct from both
      obtain ⟨k, hk3, hki, hkj⟩ : ∃ k : ℕ, k < 3 ∧ k ≠ i ∧ k ≠ j := by
        refine ⟨if i ≠ 0 ∧ j ≠ 0 then 0 else if i ≠ 1 ∧ j ≠ 1 then 1 else 2, ?_⟩
        split_ifs with h1 h2 <;> omega
      have hkP : ((k : ℝ), (0 : ℝ)) ∈ witness n :=
        mem_witness_iff.2 (Or.inl ⟨k, by omega, rfl⟩)
      have hmem := (mem_ordinaryPairs.1 he).2.2 ((i : ℝ), (0 : ℝ)) (Finset.mem_insert_self _ _)
        ((j : ℝ), (0 : ℝ)) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hab
        ((k : ℝ), (0 : ℝ)) hkP (onLine_axis i j k)
      rcases Finset.mem_insert.1 hmem with h | h
      · exact hki (Nat.cast_injective (congrArg Prod.fst h))
      · exact hkj (Nat.cast_injective (congrArg Prod.fst (Finset.mem_singleton.1 h)))
    · exact hb' h
  · exact ha' h

/-- The near-pencil has at most `n` ordinary pairs. -/
private lemma card_ordinaryPairs_witness_le {n : ℕ} (hn : 3 ≤ n) :
    (ordinaryPairs (witness n)).card ≤ n := by
  classical
  rcases eq_or_lt_of_le hn with h3 | h4
  · -- `n = 3`: there are at most `C(3, 2) = 3` two-element subsets at all
    subst h3
    have hsub : ordinaryPairs (witness 3) ⊆ (witness 3).powersetCard 2 := by
      intro e he
      obtain ⟨h1, h2, -⟩ := mem_ordinaryPairs.1 he
      exact Finset.mem_powersetCard.2 ⟨h1, h2⟩
    calc (ordinaryPairs (witness 3)).card ≤ ((witness 3).powersetCard 2).card :=
          Finset.card_le_card hsub
      _ = (witness 3).card.choose 2 := Finset.card_powersetCard _ _
      _ = 3 := by rw [card_witness (le_refl 3)]; rfl
  · -- `n ≥ 4`: every ordinary pair is `{apex, axis point}`
    have hn4 : 4 ≤ n := h4
    have hmaps : ∀ e ∈ ordinaryPairs (witness n), e.erase ((0 : ℝ), (1 : ℝ)) ∈
        ((witness n).erase ((0 : ℝ), (1 : ℝ))).powersetCard 1 := by
      intro e he
      obtain ⟨hsub, hcard, -⟩ := mem_ordinaryPairs.1 he
      refine Finset.mem_powersetCard.2 ⟨Finset.erase_subset_erase _ hsub, ?_⟩
      rw [Finset.card_erase_of_mem (apex_mem_of_mem_ordinaryPairs hn4 he), hcard]
    have hinj : Set.InjOn (fun e : Finset (ℝ × ℝ) => e.erase ((0 : ℝ), (1 : ℝ)))
        ↑(ordinaryPairs (witness n)) := by
      intro e₁ h₁ e₂ h₂ h
      have k₁ := apex_mem_of_mem_ordinaryPairs hn4 (Finset.mem_coe.1 h₁)
      have k₂ := apex_mem_of_mem_ordinaryPairs hn4 (Finset.mem_coe.1 h₂)
      have h' : e₁.erase ((0 : ℝ), (1 : ℝ)) = e₂.erase ((0 : ℝ), (1 : ℝ)) := h
      rw [← Finset.insert_erase k₁, ← Finset.insert_erase k₂, h']
    calc (ordinaryPairs (witness n)).card
        ≤ (((witness n).erase ((0 : ℝ), (1 : ℝ))).powersetCard 1).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = ((witness n).erase ((0 : ℝ), (1 : ℝ))).card.choose 1 := Finset.card_powersetCard _ _
      _ = n - 1 := by
          rw [Finset.card_erase_of_mem (apex_mem_witness n), card_witness hn, Nat.choose_one_right]
      _ ≤ n := Nat.sub_le n 1

/-- The near-pencil has at most `n` ordinary lines. -/
theorem exists_config_le (n : ℕ) (hn : 3 ≤ n) :
    ∃ P : Finset (ℝ × ℝ), P.card = n ∧ ¬ Collinear ℝ (P : Set (ℝ × ℝ)) ∧
      (ordinaryLines P).ncard ≤ n :=
  ⟨witness n, card_witness hn, (notCollinear_iff _).1 (notCollinear_witness hn), by
    rw [ncard_ordinaryLines]
    exact card_ordinaryPairs_witness_le hn⟩

/-- The trivial upper bound: `f n ≤ n` for every `n ≥ 3`. -/
theorem f_le (n : ℕ) (hn : 3 ≤ n) : f n ≤ n := by
  obtain ⟨P, hcard, hcol, hle⟩ := exists_config_le n hn
  exact le_trans (Nat.sInf_le ⟨P, hcard, hcol, rfl⟩) hle

end Erdos210
