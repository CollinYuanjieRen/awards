import Erdos806SmallBases.Definitions

/-! Covering a finite set by few chunks of bounded size. -/

namespace Erdos806

/-- The rank of `a` in `S`: the number of elements of `S` that are `< a`. -/
private def rank (S : Finset ℕ) (a : ℕ) : ℕ := (S.filter (fun x => x < a)).card

/-- `rank S` is strictly monotone along elements of `S`. -/
private theorem rank_lt_rank {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hab : a < b) :
    rank S a < rank S b := by
  have hsub : S.filter (fun x => x < a) ⊆ S.filter (fun x => x < b) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 hab⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨a, ?_, ?_⟩)
  · exact Finset.mem_filter.mpr ⟨ha, hab⟩
  · simp

/-- Ranks of elements of `S` are `< S.card`. -/
private theorem rank_lt_card {S : Finset ℕ} {a : ℕ} (ha : a ∈ S) : rank S a < S.card :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
    ⟨a, ha, by simp⟩)

theorem exists_chunks (k : ℕ) (hk : 0 < k) (S : Finset ℕ) :
    ∃ (m : ℕ) (T : ℕ → Finset ℕ), m ≤ S.card / k + 1 ∧ (∀ t, (T t).card ≤ k) ∧
      S ⊆ (Finset.range m).biUnion T := by
  refine ⟨S.card / k + 1, fun t => S.filter (fun a => rank S a / k = t), le_rfl, ?_, ?_⟩
  · intro t
    have hmap : ∀ a ∈ S.filter (fun a => rank S a / k = t),
        rank S a ∈ Finset.Ico (t * k) (t * k + k) := by
      intro a ha
      obtain ⟨-, hd⟩ := Finset.mem_filter.mp ha
      have hlt : rank S a / k < t + 1 := by rw [hd]; exact Nat.lt_succ_self t
      have hub : rank S a < (t + 1) * k := (Nat.div_lt_iff_lt_mul hk).mp hlt
      refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
      · calc t * k = rank S a / k * k := by rw [hd]
          _ ≤ rank S a := Nat.div_mul_le_self _ _
      · calc rank S a < (t + 1) * k := hub
          _ = t * k + k := by ring
    have hinj : Set.InjOn (rank S) (S.filter (fun a => rank S a / k = t)) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (Nat.ne_of_lt (rank_lt_rank ha.1 h))
      · exact h
      · exact absurd hab.symm (Nat.ne_of_lt (rank_lt_rank hb.1 h))
    calc (S.filter (fun a => rank S a / k = t)).card
        ≤ (Finset.Ico (t * k) (t * k + k)).card := Finset.card_le_card_of_injOn _ hmap hinj
      _ = k := by simp
  · intro a ha
    refine Finset.mem_biUnion.mpr ⟨rank S a / k, Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.lt_succ_of_le (Nat.div_le_div_right (le_of_lt (rank_lt_card ha)))
    · exact Finset.mem_filter.mpr ⟨ha, rfl⟩

end Erdos806
