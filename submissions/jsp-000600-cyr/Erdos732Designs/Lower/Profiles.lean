import Erdos732Designs.Lower.Completion
import Erdos732Designs.Lower.AffinePlane

/-!
# Many block-compatible multisets from line profiles

Fix a prime `p` with `p * p ≤ n` and an embedding `ι` of the affine plane `ZMod p × ZMod p`
into `Fin n`.  A *profile* is a function `m : Fin (p - 2) → Fin (p + 1)`.  It prescribes, for
each non-vertical line `L(a, b)`, a size `sz m (a, b) ∈ [2, p]`: it is `a.val + 3` when
`a.val < p - 2` and `b.val < m ⟨a.val, _⟩`, and `2` otherwise.  Choosing inside each embedded
line a subset `X m (a, b)` of that size yields a partial design `F m`, because two distinct
embedded lines meet in at most one point.  Completing `F m` gives a pairwise balanced design on
`Fin n` whose block-size multiset `profileSizes m` has, for `i : Fin (p - 2)`, exactly
`m i` blocks of size `i + 3` — the number of `b` with `b.val < m i`.  Hence the map
`m ↦ profileSizes m` is injective, and there are at least `(p + 1) ^ (p - 2)` block-compatible
multisets for `n`.
-/

namespace Erdos732Lower

open Finset

section Construction

variable (p : ℕ) [Fact p.Prime]

/-- The size prescribed by the profile `m` for the block on the line `y = a x + b`. -/
def sz (m : Fin (p - 2) → Fin (p + 1)) (ab : ZMod p × ZMod p) : ℕ :=
  if h : ab.1.val < p - 2 then
    (if ab.2.val < (m ⟨ab.1.val, h⟩).val then ab.1.val + 3 else 2)
  else 2

omit [Fact p.Prime] in
theorem two_le_sz (m : Fin (p - 2) → Fin (p + 1)) (ab : ZMod p × ZMod p) : 2 ≤ sz p m ab := by
  simp only [sz]
  split_ifs <;> omega

theorem sz_le (m : Fin (p - 2) → Fin (p + 1)) (ab : ZMod p × ZMod p) : sz p m ab ≤ p := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  simp only [sz]
  split_ifs <;> omega

/-- The number of `b : ZMod p` with `b.val < k`, for `k ≤ p`, is `k`. -/
theorem card_filter_val_lt (k : ℕ) (hk : k ≤ p) :
    ((Finset.univ : Finset (ZMod p)).filter fun b => b.val < k).card = k := by
  have himg : ((Finset.univ : Finset (ZMod p)).filter fun b => b.val < k).image ZMod.val
      = Finset.range k := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro hj
      refine ⟨(j : ZMod p), ?_, ZMod.val_natCast_of_lt (by omega)⟩
      rw [ZMod.val_natCast_of_lt (by omega)]
      exact hj
  have h := congrArg Finset.card himg
  rwa [Finset.card_image_of_injective _ (ZMod.val_injective p), Finset.card_range] at h

/-- The lines whose prescribed size is `i + 3` are those with first coordinate `i` and second
coordinate below `m i`; there are `m i` of them. -/
theorem card_filter_sz (m : Fin (p - 2) → Fin (p + 1)) (i : Fin (p - 2)) :
    ((Finset.univ : Finset (ZMod p × ZMod p)).filter fun ab => sz p m ab = i.val + 3).card
      = (m i).val := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hi : i.val < p := lt_of_lt_of_le i.isLt (by omega)
  have hival : ((i.val : ZMod p)).val = i.val := ZMod.val_natCast_of_lt hi
  have hset : ((Finset.univ : Finset (ZMod p × ZMod p)).filter fun ab => sz p m ab = i.val + 3)
      = ({(i.val : ZMod p)} : Finset (ZMod p)) ×ˢ
        ((Finset.univ : Finset (ZMod p)).filter fun b => b.val < (m i).val) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · intro h
      simp only [sz] at h
      split_ifs at h with h1 h2
      · have ha : a.val = i.val := by omega
        have haeq : a = (i.val : ZMod p) := by
          refine ZMod.val_injective p ?_
          rw [hival, ha]
        have hidx : (⟨a.val, h1⟩ : Fin (p - 2)) = i := Fin.ext ha
        rw [hidx] at h2
        exact ⟨haeq, h2⟩
      · omega
      · omega
    · rintro ⟨rfl, hb⟩
      simp only [sz]
      split_ifs with h1 h2
      · rw [hival]
      · refine absurd ?_ h2
        have hidx : (⟨((i.val : ZMod p)).val, h1⟩ : Fin (p - 2)) = i := Fin.ext hival
        rw [hidx]
        exact hb
      · exact absurd (show ((i.val : ZMod p)).val < p - 2 by rw [hival]; exact i.isLt) h1
  rw [hset, Finset.card_product, Finset.card_singleton, one_mul]
  exact card_filter_val_lt p (m i).val (by omega)

variable (n : ℕ) (ι : ZMod p × ZMod p ↪ Fin n)

theorem sz_le_card_map (m : Fin (p - 2) → Fin (p + 1)) (ab : ZMod p × ZMod p) :
    sz p m ab ≤ ((line p ab.1 ab.2).map ι).card := by
  rw [Finset.card_map, card_line]
  exact sz_le p m ab

/-- A subset of the embedded line `ι (L(a, b))` of the prescribed size. -/
noncomputable def X (m : Fin (p - 2) → Fin (p + 1)) (ab : ZMod p × ZMod p) : Finset (Fin n) :=
  (Finset.exists_subset_card_eq (sz_le_card_map p n ι m ab)).choose

theorem X_subset (m : Fin (p - 2) → Fin (p + 1)) (ab : ZMod p × ZMod p) :
    X p n ι m ab ⊆ (line p ab.1 ab.2).map ι :=
  (Finset.exists_subset_card_eq (sz_le_card_map p n ι m ab)).choose_spec.1

theorem card_X (m : Fin (p - 2) → Fin (p + 1)) (ab : ZMod p × ZMod p) :
    (X p n ι m ab).card = sz p m ab :=
  (Finset.exists_subset_card_eq (sz_le_card_map p n ι m ab)).choose_spec.2

theorem card_inter_X_le (m : Fin (p - 2) → Fin (p + 1)) {ab ab' : ZMod p × ZMod p}
    (h : ab ≠ ab') : (X p n ι m ab ∩ X p n ι m ab').card ≤ 1 := by
  obtain ⟨a, b⟩ := ab
  obtain ⟨a', b'⟩ := ab'
  have hsub : X p n ι m (a, b) ∩ X p n ι m (a', b')
      ⊆ (line p a b ∩ line p a' b').map ι := by
    rw [Finset.map_inter]
    exact Finset.inter_subset_inter (X_subset p n ι m (a, b)) (X_subset p n ι m (a', b'))
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Finset.card_map]
  exact line_inter_card_le_one p h

/-- A block has at least two points, hence determines the line it was cut from. -/
theorem X_injective (m : Fin (p - 2) → Fin (p + 1)) : Function.Injective (X p n ι m) := by
  intro ab ab' hEq
  by_contra hne
  have h1 : (X p n ι m ab ∩ X p n ι m ab').card ≤ 1 := card_inter_X_le p n ι m hne
  rw [hEq, Finset.inter_self, card_X] at h1
  have h2 := two_le_sz p m ab'
  omega

/-- The family of blocks attached to the profile `m`. -/
noncomputable def F (m : Fin (p - 2) → Fin (p + 1)) : Finset (Finset (Fin n)) :=
  Finset.univ.map ⟨X p n ι m, X_injective p n ι m⟩

theorem isPartialDesign_F (m : Fin (p - 2) → Fin (p + 1)) : IsPartialDesign (F p n ι m) := by
  constructor
  · intro B hB
    obtain ⟨ab, -, rfl⟩ := Finset.mem_map.1 hB
    simp only [Function.Embedding.coeFn_mk]
    rw [card_X]
    exact two_le_sz p m ab
  · intro B hB B' hB' hne
    obtain ⟨ab, -, rfl⟩ := Finset.mem_map.1 hB
    obtain ⟨ab', -, rfl⟩ := Finset.mem_map.1 hB'
    simp only [Function.Embedding.coeFn_mk] at hne ⊢
    exact card_inter_X_le p n ι m fun hh => hne (by rw [hh])

/-- The block-size multiset of the completed design attached to the profile `m`. -/
noncomputable def profileSizes (m : Fin (p - 2) → Fin (p + 1)) : Multiset ℕ :=
  (completionDesign (F p n ι m) (isPartialDesign_F p n ι m)).blockSizes

theorem blockCompatible_profileSizes (m : Fin (p - 2) → Fin (p + 1)) :
    Erdos732Upper.BlockCompatible n (profileSizes p n ι m) :=
  ⟨completionDesign (F p n ι m) (isPartialDesign_F p n ι m), rfl⟩

theorem count_profileSizes (m : Fin (p - 2) → Fin (p + 1)) (s : ℕ) (hs : s ≠ 2) :
    Multiset.count s (profileSizes p n ι m)
      = ((Finset.univ : Finset (ZMod p × ZMod p)).filter fun ab => sz p m ab = s).card := by
  have hmap : (F p n ι m).val.map Finset.card
      = (Finset.univ : Finset (ZMod p × ZMod p)).val.map (sz p m) := by
    simp only [F, Finset.map_val, Multiset.map_map]
    refine Multiset.map_congr rfl ?_
    intro ab _
    simpa using card_X p n ι m ab
  rw [profileSizes, count_completionDesign_blockSizes _ _ s hs, hmap, Multiset.count_map,
    Finset.card_def, Finset.filter_val]
  refine congrArg Multiset.card ?_
  exact Multiset.filter_congr fun ab _ => eq_comm

theorem count_profileSizes_add_three (m : Fin (p - 2) → Fin (p + 1)) (i : Fin (p - 2)) :
    Multiset.count (i.val + 3) (profileSizes p n ι m) = (m i).val := by
  rw [count_profileSizes p n ι m (i.val + 3) (by omega), card_filter_sz]

theorem profileSizes_injective : Function.Injective (profileSizes p n ι) := by
  intro m m' hmm
  funext i
  have h := count_profileSizes_add_three p n ι m i
  rw [hmm, count_profileSizes_add_three] at h
  exact Fin.ext h.symm

end Construction

/-- For a prime `p` with `p * p ≤ n` there are at least `(p + 1) ^ (p - 2)` block-compatible
multisets for `n`, indexed injectively by the profiles `Fin (p - 2) → Fin (p + 1)`. -/
theorem exists_many_blockCompatible (p n : ℕ) [Fact p.Prime] (hn : p * p ≤ n) :
    ∃ f : (Fin (p - 2) → Fin (p + 1)) → Multiset ℕ,
      Function.Injective f ∧ ∀ m, Erdos732Upper.BlockCompatible n (f m) := by
  have hcard : Fintype.card (ZMod p × ZMod p) ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
    exact hn
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨profileSizes p n ι, profileSizes_injective p n ι, blockCompatible_profileSizes p n ι⟩

end Erdos732Lower
