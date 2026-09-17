import Erdos926Furedi.Definitions

/-! Embedding `H_k` from a centre, `k` neighbours, and a family of large disjoint-from-`{x, y_i}`
sets of common neighbours (one per pair). -/

namespace Erdos926

open SimpleGraph Finset

/-- Hall's condition for the family `S`: any union of `s` of the sets `S p` has at least `s.card`
elements, because a single `S p` already has at least `card (PairIdx k)` elements. -/
theorem hall_condition_of_card_le {V : Type*} [DecidableEq V] {k : ℕ} (S : PairIdx k → Finset V)
    (hcard : ∀ p, Fintype.card (PairIdx k) ≤ (S p).card) (s : Finset (PairIdx k)) :
    s.card ≤ (s.biUnion S).card := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  · calc s.card ≤ Fintype.card (PairIdx k) := by simpa using Finset.card_le_univ s
      _ ≤ (S p₀).card := hcard p₀
      _ ≤ (s.biUnion S).card := Finset.card_le_card (Finset.subset_biUnion_of_mem S hp₀)

/-- If `x` has `k` distinct neighbours `y i`, and every pair `p` has a set `S p` of at least
`card (PairIdx k)` common neighbours of `y p.1` and `y p.2` avoiding `x` and all `y i`, then `H_k`
is contained in `G`. -/
theorem isContained_of_rich (k : ℕ) {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (y : Fin k → V) (hy : Function.Injective y)
    (hyx : ∀ i, G.Adj x (y i)) (S : PairIdx k → Finset V)
    (hS : ∀ p, ∀ z ∈ S p, G.Adj (y p.1.1) z ∧ G.Adj (y p.1.2) z)
    (hSx : ∀ p, x ∉ S p) (hSy : ∀ p i, y i ∉ S p)
    (hcard : ∀ p, Fintype.card (PairIdx k) ≤ (S p).card) :
    Hk k ⊑ G := by
  classical
  -- (a) Hall's theorem gives an injective system of distinct representatives `z p ∈ S p`.
  obtain ⟨z, hzinj, hz⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' S).1
    (hall_condition_of_card_le S hcard)
  -- the basic distinctness facts
  have hxy : ∀ i, x ≠ y i := fun i => (hyx i).ne
  have hxz : ∀ p, x ≠ z p := by
    intro p h
    exact hSx p (by rw [h]; exact hz p)
  have hyz : ∀ (i : Fin k) (p : PairIdx k), y i ≠ z p := by
    intro i p h
    exact hSy p i (by rw [h]; exact hz p)
  -- (b) the map, (c) it is a homomorphism, (d) it is injective
  refine ⟨⟨⟨fun v => v.elim x (Sum.elim y z), ?_⟩, ?_⟩⟩
  · intro a b hab
    replace hab : HAdj k a b := hab
    revert hab
    rcases a with _ | ⟨i | p⟩ <;> rcases b with _ | ⟨j | q⟩ <;> intro hab
    · exact ((hab : False)).elim
    · exact hyx j
    · exact ((hab : False)).elim
    · exact (hyx i).symm
    · exact ((hab : False)).elim
    · replace hab : q.1.1 = i ∨ q.1.2 = i := hab
      rcases hab with rfl | rfl
      · exact (hS q _ (hz q)).1
      · exact (hS q _ (hz q)).2
    · exact ((hab : False)).elim
    · replace hab : p.1.1 = j ∨ p.1.2 = j := hab
      rcases hab with rfl | rfl
      · exact ((hS p _ (hz p)).1).symm
      · exact ((hS p _ (hz p)).2).symm
    · exact ((hab : False)).elim
  · intro a b hab
    rcases a with _ | ⟨i | p⟩ <;> rcases b with _ | ⟨j | q⟩
    · rfl
    · exact absurd (hab : x = y j) (hxy j)
    · exact absurd (hab : x = z q) (hxz q)
    · exact absurd ((hab : y i = x).symm) (hxy i)
    · exact congrArg (fun t => (some (Sum.inl t) : HVertex k)) (hy (hab : y i = y j))
    · exact absurd (hab : y i = z q) (hyz i q)
    · exact absurd ((hab : z p = x).symm) (hxz p)
    · exact absurd ((hab : z p = y j).symm) (hyz j p)
    · exact congrArg (fun t => (some (Sum.inr t) : HVertex k)) (hzinj (hab : z p = z q))

end Erdos926
