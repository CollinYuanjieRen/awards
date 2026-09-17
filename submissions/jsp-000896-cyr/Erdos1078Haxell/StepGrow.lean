import Erdos1078Haxell.Invariants

/-! Growth steps of the augmenting procedure: choosing and appending a new centre. -/

set_option linter.unusedSectionVars false

namespace Erdos1078

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → ι)

/-- When every centre has a leaf, the non-domination hypothesis provides a new centre. -/
theorem exists_new_center (hND : NonDom G part) {a : ι} {M : Finset V} {xs : List V}
    (hV : Valid G part a M xs)
    (hall : ∀ j (hj : j < xs.length), (leaves G M xs[j]).Nonempty) :
    ∃ x, part x ∈ classes G part M a xs ∧ ∀ u ∈ Tset G M xs, ¬ G.Adj u x := by
  -- `|T| ≤ ℓ + S`, `ℓ ≤ S` and `|classes| = 1 + S`, so `|T| ≤ 2 S = 2 (|classes| − 1)`.
  have h1 := card_Tset_le G M xs
  have h2 := card_classes G part hV
  have h3 : xs.length ≤ ∑ j : Fin xs.length, (leaves G M xs[j]).card := by
    calc xs.length = ∑ _j : Fin xs.length, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => Finset.card_pos.mpr (hall j j.isLt))
  have hcard : (Tset G M xs).card ≤ 2 * ((classes G part M a xs).card - 1) := by omega
  exact hND (classes G part M a xs) ⟨a, Finset.mem_insert_self _ _⟩ (Tset G M xs)
    (Tset_subset_classes G part hV) hcard

/-- Growth: appending a new centre keeps validity and decreases the signature. -/
theorem step_grow {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs)
    (hall : ∀ j (hj : j < xs.length), (leaves G M xs[j]).Nonempty) {x : V}
    (hx : part x ∈ classes G part M a xs) (hxT : ∀ u ∈ Tset G M xs, ¬ G.Adj u x) :
    Valid G part a M (xs ++ [x]) ∧ vec ι G M (xs ++ [x]) < vec ι G M xs := by
  have hlenapp : (xs ++ [x]).length = xs.length + 1 := by simp
  have hget : ∀ (j : ℕ) (hj : j < xs.length), (xs ++ [x])[j]'(by omega) = xs[j] :=
    fun _ hj => List.getElem_append_left hj
  have hlast : (xs ++ [x])[xs.length]'(by omega) = x := by simp
  have htake : ∀ (j : ℕ), j ≤ xs.length → (xs ++ [x]).take j = xs.take j :=
    fun _ hj => List.take_append_of_le_length hj
  constructor
  · -- Validity: `pit` and `miss` are untouched; the new centre satisfies `chain` by `hx`, `hxT`.
    refine ⟨hV.pit, hV.miss, ?_, ?_⟩
    · intro j hj
      rw [hlenapp] at hj
      rcases Nat.lt_or_ge j xs.length with h | h
      · rw [hget j h, htake j h.le]
        exact hV.chain j h
      · have hje : j = xs.length := by omega
        subst hje
        rw [hlast, htake xs.length le_rfl, List.take_length]
        exact ⟨hx, hxT⟩
    · intro j hj
      rw [hlenapp] at hj
      have h : j < xs.length := by omega
      rw [hget j h]
      exact hall j h
  · -- Measure: the signature first differs at index `xs.length`, where the padding
    -- `Fintype.card ι` is replaced by the (strictly smaller) leaf count of the new centre.
    have hMlt : M.card < Fintype.card ι := card_lt_of_valid G part hV
    have hxsM : xs.length ≤ M.card := length_le_card G part hV hall
    have hlen : xs.length < Fintype.card ι + 1 := by omega
    have hvecT : ∀ (ys : List V) (j : Fin (Fintype.card ι + 1)) (h : (j : ℕ) < ys.length),
        vec ι G M ys j = (leaves G M (ys[(j : ℕ)]'h)).card := by
      intro ys j h
      simp only [vec, Pi.toLex_apply]
      split_ifs
      rfl
    have hvecF : ∀ (ys : List V) (j : Fin (Fintype.card ι + 1)), ¬ (j : ℕ) < ys.length →
        vec ι G M ys j = Fintype.card ι := by
      intro ys j h
      simp only [vec, Pi.toLex_apply]
      split_ifs
      rfl
    -- `<` on `Lex (Fin k → ℕ)` is `Pi.Lex (· < ·) (· < ·)`, i.e. definitionally
    -- `∃ i, (∀ j, j < i → f j = g j) ∧ f i < g i`.
    show ∃ i : Fin (Fintype.card ι + 1), _ ∧ _
    refine ⟨⟨xs.length, hlen⟩, ?_, ?_⟩
    · rintro ⟨j, hjk⟩ hji
      have hj : j < xs.length := hji
      have hj' : ((⟨j, hjk⟩ : Fin (Fintype.card ι + 1)) : ℕ) < (xs ++ [x]).length := by
        simp only [hlenapp]; omega
      rw [hvecT _ _ hj',
        hvecT _ _ (show ((⟨j, hjk⟩ : Fin (Fintype.card ι + 1)) : ℕ) < xs.length from hj)]
      exact congrArg _ (congrArg _ (hget j hj))
    · have hT : ((⟨xs.length, hlen⟩ : Fin (Fintype.card ι + 1)) : ℕ) < (xs ++ [x]).length := by
        simp only [hlenapp]; omega
      have hF : ¬ ((⟨xs.length, hlen⟩ : Fin (Fintype.card ι + 1)) : ℕ) < xs.length := by simp
      rw [hvecT _ _ hT, hvecF _ _ hF]
      have hle : (leaves G M
          ((xs ++ [x])[((⟨xs.length, hlen⟩ : Fin (Fintype.card ι + 1)) : ℕ)]'hT)).card ≤ M.card :=
        Finset.card_le_card (leaves_subset G M _)
      exact Nat.lt_of_le_of_lt hle hMlt

end Erdos1078
