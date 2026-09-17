import Erdos1078Haxell.StepGrow
import Erdos1078Haxell.StepImprove

/-! The augmenting procedure terminates: Haxell's theorem in non-domination form. -/

namespace Erdos1078

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → ι)

/-- From any valid state, a partial independent transversal covering one more class exists. -/
theorem exists_pit_of_valid (hND : NonDom G part) (a : ι) :
    ∀ (M : Finset V) (xs : List V), Valid G part a M xs →
      ∃ M' : Finset V, IsPIT G part M' ∧ M'.image part = insert a (M.image part) := by
  suffices H : ∀ m : Lex (Fin (Fintype.card ι + 1) → ℕ), ∀ (M : Finset V) (xs : List V),
      vec ι G M xs = m → Valid G part a M xs →
      ∃ M' : Finset V, IsPIT G part M' ∧ M'.image part = insert a (M.image part) by
    intro M xs hV
    exact H (vec ι G M xs) M xs rfl hV
  intro m
  induction m using WellFoundedLT.induction with
  | _ m IH =>
    intro M xs hm hV
    subst hm
    by_cases hall : ∀ j (hj : j < xs.length), (leaves G M xs[j]).Nonempty
    · -- Growth: every centre has a leaf, so a new centre can be appended.
      obtain ⟨x, hx, hxT⟩ := exists_new_center G part hND hV hall
      obtain ⟨hV', hlt⟩ := step_grow G part hV hall hx hxT
      exact IH (vec ι G M (xs ++ [x])) hlt M (xs ++ [x]) rfl hV'
    · -- Some centre has no leaves; by validity it has to be the last one.
      push Not at hall
      obtain ⟨j, hj, hjempty⟩ := hall
      have hne : xs ≠ [] := by
        intro h
        rw [h] at hj
        simp at hj
      have hjlast : j = xs.length - 1 := by
        by_contra hcon
        have hj1 : j + 1 < xs.length := by omega
        obtain ⟨y, hy⟩ := hV.nonempty j hj1
        rw [Finset.eq_empty_iff_forall_notMem] at hjempty
        exact hjempty y hy
      subst hjlast
      have hlast : leaves G M (xs.getLast hne) = ∅ := by
        rw [List.getLast_eq_getElem]
        exact hjempty
      by_cases ha : part (xs.getLast hne) = a
      · -- Completion.
        obtain ⟨hPIT, himg⟩ := step_done G part hV hne hlast ha
        exact ⟨insert (xs.getLast hne) M, hPIT, himg⟩
      · -- Improvement: recurse on a strictly smaller state with the same covered classes.
        obtain ⟨M', xs', hV', hlt, himg⟩ := step_improve G part hV hne hlast ha
        obtain ⟨M'', hPIT'', himg''⟩ := IH (vec ι G M' xs') hlt M' xs' rfl hV'
        exact ⟨M'', hPIT'', by rw [himg'', himg]⟩

/-- Haxell's theorem (non-domination form): the hypothesis `NonDom` yields an independent
transversal. -/
theorem exists_IT (hND : NonDom G part) : ∃ M : Finset V, IsIT G part M := by
  -- Induction on the number of classes not yet covered by a partial independent transversal.
  have key : ∀ k : ℕ, ∀ M : Finset V, IsPIT G part M →
      (Finset.univ \ M.image part).card = k → ∃ M' : Finset V, IsIT G part M' := by
    intro k
    induction k with
    | zero =>
      intro M hPIT hcard
      refine ⟨M, hPIT, fun i => ?_⟩
      have hsub : (Finset.univ : Finset ι) ⊆ M.image part :=
        Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard)
      obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp (hsub (Finset.mem_univ i))
      exact ⟨v, hv, hvi⟩
    | succ k IH =>
      intro M hPIT hcard
      have hnonempty : (Finset.univ \ M.image part).Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨a, ha⟩ := hnonempty
      rw [Finset.mem_sdiff] at ha
      have hV : Valid G part a M [] :=
        { pit := hPIT
          miss := by
            intro v hv hva
            exact ha.2 (Finset.mem_image.mpr ⟨v, hv, hva⟩)
          chain := by intro j hj; simp at hj
          nonempty := by intro j hj; simp at hj }
      obtain ⟨M', hPIT', himg⟩ := exists_pit_of_valid G part hND a M [] hV
      refine IH M' hPIT' ?_
      rw [himg, Finset.sdiff_insert, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ha), hcard]
      omega
  obtain ⟨M', hM'⟩ :=
    key ((Finset.univ \ (∅ : Finset V).image part).card) ∅
      ⟨by simp, by simp⟩ rfl
  exact ⟨M', hM'⟩

end Erdos1078
