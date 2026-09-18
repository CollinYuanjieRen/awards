import Erdos1183Lattices.Definitions

/-!
# Erdős Problem 1183 — basic API for `Good` and `f`

`Good n ·` is downward closed and bounded above by `2 ^ n`, and `Good n 0` always holds; hence
`f n = sSup {m | Good n m}` is attained and `Good n m ↔ m ≤ f n`.
-/

namespace Erdos1183

variable {n m k : ℕ}

/-- `Good n ·` is downward closed (the same witness works). -/
theorem Good.mono (h : Good n m) (hk : k ≤ m) : Good n k := by
  intro c
  obtain ⟨F, hne, hcl, hmo, hcard⟩ := h c
  exact ⟨F, hne, hcl, hmo, hk.trans hcard⟩

/-- A monochromatic family lives inside the `2 ^ n` subsets of `Fin n`. -/
theorem Good.le_two_pow (h : Good n m) : m ≤ 2 ^ n := by
  obtain ⟨F, _, _, _, hcard⟩ := h (fun _ => true)
  refine hcard.trans ?_
  calc F.card ≤ (Finset.univ : Finset (Finset (Fin n))).card :=
        Finset.card_le_card (Finset.subset_univ F)
    _ = 2 ^ n := by simp

/-- The family `{∅}` is nonempty, closed and monochromatic, so `Good n 0` always holds. -/
theorem good_zero : Good n 0 := by
  intro c
  refine ⟨{∅}, ⟨∅, Finset.mem_singleton_self _⟩, ?_, ⟨c ∅, ?_⟩, Nat.zero_le _⟩
  · intro A hA B hB
    rw [Finset.mem_singleton] at hA hB
    subst hA; subst hB
    simp
  · intro A hA
    rw [Finset.mem_singleton] at hA
    subst hA
    rfl

/-- `{m | Good n m}` is bounded above by `2 ^ n`. -/
theorem bddAbove_good (n : ℕ) : BddAbove {m : ℕ | Good n m} :=
  ⟨2 ^ n, fun _ hm => Good.le_two_pow hm⟩

/-- `{m | Good n m}` is nonempty. -/
theorem nonempty_good (n : ℕ) : {m : ℕ | Good n m}.Nonempty :=
  ⟨0, good_zero⟩

/-- The supremum defining `f n` is attained. -/
theorem good_f (n : ℕ) : Good n (f n) :=
  Nat.sSup_mem (nonempty_good n) (bddAbove_good n)

/-- The characterisation of `f n`. -/
theorem good_iff_le_f : Good n m ↔ m ≤ f n := by
  constructor
  · intro h
    exact le_csSup (bddAbove_good n) h
  · intro h
    exact (good_f n).mono h

theorem le_f_of_good (h : Good n m) : m ≤ f n := good_iff_le_f.mp h

theorem f_lt_of_not_good (h : ¬ Good n m) : f n < m := by
  by_contra hcon
  exact h (good_iff_le_f.mpr (Nat.le_of_not_lt hcon))

/-- Alias of `f_lt_of_not_good` (the name used in the design). -/
theorem f_le_of_not_good (h : ¬ Good n m) : f n < m := f_lt_of_not_good h

end Erdos1183
