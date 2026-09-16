import Mathlib
import Proof.Counting
import Proof.Estimates

/-!
# Existence of a good choice function

For `n ≥ 2 ^ 40` the union bound shows that fewer than `|Choice n|` choice functions are bad,
so a good one exists.
-/

namespace Erdos803

/-- For `n ≥ 2 ^ 40` a good choice function exists: the union bound makes the number of bad
choice functions strictly smaller than `|Choice n|`. -/
theorem exists_good (n : ℕ) (hn : 2 ^ 40 ≤ n) : ∃ f : Choice n, Good f := by
  have hn4 : 4 ≤ n := le_trans (by norm_num) hn
  have hne : Nonempty (Choice n) := by
    refine ⟨fun _ p ↦ ⟨0, ?_⟩⟩
    have h := le_four_mul_bsize_sq hn4 p
    rcases Nat.eq_zero_or_pos (bsize n p) with h0 | h0
    · rw [h0] at h
      norm_num at h
      omega
    · exact h0
  have hcardpos : (0 : ℝ) < (Fintype.card (Choice n) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Choice n)
  have hlt : ({f : Choice n | ¬ Good f}.ncard : ℝ) < (Fintype.card (Choice n) : ℝ) :=
    calc ({f : Choice n | ¬ Good f}.ncard : ℝ)
        ≤ (Fintype.card (Choice n) : ℝ) * ∑ m ∈ Finset.Icc 1 n, badBound n m :=
          card_bad_le n hn4
      _ < (Fintype.card (Choice n) : ℝ) * 1 :=
          mul_lt_mul_of_pos_left (sum_badBound_lt_one n hn) hcardpos
      _ = (Fintype.card (Choice n) : ℝ) := mul_one _
  by_contra hcon
  simp only [not_exists] at hcon
  have huniv : {f : Choice n | ¬ Good f} = Set.univ := by
    ext f
    simp [hcon f]
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card] at hlt
  exact lt_irrefl _ hlt

end Erdos803
