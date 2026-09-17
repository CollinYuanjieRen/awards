import Mathlib

namespace Erdos308

/-- `k` is representable with denominators from `{1,…,N}`: some subset `S ⊆ {1,…,N}` of distinct
denominators has `∑_{n∈S} 1/n = k`. -/
def Representable (N k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ ∑ n ∈ S, (1 : ℚ) / n = k

theorem representable_one {N : ℕ} (hN : 1 ≤ N) : Representable N 1 := by
  refine ⟨{1}, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    simp only [Finset.mem_Icc]
    exact ⟨le_refl 1, hN⟩
  · simp

theorem representable_two_six : Representable 6 2 := by
  refine ⟨{1, 2, 3, 6}, by decide, ?_⟩
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

theorem not_representable_ge_three_six {k : ℕ} (hk : 3 ≤ k) : ¬ Representable 6 k := by
  rintro ⟨S, hS, hsum⟩
  have hle : ∑ n ∈ S, (1 : ℚ) / n ≤ ∑ n ∈ (Finset.Icc 1 6 : Finset ℕ), (1 : ℚ) / n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hS
    intro i _ _
    positivity
  have htot : ∑ n ∈ (Finset.Icc 1 6 : Finset ℕ), (1 : ℚ) / n = 49 / 20 := by
    rw [show (Finset.Icc 1 6 : Finset ℕ) = {1, 2, 3, 4, 5, 6} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  rw [hsum, htot] at hle
  have hk' : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  linarith

/-- the representable positive integers for `N = 6` are exactly `{1, 2}`. -/
theorem representable_six_iff {k : ℕ} (hk : 1 ≤ k) : Representable 6 k ↔ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    rcases Nat.lt_or_ge k 3 with hlt | hge
    · omega
    · exact absurd h (not_representable_ge_three_six hge)
  · rintro (rfl | rfl)
    · exact representable_one (by norm_num)
    · exact representable_two_six

#print axioms representable_one
#print axioms representable_two_six
#print axioms not_representable_ge_three_six
#print axioms representable_six_iff

end Erdos308
