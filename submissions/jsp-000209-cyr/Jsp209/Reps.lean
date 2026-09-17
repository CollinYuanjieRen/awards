import Mathlib

namespace Erdos2kp

/-- Number of exponents `k ∈ [1,K]` giving a representation `n = 2^k + p` with `p = n - 2^k` prime. -/
def repExps (n K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun k => 2 ^ k < n ∧ Nat.Prime (n - 2 ^ k))

theorem card_repExps_105 : 6 ≤ (repExps 105 6).card := by
  have h : ({1, 2, 3, 4, 5, 6} : Finset ℕ) ⊆ repExps 105 6 := by
    intro k hk
    fin_cases hk <;>
      · simp only [repExps, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by decide, by decide⟩, by decide, ?_⟩
        norm_num
  calc 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ).card := by decide
    _ ≤ (repExps 105 6).card := Finset.card_le_card h

theorem exists_six_representations :
    ∃ S : Finset ℕ, S.card = 6 ∧ ∀ k ∈ S, Nat.Prime (105 - 2 ^ k) ∧ 2 ^ k + (105 - 2 ^ k) = 105 := by
  refine ⟨{1, 2, 3, 4, 5, 6}, by decide, ?_⟩
  intro k hk
  fin_cases hk <;> exact ⟨by norm_num, by decide⟩

#print axioms Erdos2kp.card_repExps_105
#print axioms Erdos2kp.exists_six_representations

end Erdos2kp
