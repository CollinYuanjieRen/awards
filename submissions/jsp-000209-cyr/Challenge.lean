import Mathlib
/-!
Mathlib-only comparator for JSP-000209 / Er50 (integers of form 2^k + p), scoped ≥6-representation
certificate at n = 105. Real proofs live in `Jsp209/Reps.lean`. NOT imported by the build.
-/
namespace Erdos2kpChallenge

def repExps (n K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun k => 2 ^ k < n ∧ Nat.Prime (n - 2 ^ k))

theorem card_repExps_105 : 6 ≤ (repExps 105 6).card := by sorry

theorem exists_six_representations :
    ∃ S : Finset ℕ, S.card = 6 ∧ ∀ k ∈ S, Nat.Prime (105 - 2 ^ k) ∧ 2 ^ k + (105 - 2 ^ k) = 105 := by
  sorry

end Erdos2kpChallenge
