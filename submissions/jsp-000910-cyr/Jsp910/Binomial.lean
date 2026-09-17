import Mathlib

namespace BinomNoSmallPrime

theorem choose_23_5_eq : Nat.choose 23 5 = 33649 := by decide

theorem choose_23_5_coprime_six : Nat.Coprime (Nat.choose 23 5) 6 := by
  rw [Nat.Coprime, choose_23_5_eq]; decide

theorem choose_23_5_no_small_prime :
    ∀ p : ℕ, p.Prime → p < 5 → ¬ p ∣ Nat.choose 23 5 := by
  intro p hp hlt hdvd
  have h2 := hp.two_le
  interval_cases p <;>
    · rw [choose_23_5_eq] at hdvd; revert hdvd; decide

#print axioms BinomNoSmallPrime.choose_23_5_no_small_prime
#print axioms BinomNoSmallPrime.choose_23_5_coprime_six

end BinomNoSmallPrime
