import Mathlib
/-! Mathlib-only comparator for JSP-000910 (binomial with no small prime factor). NOT imported by the build. -/
namespace BinomNoSmallPrimeChallenge

theorem choose_23_5_no_small_prime :
    ∀ p : ℕ, p.Prime → p < 5 → ¬ p ∣ Nat.choose 23 5 := by sorry

theorem choose_23_5_coprime_six : Nat.Coprime (Nat.choose 23 5) 6 := by sorry

end BinomNoSmallPrimeChallenge
