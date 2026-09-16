import MerLeanExperiment.IntegerSeparation
import Mathlib.Data.Finset.Basic

namespace ReciprocalSquares

/-- Nearby multiples with a sufficiently large common factor must coincide. -/
theorem exists_common_near_multiple
    (P H h : ℤ) (Q : Finset ℕ) (hne : Q.Nonempty)
    (hsep : 2 * H < P)
    (hnear : ∀ q ∈ Q, ∃ M : ℤ, P * (q : ℤ) ∣ M ∧ |h - M| ≤ H) :
    ∃ M : ℤ, P ∣ M ∧ |h - M| ≤ H ∧ ∀ q ∈ Q, (q : ℤ) ∣ M := by
  obtain ⟨q₀, hq₀⟩ := hne
  obtain ⟨M₀, hdiv₀, hnear₀⟩ := hnear q₀ hq₀
  have hPM₀ : P ∣ M₀ := (dvd_mul_right P (q₀ : ℤ)).trans hdiv₀
  refine ⟨M₀, hPM₀, hnear₀, ?_⟩
  intro q hq
  obtain ⟨M, hdiv, hnearM⟩ := hnear q hq
  have hPM : P ∣ M := (dvd_mul_right P (q : ℤ)).trans hdiv
  have heq : M₀ = M := nearby_multiples_eq h M₀ M P H hPM₀ hPM hnear₀ hnearM hsep
  rw [heq]
  exact (dvd_mul_left (q : ℤ) P).trans hdiv

end ReciprocalSquares
