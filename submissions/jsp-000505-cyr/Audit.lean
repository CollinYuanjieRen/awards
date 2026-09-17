import Erdos624Alon

open Erdos624 Finset

#print axioms erdos_624_alon
#print axioms erdos_624_alon_closed
#print axioms H_two_eq_one

/-- Erdős #624, the weaker statement (Alon): `H(2^k) ≥ k + 1` for every `k ≥ 2`. -/
example (k : ℕ) (hk : 2 ≤ k) : k + 1 ≤ H (2 ^ k) := erdos_624_alon k hk

/-- The range `k ≥ 2` is optimal. -/
example : ¬ (1 + 1 ≤ H (2 ^ 1)) := by rw [pow_one, H_two_eq_one]; decide

/-- The definitions are the formal-conjectures ones. -/
example (n m : ℕ) : ExistsEventuallySurjective n m ↔
    ∃ (f : Finset (Fin n) → Fin n), ∀ (Y : Finset (Fin n)), #Y ≥ m →
      Y.powerset.image f = Finset.univ := Iff.rfl
example (n : ℕ) : H n = if 0 < n then sInf {m : ℕ | ExistsEventuallySurjective n m} else 0 := rfl
