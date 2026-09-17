import Erdos1074PillaiPrimes

open Erdos1074
open scoped Nat
open Nat

#print axioms pillaiPrimes_infinite
#print axioms pillaiPrimes_not_finite

/-- Erdős #1074: the Pillai primes are infinite, in the formal-conjectures shape
`erdos_1074.variants.PillaiPrimes_infinite`. -/
example : PillaiPrimes.Infinite := pillaiPrimes_infinite

/-- The definition is the formal-conjectures one. -/
example (p : ℕ) : p ∈ PillaiPrimes ↔ p.Prime ∧ ∃ m ≥ 1, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1 := Iff.rfl
example (m : ℕ) : m ∈ EHSNumbers ↔ 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1 := Iff.rfl
