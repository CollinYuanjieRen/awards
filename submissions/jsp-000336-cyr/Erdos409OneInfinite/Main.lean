import Mathlib

/-!
# Erdős Problem #409: `F(n) = 1` infinitely often

For `n ≥ 1` iterate `n ↦ φ(n) + 1` until a prime is reached, and let `F(n)` be the number of
iterations needed.  Erdős (after Finucane) asked how many iterations are needed, whether
infinitely many `n` reach the same prime, and about densities (OPEN; not addressed here).  The
problem page records: "Cambie notes in the comments that `F(n) = o(n)` is trivial, and
`F(n) = 1` infinitely often."  This file proves the second of these two claims, using the
formal-conjectures encoding of `F(n)` from `Erdos409.erdos_409.parts.i`
(`IsLeast {i | ((φ · + 1)^[i] n).Prime} (F n)`): the set of `n` with `F(n) = 1` is infinite.  The
`o(n)` bound and the open questions are not claimed.

Proof.  For an odd prime `p`, `n = 2p` is not prime and `φ(2p) + 1 = (p − 1) + 1 = p` is prime,
so exactly one iteration is needed; there are infinitely many odd primes.
-/

open scoped Topology ArithmeticFunction.sigma Nat
open Filter

/-- For an odd prime `p`, exactly one iteration of `n ↦ φ(n) + 1` starting from `n = 2 * p`
reaches a prime: `φ(2p) + 1 = (p - 1) + 1 = p` is prime, while `2 * p` itself is not. -/
theorem isLeast_one_of_two_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsLeast { i | ((φ · + 1)^[i] (2 * p)).Prime } 1 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  constructor
  · have h : (φ · + 1)^[1] (2 * p) = p := by
      have h2 := hp.two_le
      rw [Function.iterate_one]
      show Nat.totient (2 * p) + 1 = p
      rw [Nat.totient_mul hcop, Nat.totient_two, Nat.totient_prime hp, one_mul]
      omega
    show ((φ · + 1)^[1] (2 * p)).Prime
    rw [h]
    exact hp
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | h
    · have hi' : (2 * p).Prime := hi
      exact absurd hi' (Nat.not_prime_mul (by norm_num) hp.ne_one)
    · exact h

/-- **Erdős #409, Cambie's remark**: `F(n) = 1` for infinitely many `n`, where `F(n)` is the least
number of iterations of `n ↦ φ(n) + 1` reaching a prime (formal-conjectures encoding). -/
theorem erdos_409_F_eq_one_infinite :
    { n : ℕ | IsLeast { i | ((φ · + 1)^[i] n).Prime } 1 }.Infinite := by
  refine Set.infinite_of_injOn_mapsTo (f := fun p => 2 * p)
    (s := { p : ℕ | p.Prime } \ {2}) ?_ ?_
    (Nat.infinite_setOfPred_prime.sdiff (Set.finite_singleton 2))
  · exact (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)).injOn
  · rintro p ⟨hp, hp2⟩
    exact isLeast_one_of_two_mul_prime hp (by simpa using hp2)

/-- The same statement as a negation (`Set.Infinite` is by definition `¬ Set.Finite`), used as
the graded root. -/
theorem erdos_409_F_eq_one_not_finite :
    ¬ { n : ℕ | IsLeast { i | ((φ · + 1)^[i] n).Prime } 1 }.Finite :=
  erdos_409_F_eq_one_infinite
