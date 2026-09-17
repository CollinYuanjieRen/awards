import Mathlib

/-!
# Erdős Problem #983: the trivial bound `f(k, n) ≤ π(n)`

Let `n ≥ 2` and `π(n) < k ≤ n`, and let `f(k, n)` be the smallest integer `r` such that in any
`A ⊆ {1, …, n}` of size `k` there exist primes `p₁, …, p_r` such that more than `r` elements
`a ∈ A` are only divisible by primes from `{p₁, …, p_r}`.  Erdős asked whether
`2π(n^{1/2}) − f(π(n) + 1, n) → ∞` and, in general, to estimate `f(k, n)` (OPEN; not addressed
here, nor the Erdős–Straus asymptotics).  The problem page records: "It is trivial that
`f(k, n) ≤ π(n)`."  This file proves it: taking all `π(n)` primes up to `n`, every element of
`A ⊆ {1, …, n}` is only divisible by those primes, and `|A| = k > π(n)`.  The hypotheses `n ≥ 2`
and `k ≤ n` of the page's setting are not needed for this bound and are not assumed.

There is no formal-conjectures statement for #983, so the definitions are ours: "`a` is only
divisible by primes from `P`" is `a.primeFactors ⊆ P`, and `f k n` is the least `r` such that every
`A ⊆ Finset.Icc 1 n` with `#A = k` admits a set `P` of `r` primes with more than `r` elements of
`A` having `a.primeFactors ⊆ P` (`sInf`, which is `0` if no such `r` exists).
-/

open Finset

/-- `A` admits a set `P` of `r` primes such that more than `r` elements of `A` are only divisible
by primes from `P`. -/
def SupportedBy (A : Finset ℕ) (r : ℕ) : Prop :=
  ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ #P = r ∧ r < #(A.filter fun a => a.primeFactors ⊆ P)

/-- `f(k, n)`: the least `r` such that every `A ⊆ {1, …, n}` of size `k` is `SupportedBy r`. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {r | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → #A = k → SupportedBy A r}

/-- The primes up to `n` are `π(n)` many. -/
theorem card_primesBelow_succ (n : ℕ) : #(Nat.primesBelow (n + 1)) = Nat.primeCounting n := by
  simp [Nat.primeCounting, Nat.primesBelow_card_eq_primeCounting']

/-- Every `A ⊆ {1, …, n}` with more than `π(n)` elements is supported by the `π(n)` primes up
to `n`. -/
theorem supportedBy_primeCounting (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hk : Nat.primeCounting n < #A) : SupportedBy A (Nat.primeCounting n) := by
  refine ⟨Nat.primesBelow (n + 1), fun p hp => (Nat.mem_primesBelow.mp hp).2,
    card_primesBelow_succ n, ?_⟩
  have hfil : (A.filter fun a => a.primeFactors ⊆ Nat.primesBelow (n + 1)) = A := by
    refine Finset.filter_true_of_mem fun a ha p hp => ?_
    obtain ⟨hpp, hpd, ha0⟩ := Nat.mem_primeFactors.mp hp
    have han := (Finset.mem_Icc.mp (hA ha)).2
    have hpa : p ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hpd
    exact Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le (hpa.trans han), hpp⟩
  rw [hfil]
  exact hk

/-- **Erdős #983, the page's trivial bound**: `f(k, n) ≤ π(n)` whenever `π(n) < k`. -/
theorem erdos_983_f_le_primeCounting (k n : ℕ) (hk : Nat.primeCounting n < k) :
    f k n ≤ Nat.primeCounting n := by
  refine Nat.sInf_le ?_
  intro A hA hAk
  exact supportedBy_primeCounting n A hA (by omega)

/-- Closed form of `erdos_983_f_le_primeCounting`. -/
theorem erdos_983_f_le_primeCounting_closed :
    ¬ ∃ k n : ℕ, Nat.primeCounting n < k ∧ Nat.primeCounting n < f k n := by
  rintro ⟨k, n, hk, h⟩
  exact absurd (erdos_983_f_le_primeCounting k n hk) (not_le.mpr h)
