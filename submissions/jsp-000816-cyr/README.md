# JSP-000816: Erdős #983, the trivial bound `f(k, n) ≤ π(n)`

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-000816](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000816) / [Erdős Problem #983](https://www.erdosproblems.com/983): for `n ≥ 2` and `π(n) < k ≤ n`, let `f(k, n)` be the smallest `r` such that in any `A ⊆ {1, …, n}` of size `k` there exist primes `p₁, …, p_r` such that more than `r` elements of `A` are only divisible by primes from `{p₁, …, p_r}`; is `2π(n^{1/2}) − f(π(n) + 1, n) → ∞`, and, in general, estimate `f(k, n)`.

**Scope statement.** The estimates are open and are not addressed, nor are the Erdős–Straus asymptotics quoted on the page. The problem page records: "It is trivial that `f(k, n) ≤ π(n)`." This package proves it for every `k > π(n)` (the page's further hypotheses `n ≥ 2`, `k ≤ n` are not needed and not assumed). There is no formal-conjectures statement for #983, so the definitions are ours: "`a` is only divisible by primes from `P`" is `a.primeFactors ⊆ P`, and `f k n` is the least admissible `r` (as `sInf`).

## Statement and proof

[Erdos983TrivialBound/Main.lean](Erdos983TrivialBound/Main.lean) defines

```lean
def SupportedBy (A : Finset ℕ) (r : ℕ) : Prop :=
  ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ #P = r ∧ r < #(A.filter fun a => a.primeFactors ⊆ P)
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {r | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → #A = k → SupportedBy A r}
```

and proves

```lean
theorem erdos_983_f_le_primeCounting (k n : ℕ) (hk : Nat.primeCounting n < k) :
    f k n ≤ Nat.primeCounting n
theorem erdos_983_f_le_primeCounting_closed :
    ¬ ∃ k n : ℕ, Nat.primeCounting n < k ∧ Nat.primeCounting n < f k n
```

Proof. Take `P` to be the `π(n)` primes up to `n`; every element of `A ⊆ {1, …, n}` has all its prime factors in `P`, so all `k > π(n)` elements of `A` qualify, and `r = π(n)` is admissible.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
