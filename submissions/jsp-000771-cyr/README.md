# JSP-000771: Erdős #929, the trivial bound `S(k) ≤ k + 1`

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-000771](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000771) / [Erdős Problem #929](https://www.erdosproblems.com/929): let `S(k)` be the minimal `x` such that there is a positive-density set of `n` for which `n + 1, …, n + k` are all divisible by primes `≤ x`; estimate `S(k)`, in particular is `S(k) ≥ k^{1 − o(1)}`?

**Scope statement.** The estimates are open and are not addressed, nor are the sieve lower bound and the Ford–Green–Konyagin–Maynard–Tao upper bound quoted on the page. The problem page records: "It is trivial that `S(k) ≤ k + 1` since, for example, one can take `n ≡ 1 (mod (k + 1)!)`." This package proves that bound for every `k`. There is no formal-conjectures statement for #929, so the definitions are ours: "positive density" is positive lower density in the elementary form `HasPosDensity T` (for some `d ≥ 1` and all large `N`, `N ≤ d · |T ∩ [1, N]|`), and `S k` is the least `x` admitting a positive-density set `T` such that every `n ∈ T` has each `n + i` (`1 ≤ i ≤ k`) divisible by a prime `≤ x`.

## Statement and proof

[Erdos929TrivialBound/Main.lean](Erdos929TrivialBound/Main.lean) proves

```lean
theorem erdos_929_S_le (k : ℕ) : S k ≤ k + 1
theorem erdos_929_S_le_closed : ¬ ∃ k : ℕ, k + 1 < S k
```

Proof. The class `{n : n ≡ 1 (mod (k + 1)!)}` has lower density at least `1/(2 (k + 1)!)`, and for `n` in it each `n + i` (`1 ≤ i ≤ k`) is divisible by `i + 1`, hence by a prime `≤ i + 1 ≤ k + 1`; so `x = k + 1` is admissible.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
