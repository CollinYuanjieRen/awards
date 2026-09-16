# JSP-000247: Erdős #291, part (ii) — gcd(aₙ, Lₙ) > 1 infinitely often

This package submits, for intake and eligibility review, a Lean proof of the answered half of [JSP-000247](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000247) / [Erdős Problem #291](https://www.erdosproblems.com/291). With `Lₙ = lcm(1, …, n)` and `∑_{k ≤ n} 1/k = aₙ / Lₙ`, Erdős and Graham asked whether `gcd(aₙ, Lₙ) = 1` and `gcd(aₙ, Lₙ) > 1` each occur for infinitely many `n`.

**Scope statement.** Part (i), whether `gcd(aₙ, Lₙ) = 1` occurs infinitely often, is open. Part (ii) was settled by Steinerberger's observation, recorded on the problem page: whenever the leading base-3 digit of `n` is 2, the prime 3 divides `aₙ`, and it divides `Lₙ` as soon as `n ≥ 3`. This package proves part (ii) only; no progress on part (i) is claimed.

## Statement and proof

[Erdos291ii/Main.lean](Erdos291ii/Main.lean) proves `erdos_291_part_ii`:

```lean
def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm (fun x ↦ x)
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, L n / k

theorem erdos_291_part_ii : {n : ℕ | Nat.gcd (a n) (L n) > 1}.Infinite
```

(`erdos_291_part_ii_not_finite` restates the same proposition with the head symbol `¬`; `Set.Infinite` is by definition `¬ Set.Finite`.)

The definitions and the statement are those of the [formal-conjectures rendering `Erdos291.erdos_291.parts.ii`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/291.lean), which records the answer as "true" with a `sorry`. The proof: for `2·3^j ≤ n < 3^(j+1)` every term `Lₙ / m` with `3^j ∤ m` is divisible by 3 (because `3m` still divides `Lₙ`), and the two remaining terms, for `m = 3^j` and `m = 2·3^j`, sum to `3 · Lₙ/(2·3^j)`; hence `3 ∣ aₙ`, and `3 ∣ Lₙ` for `n ≥ 3`. The numbers `n = 2·3^j` are unbounded, so the set is infinite.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints its axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The observation is Steinerberger's (recorded on erdosproblems.com/291; see also OEIS A110566). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000247-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
