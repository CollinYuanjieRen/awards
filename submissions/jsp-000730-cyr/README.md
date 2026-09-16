# JSP-000730: Erdős #879, the elementary Erdős–van Lint upper bound G(n) < H(n)

This package submits, for intake and eligibility review, a Lean proof of the elementary half of the known bounds in [JSP-000730](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000730) / [Erdős Problem #879](https://www.erdosproblems.com/879). Call `S ⊆ {1, …, n}` admissible if its elements are pairwise coprime; let `G(n)` be the largest sum of an admissible set and `H(n) = ∑_{p ≤ n} p + n·π(√n)`. Erdős asked whether `G(n) > H(n) − n^{1+o(1)}` and about the structure of the extremal sets; both are open. Erdős and van Lint proved `H(n) − n^{3/2−o(1)} < G(n) < H(n)` and `(H(n) − G(n))/n → ∞`.

**Scope statement.** This package proves only the elementary upper bound `G(n) < H(n)` for every `n ≥ 4`. The lower bound, the divergence of `(H − G)/n`, the open question and the extremal-set structure are not claimed. There is no formal-conjectures statement of #879; the definitions are stated from scratch.

**Convention (disclosed).** The problem page writes `H(n) = ∑_{p<n} p + n π(n^{1/2})`. With a strict `p < n` the inequality `G(n) < H(n)` is false for every prime `n ≥ 5` (the primes up to `n` already form an admissible set with sum `∑_{p≤n} p`; e.g. `G(11) = 41 > 39`), while the Erdős–van Lint asymptotics are unaffected by the difference `n` between the two readings. The package therefore uses `∑_{p ≤ n} p`, under which the elementary bound holds for all `n ≥ 4` (checked by brute force for `n ≤ 40` and proved in general).

## Statement and proof

[Erdos879UpperBound/Main.lean](Erdos879UpperBound/Main.lean) defines `IsAdmissible`, `G n` (the `Finset.sup` of sums over admissible subsets of `Icc 1 n`) and `H n` (with Mathlib's `Nat.primeCounting` and `Nat.sqrt`) and proves

```lean
theorem erdos_879_upper_bound (n : ℕ) (hn : 4 ≤ n) : G n < H n
theorem erdos_879_upper_bound_closed : ¬ ∃ n : ℕ, 4 ≤ n ∧ H n ≤ G n
```

together with the sanity check `G 4 = 8 ∧ H 4 = 9`. Proof: in an admissible set, distinct elements greater than `1` have distinct least prime factors; an element `a ≤ n` whose least prime factor exceeds `√n` is prime, so those elements sum to at most `∑_{√n < p ≤ n} p`; the elements with least prime factor at most `√n` number at most `π(√n)` and are each at most `n`. Adding the element `1` gives `G(n) ≤ H(n) + 1 − ∑_{p ≤ √n} p < H(n)`, since `2 ≤ √n` for `n ≥ 4`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definitions by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The bound is the elementary half of Erdős–van Lint's result as recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000730-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
