# JSP-000631: Erdős #770, h(n) = n + 1 if and only if n + 1 is prime

This package submits, for intake and eligibility review, a Lean proof of the elementary remark on the page of [JSP-000631](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000631) / [Erdős Problem #770](https://www.erdosproblems.com/770): let `h(n)` be minimal such that `2^n − 1, 3^n − 1, …, h(n)^n − 1` are mutually coprime; Erdős asked about the densities of `{n : h(n) = p}`, whether `liminf h(n) = ∞`, and about the largest prime `p` with `p − 1 ∣ n`.

**Scope statement.** The open questions are not addressed, and the page's second remark (that `h(n)` is unbounded for odd `n`) is not claimed. The problem page records: "It is easy to see that `h(n) = n + 1` if and only if `n + 1` is prime". This package proves exactly that, in the shape of the formal-conjectures statement `Erdos770.Nat.Prime.h_eq_add_one` (tagged "textbook" with `sorry`), with the definition `Erdos770.h` copied verbatim from the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/770.lean) (which reads "mutually coprime" as: the gcd of the whole family is `1`).

## Statements and proof

[Erdos770PrimeIff/Main.lean](Erdos770PrimeIff/Main.lean) proves

```lean
theorem Erdos770.Nat.Prime.h_eq_add_one {n : ℕ} (hn : 2 < n) : h n = n + 1 ↔ (n + 1).Prime
```

via the hypothesis-free form `erdos_770_h_eq_add_one_succ (n) : h (n + 3) = n + 4 ↔ (n + 4).Prime`.

Proof. Root counting in `𝔽_q` shows that the gcd of `i^n − 1` over `2 ≤ i ≤ n + 1` is always `1` (a common prime divisor `q` would exceed `n + 1` and make `1, …, n + 1` distinct roots of `X^n − 1`), so `h(n) ≤ n + 1` for every `n ≥ 1`. If `n + 1` is prime, Fermat gives `n + 1 ∣ i^n − 1` for `2 ≤ i ≤ n`, so no smaller `m` works and `h(n) = n + 1`. If `n + 1 = ab` is composite and `h(n) = n + 1`, a common prime divisor `q` of the `i^n − 1` (`2 ≤ i ≤ n`) also divides `(ab)^n − 1`, contradicting the gcd at `m = n + 1` being `1`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definition by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The remark is the elementary observation recorded on the problem page (attributed there to Erdős, [Er74b]). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000631-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
