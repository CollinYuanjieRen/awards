# JSP-000336: Erdős #409, F(n) = 1 for infinitely many n

This package submits, for intake and eligibility review, a Lean proof of a remark on the page of [JSP-000336](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000336) / [Erdős Problem #409](https://www.erdosproblems.com/409): iterate `n ↦ φ(n) + 1` until a prime is reached; how many iterations `F(n)` are needed, can infinitely many `n` reach the same prime, and what is the density of `n` reaching a fixed prime?

**Scope statement.** The questions are open and are not addressed. The problem page records: "Cambie notes in the comments that `F(n) = o(n)` is trivial, and `F(n) = 1` infinitely often." This package proves the second of these two claims only; the `o(n)` bound is not claimed. `F(n)` is encoded as in the formal-conjectures rendering `Erdos409.erdos_409.parts.i` (`IsLeast {i | ((φ · + 1)^[i] n).Prime} (F n)`); the theorem statement is ours.

## Statement and proof

[Erdos409OneInfinite/Main.lean](Erdos409OneInfinite/Main.lean) proves

```lean
theorem erdos_409_F_eq_one_infinite :
    { n : ℕ | IsLeast { i | ((φ · + 1)^[i] n).Prime } 1 }.Infinite
```

(and its definitionally equal negated form used by our internal audit tooling).

Proof. For an odd prime `p`, `n = 2p` is not prime and `φ(2p) + 1 = (p − 1) + 1 = p` is prime, so exactly one iteration is needed; there are infinitely many odd primes and `p ↦ 2p` is injective.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The observation is Cambie's, as recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000336-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
