# JSP-000240: Erdős #282, Fibonacci's greedy unit-fraction algorithm terminates over ℕ

This package submits, for intake and eligibility review, a Lean proof of the classical observation recorded on the page of [JSP-000240](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000240) / [Erdős Problem #282](https://www.erdosproblems.com/282): for an infinite `A ⊆ ℕ` and a rational `x ∈ (0, 1)`, the greedy algorithm repeatedly picks the least unused `n ∈ A` with `n ≥ 1/x` and replaces `x` by `x − 1/n`; Erdős (after Stein) asked whether it always terminates for odd denominators over the odd numbers, and more generally for which `(x, A)`.

**Scope statement.** The open questions and Graham's results are not addressed. The problem page records: "In 1202 Fibonacci observed that this process terminates for any `x` when `A = ℕ`." This package proves that statement in the exact shape of the formal-conjectures theorem `Erdos282.erdos_282.variants.fibonacci` (tagged "textbook" with `sorry`), with the formal-conjectures model `greedyUnitFractionRem` of the remainders copied verbatim from the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/282.lean).

## Statement and proof

[Erdos282Fibonacci/Main.lean](Erdos282Fibonacci/Main.lean) proves

```lean
theorem Erdos282.erdos_282.variants.fibonacci {x : ℚ} (hx : x ∈ Set.Ioo 0 1) :
    greedyUnitFractionRem .univ x =ᶠ[atTop] 0
```

(the remainder is eventually `0`), together with a closed form used by our internal audit tooling.

Proof. For `x = p/q` in lowest terms, the chosen denominator is `n = ⌈q/p⌉`, and the remainder `x − 1/n = (np − q)/(nq)` has numerator strictly smaller than `p`; so the numerators strictly decrease and the remainder reaches `0` within `p` steps, after which the model stays at `0`. Removing used denominators never changes the choice, because the next remainder is below `1/n`, so the next denominator exceeds all previous ones.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, unfolds the model's first step, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The observation is Fibonacci's (1202), as recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000240-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
