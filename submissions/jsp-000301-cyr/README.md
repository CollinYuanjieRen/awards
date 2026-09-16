# JSP-000301: consecutive powerful nonsquares

This package submits a Lean formalization for intake and eligibility review. It answers only [JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000301): if two consecutive positive integers are powerful, must at least one be a perfect square? The answer is no.

## Statement and proof

[Proof.lean](Proof.lean) proves `consecutive_powerful_not_always_square`:

```lean
¬ (∀ n : ℕ, 0 < n →
    (∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n) →
    (∀ p : ℕ, p.Prime → p ∣ n + 1 → p ^ 2 ∣ n + 1) →
    IsSquare n ∨ IsSquare (n + 1))
```

The domain is the ordinary natural numbers. Positivity makes the pair positive integers. Powerful means that every prime divisor has its square dividing the number; the predicate is expanded in the theorem, with no bounded-prime restriction. Mathlib's `IsSquare` has its ordinary meaning of existence of a square root. There are no additional public hypotheses or custom definitions.

The explicit witness theorem `powerful_pair_witness` verifies 12167 = 23³ and 12168 = 2³ · 3² · 13². Both numbers are powerful and neither is square (110² < 12167 < 12168 < 111²). Every fact is proved in Lean; no literature theorem is assumed. This does not address the distinct counting question in Erdős #365 or three consecutive powerful numbers.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness; it avoids rebuilding dependencies.

[Audit.lean](Audit.lean) checks the precise root statement and an explicitly natural-number witness and prints both axiom sets. Both use only `propext`, `Classical.choice`, and `Quot.sound`. The proof contains no placeholders, custom axioms or native-evaluation shortcuts. [verification.txt](verification.txt) records the local build and audit of this exported package.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. No claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process; no curator signatures or attestations are fabricated.

## Attribution and submission status

The counterexample is classical, attributed to S. W. Golomb by [Erdős Problem #365](https://www.erdosproblems.com/365). The original reference is S. W. Golomb, “Powerful Numbers”, American Mathematical Monthly 77 (1970), 848–852, [DOI](https://doi.org/10.1080/00029890.1970.11992598). The primary article was not used as a proof assumption. The source code here was independently prepared with OpenAI Codex assistance; the contribution sought is formalization, not a new mathematical discovery.

Earlier public submissions of the same result include [PR #13](https://github.com/TheJustinSunPrize/awards/pull/13), [PR #17](https://github.com/TheJustinSunPrize/awards/pull/17), [PR #33](https://github.com/TheJustinSunPrize/awards/pull/33), and [issue #25](https://github.com/TheJustinSunPrize/awards/issues/25). No first-formalization priority or entitlement to an award is claimed. Please assess whether this additional implementation contributes eligible work. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000301-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
