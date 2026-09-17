# JSP-000569: Erdős #698, the Erdős–Szekeres bound is sharp for i = 1, j = p, n = 2p

This package submits, for intake and eligibility review, a Lean proof of the sharpness remark on the page of [JSP-000569](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000569) / [Erdős Problem #698](https://www.erdosproblems.com/698): Erdős and Szekeres proved `gcd(C(n,i), C(n,j)) ≥ C(n,i)/C(j,i) ≥ 2^i` for `1 ≤ i < j ≤ n/2`, and Erdős asked whether the gcd must be large.

**Scope statement.** The main question was settled by Bergman (the page's "proved" status and the existing plby Lean formalization refer to Bergman's theorem); neither Bergman's theorem nor the Erdős–Szekeres inequality itself is claimed. The problem page records: "This inequality is sharp for `i = 1`, `j = p`, and `n = 2p`." This package proves exactly that, in the shape of the formal-conjectures statement `Erdos698.erdos_698.variants.erdos_szekeres_sharp` (tagged "research solved" with `sorry`), copied verbatim from the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/698.lean).

## Statement and proof

[Erdos698Sharp/Main.lean](Erdos698Sharp/Main.lean) proves

```lean
theorem Erdos698.erdos_698.variants.erdos_szekeres_sharp (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (Nat.gcd ((2 * p).choose 1) ((2 * p).choose p) : ℝ) =
        ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) ∧
      ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) = (2 : ℝ) ^ 1
```

together with a closed form used by our internal audit tooling.

Proof. `gcd(2p, C(2p,p))` divides `2p`, is even since `2 ∣ C(2p,p)`, and is not divisible by `p` because `p ∤ C(2p,p)` for `p > 2` (the exponent of `p` in the central binomial coefficient vanishes when `2p < 3p`); hence it equals `2 = 2p/p = 2^1`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The remark is the one recorded on the problem page (Erdős–Szekeres 1978). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000569-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
