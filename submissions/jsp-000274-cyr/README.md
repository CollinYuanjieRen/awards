# JSP-000274: Erdős #329, a Sidon set with limsup |A ∩ [1,N]| / √N ≥ 1/2

This package submits, for intake and eligibility review, a Lean proof of the known lower bound in [JSP-000274](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000274) / [Erdős Problem #329](https://www.erdosproblems.com/329): for a Sidon set `A ⊆ ℕ`, how large can `limsup_{N→∞} |A ∩ {1,…,N}| / N^{1/2}` be?

**Scope statement.** The value of the supremum is open. The problem page records that Erdős proved `1/2` is possible, Krückeberg attained `1/√2`, and Erdős–Turán proved the limsup is always at most `1`. This package proves exactly the `1/2` statement; Krückeberg's `1/√2`, the upper bound `1`, and the supremum are not claimed.

## Statement and proof

[Erdos329SidonDensity/Main.lean](Erdos329SidonDensity/Main.lean) copies the definitions `IsSidon`, `sqrtPartialDensity` and `sidonUpperDensity` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/329.lean) verbatim and proves

```lean
theorem erdos_329_lower_bound : ∃ (A : Set ℕ), IsSidon A ∧ sidonUpperDensity A ≥ 1/2
```

which is exactly the formal-conjectures statement `Erdos329.erdos_329.variants.lower_bound` (tagged "research solved" with `sorry`).

Proof. For an odd prime `p` the Erdős–Turán set `S_p = {2p·i + (i² mod p) : 0 ≤ i < p}` is a Sidon set of `p` elements below `2p²` whose nonzero differences are at least `p + 1` in absolute value (`erdosTuranSet_isSidon`). Translated copies `N_k + S_{p_k}` are placed in successive blocks with `p_{k+1}` a prime beyond the previous block and `N_{k+1}` beyond twice its end, so any relation `a + b = c + d` lives in a single block and the union `A` is Sidon. At `N = N_k + 2p_k² ≤ (2p_k + 1)²` the set has at least `p_k` elements in `[1, N]`, so the partial density is at least `p_k / (2p_k + 1) → 1/2`; the limsup bound follows from `Filter.le_limsup_of_frequently_le` with an explicitly proved boundedness witness.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definitions by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

**Record correction.** An earlier revision of this package was filed under JSP-000067; that record is Erdős #39 (Sidon sets with |A ∩ [1,N]| ≫ N^{1/2−ε}, $500). The limsup question formalized here is Erdős #329, which is catalog record JSP-000274. The package was renamed accordingly; the Lean content is unchanged.

## Attribution and submission status

The construction is Erdős's, as recorded on the problem page (via Erdős–Turán Sidon sets). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000274-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
