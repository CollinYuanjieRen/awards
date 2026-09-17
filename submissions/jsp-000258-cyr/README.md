# JSP-000258: Erdős #307, solutions have P, Q disjoint with reciprocal sum at least 2

This package submits, for intake and eligibility review, a Lean proof of the easy remark on the page of [JSP-000258](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000258) / [Erdős Problem #307](https://www.erdosproblems.com/307): are there finite sets of primes `P`, `Q` with `1 = (∑_{p ∈ P} 1/p)(∑_{q ∈ Q} 1/q)`?

**Scope statement.** The main question is open and is not addressed, nor are Cambie's coprime variants or Bonfioli's machine-checked barriers. The problem page records: "It is easy to see that, if `P` and `Q` are sets of primes, then `P` and `Q` are disjoint, and `∑_{p ∈ P ∪ Q} 1/p ≥ 2`, whence `|P ∪ Q| ≥ 60`." This package proves the first two claims (disjointness and the reciprocal-sum bound), with the hypotheses in the exact shape of the formal-conjectures statements for #307; the numerical consequence `|P ∪ Q| ≥ 60`, which needs the sizes of the reciprocal sums of the first primes, is not claimed. The theorem statement is ours.

## Statement and proof

[Erdos307Disjoint/Main.lean](Erdos307Disjoint/Main.lean) proves

```lean
theorem Erdos307.erdos_307_disjoint_and_two_le {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    Disjoint P Q ∧ 2 ≤ ∑ p ∈ P ∪ Q, (p : ℚ)⁻¹
```

together with a closed form used by our internal audit tooling.

Proof. Write `∑_{p ∈ P} 1/p = a/N` with `N = ∏ P` and `a = ∑_{p ∈ P} N/p`; each `p ∈ P` divides every term of `a` except `N/p`, so `p ∤ a`; likewise `∑_{q ∈ Q} 1/q = b/M`. The equation gives `ab = NM`. A prime in both `P` and `Q` would satisfy `p² ∣ NM = ab` with `p ∤ a` and `p ∤ b`, which is impossible; so `P`, `Q` are disjoint, the sum over `P ∪ Q` is `S + T` with `ST = 1`, and `S + T ≥ 2` by AM–GM.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The remark is the one recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000258-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
