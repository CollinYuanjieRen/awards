# JSP-000930: Wetzel's problem — Erdős's theorem, both halves (Erdős #1119)

This package submits a Lean formalization for intake and eligibility review of the theorem of Erdős that answers Wetzel's question, the historical core of [JSP-000930](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000930) / [Erdős Problem #1119](https://www.erdosproblems.com/1119). Wetzel asked whether a family of entire functions taking only countably many values at every point must itself be countable. Erdős (Michigan Math. J. 11 (1964), 9–10) showed that the answer depends on the continuum hypothesis: if 𝔠 > ℵ₁ every such family is countable, and if 𝔠 = ℵ₁ there is such a family of cardinality 𝔠.

**Scope statement.** The catalog record and the problem page concern the more general question with an arbitrary cardinal 𝔪 of values, whose answer is *independent of ZFC* (Kumar–Shelah 2017; Schilhan–Weinert 2024). Independence results are model-theoretic and are not formalized here. This package formalizes exactly the ZFC theorem of Erdős for 𝔪 = ℵ₀ as a single closed biconditional; it is a component contribution to the record, not a claim that the general-𝔪 question is closed.

## Statement and proof

[Erdos1119Wetzel/Main.lean](Erdos1119Wetzel/Main.lean) proves `exists_uncountable_wetzelFamily_iff_continuum_eq_aleph_one`:

```lean
theorem exists_uncountable_wetzelFamily_iff_continuum_eq_aleph_one :
    (∃ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) ∧
        (∀ z : ℂ, {y : ℂ | ∃ f ∈ F, f z = y}.Countable) ∧ ¬ F.Countable) ↔
      (𝔠 : Cardinal.{0}) = ℵ₁
```

Entire means `Differentiable ℂ` on all of `ℂ`; the family is a set of functions with a countable value set at every point (Mathlib `Set.Countable`); uncountable means `¬ F.Countable`; `𝔠 = ℵ₁` is `Cardinal.continuum = Cardinal.aleph 1`, the continuum hypothesis. Since `ℵ₁ ≤ 𝔠` is a theorem, the right-hand side is equivalent to the negation of `ℵ₁ < 𝔠`.

- **(→), 𝔠 > ℵ₁ ⇒ countable** ([Erdos1119Wetzel/Countable.lean](Erdos1119Wetzel/Countable.lean), `Erdos1119.erdos_1119`): two distinct entire functions agree on a countable set, so ℵ₁ of them are separated at some point. This Lean proof is vendored from [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1119.lean) (Apache License 2.0; formal authors Codex and GPT-5.6 Sol), unchanged apart from the attribution header and the removal of a trailing `#print axioms`.
- **(←), 𝔠 = ℵ₁ ⇒ an uncountable family exists** (new; `exists_uncountable_wetzelFamily_of_continuum_eq` in [Recursion.lean](Erdos1119Wetzel/Recursion.lean)): Erdős's transfinite construction. Under CH the complex numbers are indexed by the well-ordered type `Omega1 = ℵ₁.ord.ToType`, all of whose initial segments are countable ([IndexType.lean](Erdos1119Wetzel/IndexType.lean)). By well-founded recursion, for every index γ an entire function `fam γ` is chosen that takes Gaussian-rational values ([RationalLattice.lean](Erdos1119Wetzel/RationalLattice.lean)) at all points with index below γ and differs from every earlier function. The choice at each stage is Erdős's interpolation lemma ([Interpolation.lean](Erdos1119Wetzel/Interpolation.lean), `exists_entire_interpolant`): for an injective sequence of nodes `w`, the series `f(z) = Σ εₙ ∏_{i<n}(z − wᵢ)` with `‖εₙ‖ ≤ 1/(n! ∏_{i<n}(1+‖wᵢ‖))` converges uniformly on discs, hence is entire ([SeriesConvergence.lean](Erdos1119Wetzel/SeriesConvergence.lean)), and its value at `wₙ` depends only on `ε₀,…,εₙ`, so the coefficients are chosen one at a time to place each value in a prescribed dense countable set while avoiding one forbidden value. The resulting family is injective in γ, hence of cardinality ℵ₁, and at every point `z` all but countably many of its members take Gaussian-rational values. Erdős's literal conclusion, a family of power 𝔠, is stated separately as `exists_wetzelFamily_card_continuum` in [Cardinality.lean](Erdos1119Wetzel/Cardinality.lean).

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the exact theorem as a typed `example` closed by the root and prints the axioms of the root, of the CH construction, of the vendored countable half, and of the interpolation lemma. Every declaration depends exactly on `propext`, `Classical.choice`, and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide`, or custom trust extension occurs anywhere in the dependency cone. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit by the designated verifiers and do not enumerate accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The theorem is Erdős's (1964); R. D. Dixon independently proved the 𝔠 > ℵ₁ half. The Lean proof of that half is by Codex and GPT-5.6 Sol in plby/lean-proofs, reused under the Apache License 2.0 with its notice preserved; the full license text is included as [LICENSE-APACHE-2.0](LICENSE-APACHE-2.0). The CH construction and the biconditional were prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No new mathematical discovery, first-formalization priority for the vendored half, or entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000930-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT); the vendored file retains its Apache License 2.0 notice.
