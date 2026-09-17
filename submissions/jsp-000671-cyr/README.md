# JSP-000671: k-core existence from the degeneracy bound (scoped component of Erdős #814)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000671](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000671) (Erdős Problem [#814](https://www.erdosproblems.com/814), Erdős–Faudree–Rousseau–Schelp): does slightly exceeding a specified edge threshold force a *small* induced subgraph of minimum degree at least `k`?

**The full theorem — an induced subgraph on at most `(1−c_k)n` vertices, at the exact threshold `(k−1)(n−k+2)+\binom{k−2}{2}+1`, proved by Sauermann (2019) — is hard and is not claimed here.** This package formalizes the clean, size-uncapped **existence** direction: enough edges force *some* nonempty induced subgraph of minimum degree `≥ k`.

## Statement and proof

With `InducedMinDegGe G k S := ∀ v ∈ S, k ≤ (S.filter (fun w => G.Adj v w)).card` (every vertex of `S` has at least `k` neighbours inside `S`, i.e. the subgraph induced on `S` has minimum degree `≥ k`), the package proves

```lean
theorem exists_core (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : (k - 1) * Fintype.card V < G.edgeFinset.card) :
    ∃ S : Finset V, S.Nonempty ∧ InducedMinDegGe G k S
```

The proof is the degeneracy / repeated-deletion argument: if no nonempty induced subgraph had minimum degree `≥ k`, one could delete a vertex of degree `< k` at each step; each deletion removes at most `k−1` edges, so deleting all `n` vertices removes at most `(k−1)n` edges — but the graph has more than `(k−1)n` edges, a contradiction. (The threshold `(k−1)n` is the elementary degeneracy bound; it is weaker than the tight extremal number in Sauermann's size-capped theorem, which is not claimed.)

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definition and `exists_core` with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/814, retrieved 2026-09-17) is recorded verbatim in `sources/erdos814-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of `exists_core`: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The k-core existence via degeneracy is classical. **Prior art:** an independent Lean formalization of Erdős #814 exists in plby/lean-proofs; this package was authored independently, without reading or copying that source. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000671-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
