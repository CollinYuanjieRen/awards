# JSP-000058: Erdős #23, the blow-up of C₅ shows that n² deleted edges can be necessary

This package submits, for intake and eligibility review, a Lean proof of the tightness example in [JSP-000058](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000058) / [Erdős Problem #23](https://www.erdosproblems.com/23): can every triangle-free graph on `5n` vertices be made bipartite by deleting at most `n²` edges?

**Scope statement.** The question is open. The problem page records that the blow-up of `C₅` shows `n²` would be best possible. This package proves that: in the balanced blow-up of the `5`-cycle with parts of size `n`, every bipartite subgraph omits at least `n²` edges, and in particular there is a triangle-free graph on `25` vertices from which at least `25` edges must be deleted to make it bipartite. The upper-bound question, and its `n = 5` case (Balogh–Clemen–Lidický with McKay's catalogue), are not claimed.

## Statement and proof

[Erdos23BlowupC5/Main.lean](Erdos23BlowupC5/Main.lean) copies the definition `blowupC5` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/23.lean) verbatim and proves `blowupC5_tight` (the formal-conjectures statement of the same name) and

```lean
theorem erdos_23_n5_tight :
    ∃ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 25)),
        H ≤ G → H.IsBipartite → 25 ≤ (G.edgeFinset \ H.edgeFinset).card
```

which is exactly the formal-conjectures statement `Erdos23.erdos_23.variants.n5_tight` (tagged "research solved" with `sorry`); `blowupC5_cliqueFree` shows the blow-up is triangle-free.

Proof. The blow-up contains `n²` edge-disjoint `5`-cycles `(0,a), (1,b), (2,a+b), (3,a), (4,b)` for `(a, b) ∈ (ℤ/n)²`. A bipartite (2-colourable) subgraph contains no odd cycle, so it omits an edge of each cycle, and the omitted edges are distinct, giving `n²` omitted edges. Triangle-freeness: no three classes of `C₅` are pairwise adjacent. The `25`-vertex instance is the image of the blow-up with `n = 5` under a bijection `ℤ/5 × Fin 5 ≃ Fin 25`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the graph definition, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The example is the classical one recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000058-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
