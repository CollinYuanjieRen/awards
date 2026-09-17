# JSP-000769: the extremal number of the apexed pair-subdivision graph H_k (Erdős #926)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000769](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000769), which is [Erdős Problem #926](https://www.erdosproblems.com/926) (catalog references [Er71], [Fu91], [AKS03]): for `k ≥ 4`, let `H_k` be the graph on the vertices `x`, `y_1, …, y_k` and `z_{ij}` (one for each pair `i < j`), where `x` is adjacent to every `y_i` and `z_{ij}` is adjacent to `y_i` and `y_j`; is `ex(n; H_k) ≪_k n^{3/2}`? The answer is yes: Füredi (Combinatorica 11 (1991), 75–79) proved `ex(n; H_k) ≪ (kn)^{3/2}`, later sharpened to `≪ k n^{3/2}` by Alon, Krivelevich and Sudakov.

## Statement and proof

[Erdos926Furedi/Main.lean](Erdos926Furedi/Main.lean) proves

```lean
theorem extremalNumber_Hk_le (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    (extremalNumber n (Hk k) : ℝ) ≤ (k : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) + k * n
theorem erdos_926 (k : ℕ) (hk : 4 ≤ k) :
    (fun n : ℕ => (extremalNumber n (Hk k) : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)
```

where `extremalNumber n H` is Mathlib's extremal number (the largest number of edges of a graph on `Fin n` containing no copy of `H`, `SimpleGraph.extremalNumber`), and `Hk k` ([Erdos926Furedi/Definitions.lean](Erdos926Furedi/Definitions.lean)) is the graph of the problem on the vertex type `Option (Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2})`: `none` is the centre `x`, `some (Sum.inl i)` is `y_i`, `some (Sum.inr p)` is `z_p`, and the only edges are `x y_i` and `z_p y_i` for `i ∈ p`. `Main.lean` also states the closed form `erdos_926_closed : ¬ ∃ k, 4 ≤ k ∧ ¬ (…)`. The first theorem is the explicit Füredi-type bound with the constant `k^{3/2}` (plus a lower-order term `k n`) for every `k ≥ 2`; the second is the `O_k(n^{3/2})` statement of the problem for `k ≥ 4`. [Audit.lean](Audit.lean) restates both as typed `example`s.

The proof is an elementary Turán-plus-double-counting argument, written for this package from the problem statement (Füredi's paper was not available to us; the argument reaches the `(kn)^{3/2}` strength of his bound and makes no claim to reproduce his proof), with the threshold `T = |pairs| + k + 1` on codegrees:

1. [Embed.lean](Erdos926Furedi/Embed.lean): if a vertex `x` has `k` distinct neighbours `y_i` such that every pair `y_i, y_j` has at least `|pairs|` common neighbours outside `{x, y_1, …, y_k}`, then a system of distinct representatives (Hall's theorem) provides the `z_p`, and `H_k` embeds.
2. [Rich.lean](Erdos926Furedi/Rich.lean): hence in an `H_k`-free graph the "rich graph" at `x`, joining two neighbours of `x` with at least `T` common neighbours, has no `k`-clique.
3. [Turan.lean](Erdos926Furedi/Turan.lean): by Turán's theorem (Mathlib's `turanNumber`) the rich graph on the `d` neighbours of `x` has at most `(1 − 1/(k−1)) d²/2` edges, so at least `d²/(k−1) − d` ordered pairs of neighbours of `x` are poor (fewer than `T` common neighbours).
4. [Count.lean](Erdos926Furedi/Count.lean): summing over `x`, each poor ordered pair is counted at most `T − 1` times, so `Σ_x d_x²/(k−1) − 2e ≤ (T−1) n²`; with Cauchy–Schwarz `Σ d_x² ≥ 4e²/n` this gives `e ≤ k^{3/2} n^{3/2} + k n`.

No numerical certificate or decision procedure is used.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness.

[Audit.lean](Audit.lean) prints the axioms of both roots and of the main lemmas. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the package. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (https://www.hejustinsun.com/prize/rules, v1.0, retrieved 16 September 2026; the rules are not part of this repository) require in their section 6 an offline axiom audit by the designated verifiers, list in section 7 the failure to detect placeholder or unreviewed axioms as a ground for revocation, and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official process.

## Attribution and submission status

The theorem is Füredi's (1991); the argument formalized here is an elementary Turán-plus-double-counting proof of a bound of the same `(kn)^{3/2}` strength, written for this package with explicit constants from the problem statement alone (the original paper was not consulted), and it does not reproduce the sharper `k n^{3/2}` bound of Alon–Krivelevich–Sudakov. A Lean formalization of this problem exists in the repository plby/lean-proofs (file `src/latest/ErdosProblems/Erdos926.lean`, formal authors Codex and GPT-5.6 Sol); that file carries no copyright or license line, the repository has no root LICENSE, and the notice `src/latest/LICENSE` covers only externally sourced files, so no license grant applies to it; the present package is an independent formalization written from the mathematical argument without consulting or reusing its proof text. It was prepared with Claude Code (Claude Fable 5.1 planning, Claude Opus implementation) assistance. The contribution sought is a reusable kernel-checked formalization of the exact catalog question; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed.

Proposed formalizer: `RECIPIENT-jsp-000769-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
