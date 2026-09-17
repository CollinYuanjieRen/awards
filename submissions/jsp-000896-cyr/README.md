# JSP-000896: transversal cliques in balanced multipartite graphs (Erdős #1078)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000896](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000896), which is [Erdős Problem #1078](https://www.erdosproblems.com/1078) ([BES75b], [Er75]): let `G` be an `r`-partite graph with `n` vertices in each part; if `G` has minimum degree at least `(r − 3/2 − o(1)) n`, must `G` contain a `K_r`? Bollobás, Erdős and Szemerédi conjectured this and showed `r − 3/2` is best possible; Haxell [Ha01] proved it, and Haxell–Szabó [HaSz06] later found the sharp threshold `(r − 1) n − ⌈sn/(2s − 1)⌉`, `s = ⌊r/2⌋`.

## Statement and proof

[Erdos1078Haxell/Main.lean](Erdos1078Haxell/Main.lean) proves

```lean
theorem erdos_1078 (r n : ℕ) (hn : 1 ≤ n) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → Fin r)
    (hsize : ∀ i : Fin r, (univ.filter (fun v => part v = i)).card = n)
    (hcross : ∀ v w, G.Adj v w → part v ≠ part w)
    (hdeg : ∀ v, ((r : ℝ) - 3 / 2) * n ≤ G.degree v) :
    ∃ S : Finset V, G.IsNClique r S
```

together with its closed form `erdos_1078_closed` (no such graph is `CliqueFree r`). Here the `r` parts are the fibres of `part : V → Fin r`, each of size `n`, with no edges inside a part; the degree condition is stated over the reals exactly as written; and "contains a `K_r`" is Mathlib's `IsNClique r`. The theorem is Haxell's bound: the page's `o(1)` term is taken to be `0`. A larger `o(1)` term weakens the hypothesis, so a statement with a positive `o(1)` term would be stronger than the one proved here, and a reviewer may reasonably regard the formalization as the weakest member of the family the page describes. It is, however, exactly the statement the page credits Haxell with proving (her theorem that classes of size at least `2Δ` admit an independent transversal gives precisely `(r − 3/2) n`), and it is the natural precise reading of the page: Bollobás, Erdős and Szemerédi showed that `r − 3/2` is best possible only asymptotically in `r`, while for a fixed `r ≥ 4` the Haxell–Szabó threshold `(r − 1) n − ⌈⌊r/2⌋ n/(2⌊r/2⌋ − 1)⌉ ≤ (r − 3/2 − 1/(4⌊r/2⌋ − 2)) n` lies strictly below `(r − 3/2) n`, so the `o(1)` in the conjecture is a term vanishing as `r → ∞` rather than a sharp constant for fixed `r`. No positive `o(1)` term and no sharp threshold are claimed. The hypothesis `n ≥ 1` is needed: the empty graph satisfies the degree condition vacuously and contains no `K_r` for `r ≥ 1`. [Audit.lean](Audit.lean) restates the theorems as typed `example`s.

The proof is Haxell's, in the form of the [Erdos1078Haxell/Degree.lean](Erdos1078Haxell/Degree.lean) theorem `haxell`: a graph with maximum degree at most `Δ` whose vertex classes are nonempty and have at least `2Δ` vertices has an independent transversal (an independent set with one vertex from each class).

1. [Definitions.lean](Erdos1078Haxell/Definitions.lean) and [Invariants.lean](Erdos1078Haxell/Invariants.lean): partial independent transversals `IsPIT`, the non-domination hypothesis `NonDom` (for every nonempty set `B` of classes, no set of at most `2(|B| − 1)` vertices from those classes dominates their union), and the *constellation* states of the augmenting procedure: a partial transversal `M` missing a root class `a`, and a list of centres `x_1, …, x_t`, each lying in a class already reached and adjacent to no earlier centre or leaf, with leaves `N_M(x_j)`; the leaves of distinct centres lie in distinct new classes, so `|T| ≤ 2(|A(T)| − 1)` for the vertex set `T` and reached classes `A(T)`.
2. [StepGrow.lean](Erdos1078Haxell/StepGrow.lean) and [StepImprove.lean](Erdos1078Haxell/StepImprove.lean): when every centre has a leaf, `NonDom` yields a new centre (growth); when the last centre has no leaf it either lies in the root class (then `M` extends) or replaces the leaf of its class in `M`, truncating the constellation (improvement). Each step decreases the signature `(|N_M(x_1)|, …, |N_M(x_t)|, ∞, …)` in the lexicographic order on `Fin (m+1) → ℕ`, which is well-founded.
3. [Augment.lean](Erdos1078Haxell/Augment.lean): well-founded induction on the signature shows that every valid state leads to a partial transversal covering one more class; iterating from the empty transversal gives `exists_IT`.
4. [Degree.lean](Erdos1078Haxell/Degree.lean): degree at most `Δ` and classes of size at least `2Δ` imply `NonDom` (at most `2Δ(|B| − 1) < 2Δ|B| ≤ |V_B|` vertices are dominated), giving `haxell`.
5. [Main.lean](Erdos1078Haxell/Main.lean): in the cross-part complement `H` (`v ~ w` iff they lie in different parts and are not adjacent in `G`) every degree is at most `(r − 1) n − (r − 3/2) n = n/2`, so `H` has an independent transversal, which is an `r`-clique of `G`.

No numerical certificate, `decide` or `native_decide` is used.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness.

[Audit.lean](Audit.lean) prints the axioms of the theorems and of the main lemmas. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the package. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (https://www.hejustinsun.com/prize/rules, v1.0, retrieved 16 September 2026; the rules are not part of this repository) require in their section 6 an offline axiom audit by the designated verifiers, list in section 7 the failure to detect placeholder or unreviewed axioms as a ground for revocation, and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official process.

## Attribution and submission status

The theorem is due to Haxell (A note on vertex list colouring, Combin. Probab. Comput. 10 (2001), 345–347), answering the conjecture of Bollobás, Erdős and Szemerédi (On complete subgraphs of r-chromatic graphs, Discrete Math. 13 (1975), 97–107); the sharp threshold is due to Haxell and Szabó (Odd independent transversals are odd, Combin. Probab. Comput. 15 (2006), 193–211) and is not formalized here. The argument formalized is the proof sketch of the domination form of Haxell's theorem given by Graf and Haxell in "Finding independent transversals efficiently" (arXiv:1811.02687, Section 2), written for this package with an explicit well-founded signature and the non-domination hypothesis taken in the slightly stronger form that also forbids domination through edges inside a class (which the degree hypothesis provides equally); Haxell's original note was not consulted. A Lean formalization of this problem exists in the repository plby/lean-proofs (file `src/latest/ErdosProblems/Erdos1078.lean` at commit `8822f7dd`, whose header a coverage screen of that repository read to identify the problem; its proof text was not opened); that repository has no root LICENSE and its notice `src/latest/LICENSE` covers only externally sourced files, so no license grant applies to it. The present package is an independent formalization written from the published argument without consulting or reusing that proof text; it is offered as a license-clean, first-party kernel-checked proof of the catalog question and does not dispute the credit of that earlier formalization. It was prepared with Claude Code (Claude Fable 5.1 planning, Claude Opus implementation) assistance. The contribution sought is a reusable kernel-checked formalization of the exact catalog question; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed.

Proposed formalizer: `RECIPIENT-jsp-000896-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
