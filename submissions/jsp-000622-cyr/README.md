# JSP-000622: the maximum cochromatic numbers z(1), …, z(19) and z(20) = 6

This package submits a Lean formalization for intake and eligibility review. It addresses [JSP-000622](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000622) ([Erdős Problem #758](https://www.erdosproblems.com/758)). Here `z(G)` is the cochromatic number, the least number of classes in a partition of the vertices into cliques and independent sets, and `z(n)` its maximum over `n`-vertex graphs. The problem page asks to determine `z(n)` for small `n` and, in particular, whether `z(12) = 4`; it records the values `z(1), …, z(19)` as known (with `z(12) = 4` established computationally by Bhavik Mehta), remarks that the only significant difficulty is proving `z(12) = 4`, and states that it is unknown whether `z(20) = 6` or `7`. This package proves the entire published table `z(1), …, z(19)` (`cochromatic_table`, and `cochromatic_zmax_table` for `z(n)` defined literally as the maximum of the cochromatic number over all graphs on `n` vertices), in particular `z(12) = 4` (`cochromatic_twelve`), together with `z(20) = 6` (`cochromatic_twenty`, `cochromatic_zmax_twenty`; a value the problem page records as unknown; the mathematical route is the cited `ipitchford/z20-cochromatic` document, re-derived and fully checked here).

Scope, stated plainly (revised 2026-09-17 after an independent hard-gate re-audit): the catalog entry asks, for a prescribed small graph order, for the worst-case number of parts; the problem page's resolved content is the table `z(1), …, z(19)` with `z(12) = 4` as the named question. This package formalizes the whole table `z(1), …, z(19)` (revision of 2026-09-18) and `z(20) = 6`, so both readings are covered: the named question `z(12) = 4`, the full small-`n` table recorded as known on the page, and the next order `n = 20`. The table values `z(n)` for `n ≠ 12, 20` are, mathematically, short consequences of the anchors already in the tree (see step 9 below); no new deep computation was needed for them. `z(20) = 6` is not contained in the cited publication [Gi86] (which proves `z(n) ≍ n / log n`) and no solver credit for it is attached to the cited publications.

## Statement

[MerLeanExperiment/Target.lean](MerLeanExperiment/Target.lean) states the problem with Mathlib's `SimpleGraph (Fin 20)`: a set is `Homogeneous` if it is pairwise adjacent or pairwise nonadjacent; `HasCocoloring G k` is the existence of a function to `Fin k` all of whose fibers are homogeneous (a class may be empty, so this is an upper bound on the number of classes); `UpperBound` says every twenty-vertex graph has a six-cocoloring; `LowerBound` says some twenty-vertex graph has no five-cocoloring; `Target := UpperBound ∧ LowerBound`. [MerLeanExperiment/Main.lean](MerLeanExperiment/Main.lean) proves

```lean
theorem cochromatic_twenty : CochromaticTwenty.Target
```

with no premises. [MerLeanExperiment/Audit.lean](MerLeanExperiment/Audit.lean) additionally derives `cochromatic_twenty_on_finite_type`, the same two statements on every twenty-element vertex type, so the labelled statement is the ordinary one.

[MerLeanExperiment/Twelve.lean](MerLeanExperiment/Twelve.lean) states and proves the twelve-vertex value in the same vocabulary: `UpperBoundTwelve := ∀ G : SimpleGraph (Fin 12), HasCocoloring G 4`, `LowerBoundTwelve := ∃ G : SimpleGraph (Fin 12), ¬ HasCocoloring G 3`, `TargetTwelve := UpperBoundTwelve ∧ LowerBoundTwelve`, and

```lean
theorem cochromatic_twelve : CochromaticTwenty.TargetTwelve
```

with no premises, together with `cochromatic_twelve_on_finite_type` on every twelve-element vertex type; `Main.lean` re-exports it as `cochromatic_twelve'`.

[MerLeanExperiment/CochromaticNumber.lean](MerLeanExperiment/CochromaticNumber.lean) defines the quantities the problem speaks of: `cochromaticNumber G := Nat.find (∃ k, HasCocoloring G k)`, the least number of homogeneous classes of a finite graph, and `zmax n := Finset.univ.sup (fun G : SimpleGraph (Fin n) => cochromaticNumber G)`, the maximum over all graphs on `n` labelled vertices; `zmax_eq_iff` shows that for `k ≥ 1`, `zmax n = k` is exactly `CochromaticValue n k := (∀ G : SimpleGraph (Fin n), HasCocoloring G k) ∧ (∃ G : SimpleGraph (Fin n), ¬ HasCocoloring G (k - 1))`. [MerLeanExperiment/Table.lean](MerLeanExperiment/Table.lean) defines `zTable : ℕ → ℕ` as the published values (1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6 for `n = 1, …, 19`) and proves

```lean
theorem cochromatic_table (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 19) :
    CochromaticTwenty.CochromaticValue n (CochromaticTwenty.zTable n)

theorem cochromatic_zmax_table (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 19) :
    CochromaticTwenty.zmax n = CochromaticTwenty.zTable n

theorem cochromatic_zmax_twenty : CochromaticTwenty.zmax 20 = 6
```

with no hypotheses beyond the range of `n`.

## Proof structure

The argument follows the candidate computer-assisted proof published in the `ipitchford/z20-cochromatic` repository (see attribution below), re-derived and fully checked in Lean. Every finite claim is proved inside Lean; solvers and generators were used only to discover certificates and are not trusted.

1. **Small Ramsey bounds.** `R(3,3) ≤ 6`, `R(3,4) ≤ 9` (with the odd-order degree-sum obstruction) and `R(4,4) ≤ 18` are proved directly ([SmallRamsey.lean](MerLeanExperiment/SmallRamsey.lean)).
2. **Small catalogs.** Complete catalogs of `R(3,4)`-free graphs through order eight are proved complete by extension induction ([SmallCatalog.lean](MerLeanExperiment/SmallCatalog.lean), [SmallCatalogData.lean](MerLeanExperiment/SmallCatalogData.lean)); every rejected extension exhibits a forbidden set and every accepted one an adjacency-preserving bijection.
3. **Eight vertices.** Every five-vertex graph has a two-cocoloring or is the five-cycle ([FiveVertexClassification.lean](MerLeanExperiment/FiveVertexClassification.lean)); a Ramsey triple and a checked triangle-plus-five-cycle computation give three colors for every eight-vertex graph ([TriangleCycleSplit.lean](MerLeanExperiment/TriangleCycleSplit.lean)).
4. **Twelve vertices.** A homogeneous four-set reduces to the eight-vertex theorem; otherwise Ramsey degree bounds, complementation and explicit neighbourhood isomorphisms reduce the graph to 198 neighbourhood patterns, each excluded by a kernel-checked certificate whose every retained clause carries a proved graph explanation ([TwelveColoringReduction.lean](MerLeanExperiment/TwelveColoringReduction.lean), [TwelveColoring.lean](MerLeanExperiment/TwelveColoring.lean), `NeighborhoodMeaning/`, `Certificates/`).
5. **Sixteen vertices.** A sixteen-vertex graph without a homogeneous four-set reduces to 27 neighbourhood patterns; 25 are excluded by certificates and the two survivors have explicitly listed models mapped by checked isomorphisms to two fixed cores ([SixteenClassification.lean](MerLeanExperiment/SixteenClassification.lean), `B16Meaning/`).
6. **Twenty vertices.** Ramsey supplies a homogeneous four-set; either its complement contains another, disjoint, one, or the sixteen-vertex classification fixes one of the two cores, and two cross certificates (7550 and 5880 inputs, 3932 and 3553 derived clauses, each clause with a proved graph explanation) give two disjoint homogeneous four-sets ([TwentyTwoFours.lean](MerLeanExperiment/TwentyTwoFours.lean), [FixedCoreTwoFours.lean](MerLeanExperiment/FixedCoreTwoFours.lean), `FixedCore0Meaning/`, `FixedCore1Meaning/`). Removing them, the twelve-vertex theorem colors the rest with four classes ([UpperBound.lean](MerLeanExperiment/UpperBound.lean), [CocoloringAssembly.lean](MerLeanExperiment/CocoloringAssembly.lean)).
7. **Lower bound.** The Paley graph on seventeen vertices with three isolated vertices added has no five-cocoloring: it has no homogeneous four-set (kernel computation), so five classes cover at most fifteen of its seventeen vertices ([LowerBound.lean](MerLeanExperiment/LowerBound.lean)).
8. **Twelve vertices, both bounds.** The upper bound `z(12) ≤ 4` is step 4 (`fin12_hasCocoloring_four`). For the lower bound, the Paley graph of order seventeen induced on its first twelve vertices inherits the absence of homogeneous four-sets, so three classes cover at most nine of its twelve vertices ([Twelve.lean](MerLeanExperiment/Twelve.lean)).
9. **The whole table `z(1), …, z(19)`.** Since `z` is monotone in `n` (restrict a cocoloring to an induced subgraph, [TableMonotone.lean](MerLeanExperiment/TableMonotone.lean)), the table reduces to six upper anchors and six lower anchors. Upper: `z(2) ≤ 1`, `z(4) ≤ 2` (any two vertices form a homogeneous set), `z(8) ≤ 3` (step 3), `z(12) ≤ 4` (step 4), `z(15) ≤ 5` (`R(3,3) ≤ 6` gives a homogeneous triple on fifteen vertices; the remaining twelve use step 4; [TableUpper.lean](MerLeanExperiment/TableUpper.lean)), `z(20) ≤ 6` (step 6). Lower: `z(1) ≥ 1`, `z(3) ≥ 2` (one edge plus an isolated vertex), `z(5) ≥ 3` (the five-cycle), `z(13) ≥ 5` and `z(16) ≥ 6` (the Paley graph of order seventeen induced on 13 resp. 16 vertices has no homogeneous four-set, so `k` classes cover at most `3k` vertices; [TableLower.lean](MerLeanExperiment/TableLower.lean)), and `z(9) ≥ 4` from an explicit four-regular nine-vertex graph `G9` (edges 01 02 03 04 12 15 16 25 26 34 37 38 47 48 57 58 67 68, found by our own search among the (4,4)-Ramsey graphs on nine vertices), whose lack of a three-cocoloring is checked by the kernel over all `3^9` colourings with `decide +kernel` (about 100 s; [NineLowerBound.lean](MerLeanExperiment/NineLowerBound.lean)). The assembly is [Table.lean](MerLeanExperiment/Table.lean). The deep content of the package remains steps 4–6 (the twelve-vertex theorem, the sixteen-vertex classification and `z(20) ≤ 6`); the table itself adds about 570 lines.

The certificate modules replay LRAT-style refutations through transparent clause records and Lean's proved checker soundness theorem; no `native_decide`, `Lean.ofReduceBool`, opaque hashing verifier, project axiom, `sorry` or `admit` occurs anywhere in the 2057-module cone. Each certificate is bridged to the actual graph statement by a proved semantic lemma, so no encoding correspondence, catalog completeness, SAT result or coloring theorem is an assumption of the root.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean MerLeanExperiment/Audit.lean
```

The exact toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`; Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). The cone is large (2057 modules, about 117 MB of Lean source, most of it generated certificate data); a full build takes several hours. SHA-256 values of every module are listed in [source-hashes.txt](source-hashes.txt).

**Axioms.** Every audited theorem depends on exactly the three standard axioms of Lean's core logic used throughout Mathlib, and on nothing else:

| Theorem | Axioms |
| --- | --- |
| `cochromatic_twenty` | `propext`, `Classical.choice`, `Quot.sound` |
| `cochromatic_table`, `cochromatic_zmax_table`, `cochromatic_zmax_twenty`, `cochromatic_zmax_twelve`, `CochromaticTwenty.zmax_eq_iff`, `fin15_hasCocoloring_five`, `fin9_not_hasCocoloring_three` | `propext`, `Classical.choice`, `Quot.sound` |
| `cochromatic_twelve`, `cochromatic_twelve_on_finite_type`, `CochromaticTwenty.paley17OnTwelve_lowerBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CochromaticTwenty.universal_six_upperBound`, `paley17_lowerBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CochromaticTwenty.fin8_hasCocoloring_three`, `fin12_hasCocoloring_four`, `sixteen_classification`, `twenty_twoFours`, `fixedCore0_twoFours`, `fixedCore1_twoFours`, `target_iff_on_card_twenty` | `propext`, `Classical.choice`, `Quot.sound` |
| `cochromatic_twenty_on_finite_type` | `propext`, `Classical.choice`, `Quot.sound` |

The published selection rules describe Lean verification as a pass/fail entry threshold without naming an axiom policy; this repository's verification-record schema records an explicit axiom list per theorem, which is why the lists are declared here in full. No organizer-issued Lean statement or comparator challenge for JSP-000622 was found at the repository revision inspected, so no comparator run is claimed.

Local verification used cached upstream dependencies on arm64 macOS; the results are in [verification.txt](verification.txt). It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process; no curator signatures or attestations are fabricated.

## Attribution and submission status

The mathematical route follows the candidate computer-assisted proof "The cochromatic number of graphs on twenty vertices: z(20) = 6" published in the GitHub repository `ipitchford/z20-cochromatic` (author identified there only by that account; the document states no license, so it is cited, not reproduced) ([revision 8dc4b8cd](https://github.com/ipitchford/z20-cochromatic/blob/8dc4b8cd31f4323d6a032752f4cfd69c06d5ca90/z20_proof_paper.md)); that document was used as the source of the reduction strategy only, and none of its computations or certificates is an input to the Lean proof, which recomputes and proves every step. The two sixteen-vertex Ramsey (4,4) cores used as fixed targets of the classification are the two known such graphs; the proof re-derives everything it needs about them from their adjacency data and does not assume their uniqueness. The small Ramsey graph representatives are adapted from Brendan McKay's [Ramsey graph data](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html), released under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); the data were converted into Lean literals, and their completeness as catalogs is proved in Lean rather than taken from the data. The problem is Erdős's (#758); the known values `z(1), …, z(19)` (in particular `z(12) = 4`, established computationally by Bhavik Mehta) and the bounds `6 ≤ z(20) ≤ 7` are due to earlier authors as documented on the problem page; the problem page records the exact value of `z(20)` as unknown, and the cited publication [Gi86] does not contain it. The open draft [PR #41](https://github.com/TheJustinSunPrize/awards/pull/41) registers an English plan for the same target without Lean code; its history is preserved and no priority is claimed over it.

All Lean proofs in this package were written for this formalization, with OpenAI Codex (GPT-5.6 Astra/Sol) assistance for the original development and Claude Code (Claude Fable 5.1 and Claude Opus) assistance for its completion and verification; the contribution sought is the formalization, not a new mathematical discovery. No first-formalization priority or entitlement to an award is claimed. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000622-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
