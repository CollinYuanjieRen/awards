# JSP-000527: three-dimensional Erdős–Szekeres numbers are subexponential

This package submits a Lean formalization for intake and eligibility review. It addresses [JSP-000527](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000527): in higher-dimensional general position, is the number of points forcing a convex subset exponential in the target size? This is [Erdős Problem #651](https://www.erdosproblems.com/651): with `f_k(n)` the least `N` such that every `N` points in general position in `ℝ^k` contain `n` points in convex position, Erdős asked whether `f_k(n) > (1 + c_k)^n` for some `c_k > 0`. The catalog credits the negative answer to Pohoata–Zakharov, *Convex polytopes from fewer points* (arXiv:2208.04878, 2022), who prove `f_3(n) ≤ 2^{o(n)}`.

## What is proved, and what already existed

[plby/lean-proofs](https://github.com/plby/lean-proofs) (Codex / GPT-5.6 Sol) contains an `Erdos651` development of nineteen files and about sixteen thousand lines: the definitions (`Point`, `InGeneralPosition`, `InConvexPosition`, `erdosSzekeresNumber`, `HasSubexponentialUpperBound`, `Erdos651Claim`), a self-contained proof of the planar ham-sandwich theorem, the Pór–Valtr positive-fraction theorem, the two-separation and lifting propositions (2.5, 2.7), the above/below Ramsey corollary (2.4), the trihedral construction of Proposition 3.1, the projected cups-and-caps Proposition 2.1, explicit hypergraph Ramsey and Dilworth bounds, and all numerical estimates. Its headline theorem, however, is only the *conditional* `erdos_651_of_pohoata_zakharov (hPZ : PohoataZakharovConclusion) : ¬ Erdos651Claim` and the incompatibility statement `not_erdos_651`; the subexponential bound itself is a hypothesis there. Only three of the nineteen files were in that repository's build target, and its draft assembly file `PohoataZakharovProof.lean`, which reduces Theorem 1.1 to an unproved extraction hypothesis, was never compiled.

This submission supplies the missing unconditional theorem: the extraction of the alternating free-set family at the paper's parameters (Section 3 of the paper), assembled with the replayed plby ingredients into `f_3(n) ≤ 2^{o(n)}`.

## Statement and proof

[JSP527/PZ/Main.lean](JSP527/PZ/Main.lean) proves

```lean
theorem theorem_one_one : Erdos651.PohoataZakharovTheoremOneOne

theorem hasErdosSzekeresNumber_three (n : ℕ) : Erdos651.HasErdosSzekeresNumber 3 n

theorem erdos_651_subexponential :
    Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber 3)

theorem erdos_651_disproved : ¬ Erdos651.Erdos651Claim
```

and [JSP527/PZ/Dimensions.lean](JSP527/PZ/Dimensions.lean) extends all of this to every dimension `d ≥ 3` (the catalog's "higher-dimensional" phrasing; Erdős asked about each `k`):

```lean
theorem erdos_651_subexponential_all_dimensions (d : ℕ) :
    Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber (d + 3))

theorem erdos_651_disproved_all_dimensions (d : ℕ) :
    ¬ Erdos651.HasExponentialLowerBound (Erdos651.erdosSzekeresNumber (d + 3))
```

together with the premise-free `k`-indexed forms `erdos_651_subexponential_inv` and `erdos_651_subexponential_inv_all_dimensions` (for every `k`, eventually `f_d(n) ≤ 2^{n/(k+1)}`), which are the forms bound by the local verification contract.

with plby's verbatim definitions: `PohoataZakharovTheoremOneOne` says that for every `ε > 0` and all large `n`, every general-position set in `ℝ³` of size at least `2^{εn}` contains `n` points in convex position; `HasSubexponentialUpperBound f` says that for every `ε > 0`, eventually `f n ≤ 2^{εn}`; `erdosSzekeresNumber 3 n` is the infimum of the forcing thresholds, which the second theorem shows to be attained; and `Erdos651Claim` is the existence of `c > 0` with `(1 + c)^n < f_3(n)` for all large `n`.

The new modules under `JSP527/PZ/` are:

* [Assembly.lean](JSP527/PZ/Assembly.lean): derived from plby's never-built draft (attribution retained): the lifted positive-fraction configuration, separated and uniform cluster families, the disjointness of representative and full-cluster hulls, the generic vertical projection, the cap-union count, the Ramsey scales `pzQuarterRoot`, `pzAboveBelowScale`, `pzSourceScale`, the envelope estimates, and the passage from an envelope certificate to the point-set theorem. Two draft statements that were false as written were repaired (listed in [external-changes.txt](external-changes.txt)).
* [Clusters.lean](JSP527/PZ/Clusters.lean): a large general-position set with generic vertical projection carries `m` two-separated, strongly convex clusters whose representatives form a projected convex chain with a uniform above/below pattern (Pór–Valtr, Proposition 2.5, Corollary 2.4); the generic affine change of coordinates.
* [Gadgets.lean](JSP527/PZ/Gadgets.lean): Proposition 3.1 applied to every ordered triple of clusters gives the triple gadget family with the containments (4.8) and Proposition 2.1 certificates on every subset of the middle cluster.
* [Extraction.lean](JSP527/PZ/Extraction.lean): the monochromatic triple clique at scale `pzSourceScale n`, the alternating free-set family for either color (the "blue" color uses the reversed clique, which the paper leaves to symmetry), and the eventual forcing statement that discharges the envelope certificate.
* [Main.lean](JSP527/PZ/Main.lean): the headline theorems through plby's bridge lemmas.
* [Dimensions.lean](JSP527/PZ/Dimensions.lean): the passage to higher dimensions. A generic linear projection `ℝ^{d+2} → ℝ^{d+1}` (a direction avoiding the finitely many spans of small subsets) is injective on a finite general-position set and keeps its image in general position, and convex position lifts along any affine map injective on the set; hence `f_{d+2}(n) ≤ max(f_{d+1}(n), d + 3)` (the additive constant is forced: a set of `d + 2` collinear points in `ℝ^{d+2}` is vacuously in general position), and by induction `f_d(n) ≤ max(f_3(n), d + 1)` for `d ≥ 3`, which is subexponential.

The third-party tree is included verbatim under `JSP527/External/` (Apache License 2.0, headers retained) up to the changes listed in [external-changes.txt](external-changes.txt): the module prefix in `import` lines; minimal ports to the pinned Lean 4.34 / Mathlib in `CapRamsey.lean`, `TrihedralGadget.lean` and `Existence.lean` (renamed lemmas, changed argument explicitness, binder ascriptions, one `maxHeartbeats` increase; no statement is weakened); the strengthening of the two projection-family fields of `TrihedralClusterGadget` to all subsets of the middle cluster, filled at the only construction site; and the omission of the draft `PohoataZakharovProof.lean`, replaced by `JSP527/PZ/Assembly.lean`. SHA-256 values of every original file at plby/lean-proofs commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` are in [plby-source-hashes.txt](plby-source-hashes.txt). The formalization credit for the definitions and all the geometric and combinatorial ingredients belongs to those authors; this submission claims only the files under `JSP527/PZ/` (with the derived `Assembly.lean` claimed for its repairs and completion only), the interface change, and the challenge module.

Every fact is proved in Lean; no literature theorem is assumed. All parts use only Mathlib and the pinned dependencies.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness; it avoids rebuilding dependencies.

[Audit.lean](Audit.lean) restates the headline theorems as explicit `example`s (including the unfolded `∀ ε > 0, ∀ᶠ n, f_3(n) ≤ 2^{εn}` form) and prints the axioms of the headline theorems, the main new lemmas and the imported third-party theorems.

**Axioms.** Every audited theorem depends on exactly the three standard axioms of Lean's core logic used throughout Mathlib, and on nothing else:

| Theorem | Axioms |
| --- | --- |
| `PohoataZakharov.erdos_651_subexponential_inv`, `erdos_651_subexponential` | `propext`, `Classical.choice`, `Quot.sound` |
| `PohoataZakharov.theorem_one_one` | `propext`, `Classical.choice`, `Quot.sound` |
| `PohoataZakharov.hasErdosSzekeresNumber_three` | `propext`, `Classical.choice`, `Quot.sound` |
| `PohoataZakharov.erdos_651_disproved` | `propext`, `Classical.choice`, `Quot.sound` |
| `PohoataZakharov.erdos_651_subexponential_all_dimensions`, `erdos_651_subexponential_inv_all_dimensions`, `erdos_651_disproved_all_dimensions`, `exists_generic_projection`, `erdosSzekeresNumber_add_three_le` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos651.pohoataZakharov_forces_eventually`, `exists_tripleGadgetFamily`, `exists_uniformSeparatedClusters`, `exists_generic_image`, `PohoataZakharovEnvelopeCertificate.theoremOneOne`, `AlternatingFreeFamily.containsConvexSubset_of_sourceEnvelope` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos651.pohoata_zakharov_prop_three_one`, `pohoata_zakharov_prop_two_one_three_edges`, `exists_orderedStrongPositiveFractionConfiguration`, `exists_twoSeparated_subclusters`, `alternatingBlock_hulls_disjoint`, `exists_alternating_free_subsets_of_monochromatic_clique`, `hasErdosSzekeresNumber_three`, `pohoataZakharovTheoremOneOne_imp_subexponential`, `erdos_651_of_pohoata_zakharov`, `not_erdos_651` (third-party) | `propext`, `Classical.choice`, `Quot.sound` |

No project axiom is declared, no `sorry` or `admit` occurs outside the intentionally `sorry`-ed comparator challenge, `native_decide` is not used, and the headline theorems are premise-free. The published selection rules describe Lean verification as a pass/fail entry threshold without naming an axiom policy; this repository's verification-record schema records an explicit axiom list per theorem, which is why the lists are declared here in full.

**Comparator challenge.** [Challenge.lean](Challenge.lean) is a self-contained challenge module (imports only Mathlib; statements proved by `sorry`) restating plby's definitions verbatim together with the eight headline theorems, with [Comparator/PohoataZakharov.json](Comparator/PohoataZakharov.json) naming `JSP527.PZ.Dimensions` (which imports `JSP527.PZ.Main`) as the solution module and the three standard axioms as the only permitted ones. A textual identity check of every challenge definition and statement against the solution is recorded in [verification.txt](verification.txt). Running Comparator itself requires its Linux sandbox tooling and was not performed locally.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process; no curator signatures or attestations are fabricated.

## Attribution and submission status

The mathematics is due to C. Pohoata and D. Zakharov, "Convex polytopes from fewer points", arXiv:2208.04878 (2022), building on the positive-fraction Erdős–Szekeres theorem of Bárány–Valtr and Pór–Valtr, on Kirchberger's theorem, on Dilworth's theorem and on hypergraph Ramsey theory; the problem is Erdős's (1997). None of these papers was used as a proof assumption. The Lean code under `JSP527/PZ/` was prepared with Claude Code (Claude Fable 5.1 and Claude Opus) assistance; the contribution sought is the completion of the formalization of Theorem 1.1, not a new mathematical discovery.

At the time of submission no other pull request or issue in this repository was found that submits or registers a Lean proof for JSP-000527. No first-formalization priority or entitlement to an award is claimed. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000527-cyr-A`, identity confirmation pending, for the files under `JSP527/PZ/`, the documented changes to the third-party tree, and the challenge module only. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT); the files under `JSP527/External/` and `JSP527/PZ/Assembly.lean` retain their original Apache License 2.0 notices.
