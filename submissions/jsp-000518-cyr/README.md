# JSP-000518: distinct degrees in induced subgraphs of Ramsey graphs

This package submits a Lean formalization for intake and eligibility review. It addresses [JSP-000518](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000518): if a graph has neither large cliques nor large independent sets, must a large induced subgraph have many distinct vertex degrees? This is [Erdős Problem #637](https://www.erdosproblems.com/637) (Erdős–Faudree–Sós). The catalog credits its resolution to Bukh–Sudakov (2007) and Jenssen–Keevash–Long–Yepremyan (2020).

## What is proved, and what already existed

A `C`-Ramsey graph on `n` vertices has no clique or independent set of size `C·log₂ n`. Bukh and Sudakov proved that such a graph has an induced subgraph on `≫ n` vertices with `≫ n^{1/2}` distinct degrees; this is the statement printed on the problem page and it is fully formalized by Codex / GPT-5.6 Sol in [plby/lean-proofs](https://github.com/plby/lean-proofs) (`Erdos637.erdos_637`, replayed here and credited). Jenssen, Keevash, Long and Yepremyan (*Distinct degrees in induced subgraphs*, Proc. AMS 148 (2020) 3835–3846, arXiv:1910.01361) proved that some induced subgraph has `≫_C n^{2/3}` distinct degrees, with no restriction on the number of vertices of that subgraph (as the problem page notes). The JKLY theorem is therefore not a strengthening of the Bukh–Sudakov statement but incomparable with it: a better exponent, without the `≫ n` vertex-count conclusion; it does not by itself imply the statement printed on the problem page, and the catalog question ("must a *large* induced subgraph have many distinct vertex degrees?") is answered in this package only by the reused `Erdos637.erdos_637`. The catalog cites both papers; the JKLY theorem had no Lean proof. This submission formalizes JKLY Theorems 1 and 2. Eligibility disclosure (added 2026-09-17 after an independent hard-gate re-audit): the theorem matching the original statement is third-party reused work; the submitter's own new theorem is the second result cited by the entry.

## Statement and proof

[JSP518/JKLY/Main.lean](JSP518/JKLY/Main.lean) proves

```lean
theorem jkly_distinct_degrees (C : ℝ) (hC : 0 < C) : ∃ β : ℝ, 0 < β ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
      ∃ W : Finset (Fin n), β * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ Erdos637.numDistinctDegrees G W

theorem jkly_theorem2 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
        ∀ (G : SimpleGraph V) (U : Finset V), Diverse G δ U →
          (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) ≤ U.card →
            ∃ W : Finset V,
              c * (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) ≤ Erdos637.numDistinctDegrees G W
```

together with the premise-free form `jkly_distinct_degrees_nat (k : ℕ)` (Ramsey constant `k + 1`), which is the form bound by the local verification contract. Here `Erdos88.RamseyFree C G`, `Erdos637.numDistinctDegrees G W` (the number of distinct degrees of the subgraph induced on `W`) and `Erdos637.neighborhoodDiff` are plby's verbatim definitions, and `Diverse G δ U` says that any two distinct vertices of `U` have neighbourhoods differing in at least `δ·|V|` vertices.

The proof follows the paper. All probability is finite: a random induced subgraph is a weighted sum over `Finset V`.

* [JKLY/ProductBernoulli.lean](JSP518/JKLY/ProductBernoulli.lean): the product Bernoulli measure with vertex-dependent probabilities `p_v`, its expectation and variance, linear statistics, Markov and Chebyshev inequalities.
* [JKLY/Counting.lean](JSP518/JKLY/Counting.lean): the Erdős–Littlewood–Offord count for `±1` coefficients over a ground set, window counting for functions with increments ≥ s, a Cauchy–Schwarz bound relating distinct degrees to equal-degree pairs, and close-pair counting under 1-separation.
* [JKLY/Turan.lean](JSP518/JKLY/Turan.lean): Turán-type independent sets of size `≥ |S|²/(|S| + 4e)` and `≥ n/(1 + 2d)` (constant-density sampling and endpoint deletion).
* [JKLY/Anticoncentration.lean](JSP518/JKLY/Anticoncentration.lean): Proposition 5, the anticoncentration bound `P(|W ∩ P| − |W ∩ Q| = t) ≤ C/√|P ∪ Q|` for `p_v ∈ [0.1, 0.9]`, by the mixture decomposition to the `p = 1/2` case and the central binomial bound.
* [JKLY/Relaxation.lean](JSP518/JKLY/Relaxation.lean): Lemma 4, the continuous relaxation: pairwise 1-separated expected degrees and diversity give an induced subgraph with `≥ |U'|/(4 + 160C/√δ)` distinct degrees.
* [JKLY/RandomVector.lean](JSP518/JKLY/RandomVector.lean): Lemma 7, the random probability vector `p = 1/2 + Σ m_u σ_u / N` with uniform integer `m_u`, truncation to `[0.1, 0.9]`, the step bound `δ/2`, and Turán on the graph of bad pairs, yielding `U' ⊆ U` with `|U'| ≥ (δ²/1460)|U|` and 1-separated expected degrees.
* [JKLY/Diversity.lean](JSP518/JKLY/Diversity.lean): the passage from Ramsey graphs to diverse sets through plby's Kwan–Sudakov richness lemma (`Erdos88.ksssLemma44`) at exponent `1/4` and Turán.
* [JKLY/Main.lean](JSP518/JKLY/Main.lean): the assembly with explicit constants.

The third-party modules are included verbatim under `JSP518/External/` (Apache License 2.0, headers retained; the only change is the module prefix in `import` lines, listed in [external-changes.txt](external-changes.txt)): plby's `Erdos637` and its import cone (`Erdos88/{Foundations,Probability,Richness,FiniteES}`, `Erdos920/{Sampling,Averaging}`, `Erdos487`, `Erdos202`, `Erdos447`, `Util/Ramsey`). SHA-256 values of every original file at plby/lean-proofs commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` are in [plby-source-hashes.txt](plby-source-hashes.txt). The formalization credit for the Bukh–Sudakov theorem and the Kwan–Sudakov richness lemma belongs to those authors; this submission claims only the files under `JSP518/JKLY/` and the challenge module.

Every fact is proved in Lean; no literature theorem is assumed. All parts use only Mathlib and the pinned dependencies.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness; it avoids rebuilding dependencies.

[Audit.lean](Audit.lean) restates the headline theorems as explicit `example`s and prints the axioms of the headline theorems, the main lemmas and the imported third-party theorems.

**Axioms.** Every audited theorem depends on exactly the three standard axioms of Lean's core logic used throughout Mathlib, and on nothing else:

| Theorem | Axioms |
| --- | --- |
| `JKLY.jkly_distinct_degrees_nat`, `jkly_distinct_degrees`, `jkly_theorem2` | `propext`, `Classical.choice`, `Quot.sound` |
| `JKLY.lemma7`, `lemma4`, `antic_bound`, `exists_diverse_subgraph_of_ramseyFree`, `exists_indepSet_subset_card_ge_of_edges`, `PB.chebyshev_sq_bound`, `card_filter_shift_le` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos637.erdos_637`, `Erdos88.ksssLemma44` (third-party) | `propext`, `Classical.choice`, `Quot.sound` |

No project axiom is declared, no `sorry` or `admit` occurs outside the intentionally `sorry`-ed comparator challenge, `native_decide` is not used, and no hypothesis beyond `0 < C` (resp. `0 < δ ≤ 1`, the ranges of the theorems; the root `jkly_distinct_degrees_nat` is premise-free) appears. One declaration (`JKLY.lemma7`) raises the elaborator's `maxHeartbeats` budget; this affects elaboration time only. The published selection rules describe Lean verification as a pass/fail entry threshold without naming an axiom policy; this repository's verification-record schema records an explicit axiom list per theorem, which is why the lists are declared here in full.

**Comparator challenge.** [Challenge.lean](Challenge.lean) is a self-contained challenge module (imports only Mathlib; statements proved by `sorry`) restating the definitions verbatim together with the three JKLY theorems and, credited, plby's `Erdos637.erdos_637`, with [Comparator/JKLY.json](Comparator/JKLY.json) naming `JSP518.JKLY.Main` as the solution module and the three standard axioms as the only permitted ones. A textual identity check of every challenge definition and statement against the solution is recorded in [verification.txt](verification.txt). Running Comparator itself requires its Linux sandbox tooling and was not performed locally.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process; no curator signatures or attestations are fabricated.

## Attribution and submission status

The mathematics is due to M. Jenssen, P. Keevash, E. Long and L. Yepremyan, "Distinct degrees in induced subgraphs", Proc. Amer. Math. Soc. 148 (2020), 3835–3846, building on B. Bukh and B. Sudakov, "Induced subgraphs of Ramsey graphs with many distinct degrees", J. Combin. Theory Ser. B 97 (2007), 612–619, and on the diversity lemma of M. Kwan and B. Sudakov; the problem is Erdős–Faudree–Sós's. None of these papers was used as a proof assumption. The Lean code under `JSP518/JKLY/` was prepared with Claude Code (Claude Fable 5.1 and Claude Opus) assistance; the contribution sought is the formalization of the JKLY theorem, not a new mathematical discovery.

At the time of submission no other pull request or issue in this repository was found that submits or registers a Lean proof for JSP-000518. No first-formalization priority or entitlement to an award is claimed. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000518-cyr-A`, identity confirmation pending, for the files under `JSP518/JKLY/` and the challenge module only. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT); the files under `JSP518/External/` retain their original Apache License 2.0 notices.
