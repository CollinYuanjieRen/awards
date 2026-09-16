# JSP-000895: three-uniform hypergraphs without small dense configurations

This package submits a Lean formalization for intake and eligibility review. It addresses [JSP-000895](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000895): how many edges can a three-uniform hypergraph have while excluding configurations with a prescribed vertex count and two fewer edges? This is [Erdős Problem #1076](https://www.erdosproblems.com/1076) (Brown–Erdős–Sós), whose resolution the catalog credits to Bohman–Warnke (2019) and Glock–Kühn–Lo–Osthus (2020).

## Two readings, and which one is proved

The problem page writes: for `k ≥ 5` let `𝓕_k` be the family of all 3-uniform hypergraphs with `k` vertices and `k − 2` edges; is `ex₃(n, 𝓕_k) ~ n²/6`? Read literally, one configuration size at a time, this is **false**: for `k = 5` the constant is `1/5` (Glock 2019), and the existing formalization `Erdos1076.not_erdos_1076` in [plby/lean-proofs](https://github.com/plby/lean-proofs) disproves the per-`k` statement. The result that the page marks as proved, and that Bohman–Warnke and Glock–Kühn–Lo–Osthus actually establish (the page itself calls it "essentially a weaker version of [207]"), is the **locally sparse** reading: forbid every `j`-vertex, `(j − 2)`-edge configuration for all `4 ≤ j ≤ k` simultaneously; then the extremal number is `(1/6 + o(1)) n²` for every `k`. This submission formalizes that theorem.

## Statement and proof

[JSP895/Assembly.lean](JSP895/Assembly.lean) proves `Erdos1076Sparse.erdos_1076_locally_sparse_of_le`:

```lean
theorem erdos_1076_locally_sparse_of_le (k : ℕ) (hk : 4 ≤ k) :
    (∀ n : ℕ, 3 * exLe k n ≤ n.choose 2) ∧
      (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * exLe k n) ∧
      Tendsto (fun n : ℕ => (exLe k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6))
```

together with the premise-free root form `erdos_1076_locally_sparse (k : ℕ)`, which states the same conjunction for the configuration size `k + 4` (so that no hypothesis is needed), and the corollary `exLe_isEquivalent`: `(fun n => (exLe k n : ℝ)) ~[atTop] (fun n => n² / 6)` in Mathlib's `Asymptotics.IsEquivalent`. Here, in [JSP895/Bridge.lean](JSP895/Bridge.lean), a three-uniform hypergraph on `Fin n` is a `Finset` of 3-element subsets; `FkFree j G` says that no `j − 2` triples of `G` span at most `j` vertices (equivalently, `G` contains no member of `𝓕_j`, isolated vertices being allowed in a configuration); `FamilyFree k G` says `FkFree j G` for all `4 ≤ j ≤ k`; and `exLe k n` is the maximum number of triples of a `FamilyFree k` hypergraph on `Fin n`, i.e. `ex₃(n, 𝓕_4 ∪ ⋯ ∪ 𝓕_k)`. [JSP895/Statement.lean](JSP895/Statement.lean) collects the headline theorems and re-exports the third-party disproof of the literal reading next to them.

The upper bound is elementary: `FkFree 4` means two distinct triples share at most one vertex, so their pair sets are disjoint and `3 · |G| ≤ C(n, 2)`. The lower bound is the deep part and is **not our work**: for `k ≥ 4` the theorem `Erdos207.erdos_207` (Kwan–Sah–Sawhney–Simkin, *High-girth Steiner triple systems*, Ann. of Math. 200 (2024)) gives, for all large admissible `m ≡ 1, 3 (mod 6)`, a Steiner triple system on `Fin m` in which every `2 ≤ j ≤ k − 2` triples span at least `j + 3` vertices. Such a system is `FamilyFree k` with exactly `C(m, 2)/3` triples (`three_mul_card_of_isSteiner`); choosing the largest admissible `m ∈ [n − 3, n]` and transporting along `Fin.castLE` gives `C(n − 3, 2) ≤ 3 · exLe k n`. The two binomial bounds squeeze `exLe k n / n²` to `1/6`.

`Erdos207.erdos_207` is the existing public formalization by Codex / GPT-5.6 Sol in plby/lean-proofs at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` ([Erdos207.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos207.lean) and the directory `Erdos207/`, 1518 modules, Mathlib-only). It is included verbatim under `JSP895/External/` (Apache License 2.0, headers retained; the only change is the module prefix in `import` lines, listed in [external-changes.txt](external-changes.txt)), together with `Erdos1076.lean` (the literal-reading disproof; three identifiers renamed for the pinned Mathlib, also listed there), so that the assembled theorem is reproducible from this directory alone. SHA-256 values of every original file at the pinned commit are in [plby-source-hashes.txt](plby-source-hashes.txt). The formalization credit for the high-girth Steiner systems and for the literal-reading disproof belongs to those authors; this submission claims only `Bridge.lean`, `Assembly.lean`, `Statement.lean` and the challenge module.

Every fact is proved in Lean; no literature theorem is assumed. Both parts use only Mathlib and the pinned dependencies.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness; it avoids rebuilding dependencies. The 1518-module Steiner-system development takes some hours to compile.

[Audit.lean](Audit.lean) restates the main theorem as an explicit `example` and prints the axioms of the headline theorems, the imported Steiner-system theorem and the imported disproof.

**Axioms.** Every audited theorem depends on exactly the three standard axioms of Lean's core logic used throughout Mathlib, and on nothing else:

| Theorem | Axioms |
| --- | --- |
| `Erdos1076Sparse.three_mul_exLe_le_choose` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1076Sparse.choose_le_three_mul_exLe` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1076Sparse.erdos_1076_locally_sparse_of_le` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1076Sparse.erdos_1076_locally_sparse` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1076Sparse.exLe_isEquivalent` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1076Sparse.statement_locally_sparse`, `statement_locally_sparse'`, `statement_isEquivalent`, `statement_literal_reading_false` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos207.erdos_207` (third-party) | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1076.not_erdos_1076` (third-party) | `propext`, `Classical.choice`, `Quot.sound` |

No project axiom is declared, no `sorry` or `admit` occurs outside the intentionally `sorry`-ed comparator challenge, `native_decide` is not used, and no hypothesis beyond `4 ≤ k` (the range in which the family `𝓕_{≤k}` is nonempty) appears. The published selection rules describe Lean verification as a pass/fail entry threshold without naming an axiom policy; this repository's verification-record schema records an explicit axiom list per theorem, which is why the lists are declared here in full.

**Comparator challenge.** [Challenge.lean](Challenge.lean) is a self-contained challenge module (imports only Mathlib; statements proved by `sorry`) restating the definitions verbatim and the three headline theorems, with [Comparator/Erdos1076Sparse.json](Comparator/Erdos1076Sparse.json) naming `JSP895.Statement` as the solution module and the three standard axioms as the only permitted ones. A textual identity check of every challenge definition and statement against the solution is recorded in [verification.txt](verification.txt). Running Comparator itself requires its Linux sandbox tooling and was not performed locally.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process; no curator signatures or attestations are fabricated.

## Attribution and submission status

The mathematics is due to W. G. Brown, P. Erdős and V. T. Sós (the problem and the `k = 4` case), T. Bohman and L. Warnke, "Large girth approximate Steiner triple systems", J. London Math. Soc. 100 (2019), 895–913, S. Glock, D. Kühn, A. Lo and D. Osthus, "On a conjecture of Erdős on locally sparse Steiner triple systems", Combinatorica 40 (2020), 363–403, and, for the exact Steiner systems used here, M. Kwan, A. Sah, M. Sawhney and M. Simkin, "High-girth Steiner triple systems", Ann. of Math. 200 (2024), 1059–1156; the failure of the literal reading is due to S. Glock, "Triple systems with no three triples spanning at most five points", Bull. London Math. Soc. 51 (2019), 230–236. None of these papers was used as a proof assumption. The bridge Lean code was prepared with Claude Code (Claude Fable 5.1) assistance; the contribution sought is the formalization of the intended theorem's statement and its assembly from the existing Steiner-system formalization, not a new mathematical discovery.

At the time of submission no other pull request or issue in this repository was found that submits or registers a Lean proof for JSP-000895. No first-formalization priority or entitlement to an award is claimed. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000895-cyr-A`, identity confirmation pending, for the bridge and assembly only. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT); the files under `JSP895/External/` retain their original Apache License 2.0 notices.
