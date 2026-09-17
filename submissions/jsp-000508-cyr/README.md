# JSP-000508: the Tutte–Zykov theorem — triangle-free graphs of every chromatic number (Erdős #627, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000508](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000508) / [Erdős Problem #627](https://www.erdosproblems.com/627): if `f(n)` is the maximum of `χ(G)/ω(G)` over graphs on `n` vertices, does `lim f(n)/(n/(log₂ n)²)` exist? The component formalized here is the theorem recorded on the problem page, **"Tutte and Zykov independently proved that for every `k` there is a graph with `ω(G) = 2` and `χ(G) = k`"**, proved with the shift graph: for every `k` there is a finite triangle-free graph with chromatic number exactly `k`, and for `k ≥ 2` one with an edge (clique number exactly `2`). Erdős's constructions with `χ ≫ n^{1/2}/log n`, the asymptotics `f(n) ≍ n/(log₂ n)²`, the limit question and the Araujo–Filipe–Miyazaki results are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos627`, [Proof/Shift.lean](Proof/Shift.lean)); clique-freeness and the chromatic number are Mathlib's:

```lean
def ShiftVertex (N : ℕ) : Type := {p : Fin N × Fin N // p.1 < p.2}

def shiftGraph (N : ℕ) : SimpleGraph (ShiftVertex N) :=
  SimpleGraph.fromRel (fun p q => p.1.2 = q.1.1)

theorem exists_cliqueFree_chromatic (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.CliqueFree 3 ∧ G.chromaticNumber = (k : ℕ∞)

theorem exists_cliqueNum_two_chromatic (k : ℕ) (hk : 2 ≤ k) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.CliqueFree 3 ∧ (∃ u v, G.Adj u v) ∧ G.chromaticNumber = (k : ℕ∞)

theorem shiftGraph_cliqueFree (N : ℕ) : (shiftGraph N).CliqueFree 3

theorem shiftGraph_chromaticNumber (k : ℕ) : (shiftGraph (2 ^ k)).chromaticNumber = (k : ℕ∞)

theorem shiftGraph_cliqueNum (k : ℕ) (hk : 2 ≤ k) : (shiftGraph (2 ^ k)).cliqueNum = 2
```

The shift graph on `{0, …, N−1}` has as vertices the ordered pairs `(i, j)` with `i < j`, with `(i, j)` adjacent to `(j, l)`. The first theorem is the Tutte–Zykov statement for every `k`; the second adds an edge (so the clique number is exactly `2`) for `k ≥ 2`; the third and fourth are the two properties of the witness (`χ = ⌈log₂ N⌉` in general; here `N = 2^k`); the fifth states `ω = 2` literally with Mathlib's `cliqueNum`. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Triangle-free: three mutually adjacent pairs would give `i < j < l < i`. Upper bound `χ ≤ k` on `2^k` points: colour `(i, j)` by the highest binary digit `h` in which `i` and `j` differ (`h < k`); since `i < j`, the digit `h` of `i` is `0` and that of `j` is `1`, so `(i, j)` and `(j, l)` cannot share the colour `h`. Lower bound `χ ≥ k`: given a proper colouring with `m` colours, let `A_i` be the set of colours of the pairs `(i, j)` with `j > i`; for `i < j` the colour of `(i, j)` lies in `A_i` but not in `A_j` (every `(j, l)` is adjacent to `(i, j)`), so `i ↦ A_i` is injective from `2^k` points into the `2^m` subsets of the colours, hence `k ≤ m`. For `k ≥ 2` the pairs `(0, 1)` and `(1, 2)` are adjacent.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's (Er61d, Er67c, Er69b). The theorem is due independently to W. T. Tutte (writing as Blanche Descartes, *A three colour problem*, Eureka 9 (1947), and *Solution to advanced problem 4526*, Amer. Math. Monthly 61 (1954)) and A. A. Zykov (*On some properties of linear complexes*, Mat. Sbornik 24 (1949); cited on the page as [Zy52]); the shift-graph proof formalized here is the standard one. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000508-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
