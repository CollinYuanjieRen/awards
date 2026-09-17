# JSP-000462: the odd-cycle Turán bound ⌊n²/4⌋ ≤ ex(n; C₂ₖ₊₁) and Mantel's equality (Erdős #572, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000462](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000462) / [Erdős Problem #572](https://www.erdosproblems.com/572): show that `ex(n; C_{2k}) ≫ n^{1+1/k}` for `k ≥ 3`. The component formalized here is the remark recorded on the problem page, **"It is easy to see that `ex(n; C_{2k+1}) = ⌊n²/4⌋` for any `k ≥ 1` (and `n > 2k+1`) (since no bipartite graph contains an odd cycle)"**, in the part that its parenthetical proves: the lower bound `⌊n²/4⌋ ≤ ex(n; C_{2k+1})` for every `n` and every `k ≥ 1`, witnessed by the balanced complete bipartite graph, its general form for every non-bipartite `H`, and the exact equality `ex(n; C₃) = ⌊n²/4⌋` (Mantel's theorem, `k = 1`). The open even-cycle conjecture, the Erdős–Klein, Bondy–Simonovits, Benson and Lazebnik–Ustimenko–Woldar results, and the upper bound `ex(n; C_{2k+1}) ≤ ⌊n²/4⌋` for `k ≥ 2` (which needs `n` large relative to `k` and is not elementary) are **not** claimed.

## Statements

Every object is Mathlib's: `extremalNumber n H` is the maximum number of edges of an `H`-free simple graph on `Fin n`, `cycleGraph m` the cycle on `Fin m`, `turanGraph n 2` the balanced complete bipartite graph on `Fin n` (adjacency `v % 2 ≠ w % 2`), `Free` and `Colorable` the containment and colouring predicates; `n ^ 2 / 4` is natural-number division, i.e. `⌊n²/4⌋` (namespace `Erdos572`, [Proof/Main.lean](Proof/Main.lean) and [Proof/Witness.lean](Proof/Witness.lean)):

```lean
theorem le_extremalNumber_oddCycle (n k : ℕ) :
    n ^ 2 / 4 ≤ extremalNumber n (cycleGraph (2 * k + 3))

theorem le_extremalNumber_oddCycle' (n k : ℕ) (hk : 1 ≤ k) :
    n ^ 2 / 4 ≤ extremalNumber n (cycleGraph (2 * k + 1))

theorem le_extremalNumber_of_not_colorable_two (n : ℕ) {W : Type*} (H : SimpleGraph W)
    (h : ¬ H.Colorable 2) : n ^ 2 / 4 ≤ extremalNumber n H

theorem extremalNumber_cycleGraph_three (n : ℕ) : extremalNumber n (cycleGraph 3) = n ^ 2 / 4

theorem turanGraph_two_colorable (n : ℕ) : (turanGraph n 2).Colorable 2

theorem cycleGraph_odd_free_turanGraph_two (n k : ℕ) :
    (cycleGraph (2 * k + 3)).Free (turanGraph n 2)
```

The first theorem (hypothesis-free; `C_{2k+3}` runs over all odd cycles of length at least `3`) is the page's lower bound; the second restates it with the page's indexing `k ≥ 1`; the third is its general form for every non-bipartite `H`; the fourth is the exact equality for `k = 1`; the last two are the two facts about the witness: the balanced complete bipartite graph is `2`-colourable and therefore contains no odd cycle. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Colouring `v ↦ v mod 2` is a proper `2`-colouring of `turanGraph n 2`. An odd cycle has chromatic number `3` (Mathlib), so it is not `2`-colourable, and a copy of a non-`2`-colourable graph inside a `2`-colourable one would pull the colouring back; hence `turanGraph n 2` contains no odd cycle and no non-bipartite `H`. Its edge count is `⌊n²/4⌋` (Mathlib's `turanNumber_two`), which is therefore at most `ex(n; H)`. For `k = 1`, `C₃` is the complete graph on three vertices, so `C₃`-free graphs are triangle-free and Mantel's theorem (Mathlib's Turán bound with `r = 2`) gives at most `⌊n²/4⌋` edges.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the Mathlib definitions used and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's (Er64c, Er71, Er74c). The lower bound is the folklore observation recorded on the problem page (the balanced complete bipartite graph is odd-cycle-free); the `k = 1` equality is Mantel's theorem (1907), whose upper bound is taken from Mathlib's Turán development. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's conjecture. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000462-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
