# JSP-000841: the Erdős–Gallai value f₃(n) = ⌊(n − 1)²/4⌋ + 2 (Erdős #1011, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000841](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000841) / [Erdős Problem #1011](https://www.erdosproblems.com/1011): let `f_r(n)` be the least number of edges such that every graph on `n` vertices with at least `f_r(n)` edges and chromatic number at least `r` contains a triangle; the problem asks to determine `f_r(n)`. The component formalized here is the value recorded on the problem page for `r = 3`, due to Erdős and Gallai: **`f₃(n) = ⌊(n − 1)²/4⌋ + 2` for all `n ≥ 5`**. The values `f_r(n)` for `r ≥ 4` (Ren–Wang–Wang–Yang's `f₄`, Simonovits's asymptotics) are **not** claimed.

## Statements

All definitions are our own, on top of Mathlib's `SimpleGraph` (namespace `Erdos1011`, [Proof/Defs.lean](Proof/Defs.lean)). Chromatic number at least `3` is rendered as "not `2`-colourable", `¬ G.Colorable 2`, which is equivalent to `3 ≤ G.chromaticNumber` (`not_colorable_two_iff`); a triangle-free graph is `G.CliqueFree 3`.

```lean
noncomputable def f3 (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.Colorable 2 → m ≤ G.edgeSet.ncard → ¬ G.CliqueFree 3}
```

[Proof/Main.lean](Proof/Main.lean) proves:

```lean
theorem f3_eq (n : ℕ) (hn : 5 ≤ n) : f3 n = (n - 1) ^ 2 / 4 + 2

theorem edges_le_of_cliqueFree_of_not_colorable (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) (hb : ¬ G.Colorable 2) : G.edgeSet.ncard ≤ (n - 1) ^ 2 / 4 + 1

theorem exists_extremal (n : ℕ) (hn : 5 ≤ n) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ ¬ G.Colorable 2 ∧
      G.edgeSet.ncard = (n - 1) ^ 2 / 4 + 1
```

The first theorem is the Erdős–Gallai value; `n ≥ 5` is exactly the range on which the formula is meaningful, since a triangle-free graph of chromatic number at least `3` contains a `5`-cycle (for `n ≤ 4` no such graph exists, every threshold works vacuously, and the infimum is `0`). The second theorem is the upper bound for every `n` (vacuous below `5`), the third the extremal graph. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Upper bound ([Proof/OddCycle.lean](Proof/OddCycle.lean), [Proof/ShortestOddCycle.lean](Proof/ShortestOddCycle.lean), [Proof/Counting.lean](Proof/Counting.lean)): a graph all of whose closed walks have even length is `2`-colourable (colour by the parity of the distance to a representative of each component), so a non-`2`-colourable graph has an odd closed walk, and one of minimal odd length is a cycle. Let `C` be an odd cycle of minimal length `m`; triangle-freeness gives `m ≥ 5`. `C` is chordless (a chord would cut it into two cycles with lengths summing to `m + 2`, one odd and shorter), and a vertex outside `C` has at most two neighbours on `C` (two neighbours cut `C` into arcs; the arc closing to an odd cycle through the vertex must have length at least `m − 2`, so the other arc has length exactly `2`, and three neighbours pairwise at arc-distance `2` cannot exist on an odd cycle of length at least `5`). Counting edges by the number of endpoints on `C`: `m` inside, at most `2(n − m)` between `C` and the rest, and at most `⌊(n − m)²/4⌋` inside the rest by Mantel's theorem (Mathlib's Turán bound). For odd `m ≥ 5` this is at most `⌊(n − 1)²/4⌋ + 1`. Extremal graph ([Proof/Extremal.lean](Proof/Extremal.lean)): with `a = ⌊(n − 1)/2⌋`, the complete bipartite graph between `{0, …, a − 1}` and `{a, …, n − 2}` minus the edge `{0, a}`, plus the vertex `n − 1` joined to `0` and `a`; it is triangle-free, contains a `5`-cycle, and has `a(n − 1 − a) + 1 = ⌊(n − 1)²/4⌋ + 1` edges.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definition of `f3` and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definition and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all three theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's; the value `f₃(n) = ⌊(n − 1)²/4⌋ + 2` is due to P. Erdős and T. Gallai (P. Erdős, *On a theorem of Rademacher–Turán*, Illinois J. Math. 6 (1962), 122–127; the standard shortest-odd-cycle argument is the one formalized). Mantel's theorem is used from Mathlib (Turán's theorem). The later results on `f_r(n)` for `r ≥ 4` are not formalized. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the open questions. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000841-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
