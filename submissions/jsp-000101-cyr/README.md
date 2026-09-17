# JSP-000101: f(4) = 2 for the minimum-degree threshold forcing a C₄ (Erdős #85, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000101](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000101) / [Erdős Problem #85](https://www.erdosproblems.com/85): for `n ≥ 4` let `f(n)` be minimal such that every graph on `n` vertices with minimum degree `≥ f(n)` contains a `C₄`; is `f(n+1) ≥ f(n)` for all large `n`? The component formalized here is the remark recorded on the problem page, **"It is easy to check that `f(4) = 2`"**: the perfect matching on four vertices has minimum degree `1` and no `C₄`, while a graph on four vertices with minimum degree `≥ 2` has a complement that is a matching, which forces a `4`-cycle. The monotonicity question and the bounds `f(n) < √n + 1`, `f(n) = (1+o(1))√n` are **not** claimed.

## Statements

Graphs are Mathlib's `SimpleGraph`, `minDegree` is Mathlib's, and "`G` contains a `C₄`" is Mathlib's `cycleGraph 4 ⊑ G` (`SimpleGraph.IsContained`, an injective homomorphism, i.e. a not-necessarily-induced `4`-cycle). `f` is defined in this package in the shape of the formal-conjectures statement of the problem (namespace `Erdos85`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  sInf {k : ℕ | ∀ G : SimpleGraph (Fin n), k ≤ G.minDegree → cycleGraph 4 ⊑ G}

def perfectMatching : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun a b => (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3))

theorem f_four : f 4 = 2

theorem f_four_le : f 4 ≤ 2

theorem cycleGraph_four_isContained_of_two_le_minDegree (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] (h : 2 ≤ G.minDegree) : cycleGraph 4 ⊑ G

theorem perfectMatching_witness :
    1 ≤ perfectMatching.minDegree ∧ ¬ cycleGraph 4 ⊑ perfectMatching

theorem two_le_f_four : 2 ≤ f 4
```

`f n` is the page's `f(n)`, an `sInf` over the admissible thresholds (nonempty: `k = n` belongs vacuously, since no graph on `n` vertices has minimum degree `n`; the third theorem shows `2` belongs for `n = 4` and the fourth shows `1` does not). The first theorem (a closed statement, no binders) is the page's value; the second and fifth are its two halves; the third is the combinatorial core; the fourth is the lower-bound witness. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

If `G` on four vertices has minimum degree `≥ 2`, every vertex has at most one non-neighbour, so the non-edges form a partial matching; ordering the four vertices `a, c, b, d` so that consecutive ones are never matched by a non-edge gives the `4`-cycle `a–c–b–d–a` in `G`, and mapping `Fin 4` to `(a, c, b, d)` is an injective homomorphism from `cycleGraph 4`. The perfect matching `{0,1}, {2,3}` has all degrees `1`; a copy of `C₄` would map two consecutive edges of the cycle to edges of the matching sharing a vertex, forcing two distinct cycle vertices to coincide. Hence `2 ≤ f(4) ≤ 2`.

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

The problem is Erdős's. The value `f(4) = 2` is the folklore check recorded on the problem page. The Lean development is written from scratch in this package; the definition of `f` follows the shape of the formal-conjectures statement of the problem so that the two are comparable, but no code is imported from it.

This is a scoped component of a catalog record whose status is Open; it is submitted under the fleet convention "solved (scoped component)" and does not claim the monotonicity question. The contribution sought is formalization, not a new mathematical result; the mathematical content is a small exact value. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000101-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
