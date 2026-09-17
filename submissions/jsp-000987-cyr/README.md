# JSP-000987: the trivial bound R(K₃, G) ≥ 2n − 1 for connected graphs on n vertices (Erdős #1182, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000987](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000987) / [Erdős Problem #1182](https://www.erdosproblems.com/1182): estimate `f(n)` (the largest edge count of a connected graph `G` on `n` vertices with `R(K₃, G) = 2n − 1`) and `F(n)` (the largest `F` such that every connected graph on `n` vertices with at most `F` edges has `R(K₃, G) = 2n − 1`). The component formalized here is the statement the page records as trivial, **"`R(K₃, G) ≥ 2n − 1` for any connected graph `G` on `n` vertices"**, with `R(K₃, G)` defined as the least `N` such that every red/blue colouring of `K_N` contains a red triangle or a blue copy of `G`, shown finite (at most `r(3, n)`) by Ramsey's theorem, and bounded below by the colouring of `K_{2n−2}` whose red graph is the complete bipartite graph between two parts of size `n − 1`. Chvátal's theorem `R(K₃, T) = 2n − 1` for trees, the consequences `F(n) ≥ n − 1` and `f(n) ≥ F(n)` (whose proof on the page relies on Chvátal's theorem), the Burr–Erdős–Faudree–Rousseau–Schelp and Brandt bounds, the numerical values of `f` and `F` and the `K_m` generalisations are **not** claimed.

## Statements

A red/blue colouring of `K_N` is a Mathlib `SimpleGraph (Fin N)` (red = edges, blue = non-edges); copies are Mathlib's `IsContained` (`⊑`, an injective homomorphism); `ramsey` is the two-colour Ramsey number of our own Ramsey toolbox ([Proof/Defs.lean](Proof/Defs.lean), [Proof/Ramsey.lean](Proof/Ramsey.lean), reused from our JSP-000669 package). Namespace `Erdos1182`, [Proof/TriRamsey.lean](Proof/TriRamsey.lean) and [Proof/Main.lean](Proof/Main.lean):

```lean
def TriRamseyProp (N : ℕ) {W : Type*} (G : SimpleGraph W) : Prop :=
  ∀ R : SimpleGraph (Fin N), ¬ R.CliqueFree 3 ∨ G ⊑ Rᶜ

noncomputable def triRamsey {W : Type*} (G : SimpleGraph W) : ℕ := sInf {N : ℕ | TriRamseyProp N G}

def ConnLowerBound (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.Connected → 2 * n - 1 ≤ triRamsey G

theorem not_exists_connected_triRamsey_lt (n : ℕ) :
    ¬ ∃ G : SimpleGraph (Fin n), G.Connected ∧ triRamsey G < 2 * n - 1

theorem connLowerBound (n : ℕ) : ConnLowerBound n

theorem le_triRamsey_of_connected (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    2 * n - 1 ≤ triRamsey G

theorem not_triRamseyProp_of_connected (n N : ℕ) (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hN : N ≤ 2 * n - 2) : ¬ TriRamseyProp N G

theorem triRamseyProp_ramsey (n : ℕ) (G : SimpleGraph (Fin n)) : TriRamseyProp (ramsey 3 n) G

theorem triRamsey_le_ramsey (n : ℕ) (G : SimpleGraph (Fin n)) : triRamsey G ≤ ramsey 3 n
```

`TriRamseyProp N G` says that every red/blue colouring of `K_N` has a red triangle or a blue copy of `G`, and `triRamsey G` is `R(K₃, G)`, the least such `N`. The first theorem (single data binder `n`, in negation form) says that no connected graph on `n` vertices has `R(K₃, G)` below `2n − 1`; the second is the same bound as the predicate `ConnLowerBound`; the third is its unfolded form; the fourth is the witness statement (every `N ≤ 2n − 2` fails); the last two give finiteness, `R(K₃, G) ≤ r(3, n)`, from Ramsey's theorem. Mathlib's `Connected` includes non-emptiness, so `n ≥ 1` whenever the hypothesis holds. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Let `G` be connected on `n` vertices and `N ≤ 2n − 2`. Split the vertices of `K_N` into `A = {i < n − 1}` and `B = {i ≥ n − 1}`, each of size at most `n − 1`, and colour an edge red exactly when its ends lie in different parts. Any three vertices contain two in the same part, joined by a blue edge, so there is no red triangle; the blue graph is the disjoint union of the cliques on `A` and on `B`. A copy of `G` in the blue graph maps adjacent vertices into the same part, hence, `G` being connected, all of `G` into one part, which has fewer than `n` vertices, contradicting injectivity. So no `N ≤ 2n − 2` works, and since `r(3, n)` works (a red `K₃` or a blue `K_n`, and a blue `K_n` contains a copy of every graph on `n` vertices), the least such `N` is at least `2n − 1`.

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

The problem is due to Burr, Erdős, Faudree, Rousseau and Schelp (Er78, BEFRS80). The bound formalized here is the folklore observation recorded on the problem page. The Ramsey toolbox in [Proof/Defs.lean](Proof/Defs.lean) and [Proof/Ramsey.lean](Proof/Ramsey.lean) is reused from our own JSP-000669 submission. The Lean development is written from scratch in this package and its predecessor.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's questions. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000987-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
