# JSP-000117: the double-counting bound 3·#(unit circles through ≥ 3 points) ≤ n(n−1) (Erdős #104, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000117](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000117) / [Erdős Problem #104](https://www.erdosproblems.com/104): given `n` points in the plane, is the number of distinct unit circles containing at least three of them `o(n²)`? The component formalized here is the elementary upper bound recorded on the problem page — **"every pair of points determines at most 2 unit circles, and the claimed bound follows from double counting"**, in the corrected form noted by Harborth and Mengerson, **`n(n−1)/3`** (Erdős wrote `n(n−1)`), proved as `3 · #(unit circles through ≥ 3 points) ≤ n(n−1)`. The `o(n²)` question, Erdős's `≫ n` and Elekes's `≫ n^{3/2}` constructions and the general-position questions are **not** claimed.

## Statements

Points are Mathlib's `EuclideanSpace ℝ (Fin 2)`; a unit circle is identified with its centre `c` and contains `p` iff `dist p c = 1`; the rich-centre predicate and the count are defined in this package (namespace `Erdos104`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def IsRichCenter (P : Finset (EuclideanSpace ℝ (Fin 2))) (c : EuclideanSpace ℝ (Fin 2)) : Prop :=
  3 ≤ (P.filter (fun p => dist p c = 1)).card

noncomputable def unitCircleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {c : EuclideanSpace ℝ (Fin 2) | IsRichCenter P c}

theorem not_exists_unitCircleCount_gt (n : ℕ) :
    ¬ ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧ n * (n - 1) < 3 * unitCircleCount P

theorem three_mul_unitCircleCount_le (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    3 * unitCircleCount P ≤ P.card * (P.card - 1)

theorem richCenters_finite (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    {c : EuclideanSpace ℝ (Fin 2) | IsRichCenter P c}.Finite

theorem exists_two_centers (p q : EuclideanSpace ℝ (Fin 2)) (hpq : p ≠ q) :
    ∃ c₁ c₂ : EuclideanSpace ℝ (Fin 2), ∀ c : EuclideanSpace ℝ (Fin 2),
      dist p c = 1 → dist q c = 1 → c = c₁ ∨ c = c₂

theorem three_mul_card_le_of_rich (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : ∀ c ∈ S, IsRichCenter P c) :
    3 * S.card ≤ P.card * (P.card - 1)
```

`unitCircleCount P` is the number of unit circles containing at least three points of `P` (a `Set.ncard`, honest because the set of such centres is finite by the third theorem). The first theorem (data binder `n`, in negation form) is the bound for every `n`-point set; the second is the direct form; the fourth is the page's "every pair of points determines at most two unit circles"; the fifth is the double-counting core. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

A centre at distance `1` from two distinct points `p, q` lies on both unit circles centred at `p` and `q`, and two distinct circles in the plane meet in at most two points (Mathlib's `EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`), so each pair determines at most two unit circles. Counting incidences between rich circles and ordered pairs of their points: each rich circle carries at least `3 · 2 = 6` ordered pairs, and each of the `n(n−1)` ordered pairs lies on at most two circles, so `6C ≤ 2n(n−1)`. Finiteness of the set of rich centres follows from the same two-circles fact.

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

The problem is Erdős's (Er75h, Er81d, Er83b, Er92e, Er95). The upper-bound argument is Erdős's, with the constant corrected by Harborth and Mengerson (HaMe86), as recorded on the problem page; the two-circles input is Mathlib's. Upstream PR #325 (by another contributor) formalizes Elekes's lower bound, a disjoint scope. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000117-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
