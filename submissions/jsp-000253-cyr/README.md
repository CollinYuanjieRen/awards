# JSP-000253: the lower bound f(N) ≥ ⌈N/2⌉ from the upper half, and the repeated-denominator threshold (Erdős #301, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000253](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000253) / [Erdős Problem #301](https://www.erdosproblems.com/301): with `f(N)` the largest size of `A ⊆ {1, …, N}` admitting no relation `1/a = 1/b₁ + ⋯ + 1/bₖ` with distinct `a, b₁, …, bₖ ∈ A`, estimate `f(N)`; is `f(N) = (1/2 + o(1)) N`? The components formalized here are the two elementary remarks recorded on the problem page: **"The example `A = (N/2, N] ∩ ℕ` shows that `f(N) ≥ N/2`"** (in exact form `f(N) ≥ ⌈N/2⌉`: in the upper half every `1/bᵢ ≥ 1/N` while `1/a < 2/N`, so a relation needs `k ≤ 1`, impossible with distinct elements), and the remark of Cambie and van Doorn that **if solutions with non-distinct `bᵢ` are allowed, the maximal set has at most `N/2` elements — "the classical threshold for the existence of some distinct `a, b ∈ A` such that `a ∣ b`"** (in exact form `⌈N/2⌉`, attained by the upper half). Van Doorn's `(25/28 + o(1)) N` upper bound and the `(1/2 + o(1)) N` question are **not** claimed.

## Statements

Subsets of `{1, …, N}` are Mathlib `Finset ℕ`, arithmetic is in `ℚ`; the relation predicates, the upper half and `f` are defined in this package (namespace `Erdos301`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def HasUnitSolution (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ B ⊆ A, a ∉ B ∧ B.Nonempty ∧ ((a : ℚ))⁻¹ = ∑ b ∈ B, ((b : ℚ))⁻¹

def HasRepeatedUnitSolution (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ k : ℕ, 0 < k ∧ ((a : ℚ))⁻¹ = k * ((b : ℚ))⁻¹

def upperHalf (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun n => N < 2 * n)

noncomputable def f (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => ¬ HasUnitSolution A)).sup Finset.card

theorem half_le_f (N : ℕ) : (N + 1) / 2 ≤ f N

theorem not_hasUnitSolution_upperHalf (N : ℕ) : ¬ HasUnitSolution (upperHalf N)

theorem card_upperHalf (N : ℕ) : (upperHalf N).card = (N + 1) / 2

theorem exists_dvd_of_half_lt_card (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (h : (N + 1) / 2 < A.card) : ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a ∣ b

theorem card_le_half_of_not_hasRepeatedUnitSolution (N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (h : ¬ HasRepeatedUnitSolution A) : A.card ≤ (N + 1) / 2

theorem not_hasRepeatedUnitSolution_upperHalf (N : ℕ) : ¬ HasRepeatedUnitSolution (upperHalf N)
```

`HasUnitSolution A` is the page's relation with pairwise distinct elements (`B` is the set of denominators, `k ≥ 1`); `HasRepeatedUnitSolution A` is the relation with all denominators equal to one `b ≠ a`; `f N` is the page's `f(N)`. The first theorem (data binder `N`) is the page's lower bound in exact form; the second and third are the two facts about the witness; the fourth is the classical primitive-set threshold; the fifth is the Cambie–van Doorn remark; the sixth shows the threshold is attained. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

If `a ∈ (N/2, N]` and `1/a = Σ_{b∈B} 1/b` with `B ⊆ (N/2, N]`, `a ∉ B`, `B ≠ ∅`, then each term is at least `1/N` while `1/a < 2/N`, so `|B| = 1`, and `1/a = 1/b` forces `a = b`, contradiction; `(N/2, N]` has `⌈N/2⌉` elements. Mapping each element of `A ⊆ {1, …, N}` to its odd part lands among the `⌈N/2⌉` odd numbers `≤ N`, so a set with more than `⌈N/2⌉` elements has two elements with the same odd part, and the one with the smaller power of `2` divides the other; `1/a = k · (1/b)` with `a ≠ b` is exactly `b = ka`. In `(N/2, N]`, `a ∣ b` with `a ≠ b` would force `b ≥ 2a > N`.

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

The problem is Erdős and Graham's (ErGr80). The lower-bound example is the folklore observation recorded on the page; the repeated-denominator remark is due to Stijn Cambie and Wouter van Doorn (as recorded on the page), and its content is the classical primitive-set threshold. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000253-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
