# JSP-000952: recurrence sets of squares are not additive bases (Erdős #1147)

This package submits a Lean formalization for intake and review of [JSP-000952](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000952) / [Erdős Problem #1147](https://www.erdosproblems.com/1147): for an irrational `α > 0`, is the set `A = {n ≥ 1 : ‖α n²‖ < 1/log n}` (where `‖·‖` is the distance to the nearest integer) an additive basis of order 2? The answer is no: Jakub Konieczny (2016) showed that it fails for almost every `α` and, explicitly, for `α = √2`. This package formalizes the explicit `√2` counterexample, in the general form "for every threshold `ε(n) → 0` the set `{n ≥ 1 : ‖√2 n²‖ ≤ ε(n)}` is not an asymptotic basis of order 2", and derives the negative answer to the question.

## Statements

All definitions are our own (namespace `Erdos1147`, [Proof/Defs.lean](Proof/Defs.lean)):

```lean
noncomputable def nd (x : ℝ) : ℝ := |x - round x|          -- distance to the nearest integer

def IsAsymptoticBasis2 (A : Set ℕ) : Prop :=              -- every large integer is a + b
  ∃ n₀ : ℕ, ∀ m : ℕ, n₀ ≤ m → ∃ a ∈ A, ∃ b ∈ A, a + b = m

def recSet (α : ℝ) (ε : ℕ → ℝ) : Set ℕ := {n | 1 ≤ n ∧ nd (α * (n : ℝ) ^ 2) ≤ ε n}

def erdosSet (α : ℝ) : Set ℕ := {n | 1 ≤ n ∧ nd (α * (n : ℝ) ^ 2) < 1 / Real.log n}
```

[Proof/Main.lean](Proof/Main.lean) proves:

```lean
theorem sqrtTwo_recSet_not_basis (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) :
    ¬ IsAsymptoticBasis2 (recSet (Real.sqrt 2) ε)

theorem not_erdos_1147 :
    ¬ ∀ α : ℝ, 0 < α → Irrational α → IsAsymptoticBasis2 (erdosSet α)

theorem not_erdos_1147_le :
    ¬ ∀ α : ℝ, 0 < α → Irrational α → IsAsymptoticBasis2 (recSet α (fun n => 1 / Real.log n))
```

The first theorem is Konieczny's Proposition 1.3 (case `ε(n) → 0`) for `α = √2`. The second is the question as printed, with "basis of order 2" read as in Konieczny's paper (every sufficiently large integer is a sum of two elements), which is the weakest meaning and therefore gives the strongest refutation; the third covers the non-strict threshold `‖α n²‖ ≤ 1/log n`. (The reading "every positive integer is a sum of two elements" is vacuous for any set of positive integers, since `1` is not such a sum, and is not stated.) Lean's conventions `Real.log 1 = 0` and `1/0 = 0` exclude `n = 1` from the displayed set; this is immaterial, because the general theorem allows an arbitrary threshold function and so covers the set with `n = 1` included as well. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs. The almost-every-`α` statement of Konieczny's paper is not part of the question as posed (which is universally quantified over `α`) and is not formalized.

## Proof outline (Konieczny 2016, Section 1.2)

Let `x_j + y_j √2 = (3 + 2√2)^(2j+1)`; then `x_j² − 2y_j² = 1`, `x_j` is odd and `y_j ≡ 2 (mod 4)`. Put `N_j = y_j / 2` (odd, at least `j + 1`) and `P_j = x_j`, so `P_j² = 8N_j² + 1`; the defect `η_j = P_j − 2√2 N_j = 1/(P_j + 2√2 N_j)` is positive and at most `1/(4√2 N_j)`, and `ρ_j = η_j N_j` lies below `1/(4√2)` with `|1/(4√2) − ρ_j| ≤ 1/(32 N_j²)` ([Proof/Pell.lean](Proof/Pell.lean)). For a split `N_j = n₁ + n₂` the exact identity

`√2 n₂² = ((N_j − 2n₁) P_j)/2 − ρ_j/2 + n₁ η_j + √2 n₁²`

holds, and `(N_j − 2n₁) P_j` is odd, so `‖√2 n₂²‖ = ‖1/2 + t + √2 n₁²‖` with `|t| ≤ ρ_j/2 < 9/100` ([Proof/Phase.lean](Proof/Phase.lean)). Two consequences: (a) the two summands cannot both satisfy `‖√2 n²‖ ≤ 1/5`, since then `‖√2 n₂² − √2 n₁²‖ ≤ 2/5` while this number is `‖1/2 + t‖ ≥ 41/100`; (b) for a fixed first summand `n₁` the phase tends to `θ(n₁) = 1/2 − 1/(8√2) + √2 n₁²`, which is not an integer because `√2` is irrational, so `‖√2 (N_j − n₁)²‖ ≥ ‖θ(n₁)‖/2` for large `j`. If `ε(n) → 0` and the set were an asymptotic basis, then for large `j` write `N_j = a + b` with both summands in the set; by (a) one of them, say `a`, has `‖√2 a²‖ > 1/5`, hence `ε(a) > 1/5`, which confines `a` to a finite set; then `b = N_j − a` is large, so `ε(b) < ‖θ(a)‖/2 ≤ ‖√2 b²‖`, contradicting `b`'s membership ([Proof/Main.lean](Proof/Main.lean)).

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all three theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The question is due to P. Erdős (recorded in [Va99, 1.21]); the negative answer and the `√2` construction are due to Jakub Konieczny, *Sets of recurrence as bases for the positive integers*, Acta Arithmetica 175 (2016), 309–338, Section 1.2, Proposition 1.3 ([arXiv:1504.02410](https://arxiv.org/abs/1504.02410)). The Lean development is written from scratch in this package.

The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000952-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
