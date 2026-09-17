# JSP-000260: the trivial bound δ(N) ≥ 1/[1, …, N] for unit-fraction deviations (Erdős #311, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000260](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000260) / [Erdős Problem #311](https://www.erdosproblems.com/311): with `δ(N)` the minimal non-zero value of `|1 − Σ_{n∈A} 1/n|` over `A ⊆ {1, …, N}`, is `δ(N) = e^{−(c+o(1))N}` for some `c ∈ (0, 1)`? The component formalized here is the bound recorded on the problem page as trivial, **`δ(N) ≥ 1/[1, …, N]`** where `[1, …, N]` is the least common multiple of `{1, …, N}`: multiplying `1 − Σ_{n∈A} 1/n` by the lcm gives a non-zero integer. The identification `1/[1, …, N] = e^{−(1+o(1))N}` (which needs the prime number theorem), Tang's upper bound, Kovač's equivalence with the [ErGr80] formulation and the conjecture itself are **not** claimed.

## Statements

Sums, lcm and absolute values are Mathlib's; the deviation set and `δ(N)` are defined in this package (namespace `Erdos311`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def unitSum (A : Finset ℕ) : ℚ := ∑ n ∈ A, (n : ℚ)⁻¹

def lcmUpTo (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

def deviations (N : ℕ) : Finset ℚ :=
  ((Finset.Icc 1 N).powerset.image (fun A => |1 - unitSum A|)).filter (fun d => d ≠ 0)

noncomputable def delta (N : ℕ) : ℚ := (deviations N).min' (deviations_nonempty N)

theorem one_div_lcm_le_delta (N : ℕ) : 1 / (lcmUpTo N : ℚ) ≤ delta N

theorem one_div_lcm_le_abs (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (h : 1 - unitSum A ≠ 0) : 1 / (lcmUpTo N : ℚ) ≤ |1 - unitSum A|

theorem delta_le (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (h : 1 - unitSum A ≠ 0) :
    delta N ≤ |1 - unitSum A|

theorem exists_delta_eq (N : ℕ) :
    ∃ A ⊆ Finset.Icc 1 N, 1 - unitSum A ≠ 0 ∧ delta N = |1 - unitSum A|

theorem delta_pos (N : ℕ) : 0 < delta N

theorem lcmUpTo_pos (N : ℕ) : 0 < lcmUpTo N
```

`deviations N` is the finite set of non-zero values `|1 − Σ_{n∈A} 1/n|` over `A ⊆ {1, …, N}` (non-empty because `A = ∅` contributes `1`) and `delta N` its minimum, the page's `δ(N)`. The first theorem (single data binder `N`) is the page's bound; the second is the bound for each individual `A`; the third and fourth make `delta` transparent (it is a lower bound of the deviations and is attained); the last two are positivity facts. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Let `L = [1, …, N]`. Every `n ∈ {1, …, N}` divides `L`, so `L/n` is a natural number and `L·(1 − Σ_{n∈A} 1/n) = L − Σ_{n∈A} L/n` is an integer. If `1 − Σ 1/n ≠ 0` this integer is non-zero, hence has absolute value at least `1`, so `|1 − Σ 1/n| ≥ 1/L`. `δ(N)` is one of these values, so `δ(N) ≥ 1/L`.

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

The problem is Erdős and Graham's (ErGr80, p. 40). The bound is the folklore observation recorded on the problem page. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's conjecture. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000260-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
