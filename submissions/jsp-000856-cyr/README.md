# JSP-000856: the off-diagonal Ramsey difference bounds of the problem page (Erdős #1030, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000856](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000856) / [Erdős Problem #1030](https://www.erdosproblems.com/1030): prove the existence of some `c > 0` such that `lim R(k+1, k)/R(k, k) > 1 + c`. The component formalized here consists of the two bounds recorded on the problem page: the Burr–Erdős–Faudree–Schelp bound **`R(k+1, k) − R(k, k) ≥ 2k − 5`** and the trivial bound **`R(k+1, k) − R(k, k) ≥ k − 2`**, both for every `k`, proved through the sharper **`r(k+1, k) ≥ r(k, k) + 2k − 3`** for `k ≥ 2` (Theorem 1 of the 1989 paper with the roles of the two arguments exchanged). Two-colour Ramsey numbers, Ramsey's theorem and the BEFS89 construction are reused from our own JSP-000669 package (Erdős #812, PR #362). The open question of the page (the ratio bound) and the question whether `R(k+1, k) − R(k, k) > k^c` for some `c > 1` are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos1030`, [Proof/Defs.lean](Proof/Defs.lean), reused from JSP-000669). A red/blue colouring of the complete graph on `V` is a `SimpleGraph V` (red = adjacent, blue = non-adjacent):

```lean
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop := G.CliqueFree m ∧ Gᶜ.CliqueFree n

def RamseyProp (N m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

noncomputable def R (n : ℕ) : ℕ := ramsey n n
```

[Proof/OffDiagonal.lean](Proof/OffDiagonal.lean) proves:

```lean
theorem offdiag_sub_ge (k : ℕ) : (ramsey (k + 1) k : ℤ) - (R k : ℤ) ≥ 2 * (k : ℤ) - 5

theorem offdiag_ge (k : ℕ) (hk : 2 ≤ k) : R k + (2 * k - 3) ≤ ramsey (k + 1) k

theorem offdiag_sub_ge_trivial (k : ℕ) : (ramsey (k + 1) k : ℤ) - (R k : ℤ) ≥ (k : ℤ) - 2
```

`ramsey m n` is the classical Ramsey number `r(m, n)` (the least `N` such that every red/blue colouring of `K_N` contains a red `K_m` or a blue `K_n`; the defining set is nonempty by Ramsey's theorem, proved in [Proof/Ramsey.lean](Proof/Ramsey.lean), so the infimum is attained), `R k = r(k, k)` and `ramsey (k + 1) k` is the page's `R(k+1, k)`. The first theorem is the page's BEFS89 bound, the second its sharp form, the third the page's trivial bound. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Theorem 1 of Burr, Erdős, Faudree and Schelp, `r(m, n+1) ≥ r(m, n) + 2m − 3` for `m, n ≥ 2` ([Proof/Construction.lean](Proof/Construction.lean), [Proof/Main.lean](Proof/Main.lean): from an extremal `(m, n)`-good colouring containing a red `K_{m−2}`, duplicate its vertices and add `m − 1` further vertices with the paper's colouring rules; an index count bounds red cliques by `m − 1` vertices and blue cliques by `n`), together with the symmetry `r(m, n) = r(n, m)`, gives `r(k+1, k) = r(k, k+1) ≥ r(k, k) + 2k − 3` for `k ≥ 2`. This implies `2k − 5` for `k ≥ 2` and `k − 2` for `k ≥ 3`; the remaining cases are the values `r(1, 0) = R(0) = 0`, `r(2, 1) = R(1) = 1`, `r(3, 2) = 3` and `R(2) = 2`. (The paper prints Theorem 1 for `m, n ≥ 2`, which is one step too wide at its `n = 2`; the formalized range is the one its proof establishes, as documented in the JSP-000669 package, and it suffices here.)

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

The problem is due to Erdős and Sós (Er93). The bound is due to S. A. Burr, P. Erdős, R. J. Faudree and R. H. Schelp, *On the difference between consecutive Ramsey numbers*, Utilitas Math. 35 (1989), 115–118 (Theorem 1; the scan in the Rényi Institute archive of Erdős's papers was used). The Lean development is our own, first submitted with JSP-000669 and extended here by the off-diagonal module.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000856-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
