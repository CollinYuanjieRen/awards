# JSP-000094: Erdős's bounds √2 ≤ liminf R(k)^{1/k} ≤ limsup R(k)^{1/k} ≤ 4 (Erdős #77, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000094](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000094) / [Erdős Problem #77](https://www.erdosproblems.com/77): find the value of `lim R(k)^{1/k}` for the diagonal Ramsey numbers `R(k)`. The component formalized here consists of the two inequalities recorded on the page as Erdős's, **`√2 ≤ liminf R(k)^{1/k}`** and **`limsup R(k)^{1/k} ≤ 4`**, derived from the classical bounds `R(k) > 2^{k/2}` (Erdős 1947) and `R(k) ≤ C(2k−2, k−1) < 4^k` (Erdős–Szekeres 1935) as formalized in our JSP-000855 package, which is reused here together with our JSP-000669 Ramsey development. The existence and the value of the limit (the page's question) and the improved upper bounds `4 − 1/128`, `3.7992…` and `4 − c` are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos77`, [Proof/Defs.lean](Proof/Defs.lean), reused from JSP-000669). A red/blue colouring of the complete graph on `V` is a `SimpleGraph V` (red = adjacent, blue = non-adjacent):

```lean
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop := G.CliqueFree m ∧ Gᶜ.CliqueFree n

def RamseyProp (N m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

noncomputable def R (n : ℕ) : ℕ := ramsey n n
```

[Proof/Limit.lean](Proof/Limit.lean) proves:

```lean
theorem sqrt_two_le_liminf :
    Real.sqrt 2 ≤ Filter.liminf (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop

theorem limsup_le_four : Filter.limsup (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop ≤ 4

theorem sqrt_two_le_R_rpow (k : ℕ) (hk : 3 ≤ k) : Real.sqrt 2 ≤ (R k : ℝ) ^ (1 / (k : ℝ))

theorem R_rpow_le_four (k : ℕ) (hk : 1 ≤ k) : (R k : ℝ) ^ (1 / (k : ℝ)) ≤ 4
```

`R k` is the classical diagonal Ramsey number (the least `N` such that every red/blue colouring of `K_N` contains a monochromatic `K_k`; the defining set is nonempty by Ramsey's theorem, proved in [Proof/Ramsey.lean](Proof/Ramsey.lean), so the infimum is attained), and `(R k : ℝ) ^ (1 / (k : ℝ))` is the real `k`-th root, the same expression as in the problem statement. The first two theorems are the page's inequalities (`Filter.liminf`/`Filter.limsup` along `atTop`, as in Mathlib); the last two are the termwise bounds they rest on. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

From `R(k)² > 2^k` for `k ≥ 3` ([Proof/Lower.lean](Proof/Lower.lean), Erdős's counting argument: a union bound over `k`-sets shows that some colouring of `K_N`, `N = ⌊2^{k/2}⌋`, has no monochromatic `K_k`) we get `R(k)^{1/k} > √2` for `k ≥ 3`; from `R(k) ≤ C(2k−2, k−1) ≤ 2^{2k−2} < 4^k` ([Proof/Sharp.lean](Proof/Sharp.lean), the Erdős–Szekeres recursion `r(m, n) ≤ r(m−1, n) + r(m, n−1)` with Pascal's rule) we get `R(k)^{1/k} ≤ 4` for `k ≥ 1`. A real sequence eventually bounded below by `√2` has `liminf ≥ √2`, and one bounded above by `4` has `limsup ≤ 4` (Mathlib's `Filter.le_liminf_of_le` and `Filter.limsup_le_of_le`, whose boundedness side conditions are supplied by the same termwise bounds).

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

The problem is Erdős's (Er61 and later). The bounds are due to P. Erdős and G. Szekeres, *A combinatorial problem in geometry*, Compositio Math. 2 (1935), 463–470, and P. Erdős, *Some remarks on the theory of graphs*, Bull. Amer. Math. Soc. 53 (1947), 292–294. The Lean development is our own, first submitted with JSP-000669 and JSP-000855 and extended here by the limit module.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000094-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
