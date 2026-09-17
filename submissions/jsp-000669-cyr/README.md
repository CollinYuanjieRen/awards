# JSP-000669: the Burr–Erdős–Faudree–Schelp bound on consecutive Ramsey numbers (Erdős #812, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000669](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000669) / [Erdős Problem #812](https://www.erdosproblems.com/812): is `R(n+1)/R(n) ≥ 1 + c` for all large `n`, and is `R(n+1) − R(n) ≫ n²`? The component formalized here is the lower bound recorded on the problem page, due to Burr, Erdős, Faudree and Schelp (1989): **`R(n+1) − R(n) ≥ 4n − 8` for `n ≥ 2`**, proved in the form the paper's Theorem 1 actually gives, **`r(m, n+1) ≥ r(m, n) + 2m − 3`** for `m ≥ 2`, `n ≥ 2`, hence **`R(n+1) ≥ R(n) + 4n − 4`** for every `n`. Ramsey numbers are defined in this package, and since Mathlib at the pinned revision has no Ramsey theorem for graphs, the finiteness of `r(m, n)` (Ramsey's theorem for two colours) is proved here as well. The page's two questions are open and are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos812`, [Proof/Defs.lean](Proof/Defs.lean)). A red/blue colouring of the complete graph on `V` is a `SimpleGraph V` (red = adjacent, blue = non-adjacent):

```lean
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop := G.CliqueFree m ∧ Gᶜ.CliqueFree n

def RamseyProp (N m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

noncomputable def R (n : ℕ) : ℕ := ramsey n n

theorem R_succ_ge_all (n : ℕ) : R n + (4 * n - 4) ≤ R (n + 1)

theorem R_succ_sub_ge : ∀ n : ℕ, 2 ≤ n → (R (n + 1) : ℤ) - (R n : ℤ) ≥ 4 * (n : ℤ) - 8

theorem ramsey_succ_right (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ramsey m n + (2 * m - 3) ≤ ramsey m (n + 1)

theorem ramseyProp_ramsey (m n : ℕ) : RamseyProp (ramsey m n) m n
```

`ramsey m n` is the classical Ramsey number `r(m, n)` (the least `N` such that every red/blue colouring of `K_N` contains a red `K_m` or a blue `K_n`) and `R n = r(n, n)`. The fourth theorem is Ramsey's theorem: the defining set is nonempty, so the infimum is attained and `ramsey` is a genuine minimum. The third theorem is Theorem 1 of the paper (the paper prints it as `r(m, n) ≥ r(m, n−1) + 2m − 3` for `m, n ≥ 2`; at `n = 2` that reads `r(m, 2) ≥ r(m, 1) + 2m − 3`, which is false for `m ≥ 3` because `r(m, 1) = 1` and `r(m, 2) = m`, and indeed the proof needs a red `K_{m−1}` in the extremal `(m, n−1)`-good colouring, which requires `n − 1 ≥ 2`; the formalized statement covers exactly the range the proof establishes, and the corollary and the diagonal bound are unaffected; the failure of the wider range is recorded as `not_ramsey_succ_right_of_one_le`), the first its diagonal consequence for every `n` (with truncated subtraction; for `n ≥ 2` it is `R(n+1) ≥ R(n) + 4n − 4`), and the second the weaker form printed on the problem page and in the formal-conjectures repository. The symmetric form `ramsey_succ_left`, the paper's corollary `ramsey_succ_succ` (`r(m+1, n+1) ≥ r(m, n) + 2m + 2n − 4`) and `R_succ_ge` (`n ≥ 2`) are proved in the same library. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Ramsey's theorem ([Proof/Ramsey.lean](Proof/Ramsey.lean)): `r(m+1, n+1) ≤ r(m, n+1) + r(m+1, n)`; a vertex of a colouring of `K_{a+b}` has at least `a` red or at least `b` blue neighbours, the induced colouring on that neighbourhood contains the required monochromatic clique by induction, and the vertex extends a red `K_m` to a red `K_{m+1}` (or a blue `K_n` to a blue `K_{n+1}`). Theorem 1 ([Proof/Construction.lean](Proof/Construction.lean), [Proof/Main.lean](Proof/Main.lean)): let `G` be an `(m, n)`-good colouring of `K_N` with `N = r(m, n) − 1`. `G` contains a red `K_{m−1}` (otherwise a new vertex joined red to everything gives a good colouring of `K_{r(m,n)}`), of which a red `K_{m−2}` on `u_0, …, u_{m−3}` is used. Add `m − 2` vertices `v_i` (`u_i v_i` blue, `v_i` coloured to every other old vertex like `u_i`, `v_i v_j` red) and `m − 1` vertices `x_0, …, x_{m−2}` (`x_i x_j` red, `x_j` blue to the old vertices other than the `u_i`, `u_i x_j` red iff `i ≥ j`, `v_i x_j` red iff `i < j`). A red clique without an `x` maps injectively (`v_i ↦ u_i`) onto a red clique of `G`; one with `x`'s of least index `k` and largest index `l` has at most `l − k + 1` `x`'s, `m − 2 − l` `u`'s and `k` `v`'s, so at most `m − 1` vertices. A blue clique has at most one `x` and one `v`; without an `x` it has at most `n` vertices, and exactly `n` only if it contains a pair `{u_i, v_i}`; with `x_j` the remaining `n` vertices would contain such a pair, but `x_j` is blue to `u_i` only if `i < j` and to `v_i` only if `i ≥ j`. So `K_{N+2m−3}` is `(m, n+1)`-good and `r(m, n+1) ≥ r(m, n) + 2m − 3`. Symmetry (`r(m, n) = r(n, m)` by exchanging colours) gives the corollary and the diagonal bound; the cases `n ≤ 1` of `R_succ_ge_all` are the values `R(0) = 0`, `R(1) = 1 ≤ R(2)`.

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

The problem is Erdős's (Er91). The bound is due to S. A. Burr, P. Erdős, R. J. Faudree and R. H. Schelp, *On the difference between consecutive Ramsey numbers*, Utilitas Math. 35 (1989), 115–118 (Theorem 1 and its Corollary; the scan in the Rényi Institute archive of Erdős's papers was used). Ramsey's theorem for two colours is classical. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's questions. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000669-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
