# JSP-000855: the classical diagonal Ramsey bounds in explicit form (Erdős #1029, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000855](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000855) / [Erdős Problem #1029](https://www.erdosproblems.com/1029): if `R(k)` is the diagonal Ramsey number, is `R(k)/(k 2^{k/2}) → ∞`? The component formalized here consists of the two classical bounds recorded on the problem page, `k 2^{k/2} ≪ R(k) ≤ C(2k−1, k−1)`, in explicit form: the **Erdős–Szekeres upper bound** `r(m, n) ≤ C(m+n−2, m−1)` (so `R(k) ≤ C(2k−2, k−1) ≤ C(2k−1, k−1)`), and **Erdős's 1947 lower bound**, `R(k)² > 2^k` for `k ≥ 3` and `k · 2^{k/2} ≤ 2√2 · e · (R(k) + 1)` for every `k`, proved by the counting form of the probabilistic argument (a union bound over `k`-sets, with no probability theory). Two-colour Ramsey numbers and Ramsey's theorem are reused from our own JSP-000669 package (Erdős #812, PR #362). The open question of the page, the asymptotic constants `(1+o(1))/(√2 e)` and Spencer's `√2/e`, and any improvement of the upper bound are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos1029`, [Proof/Defs.lean](Proof/Defs.lean), reused from JSP-000669). A red/blue colouring of the complete graph on `V` is a `SimpleGraph V` (red = adjacent, blue = non-adjacent):

```lean
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop := G.CliqueFree m ∧ Gᶜ.CliqueFree n

def RamseyProp (N m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

noncomputable def R (n : ℕ) : ℕ := ramsey n n
```

[Proof/Lower.lean](Proof/Lower.lean) and [Proof/Sharp.lean](Proof/Sharp.lean) prove:

```lean
theorem mul_two_pow_half_le (k : ℕ) :
    (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 2 * Real.sqrt 2 * Real.exp 1 * ((R k : ℝ) + 1)

theorem two_pow_lt_R_sq (k : ℕ) (hk : 3 ≤ k) : 2 ^ k < R k ^ 2

theorem ramsey_le_choose_sharp (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ramsey m n ≤ (m + n - 2).choose (m - 1)

theorem R_le_choose_page (k : ℕ) (hk : 1 ≤ k) : R k ≤ (2 * k - 1).choose (k - 1)

theorem lt_R_of_count (k N : ℕ) (hkN : k ≤ N)
    (h : N.choose k * 2 * 2 ^ (N.choose 2 - k.choose 2) < 2 ^ (N.choose 2)) : N < R k
```

`ramsey m n` is the classical Ramsey number `r(m, n)` (the least `N` such that every red/blue colouring of `K_N` contains a red `K_m` or a blue `K_n`; the defining set is nonempty by Ramsey's theorem, proved in [Proof/Ramsey.lean](Proof/Ramsey.lean), so the infimum is attained) and `R k = r(k, k)` is the page's `R(k)`. The first theorem is the page's lower bound `k 2^{k/2} ≪ R(k)` with the explicit constant `2√2 e` (and a harmless `+1`); the second is Erdős's classical `R(k) > 2^{k/2}`; the third is the Erdős–Szekeres bound, the fourth the form printed on the page; the fifth is the counting criterion behind the lower bounds. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Upper bound (Erdős–Szekeres 1935): a vertex of a colouring of `K_{A+B}` (with `A = r(m−1, n)`, `B = r(m, n−1)`) has at least `A` red or at least `B` blue neighbours, and the induced colouring on that neighbourhood extended by the vertex yields the required monochromatic clique; so `r(m, n) ≤ r(m−1, n) + r(m, n−1)`, and Pascal's rule with `r(1, n) = r(m, 1) = 1` gives `r(m, n) ≤ C(m+n−2, m−1)`. Lower bound (Erdős 1947, as counting): a colouring of `K_N` is a set `F` of red edges among the `C(N, 2)` edges; for a fixed `k`-set `S` the colourings in which `S` is a red clique are the supersets of the `C(k, 2)` edges inside `S` (there are `2^{C(N,2) − C(k,2)}`, counted with Mathlib's `Finset.card_Icc_finset`) and those in which `S` is a blue clique are the subsets avoiding them (again `2^{C(N,2) − C(k,2)}`, `Finset.card_powerset`); summing over the `C(N, k)` sets `S`, the number of pairs `(F, S)` with `S` monochromatic is at most `C(N, k) · 2 · 2^{C(N,2) − C(k,2)}`, and if this is less than `2^{C(N,2)}` some `F` has no monochromatic `k`-set, so the graph with edge set `F` and its complement are `K_k`-free and `N < R(k)`. With `N = ⌊2^{k/2}⌋` and `k ≥ 3` this gives `R(k)² > 2^k` (using `C(N, k) · k! ≤ N^k` and `2^{k+2} < (k!)²`); with `N = ⌊k 2^{(k−1)/2}/(2e)⌋` it gives `C(N, k) ≤ (eN/k)^k ≤ 2^{C(k,2)}/2^k` (from `k! ≥ (k/e)^k`, i.e. `k^k/k! ≤ e^k`), hence `R(k) > N` and `k 2^{k/2} < 2√2 e (R(k) + 1)`; the cases `k ≤ 2` are the values `R(0) = 0`, `R(1) = 1`, `R(2) = 2`.

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

The problem is Erdős's (Er93). The upper bound is due to P. Erdős and G. Szekeres, *A combinatorial problem in geometry*, Compositio Math. 2 (1935), 463–470; the lower bound to P. Erdős, *Some remarks on the theory of graphs*, Bull. Amer. Math. Soc. 53 (1947), 292–294 (both scans from the Rényi Institute archive of Erdős's papers were used; the counting argument formalized is the standard one). The Lean development is our own, first submitted with JSP-000669 and extended here by the two new modules.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000855-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
