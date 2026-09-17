# JSP-000103: the case ε ≥ 3/4 of R(G) > (1−ε)^k R(k) is trivial (Erdős #87, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000103](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000103) / [Erdős Problem #87](https://www.erdosproblems.com/87): for `ε > 0`, is it true that for all sufficiently large `k`, `R(G) > (1−ε)^k R(k)` for every graph `G` with chromatic number `χ(G) = k` (and, even stronger, is there `c > 0` with `R(G) > c R(k)`)? The component formalized here is the remark recorded on the problem page, **"Since `R(k) ≤ 4^k` this is trivial for `ε ≥ 3/4`"**, in the explicit form: for every graph `G` with `χ(G) = k ≥ 2` and every `3/4 ≤ ε ≤ 1`, `R(G) > (1−ε)^k R(k)`. Indeed `G` has an edge, so `R(G) ≥ 2`, while `(1−ε)^k R(k) ≤ 4^{−k} R(k) ≤ 1` by the Erdős–Szekeres bound. The two open questions of the page, Erdős's original conjecture `R(G) ≥ R(k)`, the Faudree–McKay computation `R(W) = 17` for the pentagonal wheel and Wigderson's `R(G) ≫ 2^{k/2}` are **not** claimed.

## Statements

Graphs are Mathlib's `SimpleGraph`, `χ(G)` is Mathlib's `SimpleGraph.chromaticNumber` (valued in `ℕ∞`), a red/blue colouring of `K_N` is a `SimpleGraph (Fin N)` (red = edges, blue = non-edges), and "`R` contains a copy of `G`" is Mathlib's `G ⊑ R` (`SimpleGraph.IsContained`, an injective graph homomorphism). The two-colour Ramsey numbers and the graph Ramsey number are defined in this package (namespace `Erdos87`, [Proof/RamseyDefs.lean](Proof/RamseyDefs.lean), [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop :=
  G.CliqueFree m ∧ Gᶜ.CliqueFree n

def RamseyProp (N m n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

noncomputable def R (n : ℕ) : ℕ := ramsey n n

def GraphRamseyProp {V : Type*} (N : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ G ⊑ Rᶜ

noncomputable def graphRamsey {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | GraphRamseyProp N G}

theorem not_exists_four_pow_mul_graphRamsey_le (n k : ℕ) :
    ¬ ∃ G : SimpleGraph (Fin n), 2 ≤ k ∧ G.chromaticNumber = (k : ℕ∞) ∧
      4 ^ k * graphRamsey G ≤ R k

theorem lt_graphRamsey_of_chromaticNumber {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) (hG : G.chromaticNumber = (k : ℕ∞)) (ε : ℝ) (hε : 3 / 4 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) ^ k * (R k : ℝ) < graphRamsey G

theorem R_lt_four_pow_mul_graphRamsey {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) (hG : G.chromaticNumber = (k : ℕ∞)) : R k < 4 ^ k * graphRamsey G

theorem two_le_graphRamsey_of_adj {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V}
    (h : G.Adj u v) : 2 ≤ graphRamsey G

theorem exists_adj_of_two_le_chromaticNumber {V : Type*} (G : SimpleGraph V)
    (h : 2 ≤ G.chromaticNumber) : ∃ u v : V, G.Adj u v

theorem ramsey_diag_le_four_pow (n : ℕ) : ramsey n n ≤ 4 ^ n
```

`ramsey m n` is `r(m, n)`, `R n = r(n, n)` is `R(K_n)`, and `graphRamsey G` is `R(G)`, the least `N` such that every red/blue colouring of `K_N` has a monochromatic copy of `G` (an `sInf` over a set shown nonempty for every graph on a finite vertex type, so it is honest). The first theorem (data binders `n`, `k`, in negation form) says `4^k R(G) > R(k)` for every graph on `n` vertices with `χ(G) = k ≥ 2`; the second is the page's inequality `R(G) > (1−ε)^k R(k)` for every `ε` in `[3/4, 1]` (the range of the remark; `ε ≤ 1` keeps the base nonnegative, as in the formal-conjectures statement of the problem); the third is its natural-number form; the fourth and fifth are the two elementary inputs; the last is the Erdős–Szekeres bound `r(n, n) ≤ C(2n, n) − 1 ≤ 4^n` ([Proof/Bound.lean](Proof/Bound.lean)). The threshold `k ≥ 2` is the page's "`k` sufficiently large": for `k = 0` the inequality fails (`G` is the empty graph and `R(G) = R(0) = 0`). There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

If `χ(G) ≥ 2` then `G ≠ ⊥`, so `G` has an edge `uv`. A colouring of `K_N` with `N ≤ 1` contains no copy of `G`: a copy in the red graph `⊥` would map `uv` to a red edge, and a copy in the blue graph `⊤` would map `u`, `v` to two distinct vertices of `Fin N`; hence every `N` with the monochromatic-copy property is at least `2`, and so is `R(G)`. With `R(k) ≤ 4^k`, `R(k) < 2 · 4^k ≤ 4^k R(G)`; for `3/4 ≤ ε ≤ 1`, `(1−ε)^k ≤ 4^{−k}`, so `(1−ε)^k R(k) < R(G)`.

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

The problem is Erdős's (Er95; problems #12 and #13 of the Ramsey-theory chapter of the graphs problem collection). The `ε ≥ 3/4` remark is the folklore observation recorded on the problem page; the `4^k` bound on diagonal Ramsey numbers is Erdős–Szekeres. The Lean development is written from scratch by us: the two-colour Ramsey toolbox and the graph Ramsey number ([Proof/RamseyDefs.lean](Proof/RamseyDefs.lean), [Proof/Ramsey.lean](Proof/Ramsey.lean), [Proof/Bound.lean](Proof/Bound.lean), [Proof/Defs.lean](Proof/Defs.lean)) are reused from our own earlier submissions for JSP-000669, JSP-000099 and JSP-000175, as noted in their module docstrings; the proofs of this package are new.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim either question of the page. The contribution sought is formalization, not a new mathematical result; the mathematical content is a one-line remark. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000103-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
