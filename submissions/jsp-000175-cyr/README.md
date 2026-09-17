# JSP-000175: the trivial bound R(Q_n) ≤ R(K_{2^n}) ≤ 4^{2^n} for the hypercube (Erdős #181, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000175](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000175) / [Erdős Problem #181](https://www.erdosproblems.com/181): for the `n`-dimensional hypercube graph `Q_n` (on `2^n` vertices), prove that the Ramsey number satisfies `R(Q_n) ≪ 2^n`. The component formalized here is the bound recorded on the problem page as trivial, **"The trivial bound is `R(Q_n) ≤ R(K_{2^n}) ≤ C^{2^n}` for some constant `C > 1`"**, with the explicit constant `C = 4`: a monochromatic `K_m` contains a copy of every graph on `m` vertices, so `R(G) ≤ R(m)` for every graph `G` on `m` vertices, and the Erdős–Szekeres bound gives `R(m) ≤ 4^m`. The question `R(Q_n) ≪ 2^n` (the Burr–Erdős conjecture), the successive improvements of the trivial bound and Tikhomirov's `R(Q_n) ≪ 2^{(2−c)n}` are **not** claimed.

## Statements

Graphs are Mathlib's `SimpleGraph`; a red/blue colouring of `K_N` is a `SimpleGraph (Fin N)` (red = edges, blue = non-edges); "`R` contains a copy of `G`" is Mathlib's `G ⊑ R` (`SimpleGraph.IsContained`, an injective graph homomorphism). The two-colour Ramsey numbers, the hypercube and the graph Ramsey number are defined in this package (namespace `Erdos181`, [Proof/RamseyDefs.lean](Proof/RamseyDefs.lean), [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop :=
  G.CliqueFree m ∧ Gᶜ.CliqueFree n

def RamseyProp (N m n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

noncomputable def R (n : ℕ) : ℕ := ramsey n n

def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun u v => ∃ i, u i ≠ v i ∧ ∀ j, j ≠ i → u j = v j)

def GraphRamseyProp {V : Type*} (N : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ G ⊑ Rᶜ

noncomputable def graphRamsey {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | GraphRamseyProp N G}

theorem graphRamsey_hypercube_le (n : ℕ) : graphRamsey (hypercube n) ≤ 4 ^ (2 ^ n)

theorem graphRamsey_hypercube_le_R (n : ℕ) : graphRamsey (hypercube n) ≤ R (2 ^ n)

theorem graphRamsey_le_R {V : Type*} [Fintype V] (G : SimpleGraph V) :
    graphRamsey G ≤ R (Fintype.card V)

theorem graphRamseyProp_ramsey {V : Type*} [Fintype V] (G : SimpleGraph V) :
    GraphRamseyProp (ramsey (Fintype.card V) (Fintype.card V)) G

theorem isContained_of_not_cliqueFree {V : Type*} [Fintype V] (G : SimpleGraph V) {N : ℕ}
    (R : SimpleGraph (Fin N)) (hR : ¬ R.CliqueFree (Fintype.card V)) : G ⊑ R

theorem ramsey_diag_le_four_pow (n : ℕ) : ramsey n n ≤ 4 ^ n
```

`hypercube n` is `Q_n` (vertices: the `2^n` vectors `Fin n → Bool`; adjacent when they differ in exactly one coordinate), `ramsey m n` is `r(m, n)`, `R n = r(n, n)` is `R(K_n)`, and `graphRamsey G` is `R(G)`, the least `N` such that every red/blue colouring of `K_N` has a monochromatic copy of `G` (an `sInf` over a set that the fourth theorem shows nonempty, so it is honest). The first theorem (data binder `n`) is the page's bound with `C = 4`; the second is the page's `R(Q_n) ≤ R(K_{2^n})`; the third is the general `R(G) ≤ R(|V|)`; the fourth and fifth are the two steps behind it; the last is the Erdős–Szekeres bound `r(n, n) ≤ C(2n, n) − 1 ≤ 4^n` ([Proof/Bound.lean](Proof/Bound.lean)). There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

If `R` on `Fin N` has an `m`-clique with `m = |V|`, an embedding of `K_m` into `R` composed with a bijection `V ≃ Fin m` is an injective homomorphism `G → R` (adjacent vertices of `G` are distinct, hence adjacent in the clique). By the two-colour Ramsey theorem, every colouring of `K_{r(m,m)}` has a red or a blue `K_m`, so `r(m, m)` vertices force a monochromatic copy of `G` and `R(G) ≤ R(m)`. For `G = Q_n`, `m = 2^n`. Finally `r(m, m) ≤ C(2m, m) − 1 ≤ 4^m` by the Erdős–Szekeres recursion and Mathlib's central-binomial bound.

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

The problem is due to Burr and Erdős (BuEr75; Er93). The trivial bound is the folklore observation recorded on the problem page; the `4^m` bound on diagonal Ramsey numbers is Erdős–Szekeres. The Lean development is written from scratch by us: the two-colour Ramsey toolbox ([Proof/RamseyDefs.lean](Proof/RamseyDefs.lean), [Proof/Ramsey.lean](Proof/Ramsey.lean), [Proof/Bound.lean](Proof/Bound.lean)) is reused from our own earlier submissions for JSP-000669 and JSP-000099, as noted in their module docstrings; the hypercube, the graph Ramsey number and the proofs are new to this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the Burr–Erdős conjecture. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000175-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
