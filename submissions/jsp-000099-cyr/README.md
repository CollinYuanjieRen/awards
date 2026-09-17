# JSP-000099: the Ramsey lower bound for regular induced subgraphs (Erdős #82, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000099](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000099) / [Erdős Problem #82](https://www.erdosproblems.com/82): let `F(n)` be maximal such that every graph on `n` vertices contains a regular induced subgraph on at least `F(n)` vertices; prove that `F(n)/log n → ∞`. The component formalized here is the lower bound recorded on the problem page, **"Ramsey's theorem implies that `F(n) ≫ log n`"**, in the explicit form **`F(m) ≥ ⌊log₄ m⌋`** for every `m`, equivalently **`G(k) ≤ r(k, k) ≤ C(2k, k) − 1 < 4^k`** for the page's `G(k)` (the least `m` such that every graph on `m` vertices has a regular induced subgraph on at least `k` vertices), together with the trivial values `G(0) = 0`, `G(1) = 1`, `G(2) = 2`, and the values `G(3) = 5` and `F(5) = 3` of Fajtlowicz–McColgan–Reid–Staton. The open question `F(n)/log n → ∞`, the upper bounds `F(n) ≪ n^{1/2+o(1)}` (Bollobás), `n^{1/2}(log n)^{O(1)}` (Alon–Krivelevich–Sudakov) and `n^{1/2}` (Dyson–McKay), the values `G(4) = 7`, `G(5) = 17`, `F(7) = 4` and the lower-bound witnesses `G(6) ≥ 21`, `G(7) ≥ 30` are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos82`). The two-colour Ramsey numbers and Ramsey's theorem ([Proof/RamseyDefs.lean](Proof/RamseyDefs.lean), [Proof/Ramsey.lean](Proof/Ramsey.lean)) are reused from our own JSP-000669 package (Erdős #812): a red/blue colouring of `K_N` is a `SimpleGraph (Fin N)` (red = adjacent), `IsGood G m n := G.CliqueFree m ∧ Gᶜ.CliqueFree n`, `RamseyProp N m n := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n`, `ramsey m n := sInf {N | RamseyProp N m n}`. Regular induced subgraphs ([Proof/Regular.lean](Proof/Regular.lean)):

```lean
noncomputable def IsRegularOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ d : ℕ, ∀ v ∈ S, (S.filter (fun w => G.Adj v w)).card = d

def HasRegularInduced {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ S : Finset V, n ≤ S.card ∧ IsRegularOn G S

def RegProp (m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin m), HasRegularInduced G n

noncomputable def regThreshold (n : ℕ) : ℕ := sInf {m : ℕ | RegProp m n}   -- the page's G(n)

noncomputable def regGuarantee (m : ℕ) : ℕ := sSup {n : ℕ | RegProp m n}   -- the page's F(m)
```

[Proof/Main.lean](Proof/Main.lean) proves:

```lean
theorem log_le_regGuarantee (m : ℕ) : Nat.log 4 m ≤ regGuarantee m

theorem regThreshold_le_four_pow (n : ℕ) : regThreshold n ≤ 4 ^ n

theorem regThreshold_le_ramsey (n : ℕ) : regThreshold n ≤ ramsey n n

theorem ramsey_le_choose (m n : ℕ) : ramsey m n ≤ (m + n).choose m - 1
```

`regGuarantee m` is the page's `F(m)` (`sSup` of a set bounded by `m` and containing `0`, so a genuine maximum) and `regThreshold n` the page's `G(n)` (`sInf` of a set that is nonempty by Ramsey's theorem, so a genuine minimum; `regProp_regThreshold`). The first theorem is the page's lower bound in explicit form (`Nat.log 4 m = ⌊log₄ m⌋`); the second and third are the same bound for `G`; the fourth is the classical binomial bound on Ramsey numbers. The values `regThreshold_zero`, `regThreshold_one`, `regThreshold_two` (`G(0) = 0`, `G(1) = 1`, `G(2) = 2`) and `hasRegularInduced_log` (the statement for an arbitrary graph on `m` vertices) are proved in the same file. The FMRS95 values are `regThreshold_three : regThreshold 3 = 5` and `regGuarantee_five : regGuarantee 5 = 3`, from `regProp_five_three` (every graph on five vertices has a regular induced subgraph on at least three vertices, proved by a degree argument rather than by enumeration) and two explicit witnesses (the path `P₄`, and `P₄` with an isolated vertex, checked by kernel `decide` over their vertex subsets). There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

A clique on `S` is `(|S| − 1)`-regular and an independent set is `0`-regular, so a graph on `r(k, k)` vertices, which contains a monochromatic `K_k`, has a regular induced subgraph on `k` vertices: `G(k) ≤ r(k, k)`. Our Ramsey induction gives `RamseyProp (A + B + 1) m n` from `RamseyProp A (m−1) n` and `RamseyProp B m (n−1)`; with Pascal's rule this yields `r(m, n) ≤ C(m + n, m) − 1` by induction on `m + n` (with `r(0, n) = r(m, 0) = 0`), hence `r(k, k) < C(2k, k) ≤ 4^k`. For `m ≥ 1` and `k = ⌊log₄ m⌋` we have `4^k ≤ m`; every graph on `m` vertices restricts to its first `4^k` vertices, which contain a regular induced subgraph on `k` vertices (the induced-subgraph property is monotone in the number of vertices), so `F(m) ≥ k`. For `G(3) = 5`: a graph on five vertices with no triangle and no independent triple has every vertex of degree exactly `2` (a vertex with three neighbours has two adjacent ones or three pairwise non-adjacent ones; a vertex with at most one neighbour has three non-neighbours, which are pairwise adjacent or else contain two non-adjacent ones forming an independent triple with it), so the whole vertex set is regular; `P₄` has no regular induced subgraph on three vertices, and `P₄` plus an isolated vertex has none on four, which also gives `F(5) = 3`. The trivial values: the empty set is regular; a single vertex is regular and no graph on `0` vertices has one; any two vertices induce `K₂` or its complement.

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

The problem was conjectured by Erdős, Fajtlowicz and Staton (Er93, Er95, Er97d). The lower bound is the observation recorded on the problem page ("Ramsey's theorem implies that `F(n) ≫ log n`"); the values `G(1) = 1`, `G(2) = 2`, `G(3) = 5` and `F(5) = 3` are among those of Fajtlowicz, McColgan, Reid and Staton (*Regular induced subgraphs*, Ars Combin. 39 (1995), 149–154). The two-colour Ramsey development is our own, first submitted with JSP-000669. The Lean development is written from scratch in this fleet's packages.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the open question. Third-party submissions for this record (PRs #51, #190, #282) concern certificates for the lower bounds `G(6) ≥ 21` and `G(7) ≥ 30`, a different component; nothing from them is reused. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000099-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
