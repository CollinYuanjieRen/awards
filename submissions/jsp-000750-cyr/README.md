# JSP-000750: Schütte's tournament problem — f(1) = 3, f(2) = 7 and Erdős's lower bound (Erdős #902, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000750](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000750) / [Erdős Problem #902](https://www.erdosproblems.com/902) (Schütte's problem): let `f(n)` be the least number of vertices of a tournament in which every set of `n` vertices is dominated by some other vertex (a vertex outside the set beating all of its members). The problem asks for the order of magnitude of `f(n)`, which is open (`n 2^n ≪ f(n) ≪ n² 2^n`). The component formalized here is the published elementary part: **`f(1) = 3`, `f(2) = 7`, and Erdős's 1963 lower bound `2^(n+1) − 1 ≤ f(n)`**. The open estimate of `f(n)`, Erdős's upper bound `f(n) ≪ n² 2^n` and the Szekeres–Szekeres value `f(3) = 19` are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos902`, [Proof/Defs.lean](Proof/Defs.lean)):

```lean
def IsTournament (r : V → V → Prop) : Prop :=              -- irreflexive, one direction per pair
  (∀ v, ¬ r v v) ∧ ∀ u v, u ≠ v → (r u v ↔ ¬ r v u)

def Dominates (r : V → V → Prop) (w : V) (S : Finset V) : Prop :=   -- w ∉ S beats all of S
  w ∉ S ∧ ∀ v ∈ S, r w v

def HasProperty (r : V → V → Prop) (n : ℕ) : Prop :=       -- the n-domination property
  (∃ S : Finset V, S.card = n) ∧ ∀ S : Finset V, S.card = n → ∃ w, Dominates r w S

noncomputable def schutte (n : ℕ) : ℕ :=                   -- Schütte's f(n)
  sInf {N : ℕ | ∃ r : Fin N → Fin N → Prop, IsTournament r ∧ HasProperty r n}
```

The first clause of `HasProperty` says that the tournament has at least `n` vertices; without it a tournament on fewer than `n` vertices would satisfy the condition vacuously and `f(n)` would be `0`. The clause is automatic once the tournament has at least `n` vertices (`hasProperty_iff_of_le` in [Proof/Defs.lean](Proof/Defs.lean)), so it changes nothing on the intended range. [Proof/Main.lean](Proof/Main.lean) proves:

```lean
theorem two_pow_sub_one_le_of_hasProperty (N n : ℕ) (r : Fin N → Fin N → Prop)
    (hr : IsTournament r) (hn : HasProperty r n) : 2 ^ (n + 1) - 1 ≤ N

theorem two_pow_sub_one_le_schutte (n : ℕ)
    (h : ∃ N : ℕ, ∃ r : Fin N → Fin N → Prop, IsTournament r ∧ HasProperty r n) :
    2 ^ (n + 1) - 1 ≤ schutte n

theorem schutte_one : schutte 1 = 3

theorem schutte_two : schutte 2 = 7
```

The first theorem is Erdős's lower bound in universal form: every tournament on `N` vertices with the `n`-domination property has `N ≥ 2^(n+1) − 1`. The second restates it for `f(n)`; its hypothesis is needed only because `sInf ∅ = 0` in `ℕ` (Erdős's upper bound, which shows the set is nonempty for every `n`, is outside this component). The last two are the exact values. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Lower bound ([Proof/LowerBound.lean](Proof/LowerBound.lean)), by induction on `n` over all finite vertex types. For `n = 0` the empty set must be dominated, so there is a vertex. For `n + 1`: every vertex has in-degree at least `n` (otherwise its in-neighbourhood `I` together with the vertex extends to an `(n+1)`-set whose dominator beats the vertex, hence lies in `I`, inside the set). In-degrees and out-degrees have equal sums and add up to `|V| − 1` at every vertex, so some `v` has `2·indeg(v) ≤ |V| − 1`. The tournament restricted to `I = {u : u beats v}` has the `n`-domination property: an `n`-set `S ⊆ I` together with `v` is an `(n+1)`-set, its dominator beats `v` and so lies in `I` outside `S`. By induction `|I| ≥ 2^(n+1) − 1`, hence `|V| ≥ 2|I| + 1 ≥ 2^(n+2) − 1`. Exact values ([Proof/Examples.lean](Proof/Examples.lean)): the cyclic tournament on `ℤ/3` has the `1`-domination property and the Paley tournament on `ℤ/7` (`i` beats `j` iff `j − i ∈ {1, 2, 4}`) has the `2`-domination property; both are finite checks by `decide`. Together with the lower bound this gives `f(1) = 3` and `f(2) = 7`.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all four theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems; the finite checks use the kernel-checked `decide`. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Schütte's, recorded by P. Erdős; the lower bound is P. Erdős, *On a problem in graph theory*, The Mathematical Gazette 47 (1963), 220–223 (the argument formalized is the standard double-counting induction; the paper itself is paywalled at Cambridge Core, and the statement is taken from the problem page). The values `f(1) = 3`, `f(2) = 7` are the "easy to check" facts recorded on the problem page. `f(3) = 19` and `n 2^n ≪ f(n)` are due to G. Szekeres and E. Szekeres (Math. Gazette 49 (1965), 290–293) and are not formalized. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the open question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000750-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
