# JSP-000510: the Erdős–Rubin–Taylor bounds on the least non-k-choosable bipartite graph (Erdős #629, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000510](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000510) / [Erdős Problem #629](https://www.erdosproblems.com/629): determine the minimal number of vertices `n(k)` of a bipartite graph whose list chromatic number exceeds `k`. The component formalized here is the lower bound recorded on the problem page, due to Erdős, Rubin and Taylor (1979), **`2^{k−1} < n(k)`**, proved in the sharper form **`2^k ≤ n(k)`** (every bipartite graph on fewer than `2^k` vertices is `k`-choosable), together with the ERT witness that `n(k)` is attained and **`n(k) ≤ 2·C(2k−1, k)`** (`K_{m,m}` with `m = C(2k−1, k)` is not `k`-choosable), and the consequence **`n(1) = 2`**. The exact values `n(2) = 6` (ERT) and `n(3) = 14` (Hanson–MacGillivray–Toft), the upper bound `k² 2^{k+2}`, the property-B comparison `M_k ≤ n(k) ≤ 2 M_k` and the Radhakrishnan–Srinivasan bound are **not** claimed. This is a known lower-bound component and is labelled as such.

## Statements

All definitions are our own (namespace `Erdos629`, [Proof/Main.lean](Proof/Main.lean)); colours are natural numbers, a bipartite graph is a `2`-colourable `SimpleGraph` (Mathlib's `Colorable`):

```lean
def ListColorable {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ) : Prop :=
  ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

def Choosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ListColorable G L

noncomputable def listThreshold (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.Colorable 2 ∧ ¬ Choosable G k}

theorem two_pow_le_listThreshold (k : ℕ) : 2 ^ k ≤ listThreshold k

theorem ert_lower_bound : ∀ k, 1 ≤ k → 2 ^ (k - 1) < listThreshold k

theorem listThreshold_le : ∀ k, listThreshold k ≤ 2 * (2 * k - 1).choose k

theorem listThreshold_one : listThreshold 1 = 2
```

`listThreshold k` is the page's `n(k)` (ERT's `N(2,k)`): the least order of a `2`-colourable graph that is not `k`-choosable; `Choosable G k` is the page's "`χ_L(G) ≤ k`". The first theorem is the lower bound as the random-partition argument gives it; the second is the page's form; the third is ERT's witness bound (so the infimum is a minimum, attained by a graph on at most `2·C(2k−1, k)` vertices); the fourth is the value `N(2,1) = 2` from ERT's table. The supporting theorems `choosable_of_card_lt` (every `2`-colourable graph on fewer than `2^k` vertices is `k`-choosable) and `exists_bipartite_not_choosable` (for every `k` some bipartite graph is not `k`-choosable) are proved in the same file. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Lower bound (ERT pp. 127–128, with Erdős's property-B count carried out directly): let `G` be `2`-coloured by `c`, with `n < 2^k` vertices and lists `L v` of size `k`, and let `C` be the union of the lists. For `S ⊆ C` call `v` bad if `c v = 0` and `L v ∩ S = ∅`, or `c v = 1` and `L v ⊆ S`. For each `v` exactly `2^{|C|−k}` subsets `S` make `v` bad (the subsets of `C \ L v`, resp. the supersets of `L v` inside `C`, counted with Mathlib's `Finset.card_powerset` and `Finset.card_Icc_finset`), so summing over all `S ⊆ C` the number of bad vertices totals `n · 2^{|C|−k} < 2^{|C|}`, and some `S` has no bad vertex. Colouring the vertices with `c v = 0` from `L v ∩ S` and those with `c v = 1` from `L v \ S` is proper, since adjacent vertices have different `c`. Hence every `n` in the defining set is at least `2^k`. Witness (ERT p. 126): on `K_{m,m}` with `m = C(2k−1, k)` assign the `k`-subsets of `{0, …, 2k−2}` bijectively as lists on each side. In a proper list colouring the colour sets used on the two sides are disjoint; each has at least `k` elements (otherwise its complement in `{0, …, 2k−2}` contains a `k`-subset, the list of a vertex whose colour would have to lie outside it), so together they have at least `2k > 2k−1` elements, a contradiction. For `k = 0` a single vertex with an empty list is not `0`-choosable. The witness is transported to `Fin (m + m)` along `finSumFinEquiv`, so the defining set is nonempty and `n(k) ≤ 2m`; with `2^1 ≤ n(1) ≤ 2·C(1,1)` this gives `n(1) = 2`.

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

The problem and both bounds are due to P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Proc. West Coast Conference on Combinatorics, Graph Theory and Computing (Arcata, 1979), Congressus Numerantium 26 (1980), 125–157 (pp. 126–128; the scan in the Rényi Institute archive of Erdős's papers was used). ERT state the lower bound as `2^{k−1} < M_k ≤ N(2,k)` through the property-B threshold `M_k`; the formalized argument applies Erdős's random-set count directly to the two sides of the bipartition, which yields `2^k ≤ n(k)` and is the standard argument for the choice number of bipartite graphs. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the determination of `n(k)`. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000510-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
