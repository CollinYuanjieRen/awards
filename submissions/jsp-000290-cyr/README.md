# JSP-000290: van Doorn's theorem on strongly complete sequences (Erdős #348, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000290](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000290) / [Erdős Problem #348](https://www.erdosproblems.com/348): for which `0 ≤ m < n` is there a complete sequence `a₁ ≤ a₂ ≤ ⋯` that remains complete after removing any `m` elements but is not complete after removing any `n` elements? The component formalized here is the result recorded on the problem page and named in the catalog record as its progress, **van Doorn's theorem**: under the strong notion of completeness (every natural number is a sum of distinct terms), a sequence that stays complete after the removal of any `m ≥ 2` terms stays complete after the removal of a suitable **infinite** set of terms; consequently **no pair `(m, n)` with `2 ≤ m < n` exists** under strong completeness. The weak notion of completeness (finitely many exceptions), which the page notes is probably what Erdős and Graham intended, and the positive examples `(0, 1)` (powers of two) and `(1, 2)` (Fibonacci numbers) are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos348`, [Proof/Main.lean](Proof/Main.lean)). A multiset of positive integers listed in nondecreasing order is `a : ℕ → ℕ` with `Monotone a` and `∀ i, 1 ≤ a i`; removing terms is restricting the set `T` of allowed indices:

```lean
def Complete (a : ℕ → ℕ) (T : Set ℕ) : Prop :=
  ∀ x : ℕ, ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ T ∧ ∑ i ∈ F, a i = x

def RobustlyComplete (a : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = m → Complete a (↑S : Set ℕ)ᶜ

theorem strongPairs_ge_two_eq_empty :
    {p : ℕ × ℕ | 2 ≤ p.1 ∧ p.1 < p.2 ∧ ∃ a : ℕ → ℕ, Monotone a ∧ (∀ i, 1 ≤ a i) ∧
      RobustlyComplete a p.1 ∧ ∀ S : Finset ℕ, S.card = p.2 → ¬ Complete a (↑S : Set ℕ)ᶜ} = ∅

theorem exists_infinite_removal (a : ℕ → ℕ) (ha : Monotone a) (hpos : ∀ i, 1 ≤ a i) (m : ℕ)
    (hm : 2 ≤ m) (h : RobustlyComplete a m) : ∃ R : Set ℕ, R.Infinite ∧ Complete a Rᶜ

theorem exists_removal_card (a : ℕ → ℕ) (ha : Monotone a) (hpos : ∀ i, 1 ≤ a i) (m : ℕ)
    (hm : 2 ≤ m) (h : RobustlyComplete a m) (n : ℕ) :
    ∃ S : Finset ℕ, S.card = n ∧ Complete a (↑S : Set ℕ)ᶜ
```

The first theorem is the page's question restricted to `m ≥ 2` under strong completeness, answered by "no such pair" (its hypotheses are exactly the page's: a nondecreasing sequence of positive integers, complete after removing any `m` elements, not complete after removing any `n` elements). The second is van Doorn's theorem, the third its finite consequence. `Complete` counts `0` as represented by the empty sum, which is the same as van Doorn's condition on the positive integers. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Van Doorn's argument in an index-set formulation. Write `prefixSum T k` for the sum of the allowed terms with index below `k`. (A) If `T` is infinite, all terms are positive and `a k ≤ 1 + prefixSum T k` for every allowed `k`, then every natural number is a sum over a finite subset of `T` (induction on `k` shows every `x ≤ prefixSum T k` is a sum over `T ∩ [0, k)`; the prefix sums are unbounded). (B) If removing any `m` indices keeps completeness, then `a (k + m) ≤ 1 + Σ_{i<k} a i` for all `k`: otherwise remove `{k, …, k+m−1}`; the number `a (k+m) − 1` exceeds the sum of the terms with index below `k` and is smaller than every term with index at least `k + m`, so it is not representable. (C) If the removed indices below `k` have total less than `a (p−1) + a p` for some `p ≤ k − 1`, then `1 + prefixSum Rᶜ k ≥ 1 + Σ_{i<k−2} a i ≥ a (k−2+m) ≥ a k` since `m ≥ 2` and `a` is nondecreasing. (D) If `a` is unbounded, remove greedily: `idx 0 = 0` and `idx (j+1)` is the least `i ≥ idx j + 2` with `a (i−1)` larger than the sum of the terms removed so far; this makes the removed set infinite and gives the estimate of (C) at every allowed `k ≥ 2`, while `k = 1` is handled by `a 1 ≤ a m ≤ 1` from (B). (E) If `a` is bounded it is eventually constant; removing every other index from that point on gives an infinite set for which (C)-type estimates follow from (B) directly. Van Doorn assumes `a_i → ∞` without loss of generality; the bounded case is carried out separately here. (F) Removing any `n` indices of the infinite set keeps completeness (completeness is monotone in the allowed set), contradicting "not complete after removing any `n` elements", so the set of pairs with `2 ≤ m < n` is empty.

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

The problem is due to Erdős and Graham (ErGr80). The theorem is due to Wouter van Doorn, *Any multiset which is entirely complete after removing any two elements remains entirely complete after removing a specific infinite set* (note in the author's Mathematical-shorts repository, linked from the problem page); the subset-sum criterion (his Lemma 1) is classical. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the question under the weak notion of completeness. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000290-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
