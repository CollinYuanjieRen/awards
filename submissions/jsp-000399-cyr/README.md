# JSP-000399: the Selfridge–Straus uniqueness criteria for sums of a fixed order (Erdős #494)

This package submits a Lean formalization for intake and review of **part** of [JSP-000399](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000399) / [Erdős Problem #494](https://www.erdosproblems.com/494): can a finite set `A ⊂ ℂ` be recovered from the multiset `A_k` of all sums of `k` distinct elements of `A` (together with `|A|`)? The catalog records the problem as solved on the strength of Selfridge–Straus (1958) and Gordon–Fraenkel–Straus (1962). This package formalizes the two positive criteria of Selfridge–Straus; it does **not** formalize the Gordon–Fraenkel–Straus theorem that for each `k` uniqueness holds for all sufficiently large `|A|` (its proof relies on Ridout's p-adic Roth theorem, which is not available in Mathlib), so it is partial progress on the catalog entry, not full closure.

## Statements

The definitions are reproduced verbatim from the formal-conjectures statement file [`FormalConjectures/ErdosProblems/494.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/494.lean) (Apache 2.0):

```lean
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B
```

[Proof/Main.lean](Proof/Main.lean) proves, in namespace `Erdos494`:

```lean
theorem card_divisible_by_prime_gt_k :
    ∀ (k card p : ℕ), p.Prime → k ∈ Set.Ioo 0 p → p ∣ card → Erdos494Unique k card

theorem k_eq_2_card_not_pow_two :
    ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494Unique 2 card
```

These are exactly the formal-conjectures variants `erdos_494.variants.card_divisible_by_prime_gt_k` and `erdos_494.variants.k_eq_2_card_not_pow_two` (Selfridge–Straus 1958, Corollary to Theorem 4 and Theorem 1): a finite set of complex numbers is determined by its multiset of `k`-fold sums of distinct elements whenever a prime larger than `k` divides its cardinality, and for `k = 2` whenever its cardinality is not a power of two. There are no additional hypotheses, custom axioms, or unproved inputs.

For the MerLean binder audit the same file also states `card_divisible_by_prime_gt_k_explicit` and `k_eq_2_card_not_pow_two_explicit`, one-line instances of the two theorems with every quantifier and hypothesis exposed as a named binder; the comparator statements are the verbatim `∀`-forms above.

## Proof outline

Write `S_j(A) = ∑_{a∈A} a^j` and let `E(a) = exp(a·x) ∈ ℂ⟦x⟧`. Since `E(a)E(b) = E(a+b)`, the elementary symmetric function `e_m = ∑_{|T|=m} ∏_{a∈T} E(a) = ∑_T E(∑T)` has `x^j`-coefficient `(∑_{|T|=m} (∑T)^j)/j!`, which is a function of the multiset `A_m` alone, and the power sums `p_i = ∑_a E(a)^i = ∑_a E(ia)` have `x^j`-coefficient `i^j S_j(A)/j!` ([Proof/Exp.lean](Proof/Exp.lean), including Newton's identity `m e_m = ∑_{i=1}^{m} (−1)^{i−1} e_{m−i} p_i` in `ℂ⟦x⟧`, obtained from Mathlib's Newton identities). Comparing coefficients and inducting on `m` shows ([Proof/Coeff.lean](Proof/Coeff.lean)): if `|A| = |B| = n` and `S_i(A) = S_i(B)` for `1 ≤ i < j`, then

`j!·(coeff_j e_m(A) − coeff_j e_m(B)) = acoef(n, j, m)·(S_j(A) − S_j(B))`, where `acoef(n, j, m) = ∑_{c=1}^{m} (−1)^{c−1} c^{j−1} C(n, m−c)`.

[Proof/Arith.lean](Proof/Arith.lean) proves the Newton-type recursion satisfied by this closed form, `acoef(n, j, 2) = n − 2^{j−1}`, and that `acoef(n, j, m) ≡ (−1)^{m−1} m^{j−1} (mod p)` is a unit modulo any prime `p > m` dividing `n` (because `C(n, r) ≡ 0 (mod p)` for `0 < r < p`). Hence, when `A_k = B_k`, strong induction on `j` gives `S_j(A) = S_j(B)` for all `j ≥ 1`, and in characteristic zero the power sums determine the set ([Proof/PowerSums.lean](Proof/PowerSums.lean): Newton's identities recover the elementary symmetric functions, `∏(X − a)` is then determined, and its roots are the set).

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks both root statements with typed `example`s, prints the definitions, and prints the axioms of both roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the two statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for both theorems (and for the two explicit-binder instances). These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The mathematics is due to J. L. Selfridge and E. G. Straus, *On the determination of numbers by their sums of a fixed order*, Pacific J. Math. 8 (1958), 847–856 ([DOI](https://doi.org/10.2140/pjm.1958.8.847)); the generating-function organization of their argument used here is a routine restatement. The complementary results — the counterexamples for `|A| = k`, `|A| = 2k` and `|A| = 2^l` (`k = 2`), formalized in the hjyuh formal-conjectures fork and in plby/lean-proofs (`Erdos494.lean`, Codex / GPT-5.6 Sol) — and the Gordon–Fraenkel–Straus eventual-uniqueness theorem are not re-proved or claimed here. The earlier third-party submission [PR #23](https://github.com/TheJustinSunPrize/awards/pull/23) contains list-based counterexamples only.

The contribution sought is formalization of the two Selfridge–Straus criteria, not a new mathematical result and not full closure of the catalog entry. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000399-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
