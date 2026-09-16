# JSP-000600: the upper bound for the number of block-compatible sequences (Erdős #732)

This package submits a Lean formalization for intake and eligibility review. It concerns [JSP-000600](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000600) / [Erdős Problem #732](https://www.erdosproblems.com/732). The catalog records the counting question of that problem as solved by an upper bound on the number of block-compatible sequences together with Noga Alon's lower bound. Alon's lower bound has an existing formal proof (see Attribution). This package formalizes the missing upper bound.

## Statement and proof

A pairwise balanced design on a finite point type `P` is a finite family of blocks (subsets of `P`) such that every block has at least two points and every pair of distinct points lies in exactly one block. A multiset `S` of natural numbers is block-compatible for `n` if some pairwise balanced design on `Fin n` has `S` as its multiset of block sizes. The three definitions `PairwiseBalancedDesign`, `blockSizes` and `BlockCompatible` in [Proof/Design.lean](Proof/Design.lean) are reproduced verbatim from the existing formalization of the lower bound, so that both bounds are stated for the same objects.

[Proof/Main.lean](Proof/Main.lean) proves `Erdos732Upper.erdos_732_upper`:

```lean
∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  {S : Multiset ℕ | BlockCompatible n S}.Finite ∧
    (({S : Multiset ℕ | BlockCompatible n S}.ncard : ℝ) ≤
      Real.exp (C * Real.sqrt n * Real.log n))
```

That is, the number of block-compatible sequences for `n` is at most `exp(O(√n log n))`, the bound stated by Erdős (Combinatorica 1981, see the problem page) and proved in Alon's note (Section 3). The finiteness conjunct makes `Set.ncard` meaningful. Sequences are counted as multisets, i.e. up to order, exactly as in the formal lower bound. There are no additional hypotheses, custom axioms, or unproved inputs; every intermediate fact is proved in Lean from Mathlib.

Proof outline (Alon, remark191.pdf, §3, third bullet; constants are not optimized):

1. Every block contains a pair of distinct points and distinct blocks contain distinct pairs, so a design on `n` points has at most `n²` blocks and every multiplicity in its size multiset is at most `n²` ([Proof/Design.lean](Proof/Design.lean)).
2. Let `T = ⌊√(2n)⌋ + 1`, so `T(T+1)/2 > n`. Two distinct blocks share at most one point, so `T` blocks with at least `T` points each would cover at least `T·T − T(T−1)/2 = T(T+1)/2 > n` points. Hence fewer than `T` block sizes are `≥ T` ([Proof/LargeBlocks.lean](Proof/LargeBlocks.lean)).
3. A block-compatible multiset is therefore determined by the multiplicities of the sizes below `T` (each `≤ n²`) together with a multiset of fewer than `T` sizes in `[T, n]`. Counting these data gives an explicit bound `(n²+1)^T · T · (T(n+1)+1)^T` ([Proof/Encoding.lean](Proof/Encoding.lean)), which is `exp(O(√n log n))` ([Proof/Main.lean](Proof/Main.lean)).

[Proof/Witness.lean](Proof/Witness.lean) additionally exhibits, for every `n`, the design of all `2`-element subsets of `Fin n` and proves that `n.choose 2` copies of `2` form a block-compatible multiset (`blockCompatible_replicate_two`), so the definitions are not vacuous; this witness is not used by the main theorem.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness; it avoids rebuilding dependencies.

[Audit.lean](Audit.lean) re-checks the root statement with a typed `example`, prints the definitions, and prints the axioms of the root theorem and of the witness theorem. [verification.txt](verification.txt) records the local build and audit of this exported package.

[Challenge.lean](Challenge.lean) is a comparator-style challenge module: it imports only Mathlib and restates the three definitions and the target theorem with a `sorry` proof, for mechanical comparison against `Proof/Main.lean`; it is not part of the proof build.

## Axiom audit

`#print axioms Erdos732Upper.erdos_732_upper` reports exactly `[propext, Classical.choice, Quot.sound]`. These three are the standard foundational axioms of Lean 4's core library on which Mathlib is built (propositional extensionality, the axiom of choice, and quotient soundness); every Mathlib-based development, including the previously registered Lean proofs in this repository, depends on them. The proof introduces no project axiom, no `sorry`/`admit` (so `sorryAx` is absent), no `native_decide` or other trusted-code shortcut, no unsafe or opaque definitions, and no hypothesis beyond the problem's own definitions: the root theorem has an empty binder prefix, and the two record fields of `PairwiseBalancedDesign` are exactly the defining properties of a pairwise balanced design. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The upper bound is due to Paul Erdős (P. Erdős, *On the combinatorial problems which I would most like to see solved*, Combinatorica 1 (1981), 25–42), who stated it without a published proof; the proof formalized here is the one printed by Noga Alon in *Blocking partial designs and block-compatible sequences* ([remark191.pdf](https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf), Section 3, concluding remarks), which is the source cited by the catalog entry. Neither source was used as a proof assumption.

The lower bound `exp(c √n log n)` is due to Alon (Theorem 2.3 of the same note) and was formalized earlier by Codex and GPT-5.6 Sol in [plby/lean-proofs, `ErdosProblems/Erdos732.lean`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos732.lean) (theorem `Erdos732.erdos_732`). This package does not re-prove the lower bound and claims no credit for it; its three shared definitions are copied verbatim from that Apache-2.0 file with attribution in the file header. The problem page's first question (necessary and sufficient conditions for block-compatibility) remains open and is not addressed.

The contribution sought is formalization of the upper bound, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000600-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
