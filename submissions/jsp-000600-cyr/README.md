# JSP-000600: the number of block-compatible sequences, both bounds (Erdős #732)

This package submits a Lean formalization for intake and eligibility review. It concerns [JSP-000600](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000600) / [Erdős Problem #732](https://www.erdosproblems.com/732). The problem page asks two things about *block-compatible* sequences for `{1, …, n}` (sequences `1 < X_1 ≤ ⋯ ≤ X_m ≤ n` that are the block sizes of a pairwise balanced block design on `{1, …, n}`, i.e. a family of subsets in which every pair of distinct points lies in exactly one subset): (i) whether there are necessary and sufficient conditions for block-compatibility, and (ii) whether there is a constant `c > 0` such that for all large `n` there are at least `exp(c n^{1/2} log n)` block-compatible sequences. The page records the problem as PROVED: the answer to (ii) is yes (Alon), and Erdős had shown the matching upper bound `exp(O(n^{1/2} log n))`. Question (i) is an open-ended request for a criterion, not a theorem; Erdős himself was not sure that a reasonable criterion exists, and nothing about it is claimed here.

This package formalizes **both bounds of (ii)**: the number of block-compatible size multisets for `n` is `exp(Θ(√n log n))`. It supersedes the earlier version of this submission (commit `bb4c53e847da438895921ee2290ca19437e08996` of this repository), which contained only the upper bound; that upper-bound development is included as the modules `Design`, `LargeBlocks`, `Encoding`, `Main` and `Witness` with every definition, statement and proof unchanged (only the module prefix in the import lines and one word of a doc-comment differ), and the lower bound is new.

## Statement and proof

A pairwise balanced design on a finite point type `P` ([Erdos732Designs/Design.lean](Erdos732Designs/Design.lean), `Erdos732Upper.PairwiseBalancedDesign`) is a finite family of blocks (subsets of `P`) such that every block has at least two points and every pair of distinct points lies in exactly one block. Its `blockSizes` is the multiset of block cardinalities, and `BlockCompatible n S` means that some design on `Fin n` has `S` as its multiset of block sizes. Block-compatible *sequences* are counted as multisets, i.e. up to order — a nondecreasing sequence of integers `> 1` is the same datum as a finite multiset of naturals `≥ 2`, and the condition `1 < X_i` of the page is the field `two_le_card`.

[Erdos732Designs/Full.lean](Erdos732Designs/Full.lean) proves `Erdos732.erdos_732`:

```lean
∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  {S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.Finite ∧
    Real.exp (c * Real.sqrt n * Real.log n) ≤
      ({S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.ncard : ℝ) ∧
    ({S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.ncard : ℝ) ≤
      Real.exp (C * Real.sqrt n * Real.log n)
```

The two halves are `Erdos732Lower.erdos_732_lower` ([Erdos732Designs/Lower.lean](Erdos732Designs/Lower.lean), with `c = 1/32`, `N = 256`) and `Erdos732Upper.erdos_732_upper` ([Erdos732Designs/Main.lean](Erdos732Designs/Main.lean), with `C = 56`). The finiteness conjunct makes `Set.ncard` meaningful; it is proved inside the upper-bound argument and repeated in the lower-bound theorem so that each half is self-contained. There are no additional hypotheses, custom axioms or unproved assumptions.

**Lower bound (Alon, Theorem 2.3 of the note cited below; constants not optimized).** The argument is Alon's, carried out on the affine plane over `ZMod p` instead of a projective plane and padded to arbitrary `n`.

1. *Completion of partial designs* ([Lower/Completion.lean](Erdos732Designs/Lower/Completion.lean)). A family `F` of subsets of `Q` with all blocks of size `≥ 2` and pairwise intersections of size `≤ 1` (`IsPartialDesign`) becomes a pairwise balanced design `completionDesign F` by adding every 2-subset of `Q` not contained in a block of `F` (`uncoveredPairs`). For `s ≠ 2` the multiplicity of `s` among the block sizes of the completion equals its multiplicity among the sizes of `F` (`count_completionDesign_blockSizes`).
2. *Lines of the affine plane* ([Lower/AffinePlane.lean](Erdos732Designs/Lower/AffinePlane.lean)). For a prime `p` and `a, b ∈ ZMod p`, `line p a b = {(x, y) | y = a x + b}` has exactly `p` points (`card_line`), and two distinct such lines share at most one point (`line_inter_card_le_one`).
3. *Profiles* ([Lower/Profiles.lean](Erdos732Designs/Lower/Profiles.lean), `exists_many_blockCompatible`). Fix a prime `p` with `p² ≤ n` and embed `ZMod p × ZMod p` into `Fin n`. For each `m : Fin (p-2) → Fin (p+1)` assign to the line `(a, b)` the size `a + 3` if `a < p - 2` and `b < m a`, and `2` otherwise; choose a sub-block of that size inside each embedded line. The chosen sub-blocks form a partial design (they sit inside lines that pairwise share at most one point); completing it gives a design on `Fin n`, and by step 1 the number of blocks of size `i + 3` in it is exactly `m i`. Hence `m ↦ blockSizes` is injective, and there are at least `(p+1)^{p-2}` block-compatible multisets for `n`.
4. *Asymptotics* ([Lower/Asymptotics.lean](Erdos732Designs/Lower/Asymptotics.lean)). For `n ≥ 256`, Bertrand's postulate (Mathlib's `Nat.exists_prime_lt_and_le_two_mul`) gives a prime `p` with `p² ≤ n` and `√n < 2p`, so `p - 2 ≥ √n / 4` and `log (p+1) ≥ log n / 8`, whence `(p+1)^{p-2} ≥ exp(√n log n / 32)` (`exp_le_pow`).

**Upper bound (Erdős; proof printed by Alon, §3).** A design on `n` points has at most `n²` blocks; fewer than `T = ⌊√(2n)⌋ + 1` of its blocks have `≥ T` points (two blocks share at most one point); so a block-compatible multiset is determined by the multiplicities of the sizes below `T` and a short list of large sizes, giving at most `exp(56 √n log n)` possibilities for `n ≥ 2` ([Erdos732Designs/LargeBlocks.lean](Erdos732Designs/LargeBlocks.lean), [Encoding.lean](Erdos732Designs/Encoding.lean), [Main.lean](Erdos732Designs/Main.lean)). [Witness.lean](Erdos732Designs/Witness.lean) shows the definitions are not vacuous (`n.choose 2` copies of `2` are block-compatible for every `n`).

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The Lean toolchain is pinned in [lean-toolchain](lean-toolchain) (`leanprover/lean4:v4.34.0-rc1`); Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the root, both halves, the profile-counting lemma and the non-vacuity witness as typed `example`s closed by the theorems, prints the three definitions, and prints the axioms of the root and of every named component. Every declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the dependency cone. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit by the designated verifiers and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly. Local verification used cached upstream dependencies on arm64 macOS; it is not a clean network-disabled rebuild, and no independent-checker claim is made.

There is no Formal Conjectures module for Erdős #732 (when fetched on 2026-09-17 the problem page listed "Formalised statement? No", and the google-deepmind/formal-conjectures checkout of the same day has no `ErdosProblems/732.lean`), so no official comparator run is possible; the statement above is this package's own transcription of the page's question (ii), argued clause by clause in this README.

## Attribution and submission status

The lower bound is due to Noga Alon, *Blocking partial designs and block-compatible sequences* ([remark191.pdf](https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf)), Theorem 2.3; the upper bound is due to Paul Erdős (*On the combinatorial problems which I would most like to see solved*, Combinatorica 1 (1981), 25–42), with the proof printed in Section 3 of Alon's note. This package formalizes established mathematics and claims no new mathematical result.

The three definitions `PairwiseBalancedDesign`, `blockSizes` and `BlockCompatible` were reproduced, in the earlier version of this submission, from the formalization of Alon's lower bound by Codex and GPT-5.6 Sol in [plby/lean-proofs, `ErdosProblems/Erdos732.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos732.lean) (Apache License 2.0; the module header of [Design.lean](Erdos732Designs/Design.lean) records this), so that both bounds are stated for the same objects as that earlier formal lower bound. That earlier Lean proof of the lower bound is prior art and is credited as such; the lower-bound proof in this package was designed from Alon's paper and written without consulting that earlier Lean proof or any other Lean proof of the result. Upstream [PR #307](https://github.com/TheJustinSunPrize/awards/pull/307) (a third party's self-described partial formalization of the finite-field profile construction) was likewise not consulted. No first-formalization or priority claim is made for the lower bound; the contribution sought is a complete, self-contained formalization of both bounds of the counting question.

The Lean code was prepared with Claude Code (Anthropic) assistance — Claude Fable 5.1 for the mathematical design and coordination, Claude Opus for the Lean implementation — and checked locally. This is a self-submission with a direct interest in the review outcome; no solver nomination, award tier, payment status or official verification status is asserted or changed.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
