# JSP-000663: small bases for square-root-size sets (Erdős #806)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000663](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000663), which is [Erdős Problem #806](https://www.erdosproblems.com/806) (Erdős–Newman [ErNe77]): let `A ⊆ {1, …, n}` with `|A| ≤ n^{1/2}`; must there exist `B ⊂ ℤ` with `|B| = o(n^{1/2})` such that `A ⊆ B + B`? The answer is yes: Alon, Bukh and Sudakov [ABS09] proved that such a `B` exists with `|B| ≪ n^{1/2} log log n / log n`.

## Statement and proof

[Erdos806SmallBases/Main.lean](Erdos806SmallBases/Main.lean) and [Erdos806SmallBases/Params.lean](Erdos806SmallBases/Params.lean) prove

```lean
theorem erdos_806 :
    ∃ β : ℕ → ℕ, (fun n : ℕ => (β n : ℝ)) =o[atTop] (fun n : ℕ => Real.sqrt n) ∧
      ∀ n, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ Real.sqrt n →
        ∃ B : Finset ℤ, HasBasis A B ∧ B.card ≤ β n
theorem erdos_806_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ Real.sqrt n →
      ∃ B : Finset ℤ, HasBasis A B ∧ (B.card : ℝ) ≤ ε * Real.sqrt n
```

where `HasBasis A B` ([Erdos806SmallBases/Definitions.lean](Erdos806SmallBases/Definitions.lean)) says that every `a ∈ A` is `b + b'` for some `b, b' ∈ B`, i.e. `A ⊆ B + B` with `B ⊂ ℤ` as in the problem. The first theorem is the statement of the problem: the size of the required basis is bounded by a single function `β(n) = o(√n)` of `n` alone, uniformly over all admissible `A` (this is the meaning of "`|B| = o(n^{1/2})`" in the question, where the bound may depend only on `n`). The second is the equivalent explicit `ε`–`N` form, from which the first is derived by taking `β(n)` to be the least uniform bound. [Audit.lean](Audit.lean) restates both as typed `example`s.

The proof is an elementary deterministic construction, written for this package:

1. [Digits.lean](Erdos806SmallBases/Digits.lean): fix `k ≥ 1`, `q ≥ 1` and `M = q^k`. The *universal set* `U` is the set of numbers below `M` having some base-`q` digit equal to `0` at a position below `k`; it has at most `k q^{k−1}` elements (`card_univSet`). For any set `T` of at most `k` numbers there is a shift `h < M` such that `(s + h) mod M ∈ U` for every `s ∈ T` (`exists_shift`): number the elements of `T` by positions `p < k` and choose the base-`q` digits of `h` from the lowest position upwards so that the digit at position `p` of `s_p + h` becomes `0` (higher digits of `h` do not affect it).
2. [Chunks.lean](Erdos806SmallBases/Chunks.lean): any finite set `S` is covered by at most `|S|/k + 1` chunks of at most `k` elements (`exists_chunks`, by ranking the elements).
3. [Assembly.lean](Erdos806SmallBases/Assembly.lean): cut `[1, n]` into blocks `[jM, (j+1)M)`, cut the part of `A` in each block into chunks, choose a shift `h` for each chunk, and take `B = U ∪ (U + M) ∪ { jM − h : chunk of block j }`. Every `a ∈ A` in block `j` and a chunk with shift `h` satisfies `a = (jM − h) + (u + eM)` with `u ∈ U` and `e ∈ {0, 1}`, so `A ⊆ B + B`, and `|B| ≤ 2k q^{k−1} + |A|/k + n/q^k + 1` (`exists_basis_bound`).
4. [Params.lean](Erdos806SmallBases/Params.lean): given `ε > 0`, take `k ≈ 4/ε` and `q` the least integer with `q^k ≥ k(⌊√n⌋ + 1)`; then `|A|/k ≤ ε√n/4`, `n/q^k ≤ ε√n/4`, `2k q^{k−1} ≤ ε√n/4` and `1 ≤ ε√n/4` once `n` is large, because `q^{k−1} = q^k/q ≤ 2^k k(√n + 1)/q` and `q ≥ (k√n)^{1/k} → ∞`. [Main.lean](Erdos806SmallBases/Main.lean) then defines `β(n)` as the least uniform bound and reads off `β = o(√n)`.

No numerical certificate or decision procedure is used.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness.

[Audit.lean](Audit.lean) prints the axioms of both theorems and of the main lemmas. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the package. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (https://www.hejustinsun.com/prize/rules, v1.0, retrieved 16 September 2026; the rules are not part of this repository) require in their section 6 an offline axiom audit by the designated verifiers, list in section 7 the failure to detect placeholder or unreviewed axioms as a ground for revocation, and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official process.

## Attribution and submission status

The theorem is due to Alon, Bukh and Sudakov (Israel J. Math. (2009), 285–301, doi:10.1007/s11856-009-0115-9; arXiv:0711.1604), whose proof gives the sharper bound `|B| ≪ √n log log n / log n`. The argument formalized here proves only the `o(√n)` statement of the problem; it takes from their paper the scheme of the proof of their Theorem 1.4 (cover `A` by translates of a universal set after cutting `A` into short chunks, and lift from the cyclic group to `ℤ` by doubling the set as `U ∪ (U + M)`), and uses in place of their universal sets (a probabilistic one, and a smaller explicit one for cyclic groups built from projective planes) a cruder explicit set of numbers with a zero base-`q` digit, so the estimates are weaker and the proof text is not theirs. A Lean formalization of this problem exists in the repository plby/lean-proofs (file `src/latest/ErdosProblems/Erdos806.lean` at commit `8822f7dd`, whose header a coverage screen of that repository read to identify the problem; its proof text was not opened); that repository has no root LICENSE and its notice `src/latest/LICENSE` covers only externally sourced files, so no license grant applies to it. The present package is an independent formalization written from the mathematical argument without consulting or reusing that proof text; it is offered as a license-clean, first-party kernel-checked proof of the catalog question. It was prepared with Claude Code (Claude Fable 5.1 planning, Claude Opus implementation) assistance. The contribution sought is a reusable kernel-checked formalization of the exact catalog question; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed.

Proposed formalizer: `RECIPIENT-jsp-000663-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
