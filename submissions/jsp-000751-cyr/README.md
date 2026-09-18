# JSP-000751 (Erdős #903): block counts of pairwise balanced designs on `p² + p + 1` points — `b > v ⇒ b ≥ v + p`

Catalog entry: [JSP-000751](../../problems/catalog-0701-0800.md#JSP-000751). Problem page:
<https://www.erdosproblems.com/903>.

## The question and its complete answer

Erdős–Sós [Er82e]: let `n = p² + p + 1` and let `A_1, …, A_t ⊆ {1, …, n}` be a block design, so that every pair of points
lies in exactly one `A_i`. Is it true that if `t > n` then `t ≥ n + p`?

Resolution (Erdős, Fowler, Sós, Wilson, *On 2-designs*, J. Combin. Theory Ser. A 38 (1985) 131–142, Theorem 2): **yes**, for
every `p` (not only prime powers): there is no 2-design with `v = p² + p + 1` points and `p² + p + 1 < b < p² + 2p + 1`
blocks. A 2-design there (pairwise balanced design of index one, linear space) has blocks with at least two points and every
pair of distinct points in exactly one block; that convention is part of the definition and is necessary (empty or singleton
blocks could otherwise pad the block count arbitrarily). Everything below is proved in Lean 4 / Mathlib with only the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

| face | statement | theorem |
|---|---|---|
| (i) | every `p`: a linear space on `p² + p + 1` points with more than `p² + p + 1` blocks has at least `p² + 2p + 1` blocks | `Erdos903.erdos_903_general` |
| (ii) | the page's form, `p` a prime power | `Erdos903.erdos_903` |
| (iii) | no linear space on `p² + p + 1` points has `p² + p + 1 < b < p² + 2p + 1` blocks | `Erdos903.no_design_in_gap` |

The definitions ([Jsp751/Defs.lean](Jsp751/Defs.lean)) are literal: `IsLinearSpace block` says every block has at least
two points and every pair of distinct points lies in exactly one block (blocks indexed by `Fin b`; repeated blocks are
impossible); `degree` counts the blocks through a point. The frozen statement is restated once more, with `sorry`, in
[Target.lean](Target.lean), which nothing imports.

## Proof structure (the paper's algebraic proof, reconstructed)

Assume `v < b < v + p`. Combinatorial lemmas ([Counting.lean](Jsp751/Counting.lean), [Lemmas.lean](Jsp751/Lemmas.lean)):
two blocks share at most one point; the blocks through a point partition the other points; Σ_i C(k_i, 2) = C(v, 2);
the Stanton–Kalbfleisch bound `l²(v − l) ≤ |T|(v − 1)` for a block of size `l` meeting `|T|` other blocks (Cauchy–Schwarz);
hence (L1) every block has at most `p + 1` points, (L3) every point has degree at least `p + 1`, (L4) some point has degree
exactly `p + 1`, and (L2) a block all of whose points have degree `p + 1` forces `b = v`.
Algebraic core ([Algebra.lean](Jsp751/Algebra.lean), [Rank.lean](Jsp751/Rank.lean)): with `N` the incidence matrix and
`D = diag(r_x − 1)`, `N Nᵀ = D + J` has the explicit inverse `K = D⁻¹ − D⁻¹ J D⁻¹ / (1 + Σ 1/(r_x − 1))`; `Q = I − Nᵀ K N`
is symmetric, idempotent, and `N Q = 0`, so every principal submatrix of `Q` is a Gram matrix of vectors in `ker N`, of rank
at most `b − v`. On the blocks through a point `x₀`, `Q = diag(β) − J/(r_{x₀} − 1) + α a aᵀ` with `β_A = 1 − Σ_{x ∈ A ∖ x₀}
1/(r_x − 1) ≥ 0`; if all `β_A > 0` the positive-definite part forces rank ≥ `r_{x₀} − 1`, so with `r_{x₀} = p + 1` we get
`p ≤ b − v ≤ p − 1`, a contradiction; hence some block through `x₀` has all its other points of degree `p + 1`, and (L2)
gives `b = v` — contradiction ([Main.lean](Jsp751/Main.lean)).

No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs anywhere outside the statement-only file `Target.lean`.

## Reproduce

```bash
cd submissions/jsp-000751-cyr
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.
`Audit.lean` prints the axioms of the audited theorems (expected output in `verification.txt`).

## Attribution and submission status

The problem is due to Erdős and Sós [Er82e]; the theorem and its algebraic proof are due to Erdős, Fowler, Sós and Wilson
(JCTA 1985, Theorem 2). The Lean formalization was written from scratch by Collin Yuanjie Ren (@CollinYuanjieRen) with
Claude Code assistance (design and review by Claude Fable 5.1, Lean implementation by Claude Opus subagents); no Lean code
from any other project was consulted or reused. An earlier, independent Lean proof of the same theorem exists publicly
(plby/lean-proofs, module `Erdos903`, by Codex / GPT-5.6 Sol, August 2026); no first-formalization priority or entitlement to an
award is claimed. An independent adversarial audit and an independent original-target scope review were performed before
submission; no organizer-supplied authoritative Lean statement of this problem exists (erdosproblems.com: "Formalised
statement: No"; formal-conjectures has no `ErdosProblems/903.lean`), so no official comparator run is claimed. The stronger
Theorems 3–4 of the paper (structure of the extremal designs, the bound `b ≥ p² + (2 + c)p`) are not part of the question and
are not formalized. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the
repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
