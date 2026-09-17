# JSP-000194: ordinary lines — `f(n) → ∞` with an explicit bound (Erdős #210)

This package submits a Lean formalization for intake and eligibility review. It concerns [JSP-000194](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000194) / [Erdős Problem #210](https://www.erdosproblems.com/210): let `f(n)` be the least number of *ordinary lines* (lines containing exactly two of the points) determined by `n` points of the plane not all on a line; does `f(n) → ∞`, and how fast? The page records the problem as PROVED: `f(n) → ∞` was proved by Motzkin (1951), and the rate was later sharpened by Kelly–Moser (`3n/7`), Csima–Sawyer (`6n/13`) and Green–Tao (`n/2` for large `n`).

This package proves that **`f(n) → ∞`**, together with the explicit bound **`n ≤ 2m + 2^m`** for every non-collinear set of `n` points with `m` ordinary lines (arithmetically `f(n) ≥ log₂ n − 1` for `n ≥ 5`; the Lean theorem is the displayed inequality `n ≤ 2 f(n) + 2^{f(n)}`). The proof is Motzkin's — as restated by Kelly–Moser (Theorems 3.1–3.2) — with his polygonal-cell count replaced by the trivial sign-vector count `2^m`, and re-engineered so that no polyhedral or metric geometry is needed; only signs of `2 × 2` determinants. **What is not claimed:** the sharper rates `√(2n) − 2` (Motzkin), `3n/7` (Kelly–Moser), `6n/13` (Csima–Sawyer) and `n/2` (Green–Tao). The answer to "does `f(n) → ∞`?" is complete; the answer to "how fast?" given here is an explicit but sublinear rate, and this is stated wherever the result is described.

## Statement and proof

Points are elements of `ℝ × ℝ`. For a finite set `P` of points, `ordinaryLines P` ([Erdos210Ordinary/Definitions.lean](Erdos210Ordinary/Definitions.lean)) is the set of affine lines `line[ℝ, a, b]` (Mathlib's `affineSpan ℝ {a, b}`) through two distinct points of `P` that contain exactly two points of `P`, and

```lean
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ ¬ Collinear ℝ (P : Set (ℝ × ℝ)) ∧
    (ordinaryLines P).ncard = m}
```

is exactly the page's `f(n)`: the minimum, over sets of `n` points not all on a line (Mathlib's `Collinear`), of the number of ordinary lines. For `n ≥ 3` such sets exist (`exists_config`), so the infimum is attained (`f_mem`); for `n ≤ 2` the defining set is empty and `f n = 0` by the convention of `sInf` on `ℕ`, which is irrelevant to a limit as `n → ∞`.

[Erdos210Ordinary/Main.lean](Erdos210Ordinary/Main.lean) proves

```lean
theorem erdos_210 : Filter.Tendsto f Filter.atTop Filter.atTop
theorem erdos_210_bound (P : Finset (ℝ × ℝ)) (hP : ¬ Collinear ℝ (P : Set (ℝ × ℝ))) :
    P.card ≤ 2 * (ordinaryLines P).ncard + 2 ^ (ordinaryLines P).ncard
theorem le_f (n : ℕ) (hn : 3 ≤ n) : n ≤ 2 * f n + 2 ^ f n
theorem erdos_210_closed :
    (∀ n : ℕ, 3 ≤ n → n ≤ 2 * f n + 2 ^ f n) ∧ Filter.Tendsto f Filter.atTop Filter.atTop
```

`erdos_210_closed` packages the explicit rate and the limit in one closed proposition. There are no additional hypotheses, custom axioms or unproved assumptions.

**Proof outline** (Motzkin's argument, affine form; `m` = number of ordinary lines, `Z` = the points of `P` on no ordinary line).

1. *Counting* ([Config.lean](Erdos210Ordinary/Config.lean), `card_sdiff_orderZero_le`): every point outside `Z` lies on an ordinary line, and each ordinary line carries two points, so `|P \ Z| ≤ 2m`.
2. *Cells* (`W`, defined in [Definitions.lean](Erdos210Ordinary/Definitions.lean); properties in [Config.lean](Erdos210Ordinary/Config.lean)): for `p ∈ Z` the open cell `W P p` is the set of points strictly on the same side as `p` of every ordinary line. It contains `p` (`mem_W_self`), is convex (`W_segment`) and open along every direction (`W_small`), and misses every ordinary line (`not_mem_W_of_onLine`).
3. *Core lemma* ([Core.lean](Erdos210Ordinary/Core.lean), `ordinary_of_visible`, the affine counterpart of Kelly–Moser Theorem 3.1): if `p ∈ Z`, `x ∉ P`, and the open segment `(p, x)` meets no connecting line missing `p`, then every connecting line through `x` missing `p` is ordinary. If such a line carried three points `pᵢ = x + αᵢ u`, a pivot `p₁` is chosen by an elementary sign lemma (`exists_pivot`: exactly one of `α₂/α₁, α₃/α₁` lies in `(0, 1)`); since `p ∈ Z`, the line `p p₁` carries a third point `p₄ = p + γ(p₁ − p)`, and the identity `D(p₄, pⱼ, p) · D(p₄, pⱼ, x) = −Δ² γ(1−γ) αⱼ(αⱼ − α₁)` (`crossing_identity`) shows that for one `j ∈ {2, 3}` the connecting line `p₄ pⱼ` strictly separates `p` from `x`, hence crosses `(p, x)` while missing `p` — a contradiction ([Algebra.lean](Erdos210Ordinary/Algebra.lean), `oppSide_of_pivot`).
4. *No connecting line missing `p` meets `W P p`* ([Cell.lean](Erdos210Ordinary/Cell.lean), `not_mem_W_of_conn_missing`): given such a line through `w ∈ W P p`, move `w` slightly along the line to avoid the finitely many rays from `p` through points of `P`, take the first crossing `x` of the segment from `p` to `w` with a connecting line `s` missing `p`; then `x ∉ P`, `(p, x)` is crossing-free, so `s` is ordinary by step 3, but `x` lies in the convex set `W P p`, which misses ordinary lines.
5. *Injectivity* ([Count.lean](Erdos210Ordinary/Count.lean), `card_orderZero_le`): the map sending `p ∈ Z` to its vector of signs with respect to the `m` ordinary lines is injective — equal signs put `q` in `W P p`, and if `q ≠ p` some connecting line through `q` misses `p` (non-collinearity, `exists_conn_missing`), contradicting step 4. Hence `|Z| ≤ 2^m` and `|P| ≤ 2m + 2^m` (`card_le_of_notCollinear`).
6. *Bridge and limit* ([Bridge.lean](Erdos210Ordinary/Bridge.lean), [Main.lean](Erdos210Ordinary/Main.lean)): membership in `line[ℝ, a, b]` is the vanishing of the determinant `D a b ·` (`mem_line_iff`); `NotCollinear P ↔ ¬ Collinear ℝ ↑P` (`notCollinear_iff`); the ordinary lines are in bijection with the ordinary pairs (`ncard_ordinaryLines`); and `n ≤ 2 f(n) + 2^{f(n)}` forces `f(n) → ∞`.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The Lean toolchain is pinned in [lean-toolchain](lean-toolchain) (`leanprover/lean4:v4.34.0-rc1`); Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the limit, the closed root, the explicit bound, `le_f`, the witness and the line bridge as typed `example`s closed by the theorems, prints the definitions, and prints the axioms of the root and of every named component. Every declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the dependency cone. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit by the designated verifiers and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly. Local verification used cached upstream dependencies on arm64 macOS; it is not a clean network-disabled rebuild, and no independent-checker claim is made.

There is no Formal Conjectures module for Erdős #210 at the checkout used (2026-09-17), so no official comparator run is possible; the statement above is this package's own transcription of the page's definition of `f(n)`, argued clause by clause in this README. Mathlib contains no Sylvester–Gallai theorem; the `m = 0` case of `erdos_210_bound` gives `|P| ≤ 1`, so the Sylvester–Gallai theorem (`f(n) ≥ 1` for `n ≥ 3`) is a corollary.

## Attribution and submission status

The theorem `f(n) → ∞` and the argument formalized here are Motzkin's (T. Motzkin, *The lines and planes connecting the points of a finite set*, Trans. Amer. Math. Soc. 70 (1951), 451–464, Theorem 2.3), in the form given by L. M. Kelly and W. O. J. Moser (*On the number of ordinary lines determined by n points*, Canad. J. Math. 10 (1958), 210–219, Theorems 3.1–3.2) and by N. Nilakantan (*Extremal problems related to the Sylvester–Gallai theorem*, MSRI Publ. 52 (2005), 479–494). The replacement of the polygonal-cell count by the sign-vector count, the elimination of projective separation in favour of the crossing identity, and the first-crossing construction are the formalization's own bookkeeping; they weaken Motzkin's `C(m+2, 2) ≥ n` to `n ≤ 2m + 2^m` and add no mathematical novelty. This package formalizes established mathematics and claims no new mathematical result. A Lean proof of this problem by other authors is known to exist in a public repository of unknown licence; it was not consulted, and no first-formalization or priority claim is made.

The Lean code was prepared with Claude Code (Anthropic) assistance — Claude Fable 5.1 for the mathematical design and coordination, Claude Opus for the Lean implementation — and checked locally. This is a self-submission with a direct interest in the review outcome; no solver nomination, award tier, payment status or official verification status is asserted or changed.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
