# JSP-000990 (Erdős #1185): dense sets, difference sets of small sets, and `k`-term progressions — the answer is **no**

Catalog entry: [JSP-000990](../../problems/catalog-0901-1000.md#JSP-000990). Problem page:
<https://www.erdosproblems.com/1185>.

## The question and its complete answer

Erdős [Er80, p. 92]: let `δ > 0` and `k ≥ 3`. Is it true that there exists `m ≥ 1` (depending only on `δ` and `k`) such
that, for all large `N`, if `A, B ⊆ {1, …, N}` with `|A| ≥ δN` and `|B| ≥ m` then there is a non-trivial `k`-term arithmetic
progression in `A` whose common difference is in `B − B`?

Resolution: **no**, already for `k = 3` (Furstenberg 1981: there is an infinite `B` such that `B − B` is not 2-intersective).
This package proves the negative answer in Lean 4 / Mathlib with a self-contained finite counterexample family, with only the
three standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

| face | statement | theorem |
|---|---|---|
| (i) | the page's universal statement (`Erdos1185.Erdos1185Statement`, quantifiers as on the page) is false | `Erdos1185.not_erdos_1185` |
| (ii) | for every `k ≥ 3`, every `δ ≤ 1/64`, every `m` and every threshold `N₀`, there are `N ≥ N₀` and `A, B ⊆ {1, …, N}` with `|A| ≥ δN`, `|B| ≥ m` and no non-trivial `k`-term progression in `A` with common difference in `B − B` | `Erdos1185.counterexample` |

The definitions ([Jsp990/Defs.lean](Jsp990/Defs.lean)) are literal: `HasAPWithStepInDiff k A B` says there are `a` and
`d > 0` with `a, a + d, …, a + (k−1)d ∈ A` and `d = b₁ − b₂` for some `b₁, b₂ ∈ B`; `Erdos1185Statement` is the page's
statement with real `δ`, "for all large `N`" read as "for all `N ≥ N₀` for some `N₀`", and `m ≥ 1`. The frozen statement is
restated once more, with `sorry`, in [Target.lean](Target.lean), which nothing imports.

## The counterexample (own construction)

Fix `m`. Let `b 0 = 1`, `b (l+1) = 256 · b l · b l` (powers of two; each ratio `b (l+1) / b l = 256 · b l` is even and a
multiple of `2 · b l`), `B = {b 0, …, b (m−1)}`, `bm = b (m−1)`, `T = Σ_{l<m} (bm / b l)²` (odd), `L = 8 · bm²`, and
`A = {1 ≤ n ≤ N : (n² T) mod L < L/16}`.

* **Phase lemma** ([Sequence.lean](Jsp990/Sequence.lean)): for `i > j`, `d = b i − b j` satisfies
  `L/8 ≤ (2 d² T) mod L ≤ 7L/8`. Term by term in `2 d² T = Σ_l 2 d² (bm / b l)²`: the terms with `l < j` are multiples of `L`,
  the term `l = j` is `L/4` mod `L`, the terms `j < l < i` and `l > i` are tiny (geometric in `1/256²`), and the term `l = i`
  is `L/4 − 4bm²/R + 2bm²/R²` with `R = b i / b j ≥ 256`; so `2 d² T ≡ L/2 + ε (mod L)` with `|ε| ≤ L/100`.
* **No progression** ([NoAP.lean](Jsp990/NoAP.lean)): if `a, a + d, a + 2d ∈ A` then, since
  `(a+2d)² − 2(a+d)² + a² = 2d²`, `2 d² T ≡ φ(a+2d) − 2φ(a+d) + φ(a) (mod L)` with `φ(n) = (n² T) mod L ∈ [0, L/16)`, so
  `(2 d² T) mod L ∈ [0, L/8) ∪ (7L/8, L)`, contradicting the phase lemma. A `k`-term progression (`k ≥ 3`) contains such a
  3-term progression with the same difference.
* **Density** ([Density.lean](Jsp990/Density.lean)): writing `n = bm · k + u` with `u < bm` odd and `k = 8k' + e`, one has
  `n² T ≡ C(u, e) + 16 · bm · uT · k' (mod L)`; since `uT` is odd and `bm` is a power of two, the residues run over the coset
  `C + 16 bm ℤ` of `ℤ/L`, which meets `[0, L/16)` in exactly `bm/32` points. Hence at least `L/32` of the residues mod `L` are
  good, `A` is periodic mod `L`, and `|A| ≥ N/64` for `N ≥ 2L`.
* **Assembly** ([Main.lean](Jsp990/Main.lean)): given `k ≥ 3`, `δ ≤ 1/64`, `m`, `N₀`, run the construction with `m' = max m 2`
  elements and take `N = max N₀ (2L)` (≥ `bm`), so `B ⊆ {1, …, N}`, `|B| = m' ≥ m`, `δN ≤ N/64 ≤ |A|`, and
  `¬ HasAPWithStepInDiff k A B`. The range `δ ≤ 1/64` is the substantive one: the page's statement only gets weaker as `δ`
  grows, and one failing `δ` (the roots use `δ = 1/64`, `k = 3`) already refutes it.

No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs anywhere outside the statement-only file `Target.lean`.

## Reproduce

```bash
cd submissions/jsp-000990-cyr
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.
`Audit.lean` prints the axioms of the audited theorems (expected output in `verification.txt`).

## Attribution and submission status

The problem is due to Erdős [Er80]; the negative answer is due to Furstenberg (1981, quadratic skew-shift / non-intersective
difference sets). The finite counterexample family above and its Lean formalization were written from scratch by
Collin Yuanjie Ren (@CollinYuanjieRen) with Claude Code assistance (design and review by Claude Fable 5.1, Lean implementation
by Claude Opus subagents); no Lean code or proof text from any other project was consulted or reused. An earlier, independent
Lean proof of the same negative answer exists publicly (plby/lean-proofs, module `Erdos1185`, by Codex / GPT-5.6 Sol, 2026);
no first-formalization priority or entitlement to an award is claimed. An independent adversarial audit and an independent
original-target scope review were performed before submission; no organizer-supplied authoritative Lean statement of this
problem exists (erdosproblems.com: "Formalised statement: No"; formal-conjectures has no `ErdosProblems/1185.lean`), so no
official comparator run is claimed. This is a self-submission with a direct interest in the review outcome. Code and
documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
