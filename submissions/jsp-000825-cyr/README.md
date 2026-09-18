# JSP-000825 (Erdős #992): discrepancy of `{α xₙ}` for almost all `α` — the answer is **no** (Berkes–Philipp)

Catalog entry: [JSP-000825](../../problems/catalog-0801-0900.md#JSP-000825). Problem page:
<https://www.erdosproblems.com/992>.

## The question and its complete answer

Erdős [Er64b, p. 56]: let `x₁ < x₂ < ⋯` be an infinite sequence of integers. Is it true that, for almost all `α ∈ [0,1]`,
the discrepancy `D(N) = max_{I ⊆ [0,1]} |#{n ≤ N : {α xₙ} ∈ I} − |I| N|` satisfies `D(N) ≪ N^{1/2} (log N)^{o(1)}`?
Or even `D(N) ≪ N^{1/2} (log log N)^{O(1)}`?

Resolution: **no** to both (Berkes and Philipp, J. London Math. Soc. 1994): there is a sequence such that, for almost all
`α ∈ [0,1]`, `limsup D(N) / (N log N)^{1/2} > 0`. This package proves that theorem in Lean 4 / Mathlib with a self-contained
elementary construction, and derives the negative answers to both questions, with only the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`):

| face | statement | theorem |
|---|---|---|
| (i) | there are a strictly increasing integer sequence `x` and `c > 0` such that for almost all `α ∈ [0,1]`, `c (N log N)^{1/2} ≤ D(N)` for infinitely many `N` | `Erdos992.berkes_philipp` |
| (ii) | the first question is false: it is not the case that for every strictly increasing sequence and almost all `α ∈ [0,1]`, for every `ε > 0` there is `C` with `D(N) ≤ C N^{1/2} (log N)^ε` for all large `N` | `Erdos992.not_erdos_992` |
| (iii) | the "or even" question is false: it is not the case that for every strictly increasing sequence and almost all `α ∈ [0,1]` there are `C, K` with `D(N) ≤ C N^{1/2} (log log N)^K` for all large `N` | `Erdos992.not_erdos_992_loglog` |

The definitions ([Jsp825/Defs.lean](Jsp825/Defs.lean)) are literal: `D x α N` is the supremum, over all sub-intervals `I` of
`[0,1]` (order-connected subsets, so open, closed and half-open intervals alike), of `|#{n < N : {α xₙ} ∈ I} − |I| N|`,
with `|I|` the Lebesgue measure of `I` and `{·}` the fractional part (degenerate and empty intervals are included; they do
not change the supremum, and restricting to intervals is the standard meaning of `max_{I ⊆ [0,1]}`, since over arbitrary
subsets `I` the discrepancy would be trivially `N`); "almost all `α ∈ [0,1]`" is `∀ᵐ α ∂volume, α ∈ Icc 0 1 → …`.
The two questions are transcribed in their weakest natural reading (`(log N)^{o(1)}` as "every fixed power `(log N)^ε`",
`(log log N)^{O(1)}` as "some fixed power"), so that their negations are the strongest. The frozen statement is restated once
more, with `sorry`, in [Target.lean](Target.lean), which nothing imports.

## The construction (own design)

Blocks `j = 1, 2, …` in dyadic groups `i = ⌊log₂ j⌋`; block `j` has length `L_j = (i+1) 2^i` and consists of the integers
`2^{m_j} s`, `1 ≤ s ≤ L_j`, where `m_{j+1} = m_j + r_j` and `2^{r_j} ≥ 16 L_j`, so the concatenated sequence `x` is strictly
increasing ([Params.lean](Jsp825/Params.lean), [Blocks.lean](Jsp825/Blocks.lean)).

* **Block deviation** ([Blocks.lean](Jsp825/Blocks.lean)): if `β_j = {2^{m_j} α} ∈ [3/(8L_j), 5/(8L_j)]` then every point of
  block `j` is `{α 2^{m_j} s} = s β_j ≤ 5/8`, and at least `5L_j/8` of them lie in `[0, 1/2)`, so the block alone
  contributes an error `≥ L_j/8` on `I = [0, 1/2)`. Hence one of `D(N_j)`, `D(N_{j−1})` is at least `L_j/16`, where `N_j`
  counts the terms of blocks `1..j`; no control of the earlier blocks is needed.
* **Growth** ([Growth.lean](Jsp825/Growth.lean)): `N_j ≤ (i+1) 4^{i+1}`, so `(N log N)^{1/2} ≤ 4 L_j` for every `N ≤ N_j`; thus
  the block deviation gives `D(N) ≥ (1/64)(N log N)^{1/2}` for some `N ∈ {N_{j−1}, N_j}`.
* **Digit events and a direct Borel–Cantelli argument** ([Digits.lean](Jsp825/Digits.lean)): `β_j` lies in the target
  interval whenever the `r_j` binary digits of `α` after position `m_j` form one of at least `2^{r_j}/(8L_j)` admissible
  patterns; these events `E_j` have probability `p_j ≥ 1/(8L_j)`, and `Σ_j p_j ≥ Σ_i 1/(8(i+1)) = ∞`. Because the events use
  disjoint digit blocks, `{α ∈ [0,1) : α ∉ E_j for J ≤ j ≤ K}` is a union of dyadic intervals whose measure is exactly
  `∏_{j=J}^{K} (1 − p_j) ≤ exp(−Σ p_j) → 0`; so almost every `α ∈ [0,1]` lies in infinitely many `E_j`. No independence
  library is used: the measure of each cylinder set is computed by counting.
* **Assembly** ([Main.lean](Jsp825/Main.lean)): `berkes_philipp` with `c = 1/64`; the two questions are refuted by
  comparing `(log N)^ε` (`ε = 1/4`) and `(log log N)^K` with `(log N)^{1/2}`.

No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs anywhere outside the statement-only file `Target.lean`.

## Reproduce

```bash
cd submissions/jsp-000825-cyr
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.
`Audit.lean` prints the axioms of the audited theorems (expected output in `verification.txt`).

## Attribution and submission status

The problem is due to Erdős [Er64b]; the negative answer is due to Berkes and Philipp [BePh94]. The construction above
and its Lean formalization were written from scratch by Collin Yuanjie Ren (@CollinYuanjieRen) with Claude Code assistance
(design and review by Claude Fable 5.1, Lean implementation by Claude Opus subagents); no Lean code or proof text from any
other project was consulted or reused. An earlier, independent Lean proof of the same theorem exists publicly
(plby/lean-proofs, proof module `src/latest/ErdosProblems/Erdos992.lean`, August 2026; only its public challenge statement
was read, for the statement comparison); no first-formalization priority or entitlement to an award is claimed. An
independent adversarial audit and an independent original-target scope review were performed before submission; no
organizer-supplied authoritative Lean statement of this problem exists (erdosproblems.com: "Formalised statement: No"), so no
official comparator run is claimed. This is a self-submission with a direct interest in the review outcome. Code and
documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
