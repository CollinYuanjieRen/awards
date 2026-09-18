# Erdős Problem #1183 (JSP-000988): bounds on f(n) — a milestone on an OPEN problem

**This is not a solution.** Erdős Problem [#1183](https://www.erdosproblems.com/1183) (Erdős–Ulam, [Er78, p. 39]; catalog entry [JSP-000988](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000988)) is OPEN and stays open. This package records a Lean proof of elementary bounds only, as a public, timestamped research note. It claims no completion, no eligibility and no award, and it is not an intake submission.

## The problem

Let `f(n)` be maximal such that in any 2-colouring of the subsets of `{1, …, n}` there is always a monochromatic family of at least `f(n)` sets which is closed under taking unions and intersections. Estimate `f(n)`. (The page also defines `F(n)` for families closed under unions only; nothing about `F(n)` is treated here.) The page records only the trivial bound `f(n) ≥ (n+1)/2` from a chain of `n+1` nested sets, and Erdős's remark that "we have no plausible conjecture for the true order of magnitude of f(n)".

## What is proved

With `{1,…,n}` modelled by `Fin n`, a colouring by `c : Finset (Fin n) → Bool`, and a family by a `Finset (Finset (Fin n))` ([Erdos1183Lattices/Definitions.lean](Erdos1183Lattices/Definitions.lean)):

```lean
def Closed (F : Finset (Finset (Fin n))) : Prop := ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F ∧ A ∩ B ∈ F
def Mono (c : Finset (Fin n) → Bool) (F : Finset (Finset (Fin n))) : Prop := ∃ b, ∀ A ∈ F, c A = b
def Good (n m : ℕ) : Prop :=
  ∀ c : Finset (Fin n) → Bool, ∃ F, F.Nonempty ∧ Closed F ∧ Mono c F ∧ m ≤ F.card
noncomputable def f (n : ℕ) : ℕ := sSup {m : ℕ | Good n m}
```

`good_iff_le_f : Good n m ↔ m ≤ f n` shows `f n` is a genuine maximum. [Erdos1183Lattices/Main.lean](Erdos1183Lattices/Main.lean) proves

```lean
theorem erdos_1183_closed :
    (∀ n : ℕ, (n + 2) / 2 ≤ f n) ∧ (∀ n : ℕ, f n ≤ (n + 1) ^ 2)
```

i.e. `⌈(n+1)/2⌉ ≤ f(n) ≤ (n+1)²` for every `n` (`(n + 2) / 2` in ℕ is `⌈(n+1)/2⌉`), together with the `f`-free forms `good_lower : Good n ((n+2)/2)` and `not_good_upper : ¬ Good n ((n+1)^2 + 1)`.

**Proof.** *Lower bound* ([Chain.lean](Erdos1183Lattices/Chain.lean)): the chain `∅ ⊂ {0} ⊂ {0,1} ⊂ ⋯` of `n+1` initial segments; any subfamily of a chain is closed under `∪` and `∩`; the majority colour class has at least `⌈(n+1)/2⌉` members. This is the page's argument. *Upper bound* ([Sublattice.lean](Erdos1183Lattices/Sublattice.lean), [Counting.lean](Erdos1183Lattices/Counting.lean)): a nonempty family `F` closed under `∪` and `∩` contains `⋂F` and `⋃F` and is determined by them together with the relation `R_F(i,j) :⟺ (every member of F containing j contains i)`: for `j ∈ ⋃F` the principal set `P_j = ⋂{X ∈ F : j ∈ X}` lies in `F` and equals `{i : R_F(i,j)}`, and any `X` with `⋂F ⊆ X ⊆ ⋃F` that is an `R_F`-down-set equals `⋂F ∪ ⋃_{j∈X} P_j ∈ F`. Hence there are at most `2^n · 2^n · 2^{n²} = 2^{n²+2n}` such families (`card_closed_le`). A fixed family with `k` members is monochromatic under at most `2·2^{2ⁿ−k}` of the `2^{2ⁿ}` colourings (`card_mono_le`). If every colouring had a monochromatic closed family with `m = (n+1)²+1` members, double counting the pairs (colouring, family) would give `2^{2ⁿ} ≤ 2^{n²+2n} · 2 · 2^{2ⁿ−m} = 2^{2ⁿ−1}`, a contradiction (when `m > 2ⁿ` the claim is immediate). ∎

## What is not claimed

The order of magnitude of `f(n)` — the bounds are polynomially apart; any improvement of either bound; anything about `F(n)` or the page's two "in particular" questions; novelty or priority (the upper bound was not found in the literature on 2026-09-18, but no first-proof claim is made); any completeness, eligibility or award.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain [lean-toolchain](lean-toolchain) (`leanprover/lean4:v4.34.0-rc1`); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` ([lake-manifest.json](lake-manifest.json)). [Audit.lean](Audit.lean) restates the roots as typed `example`s and prints their axioms: every declaration depends exactly on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit`, `native_decide`, custom axiom or added hypothesis anywhere. [verification.txt](verification.txt) records the local build and audit. There is no Formal Conjectures module for #1183 at the checkout used, so no official comparator run is possible; the definitions above are this package's own transcription of the page, argued clause by clause.

The Lean code was prepared with Claude Code (Anthropic) assistance — Claude Fable 5.1 for the mathematical design, Claude Opus for the Lean implementation and two independent audits — and checked locally. Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
