# JSP-000167: counting lower bound and a perfect-ruler certificate (scoped component of the sparse ruler problem)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000167](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000167), the **sparse ruler problem** ([ErGa48] Erdős–Gál): what is the minimum number of marks on an integer ruler needed to measure every length by a difference of two marks, and what is the limiting ratio of that minimum to `√N`?

**The open question — the exact minimum and its limiting ratio to `√N` — is not claimed here.** This package formalizes two elementary facts:

1. **Counting lower bound.** A mark set with `m` marks has at most `C(m,2)` distinct positive differences, so any ruler measuring every length in `{1,…,L}` needs `C(|S|,2) ≥ L`.
2. **Perfect-ruler certificate.** The 4-mark ruler `{0,1,4,6}` measures every length `1..6` (its pairwise differences are exactly `{1,2,3,4,5,6}`), meeting `C(4,2) = 6 = L`.

## Statement and proof

```lean
def Measures (S : Finset ℕ) (L : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 L, ∃ a ∈ S, ∃ b ∈ S, b < a ∧ a - b = k

theorem card_choose_two_ge {S : Finset ℕ} {L : ℕ} (h : Measures S L) : L ≤ S.card.choose 2
theorem perfect_ruler_0146 : Measures ({0, 1, 4, 6} : Finset ℕ) 6
```

For the bound, the lengths `{1,…,L}` embed into the set of positive differences `{a − b : a,b ∈ S, b < a}`, which is the image of the ordered-pair set `P = {(a,b) ∈ S×S : b < a}` under subtraction; `|Icc 1 L| ≤ |image| ≤ |P| ≤ C(|S|,2)`, the last step by injecting each pair `(a,b)` (with `b < a`) into the 2-subset `{a,b}` of `S` (`Finset.card_powersetCard`). The certificate is decided by `fin_cases`/`decide`.

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000167.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

Both facts are elementary (a pigeonhole counting bound and a finite difference check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000167-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
