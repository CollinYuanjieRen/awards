# JSP-000827: Marstrand's disproof of Khintchine's conjecture on strong uniform distribution

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000827](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000827) (Erdős Problem [#994](https://www.erdosproblems.com/994), Khintchine 1923): for a fixed Lebesgue-measurable `E ⊆ (0,1)`, is it true that for almost all `α`

    (1/n) · #{ 1 ≤ k ≤ n : {kα} ∈ E } → λ(E) ?

The answer is no (J. M. Marstrand, *On Khinchin's conjecture about strong uniform distribution*, Proc. London Math. Soc. (3) 21 (1970), 540–556).

## Statement and proof

`Jsp827/Root.lean` proves

```lean
theorem Erdos994.not_khintchineFixedSet : ¬ KhintchineFixedSet
theorem Erdos994.exists_counterexample_ae :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioo (0 : ℝ) 1 ∧
      ∀ᵐ α : ℝ, ¬ HasExpectedLimit E α
```

where (`Jsp827/Statement.lean`) `visitAverage E α n = (∑_{k ∈ Icc 1 n} [Int.fract (k·α) ∈ E]) / n`, `HasExpectedLimit E α` says `visitAverage E α n → (volume E).toReal`, and `KhintchineFixedSet` is `∀ E, MeasurableSet E → E ⊆ Ioo 0 1 → ∀ᵐ α : ℝ, HasExpectedLimit E α` (the fixed-set quantifier order: `E` first, the exceptional null set of `α` may depend on `E`). These three definitions are reproduced verbatim from the earlier third-party formalization [plby/lean-proofs, `ErdosProblems/Erdos994.lean` at 8822f7dd](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos994.lean) (Apache 2.0; formal authors Codex and GPT-5.6 Sol), which refutes only the quantifier-swapped reading `∀ᵐ α, ∀ E` and leaves the fixed-set predicate untouched. Quantifying over all real `α` is equivalent to `α ∈ (0,1)` because the averages depend only on `α mod 1` (they are invariant under `α ↦ α + m`, `m ∈ ℤ`), so an exceptional set is null in `ℝ` iff it is null in `(0,1)`. `MeasurableSet` on `ℝ` is Borel measurability; since the result is negative, exhibiting a Borel counterexample is at least as strong as a Lebesgue-measurable one. The `n = 0` term of `visitAverage` is `0` by the field convention and is irrelevant to the limit. The displayed statement on erdosproblems.com ends with an ambiguous trailing "for all `E`"; the fixed-set quantifier order used here is the historical conjecture (Khintchine 1923; Davenport–Erdős 1963) and is the reading requested in the open upstream correction [issue #72](https://github.com/TheJustinSunPrize/awards/issues/72), which has not yet received a maintainer response. The stronger root `exists_counterexample_ae` gives a single set failing for almost every `α`; what is proved quantitatively is `limsup ≥ 1/2 > 1/8 ≥ λ(E)` (Marstrand's original construction gives an open set with `limsup = 1` and `liminf = 0`, which is not needed for the question as posed).

The proof is a self-contained reconstruction of Marstrand's theorem (his paper was not available to us; the route follows the transference idea of Quas–Wierdl, *Rates of divergence of non-conventional ergodic averages*, ETDS 30 (2010) §5, and uses the Rokhlin lemma for commuting endomorphisms of Avila–Candela, *Towers for commuting endomorphisms, and combinatorial applications*, Ann. Inst. Fourier 66 (2016) 1529–1544, Theorem 1.2, proved here in full):

* `Jsp827/Tower/Basic.lean`, `Tower/Separation.lean` (AC Prop. 2.1), `Tower/Iterate.lean` (AC Lemma 2.3), `Tower/Sup.lean` (AC Lemma 2.4), `Tower/Main.lean` (AC Theorem 1.2): for a free measure-preserving `ℕ^d`-action by commuting endomorphisms of a probability space with a countable separating family of measurable sets, every box `n` admits an `n`-tower (pairwise disjoint preimages of a base over the box) of measure `≥ 1 − ε`.
* `Jsp827/Circle.lean`: the action `e ↦ (∏ pᵢ^{eᵢ}) • x` on the unit circle is such an action (measure preserving, free by unique factorization and finiteness of torsion).
* `Jsp827/Arith.lean`: every `n ≤ 2^J` divides `∏_{p ≤ 2^J} p^{e_p}` when all `e_p ≥ J`, and the `Nat.log 2` sandwich for `g/n`.
* `Jsp827/Marstrand/Scale.lean`: at scale `J`, with levels indexed by exponent vectors `e`, put `L(e) = ⌊log₂ ∏ pᵢ^{eᵢ}⌋`; the bad set `E_J` is the union of the levels with `L(e) mod J ∈ {0,1}` (measure `≤ 2/J`), and for `x` in a level with all `eᵢ ≥ J` and `j := L(e) mod J ≥ 1`, every `n ∈ (2^{j−1}, 2^j]` sends `x` into `E_J`, so at least half of the multiples `1 ≤ n ≤ 2^j` of `x` visit `E_J`.
* `Jsp827/Marstrand/Main.lean`: scales `J_s = 2^{s+5}`, Borel–Cantelli on the complements of the good sets, `E := ⋃_s E_{J_s}` of measure `≤ 1/8`, hence `limsup ≥ 1/2 > λ(E)` for almost every point of the circle; transfer to `ℝ` via `Int.fract (k·α) ↦ k • (α : UnitAddCircle)`.

No literature theorem is assumed: every cited result is proved inside the package. The source statement (erdosproblems.com/994, retrieved 2026-09-16) is recorded verbatim in `sources/erdos994-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain: `leanprover/lean4:v4.34.0-rc1` (`lean-toolchain`); Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of the two roots and of the main intermediate theorems; all are exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` declarations occur. `Challenge.lean` is a comparator-style challenge module (Mathlib-only definitions and the target statement with `sorry`, not imported by the build) for mechanical statement comparison. `verification.txt` records the local build and audit of this exported package (fresh checkout of the package directory, Mathlib cache from the official cache server, then `lake build` and the audit).

Local verification used arm64 macOS and cached upstream dependencies. It is not verification by an independent checker implementation and does not assert an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process; no curator signatures or attestations are fabricated.

## Attribution and submission status

The mathematical result is Marstrand's (1970). The formalization was prepared with Claude (Anthropic) assistance (design and hints by Claude Fable 5.1, Lean implementation by Claude Opus subagents) and locally checked; the contribution sought is formalization, not a new mathematical discovery. The proof route was reconstructed independently and audited by an adversarial review before implementation; it is not claimed to be Marstrand's original argument.

No first-formalization priority or entitlement to an award is claimed. This is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000827-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
