# JSP-000616 (Erdős #748): the Cameron–Erdős conjecture `f(n) ≪ 2^{n/2}` — a Lean 4 formalization of Green's proof

This package is a complete, self-contained Lean 4 / Mathlib formalization of the **Cameron–Erdős conjecture**, the result recorded as the solution of [JSP-000616](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000616) / [Erdős Problem #748](https://www.erdosproblems.com/748): if `f(n)` counts the sum-free subsets of `{1, …, n}` (sets with no solution of `a = b + c`, `a, b, c ∈ A`, not necessarily distinct), then

> **Theorem (Green 2004 [Gr04], Sapozhenko 2003 [Sa03]).** `f(n) ≪ 2^{n/2}`, i.e. there is a constant `C` with `f(n) ≤ C · 2^{n/2}` for every `n`.

Together with the trivial lower bound `f(n) ≥ 2^{⌈n/2⌉}` (all subsets of the odd numbers, or of `(n/2, n]`) this gives `f(n) ≍ 2^{n/2}`, which in turn gives the form displayed on the problem page, `f(n) = 2^{(1 + o(1)) n/2}`. All of these are proved here (see *Statements*). The formalization follows Ben Green's paper [Gr04] (arXiv [math/0304058](https://arxiv.org/abs/math/0304058)) essentially step by step; the only external ingredients are Kneser's addition theorem (a Lean proof by Mantas Bakšys and Yaël Dillies, ported with its Apache-2.0 header, see *Attribution*) and Proposition 1 of Lev–Łuczak–Schoen [LLS01], which is proved in full inside the package.

## Statements

The frozen root statement is `CameronErdos/Statement.lean`:

```lean
namespace CameronErdos
def IsSumFree (A : Finset ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A
def sumFreeCount (n : ℕ) : ℕ := ((Finset.Icc 1 n).powerset.filter IsSumFree).card
example : (List.range 7).map sumFreeCount = [1, 2, 3, 6, 9, 16, 24] := by decide
def CameronErdosStatement : Prop := ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, sumFreeCount n ^ 2 ≤ C * 2 ^ n
end CameronErdos
```

`IsSumFree` is the page's notion (`a`, `b`, `c` not necessarily distinct; in particular `b = c` is allowed, so `{1, 2}` is not sum-free). `sumFreeCount n = f(n)` counts every sum-free subset of `{1, …, n}`, including `∅`; the `example` checks the first values `1, 2, 3, 6, 9, 16, 24` (OEIS A007865) by evaluation. `CameronErdosStatement` is `f(n)² ≤ C · 2ⁿ` for all `n`, i.e. `f(n) ≤ √C · 2^{n/2}`, which is exactly `f(n) ≪ 2^{n/2}` in a form that avoids real numbers in the root.

The root theorem is in `CameronErdos/Main.lean`:

```lean
theorem CameronErdos.cameronErdos : CameronErdos.CameronErdosStatement
```

`CameronErdos/Corollaries.lean` restates the result in the forms used in the literature and on the problem page, all derived from the root theorem and the trivial lower bound (no new mathematics):

- `two_pow_half_le_sumFreeCount : 2 ^ (n / 2) ≤ sumFreeCount n` and `two_pow_ceil_half_le_sumFreeCount : 2 ^ ((n + 1) / 2) ≤ sumFreeCount n` (all-odd subsets);
- `sumFreeCount_le_mul_two_pow_half : ∃ C : ℝ, 0 < C ∧ ∀ n, (sumFreeCount n : ℝ) ≤ C * 2 ^ ((n : ℝ) / 2)`;
- `sumFreeCount_isBigO` and `two_pow_half_isBigO_sumFreeCount`: `f(n) = O(2^{n/2})` and `2^{n/2} = O(f(n))`, i.e. `f(n) ≍ 2^{n/2}`;
- `tendsto_logb_sumFreeCount_div : Tendsto (fun n => Real.logb 2 (sumFreeCount n) / n) atTop (𝓝 (1/2))` and `sumFreeCount_eq_two_pow_half_add_littleO`, the page's `f(n) = 2^{(1+o(1)) n/2}`.

`Jsp616/SumFree.lean` (library `Jsp616`) is the earlier scoped submission of the trivial lower bound, retained unchanged (`Erdos748.f_ge_two_pow_half : 2 ^ (n / 2) ≤ Erdos748.f n`, with its own equivalent definitions `Erdos748.SumFree`, `Erdos748.f`); it is not used by the main proof.

What is **not** claimed: the finer asymptotic `f(n) ∼ c_n 2^{n/2}` with two parity-dependent constants (also in [Gr04], [Sa03]) is not formalized; the problem page states that `f(n) ≪ 2^{n/2}` is the proved answer to its question, and that is what this package proves.

## Proof route (Green [Gr04]) and module map

All modules are in namespace `CameronErdos`; `CameronErdos.lean` imports everything.

| Module | Content | Green |
| --- | --- | --- |
| `Statement.lean` | frozen definitions and root statement | Thm 1 |
| `Kneser/MulStab.lean`, `Kneser/Kneser.lean` | stabilizers and Kneser's theorem `Finset.add_kneser` (Bakšys–Dillies port) | §4 |
| `Fourier/Basic.lean` | Fourier transform on `ZMod p`, convolution, Parseval | §2 |
| `Counting/Basic.lean` | additive triples, popular differences, matchings (`card_avoiding_matching`), odd sets, even-set triple count, Lemmas 8 and 9 | Lemmas 8, 9, Cor 13 tools |
| `Part1/Params.lean`, `Part1/ParamsMore.lean`, `Part1/SmallBinomial.lean` | Green's parameters `ε = (log N)^{-1/11}`, `M = ⌊N exp(−(log N)^{1/12})⌋`, all "for N large" estimates, `2^{o(N)}` binomial sums | §3 |
| `Part1/Granularization.lean` | progressions `I_i`, granularization `A′`, good lengths, the smoothing function `g` and Green (6) | §2 (2)–(7) |
| `Part1/Prop3.lean`, `Part1/Prop4.lean`, `Part1/Prop5.lean` | Propositions 3, 4, 5 | §2 |
| `Part1/Family.lean`, `Part1/Prop6.lean` | the container family `𝓕` and Proposition 6 (`eventually_container_family`) | §3 |
| `Part2/Projection.lean`, `Part2/IntervalBM.lean`, `Part2/Ineq16.lean` | Lemma 11, the choice of `m, M`, inequalities (15)–(16) | §4 |
| `Part2/LLS.lean` | Lev–Łuczak–Schoen Proposition 1 with its Lemma 6 (Green's Lemma 10), proved in full | §4, Lemma 10 |
| `Part2/Prop7.lean` | Proposition 7 (stability of almost sum-free sets; Kneser case analysis) | §4 |
| `Part2/Prop12.lean` | Proposition 12, `f(N) ≤ 2^{(1/2 + θ)N}` for large `N` | §5 |
| `Part2/Cor13Even.lean`, `Part2/Cor13Matching.lean`, `Part2/Cor13Numerics.lean`, `Part2/Cor13.lean` | Corollary 13 with explicit exponents: all but `≤ 2^{N/2}` sum-free sets are all-odd or lie in `[⌈(N+1)/3⌉, N]` (`eventually_exceptional_le`) | §5 |
| `CE/Basic.lean`, `CE/GFunction.lean`, `CE/IntervalCount.lean` | the Cameron–Erdős count of sum-free subsets of `[⌈(N+1)/3⌉, N]`: exact identity, the recurrence for Green's `g(k)`, `T(N)² ≤ 20000 · 2^N` | Green's note [Gr-CE] |
| `Assembly.lean`, `Main.lean`, `Corollaries.lean` | union bound `f(N) ≤ 2^{⌈N/2⌉} + T(N) + #exceptional`, the root theorem, corollaries | §5 |

The proof is constant-explicit throughout (no `o(1)` bookkeeping is left informal): e.g. the interval count gives `T(N) ≤ 200 · 2^{N/2}`, Corollary 13 gives `#exceptional(N) ≤ 2^{N/2}` for all `N ≥ N₀`, and the final constant is `C = 41209 + 4^{N₀}` where `N₀` is the (existential) threshold produced by the "for N large" lemmas.

### Points where the formalization corrects or sharpens the source text

These were found while formalizing and are recorded so that a reviewer comparing with the paper is not surprised; in every case the corrected statement is what is proved and it suffices for the argument.

- Lemma 8, inequality (14): the difference `0` is always popular, so the count carries an extra `+ 1` (`lem8_card_popularDiff_le`); the slack is absorbed in (16).
- Green (3): the set that has at most `ε₁ p` elements is `A ∖ A′` (points of `A` in sparse progressions), which is what Proposition 6 uses (`card_sdiff_granularization_le`).
- Proposition 3 needs `M < p` (equivalently `L ≥ 2`); for `L = 1` the smoothing degenerates. This holds for Green's parameters.
- Proposition 4: with blocks `I_i = [⌊ip/M⌋, ⌊(i+1)p/M⌋)`, a sum `x + y` with `x ∈ I_i`, `y ∈ I_j` can land in `I_{i+j−1}` when both are left endpoints; at most `M²` such triples exist and they are absorbed (`block_add_index`).
- Proposition 5 is proved with the cruder hypothesis `(8 L E^{1/4})^{E} < p` (no AM–GM/monotonicity step), which is still implied by Green's parameter choice (`eventually_prop5_hypothesis8`).
- Proposition 7, Case 1 must read `2|X| > t` (at `|X| = t/2` the difference set need not be everything); the proposition is stated for `|A| ≥ (1/2 − 1/120) N` and `ε ≤ 10⁻³²`, which is what Corollary 13 needs (with `η = 1/50` exactly the even-case margin would be zero).
- Corollary 13, interval case: `⌊N/8⌋ − 4` disjoint pairs `(x, x + t)` with `x ≥ N/2` are used instead of `⌊N/12⌋ − 4`, giving a comfortable exponent margin.

## Reproduce

```sh
lake exe cache get      # Mathlib oleans
lake build              # builds CameronErdos and Jsp616
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of the root theorem and of the main intermediate results: every line is `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, custom `axiom`, `native_decide`, `ofReduceBool`, `unsafe` or `implemented_by` occurs anywhere in the package (`grep` in `verification.txt`); the only `decide` is the seven-value sanity `example` in `Statement.lean`, which is not used by any proof. `verification.txt` records the fresh build and audit of this exported package.

## Sources

- [Gr04] B. Green, *The Cameron–Erdős conjecture*, Bull. London Math. Soc. 36 (2004), 769–778; arXiv [math/0304058](https://arxiv.org/abs/math/0304058) (the version followed here).
- [Gr-CE] B. Green, *Notes on an argument of Cameron and Erdős* (two-page note formerly at dpmms.cam.ac.uk/~bjg23/papers/ce.pdf; the recurrence for `g(k)` and the interval count).
- [Sa03] A. A. Sapozhenko, *The Cameron–Erdős conjecture*, Dokl. Akad. Nauk 393 (2003), 749–752 (independent proof; not used).
- [LLS01] V. F. Lev, T. Łuczak, T. Schoen, *Sum-free sets in abelian groups*, Israel J. Math. 125 (2001), 347–367, §4 Proposition 1 and Lemma 6 (Green's Lemma 10; proved in `Part2/LLS.lean`).
- [CaEr90] P. J. Cameron, P. Erdős, *On the number of sets of integers with various properties*, Number Theory (Banff 1988), de Gruyter 1990, 61–79 (the conjecture and the interval count).
- Kneser's theorem: M. Kneser, *Abschätzung der asymptotischen Dichte von Summenmengen*, Math. Z. 58 (1953); Lean proof by Mantas Bakšys and Yaël Dillies, YaelDillies/misc-yd (see *Attribution*).
- Problem statement snapshot: `sources/erdos748-statement.txt` (erdosproblems.com/748, retrieved 2026-09-16).

## Attribution, prior art and submission status

- **Mathematics:** Green [Gr04] (and independently Sapozhenko [Sa03]); the interval count is due to Cameron and Erdős [CaEr90] as presented in [Gr-CE]; Lemma 10 is Lev–Łuczak–Schoen [LLS01].
- **Kneser's theorem** (`CameronErdos/Kneser/MulStab.lean`, `CameronErdos/Kneser/Kneser.lean`): Lean proof by Mantas Bakšys and Yaël Dillies, taken from `MiscYD/AddCombi/Kneser/{MulStab,Kneser}.lean` of [YaelDillies/misc-yd](https://github.com/YaelDillies/misc-yd) (Apache License 2.0); the files keep their original copyright headers, the licence text is in `CameronErdos/Kneser/LICENSE`, and the only changes are those recorded in each file's porting note (the Lean module-system preamble replaced by plain imports for Mathlib `1fe0a51a`, and the stabilizer import repointed; no changes to the mathematics).
- **Everything else** in `CameronErdos/` was written for this submission from the papers above. Formalization contribution submitted by Collin Yuanjie Ren (@CollinYuanjieRen), with AI assistance (Claude Code: design, decomposition and review by Claude Fable 5.1; Lean proofs by Claude Opus subagents, each module kernel-checked and audited before inclusion).
- **Prior art:** the public repository plby/lean-proofs contains a Lean formalization of Erdős #748 (`ErdosProblems/Erdos748.lean`, graph-container method) proving the exponent-level statement `log₂ f(n) / n → 1/2`; it does not prove `f(n) ≪ 2^{n/2}`. This package was developed from Green's paper and does not reuse any code from that repository (it was inspected only in a separate scope-alignment review). No first-formalization priority is claimed for the exponent-level corollary.
- This is a self-submission with a direct interest in the review outcome; no independent verifier is claimed. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT), except the Kneser files, which are Apache-2.0 as stated above.
