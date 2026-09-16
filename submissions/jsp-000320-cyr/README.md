# JSP-000320: binomial coefficients with no divisor close to `n` (Erdős #387)

This package submits a Lean formalization for intake and eligibility review. It answers
[JSP-000320](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000320),
which is [Erdős Problem #387](https://www.erdosproblems.com/387): is there an absolute
constant `c > 0` such that for all `1 ≤ k < n` the binomial coefficient `n.choose k` has a
divisor in `(cn, n]`? The answer is no. The theorem is due to Bui, Naprienko, Pratt and
Zaharescu (catalog reference [BNPZ26], [arXiv:2605.21221](https://arxiv.org/abs/2605.21221),
2026); this package formalizes their disproof.

## Statement and proof

[Erdos387Proof/Main.lean](Erdos387Proof/Main.lean) proves

```lean
theorem Erdos387Proof.not_exists_uniform_close_divisor :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k
```

and [Erdos387Proof/Canonical.lean](Erdos387Proof/Canonical.lean) proves the canonical face

```lean
theorem Erdos387.erdos_387 : False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k
```

The second is the statement of
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
`FormalConjectures/ErdosProblems/387.lean` (pinned in the campaign at
`ref/fc387-official.lean`), which reads `theorem erdos_387 : answer(False) ↔ …`. The
`answer` macro elaborates to its argument together with a metadata annotation, so the
proposition proved there is `False ↔ …`, which is copied verbatim above; the right-hand
side is character-for-character the official one. The two faces are interderivable in one
line, and neither carries a hypothesis: there is no `c`, no `n`, no side condition and no
analytic assumption on either statement. [Audit.lean](Audit.lean) restates both as typed
`example`s closed by the theorems.

Everything below is proved unconditionally. In particular
`Erdos387.shiftedSiegelWalfiszLower`, the analytic input of the covering construction, is a
theorem (it is proved from Bombieri–Vinogradov and from the prime number theorem in
arithmetic progressions, see *Upstream sources*), not an assumption; the audit prints its
axioms too.

### The BNPZ strategy, as formalized

Fix a putative constant `c > 0` and set `B := max 3 ⌈1/c⌉₊`, so that `1/B ≤ c`. It suffices
to find a single `n > k ≥ 3` such that `n.choose k` has **no** divisor in `(n/B, n]`: since
`n/B = (1/B)·n ≤ c·n`, such an `n` contradicts the assumed `c`. (The direction of this
inequality is the one trap in the reduction — a *small* threshold `c` forces a *large* `B`.)

1. **The covering progression.** `ErdosProblems/Erdos387/UnconditionalCover.lean` produces,
   for every `B ≥ 3` and every `K`, a `BPZSection6Input B K`: an exponent `k ≥ max(K,3)`, a
   residue `α`, and a factorization `g : Fin k → ℕ` with `∏ᵢ g i = k!` and `g i ≥ B`, such
   that every `n > k` in the progression `n ≡ α (mod N_k)` satisfies `g i ∣ n - i` for all
   `i`, has `n.choose k` free of every prime `p ≤ k`, and has each `(n - i)/g i` free of
   every prime `p ≤ k`. Any divisor `d ≤ n` of `n.choose k` is then forced to factor as
   `d = ∏ᵢ E.factor i` along the cover, with `E.factor i ∣ (n - i)/g i`. Existence of the
   cover rests on `Erdos387.shiftedSiegelWalfiszLower`, a uniform lower bound for primes in
   shifted intervals and arithmetic progressions with modulus and shift up to a fixed power
   of `log X`.
2. **Refinement and the sieve.** The progression is refined by `n ≡ k (mod ∏_{k<p<2k} p)`
   (`RefinedCover.lean`, `RefinedSieve.lean`), giving modulus `M = N_k · ∏_{k<p<2k} p`. The
   candidate set `RefinedSquarefreeCandidates S X z` consists of the `n ∈ (X/2, X]` in that
   class whose `n.choose k` is **`z`-rough** (no prime factor below `z`) and whose cover
   tuple is squarefree. The parameters are run along a subpower scale
   (`SubpowerScale.lean`): `X = 2^(xExp k · N^(2k+5))`, `z = 2^(xExp k · N^(2k+3))` — so
   `log X / log z = N²` — and the derived thresholds `y`, `medium`, `large`, `secondMin`,
   `gap`. A finite Brun sieve gives the lower bound
   `ExistingCountingBounds.eventually_squarefree_card_ge`: eventually in `N`,
   `#candidates ≥ sieveScale S N / 32` with `sieveScale S N = X · refinedDensity S z / M`.
   Every error count below is normalized by this same `sieveScale`.
3. **The five error classes.** `Erdos387Proof/SquarefreeErrorExhaustion.lean` proves that
   the candidates whose `n.choose k` *does* have a divisor in `(n/B, n]` are covered by five
   explicitly defined finite sets, so that
   `#bad ≤ #E1 + #E2 + #E3 + #E4 + #E5`:
   * **E1, large** (`RefinedLargeErrors`): some component of the divisor tuple exceeds
     `large`.
   * **E2, medium** (`RefinedMediumErrors`): some component lies in `(medium, large]`.
   * **E3, convenient** (`RefinedConvenientErrors`): all components are at most `medium` and
     some component admits a *convenient* factorization above `y` — a divisor of it in a
     prescribed dyadic window, which is what makes a divisor-switching/Fourier attack
     possible.
   * **E4, comparable primes** (`RefinedComparablePrimeErrors`): two distinct primes
     `secondMin < r < q ≤ medium` with `q < gap · r` both divide `n.choose k`.
   * **E5, separated almost-primes** (`RefinedSeparatedAlmostPrimeErrors`): every component
     is at most `medium` and factors as (something `≤ y³`) times (1 or a prime `> y`), the
     largest of those primes `q_{i₀}` is separated from all the others by the factor `gap`,
     and a second one exceeds `secondMin`.
4. **The four vanishing counts and the E4 budget.** E1, E2, E3 and E5 each have normalized
   count tending to `0` as `N → ∞`; E4 is not shown to vanish, but
   `ExistingCountingBounds.exists_cover_with_comparable_budget` chooses the cover (i.e. the
   exponent `k`) so that the normalized E4 count is eventually below any prescribed `δ` —
   here `δ = 1/128`, against the candidate lower bound `1/32`. This is a choice of the
   construction, not an extra premise.
5. **Assembly.** `Erdos387Proof/MainAssembly.lean` (`main_of_limits`) picks one `N` at which
   the squarefree lower bound, the four smallness statements and the finite scale side
   conditions all hold; then `#bad < #candidates`, and
   `SquarefreeErrorExhaustion.exists_counterexample_of_bad_squarefree_card_lt` extracts an
   `n ∈ (X/2, X]` with `k < n` and no divisor of `n.choose k` in `(n/B, n]`.
   `Erdos387Proof/Main.lean` feeds it the E3 and E5 limits, which are hypotheses of
   `main_of_limits` and theorems of this package.

The analytic content is in the E2, E3 and E5 counts. Each follows the same shape: the
membership condition is turned into a finite certificate (a divisor, or a prime and a
complementary factor), the count is written as a sum over a progression, an interval weight
of bounded variation replaces the sharp cut-off, the zero Fourier mode reproduces the Brun
main term with the required saving, and the nonzero modes are bounded by character-sum
estimates — reciprocal (Kloosterman) phases, a completion step, and a bilinear moment.

### Module groups (all under [Erdos387Proof/](Erdos387Proof/))

| group | files | content |
|---|---|---|
| Generic Fourier and sieve toolkit | `FiniteAbel`, `FamilyMixedAbel`, `FourierVariation`, `FourierMixedVariation`, `WeightedFourierVariation`, `WeightedCharacterInterval`, `IntervalWeightVariation`, `WeightedIntervalCut`, `TentFourier`, `PeriodicCompletion`, `PeriodicStripping`, `FiniteLogSeparator`, `MaskedReciprocalPhase`, `InversePhaseProjection`, `TerminalPrimeCancellation`, `HarmonicInterval`, `CoprimeHarmonic`, `BrunLocalDensity`, `BrunTruncation`, `IntegerBrunSmoothing`, `ComplementResidue`, `ComplementTupleCounting`, `ConductorStripping`, `ConstrainedSieveResidues`, `IntegerSieveResidues`, `IntegerClassFourier`, `IntegerFourierWindow`, `GcdFactorReindex`, `SquarefreeTuple`, `SquarefreeTupleMultiplicity`, `TupleReplacement` | finite Abel summation and mixed-family variants; total variation of tent and interval weights and of inverse-product phases; exact discrete Fourier expansions on a full period; periodic completion and stripping of a modulus; logarithmic product separation; masked reciprocal phases; truncated Brun sieve densities and their smoothing; residue and tuple bookkeeping on the refined class |
| E2, medium errors | 41 `Medium*` files, ending in `MediumError.tendsto_medium_card_div_sieveScale_zero` | the divisor-switching count for a component in `(medium, large]`: certificate cover, complement grouping and mass, factor windows and geometry, reciprocal-phase and weighted-Kloosterman estimates, signed main term, zero mode, Fourier tail and its decay, endpoint error and decay, subpower reduction and total envelope |
| E3, convenient errors | 30 `Convenient*` files plus `VariableBoxConvenientMoment`, `VariableBoxReciprocalEnergy`, `IndexedConvenientMoment`, `SplitCertificateMass`, ending in `ConvenientError.tendsto_convenient_card_div_sieveScale_zero` | certificate cover and nonnegative enlargement, nested complement grouping, dyadic reduction, phase data and split fibres, the normalized first-moment engine (`ConvenientNormalizedMoment`) with its box identity/envelope, moment boxes, bound and saving, weighted moment/prefix/box chain, main mass and decay, mass decomposition, zero mode and decay, partial Fourier, outer partial summation, Fourier tail and decay |
| E5, separated almost-primes | 34 `Separated*` files, ending in `SeparatedError.tendsto_separated_card_div_sieveScale_zero` | Buchstab decomposition and separation of the distinguished prime, retained-residue and prime-fibre CRT, certificate cover and enlargement, key mass, rough bound, Type I bound and Type II Cauchy–Schwarz with its numeric saving, frequency and parameter windows, product window, signed cover, zero mode and decay, partial Fourier and bound, Fourier tail and decay, outer bound and total envelope |
| Interfaces and assembly | `ExistingCountingBounds`, `SquarefreeErrorExhaustion`, `MainAssembly`, `Main`, `Canonical` | the E1 limit, the squarefree lower bound and the E4 budget at the common scale; the five-error exhaustion on the squarefree candidate set; the conditional assembly; the two roots |

[Erdos387Proof/GoalConsequences.lean](Erdos387Proof/GoalConsequences.lean) is an auxiliary
file that is **not** used by either root: it records the elementary implication between the
two divisor questions in the canonical Erdős 387 file. It is built by this package so that
the whole first-party library compiles.

## Upstream sources

Four bodies of Lean code are involved besides Mathlib. Only the first two are redistributed
in this package.

* **`Erdos387Proof/` (146 files) — first-party**, original to this submission and the work
  claimed here. Under the repository [code license](../../LICENSE).
* **`PrimeNumberTheoremAnd/` (9 files) — Apache-2.0, shipped.** Derived from
  [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
  via [plby/lean-proofs](https://github.com/plby/lean-proofs) commit
  `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, from which the copies here are byte-identical.
  They supply the prime-number-theorem input of
  `ErdosProblems/Erdos387/AnalyticInputs.lean`. The Apache-2.0 text is in
  [LICENSES/PrimeNumberTheoremAnd-LICENSE](LICENSES/PrimeNumberTheoremAnd-LICENSE) and the
  required statement of changes in
  [LICENSES/PrimeNumberTheoremAnd-NOTICE](LICENSES/PrimeNumberTheoremAnd-NOTICE). plby's
  adaptation is substantive (content pruned, proofs repaired for a newer Mathlib), so **no
  exact PrimeNumberTheoremAnd base commit reproduces these files by hash**; this is the one
  provenance item in the package that cannot be pinned to a commit.
* **`ErdosProblems/` (101 files) — no license grant, fetched, never redistributed.** The
  Erdős 387 support library from plby/lean-proofs at the same commit
  `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`: the BNPZ covering construction, the refined
  sieve, the error-class definitions and exhaustion, the Kloosterman/Stepanov inputs and the
  E1/E4 counts. That repository has no `LICENSE` at its root — `src/latest/LICENSE` is only
  a notice that *some* files come from elsewhere under Apache-2.0 — and none of these 101
  files carries a copyright or license header, so none of their text is copied into this
  submission. [fetch_pinned.py](fetch_pinned.py) downloads each one and verifies its SHA-256
  against [pinned-sources.json](pinned-sources.json). All 101 are byte-identical to upstream;
  there is no import rewrite and no patch.
* **`vendor/formalpantheon/{BoundedGaps,Warning}` (886 `.lean` files, 442 in the import cone)
  — Apache-2.0, fetched.** [frenzymath/FormalPantheon](https://github.com/frenzymath/FormalPantheon)
  at commit `ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`.
  `BoundedGaps.BombieriVinogradov.Proof.MainTheorem` is what makes
  `Erdos387.shiftedSiegelWalfiszLower` a theorem; `BoundedGaps.Maynard.*` supplies Wirsing
  and coprime-harmonic estimates, and `Waring.Analytic.*` finite Fourier and
  Stepanov–Weil character-sum bounds. `fetch_pinned.py` downloads the commit tarball,
  extracts the two packages, applies [patches/formalpantheon-mathlib-v4.33.0.patch](patches/formalpantheon-mathlib-v4.33.0.patch)
  (91 files, a Mathlib v4.32 → v4.33 adaptation only: `letI` → `let`,
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `open AddChar` → `open _root_.Waring.Analytic.AddChar`,
  `[DecidableEq F]` → `classical`, and the consequent proof rewrites — no statement of any
  upstream theorem is changed), and then verifies all 886 resulting files against their
  recorded SHA-256 sums, so the adapted tree is reproduced byte-for-byte. The patch is our
  own `diff -u`, regenerated against the pristine tarball rather than redistributed from
  plby's `src/latest/patches/`. Change notice:
  [LICENSES/FormalPantheon-NOTICE](LICENSES/FormalPantheon-NOTICE).

GitHub-generated commit tarballs are not contractually byte-stable, so `fetch_pinned.py`
treats a mismatch of the recorded tarball hash as a warning and relies on the per-file
hashes, which are the authoritative check; any file-level mismatch is a hard failure.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
python3 fetch_pinned.py
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain):
`leanprover/lean4:v4.33.0`. Mathlib is pinned to `db584cd6d46c92f209a44c0f1c829460d327499d`,
with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is
optional for correctness; it avoids rebuilding Mathlib. `fetch_pinned.py` needs network
access and takes well under a minute; `--check` re-verifies an existing checkout without
downloading, and `--list` prints the two file lists. Building the fetched FormalPantheon
packages from source is the bulk of the build.

[Audit.lean](Audit.lean) restates both roots as typed `example`s closed by the theorems and
prints the axioms of the roots and of the main components. Every printed declaration depends
exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational
axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust
extension occurs anywhere in the dependency cone. [verification.txt](verification.txt)
records the local fetch, build and audit of this exported package. The published prize rules
(v1.0, 16 September 2026, section 6) require an offline axiom audit by the designated
verifiers and do not list the accepted foundational axioms; the three axioms above are
stated here so that the audit can decide on them explicitly.

Local verification used a shared Mathlib install on arm64 macOS (`.lake/packages`
symlinked, not committed); the fetched FormalPantheon packages and all local libraries were
compiled from source in this directory. It is not a clean, network-disabled rebuild or
verification by two independent checker implementations. Authorized statement review, any
required independent verification and permanent archival remain for the official review
process.

## Attribution and submission status

The theorem and the proof strategy are due to Hung Bui, Stepan Naprienko, Kyle Pratt and
Alexandru Zaharescu, *Binomial coefficients with divisors avoiding an interval*,
[arXiv:2605.21221](https://arxiv.org/abs/2605.21221) (2026); the covering construction and
the five-class error decomposition formalized here follow their Section 6 and Propositions
6.5–6.6. The canonical statement is the one from Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
(`ErdosProblems/387.lean`, Apache-2.0, where it is stated with `sorry`); this package proves
it. The pinned upstream Lean code is credited above: plby/lean-proofs for the covering
construction, the refined sieve and the E1/E4 counts; frenzymath/FormalPantheon for
Bombieri–Vinogradov and the character-sum inputs; PrimeNumberTheoremAnd for the prime number
theorem in arithmetic progressions. The 146 first-party modules — the E2, E3 and E5 counts,
the generic Fourier and sieve toolkit they rest on, and the assembly — were prepared with
Codex (GPT Astra and GPT Sol) and Claude Code (Claude Fable 5.1 and Claude Opus) assistance.

The contribution sought is formalization of the exact problem statement. No new mathematical
discovery is claimed, and no priority is claimed: the catalog entry for JSP-000320 records
"Lean proof: No" and the Formal Conjectures file carries a `sorry`, which is the only sense
in which this is offered as a first machine-checked proof; the authors of [BNPZ26] and any
other formalization effort are not surveyed here, and no entitlement to an award is
asserted.

Proposed formalizer: `RECIPIENT-jsp-000320-cyr-A`, identity confirmation pending. No solver
nomination, award tier, payment status or official verification status is asserted or
changed. The `submissions/` location is proposed intake packaging; it is not a new official
record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) (MIT)
and [content license](../../LICENSE-CONTENT) (CC BY 4.0); that MIT grant is what covers the
first-party `Erdos387Proof/` sources here. `PrimeNumberTheoremAnd/` is redistributed under
Apache-2.0 as recorded in [LICENSES/](LICENSES); the plby and FormalPantheon sources are
fetched at build time under their own terms and are not part of this contribution.
