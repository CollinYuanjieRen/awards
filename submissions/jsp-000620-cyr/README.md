# JSP-000620: favorite distances in four-dimensional point sets

This package submits a Lean formalization for intake and eligibility review. It addresses [JSP-000620](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000620): in a finite four-dimensional point set, how many other points can be at the same distance from one point? This is [Erdős Problem #754](https://www.erdosproblems.com/754). Let `f(n)` be the largest `k` such that some set of `n` points in `ℝ⁴` has, at every point `x`, at least `k` other points at one common distance (which may depend on `x`). The answer is `f(n) = n/2 + O(1)`.

## Statement and proof

[JSP620/Target.lean](JSP620/Target.lean) proves `Erdos754Lower.erdos_754_two_sided`:

```lean
(∀ n : ℕ, n / 2 ≤ f n) ∧
(∀ n : ℕ, n ≠ 0 → 8 ∣ n → n / 2 + 2 ≤ f n) ∧
(∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C)
```

together with the corollaries `abs_f_sub_half_le` (`∃ C, ∀ n, |f n − n/2| ≤ C`) and `f_sub_half_isBigO` (`f n − n/2 = O(1)` in Mathlib's `Asymptotics.IsBigO`). Here `f = Erdos754.f`, defined in [JSP620/External/Erdos754.lean](JSP620/External/Erdos754.lean): points live in `EuclideanSpace ℝ (Fin 4)` with its standard metric; `Attainable n k` means that some `n`-element `Finset` `P` admits positive distances `c : P → ℝ` such that every `x ∈ P` has at least `k` points `y ≠ x` of `P` with `dist x y = c x`; and `f n` is the supremum of the attainable `k` (with `f 0 = 0`). `n / 2` is natural-number division, so the first conjunct is `⌊n/2⌋ ≤ f(n)`.

The two conjuncts on the left are the lower bound of Avis, Erdős and Pach, formalized here. [JSP620/Circles.lean](JSP620/Circles.lean) places two orthogonal circles of radius `1/√2` in `ℝ⁴`: every point of one circle is at distance one from every point of the other, and rotating a point of a circle by a right angle gives a point at distance one on the same circle. [JSP620/Construction.lean](JSP620/Construction.lean) parametrizes `N` points of a circle by rescaled `N`-th roots of unity. With `⌈n/2⌉` and `⌊n/2⌋` points on the two circles every point has `⌊n/2⌋` others at distance one, giving `⌊n/2⌋ ≤ f(n)` for every `n`. With the vertices of `k` inscribed squares on each circle (`n = 8k`), every point additionally has two neighbours at distance one on its own circle, giving `n/2 + 2 ≤ f(n)`. The problem page states the lower bound as `n/2 + 2 ≤ f(n)` without qualification; the formal statement records the divisibility condition `8 ∣ n` under which this two-circle construction attains it, and the unconditional bound `⌊n/2⌋ ≤ f(n)` that suffices for `f(n) = n/2 + O(1)`.

The third conjunct is the upper bound `f(n) ≤ n/2 + O(1)` (Swanepoel's theorem, answering the question as asked on the problem page). It is **not** our work: `Erdos754.erdos_754` is proved, with the explicit constant 202, in the existing public formalization by Codex / GPT-5.6 Sol in the repository [plby/lean-proofs](https://github.com/plby/lean-proofs), files [`src/latest/ErdosProblems/Erdos754.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos754.lean) and [`Erdos755.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos755.lean) at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. `Erdos755.lean`, whose file header contains an Apache-2.0 notice, remains tracked byte-for-byte under `JSP620/External/`. The pinned `Erdos754.lean` has no explicit license grant, so this package does not redistribute or label it Apache-2.0: `fetch_sources.py` downloads it from its original public location, checks source SHA-256 `283f05a45942be33aa589020a8e26fc0f253409d909b3bac77c81ae3bfbca7bf`, performs one documented import replacement, and checks the adapted hash recorded in `external-proof-sources.json`. The prior tracked adaptation also carried an inaccurate three-line Apache note; the generated file intentionally omits that local note and otherwise differs from the pinned original only in the required import. The formalization credit for the upper bound belongs to those authors; this submission claims only the lower-bound development in `Circles.lean`, `Construction.lean` and the assembly in `Target.lean`.

Every fact is proved in Lean; no literature theorem is assumed. Both parts use only Mathlib and the pinned dependencies.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
python3 fetch_sources.py
lake exe cache get
lake build
lake env lean Audit.lean
```

The fetch step is required in a fresh checkout. It refuses to overwrite a changed destination and writes only the adapted bytes recorded in the manifest. The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness; it avoids rebuilding dependencies.

[Audit.lean](Audit.lean) restates the main theorem as an explicit `example`, and prints the axioms of the lower bounds, the assembled theorem, its corollaries and the imported upper bound.

**Comparator status.** The pinned package contains no authoritative external target for the assembled two-sided theorem, and the earlier self-authored `Challenge.lean` was removed before this pin. Its historical challenge transcript is not used as verification evidence. The full target is checked directly against the original page and catalog in the independent scope record; `Audit.lean` type-checks an explicit restatement of the complete theorem against the proved roots.

**Axioms.** Every audited theorem depends on exactly the three standard axioms of Lean's core logic used throughout Mathlib, and on nothing else:

| Theorem | Axioms |
| --- | --- |
| `Erdos754Lower.half_le_f` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos754Lower.half_add_two_le_f_of_eight_dvd` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos754Lower.erdos_754_two_sided` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos754Lower.abs_f_sub_half_le` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos754Lower.f_sub_half_isBigO` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos754.erdos_754` (third-party upper bound) | `propext`, `Classical.choice`, `Quot.sound` |

No project axiom is declared, no `sorry` or `admit` occurs, `native_decide` and heartbeat or recursion-depth overrides are not used, and no hypothesis beyond those of the original problem is assumed: the lower-bound theorems have no premises other than the stated `n ≠ 0` and `8 ∣ n` of the divisibility-qualified bound, and the two-sided theorem is closed. The published selection rules describe Lean verification as a pass/fail entry threshold without naming an axiom policy; this repository's verification-record schema records an explicit axiom list per theorem, which is why the lists are declared here in full. [verification.txt](verification.txt) records the local build and audit of this exported package.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process; no curator signatures or attestations are fabricated.

## Attribution and submission status

The mathematics is classical. The lower-bound construction and the asymptotic answer are due to D. Avis, P. Erdős and J. Pach, "Repeated distances in space", Graphs and Combinatorics 4 (1988), 207–217, [DOI](https://doi.org/10.1007/BF01864161). The upper bound in the form `n/2 + O(1)` (via the favourite-distance digraph bound `n²/2 + O(n)`) is due to K. J. Swanepoel, "Favourite distances in high dimensions", Discrete Geometry and Algebraic Combinatorics, Contemp. Math. 625 (2014), 499–519, [arXiv:1108.4817](https://arxiv.org/abs/1108.4817). Neither paper was used as a proof assumption. The lower-bound Lean code was prepared with Claude Code (Claude Fable 5.1) assistance; the contribution sought is formalization of the missing lower-bound component and the assembled two-sided answer, not a new mathematical discovery.

At the time of submission no other pull request or issue in this repository was found that submits or registers a Lean proof for JSP-000620. No first-formalization priority or entitlement to an award is claimed. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000620-cyr-A`, identity confirmation pending, for the lower-bound development and assembly only. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT). The tracked `Erdos755.lean` retains its explicit Apache-2.0 notice. The generated `Erdos754.lean` is fetched from its pinned public origin with unchanged authorship and is excluded from the repository archive; this package makes no license claim for it.
