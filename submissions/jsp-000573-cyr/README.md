# JSP-000573: the exact size of a set family avoiding one intersection size

This package submits a Lean formalization for intake and eligibility review. It addresses [JSP-000573](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000573): how large can a set family be if a prescribed pairwise intersection size is forbidden? This is [Erdős Problem #703](https://www.erdosproblems.com/703). For `r ≥ 0` let `T(n, r)` be the largest size of a family `𝓕` of subsets of an `n`-set with `|A ∩ B| ≠ r` for all `A, B ∈ 𝓕` (including `A = B`). The catalog credits the resolution to Frankl–Füredi (1984), Frankl (1977, the case `r = 1`), and Frankl–Rödl (1987, the exponential gap `T(n, r) < (2 − δ)^n` for `εn < r < (1/2 − ε)n`).

## What is proved, and what already existed

The Frankl–Rödl exponential gap, the trivial value `T(n, 0) = 2^(n−1)` and the two Frankl–Füredi extremal constructions with their lower bounds are already formalized by Codex / GPT-5.6 Sol in [plby/lean-proofs](https://github.com/plby/lean-proofs) (`Erdos703.erdos_703`, `T_zero`, `franklFurediOdd_card_le_T`, `franklFurediEven_card_le_T`). That development does not contain the matching upper bound, i.e. the theorem that for fixed `r` and all large `n` these constructions are optimal (Frankl–Füredi, *On hypergraphs without two edges intersecting in a given number of vertices*, J. Combin. Theory Ser. A 36 (1984), 230–236, Theorem 1.3). This submission formalizes that theorem and thereby the exact value of `T(n, r)` for every `r` and all sufficiently large `n`.

## Statement and proof

[JSP573/FF/Main.lean](JSP573/FF/Main.lean) proves

```lean
theorem frankl_furedi (t : ℕ) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Erdos703.T n t = ffBound n t

theorem erdos_703_exact (r : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Erdos703.T n r = if r = 0 then 2 ^ (n - 1) else ffBound n r
```

where `Erdos703.T n r` is plby's definition (the `Finset.sup` of the cardinalities of all `r`-avoiding subfamilies of the powerset of `range n`) and, in [JSP573/FF/Counting.lean](JSP573/FF/Counting.lean),

```lean
def ffBound (n t : ℕ) : ℕ :=
  (∑ i ∈ Finset.range t, n.choose i) + (∑ i ∈ Finset.Ioc ((n + t) / 2) n, n.choose i) +
    (if (n + t) % 2 = 0 then (n - 1).choose ((n + t) / 2) else 0)
```

is the size of the Frankl–Füredi family `𝓕*(n, t)` (all sets of size `< t` or `> (n + t)/2`, plus, when `n + t` is even, the sets of size `(n + t)/2` avoiding a fixed element). The lemmas `card_franklFurediOdd` and `card_franklFurediEven` show that `ffBound n t` is exactly the cardinality of plby's constructions `franklFurediOdd n t` and `franklFurediEven n t`, so the lower bound `ffBound n t ≤ T n t` is theirs and the upper bound `T n t ≤ ffBound n t` for `n ≥ n₀(t)` is new.

The proof follows the paper. Write `f_i` for the number of members of `𝓕` of size `i` and `q(t) = t + 1 + lcm(1, …, t)`.

* [FF/Basic.lean](JSP573/FF/Basic.lean): levels, shadows, complements, `q(t)`, inclusion vectors; `f_t = 0`; the disjointness count `|∂_{i−t} 𝓕_i| + f_{n+t−i} ≤ C(n, i − t)` (Proposition 3.1: the complement of a member of size `n + t − i` cannot contain an `(i − t)`-subset of a member of size `i`); for every `m > lcm(1, …, t)` some prime power `p^s > t` divides `m`.
* [FF/RankLemmas.lean](JSP573/FF/RankLemmas.lean) and [FF/FranklSinghi.lean](JSP573/FF/FranklSinghi.lean): the Frankl–Singhi rank theorem (Theorem 1.4): if `p^s ∣ h − t`, `t < p^s`, and `𝓕` is `h`-uniform with `|A ∩ B| ≠ t` for `A ≠ B`, the inclusion vectors of order `h − t − 1` of the members are linearly independent over `ℚ`. The Gram matrix is evaluated through the polynomial `∏_{t < i < h} (i − x)/(h − t − 1)!`, whose binomial-basis expansion has integer-rescaled coefficients not all divisible by `p`; the diagonal is `±1` and the off-diagonal entries vanish modulo `p` (Kummer-type divisibility).
* [FF/Shadow.lean](JSP573/FF/Shadow.lean): the shadow inequality (Theorem 1.5, via links as in Proposition 2.1): under the linear independence above, `|𝓕| · C(2h − t − 1, g) ≤ |∂_g 𝓕| · C(2h − t − 1, h)` for `h − t − 1 ≤ g ≤ h`.
* [FF/Counting.lean](JSP573/FF/Counting.lean): the level inequality (3), `f_i · i + f_{n+t−i} · (i − t) ≤ C(n, i − t) · (i − t)` for `q(t) ≤ i ≤ (n + t)/2`; summing over the level pairs `(i, n + t − i)` gives `|𝓕| ≤ ffBound n t + ∑_{t < i < q(t)} f_i`, and a refined version isolates the pair `(b, n + t − b)` with `b = (n + t)/2 + 1`. If some member `A₀` has size `a` with `t < a < q(t)`, level `b` misses every `b`-set meeting `A₀` in exactly `t` points: `f_b + C(a, t) · C(n − a, b − t) ≤ C(n, b)`.
* [FF/Asymptotics.lean](JSP573/FF/Asymptotics.lean) and [FF/Main.lean](JSP573/FF/Main.lean): if no member has size in `(t, q(t))` the bound is immediate; otherwise the loss `C(n − a, b − t) ≥ C(2j, j) ≥ 4^j/(2j + 1)` with `j ≥ n/2 − q(t) − 2`, transferred through the level inequality at the partner level, exceeds the polynomial `∑_{t < i < q(t)} C(n, i) ≤ q(t) · n^{q(t)}` once `n` is large. The exact value then follows from `Erdos703.T_le_of_forall`, the counting lemmas and plby's lower bounds; the `r = 0` branch is plby's `T_zero`.

The third-party module `Erdos703` (with its directory `Erdos703/`: the Frankl–Rödl proof, four files) is included verbatim under `JSP573/External/` (Apache License 2.0, headers retained; the only change is the module prefix in `import` lines, listed in [external-changes.txt](external-changes.txt)) so that the theorem is reproducible from this directory alone. SHA-256 values of every original file at plby/lean-proofs commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` are in [plby-source-hashes.txt](plby-source-hashes.txt). The formalization credit for the definitions, the constructions, `T_zero` and the Frankl–Rödl theorem belongs to those authors; this submission claims only the files under `JSP573/FF/` and the challenge module.

Every fact is proved in Lean; no literature theorem is assumed. All parts use only Mathlib and the pinned dependencies.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness; it avoids rebuilding dependencies.

[Audit.lean](Audit.lean) restates the two headline theorems as explicit `example`s and prints the axioms of the headline theorems, the main lemmas and the imported third-party theorems.

**Axioms.** Every audited theorem depends on exactly the three standard axioms of Lean's core logic used throughout Mathlib, and on nothing else:

| Theorem | Axioms |
| --- | --- |
| `FranklFuredi.erdos_703_exact` | `propext`, `Classical.choice`, `Quot.sound` |
| `FranklFuredi.frankl_furedi` | `propext`, `Classical.choice`, `Quot.sound` |
| `FranklFuredi.exists_upper_bound` | `propext`, `Classical.choice`, `Quot.sound` |
| `FranklFuredi.frankl_singhi`, `shadow_card_mul_choose_ge`, `level_inequality`, `card_le_ffBound_add_middle`, `card_le_ffBound_add_middle_sub`, `level_card_le_choose_sub`, `card_franklFurediOdd`, `card_franklFurediEven`, `shadow_card_add_level_card_le`, `exists_ffPoly_expansion`, `eventually_mul_pow_lt_two_pow` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos703.T_zero`, `franklFurediOdd_card_le_T`, `franklFurediEven_card_le_T`, `erdos_703` (third-party) | `propext`, `Classical.choice`, `Quot.sound` |

No project axiom is declared, no `sorry` or `admit` occurs outside the intentionally `sorry`-ed comparator challenge, `native_decide` is not used, and no hypothesis beyond `1 ≤ t` in `frankl_furedi` (the range of the Frankl–Füredi theorem; `erdos_703_exact` is premise-free) appears. The published selection rules describe Lean verification as a pass/fail entry threshold without naming an axiom policy; this repository's verification-record schema records an explicit axiom list per theorem, which is why the lists are declared here in full.

**Comparator challenge.** [Challenge.lean](Challenge.lean) is a self-contained challenge module (imports only Mathlib; statements proved by `sorry`) restating the definitions `Erdos703.AvoidsRIntersection`, `Erdos703.T` and `FranklFuredi.ffBound` verbatim together with the two headline theorems, with [Comparator/FranklFuredi.json](Comparator/FranklFuredi.json) naming `JSP573.FF.Main` as the solution module and the three standard axioms as the only permitted ones. A textual identity check of every challenge definition and statement against the solution is recorded in [verification.txt](verification.txt). Running Comparator itself requires its Linux sandbox tooling and was not performed locally.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process; no curator signatures or attestations are fabricated.

## Attribution and submission status

The mathematics is due to P. Frankl and Z. Füredi, "On hypergraphs without two edges intersecting in a given number of vertices", J. Combin. Theory Ser. A 36 (1984), 230–236, building on P. Frankl, "An intersection problem for finite sets", Acta Math. Acad. Sci. Hungar. 30 (1977), 371–373 (the case `r = 1`), and on the Frankl–Singhi mod-`p` rank theorem; the exponential gap already formalized by plby is due to P. Frankl and V. Rödl, "Forbidden intersections", Trans. Amer. Math. Soc. 300 (1987), 259–286. None of these papers was used as a proof assumption. The Lean code under `JSP573/FF/` was prepared with Claude Code (Claude Fable 5.1 and Claude Opus) assistance; the contribution sought is the formalization of the exact-value theorem, not a new mathematical discovery.

At the time of submission no other pull request or issue in this repository was found that submits or registers a Lean proof for JSP-000573. No first-formalization priority or entitlement to an award is claimed. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000573-cyr-A`, identity confirmation pending, for the files under `JSP573/FF/` and the challenge module only. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT); the files under `JSP573/External/` retain their original Apache License 2.0 notices.
