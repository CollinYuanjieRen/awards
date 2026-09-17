# JSP-000788: sparse sequences whose finite sums omit a colour (Erdős #948)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000788](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000788), which is [Erdős Problem #948](https://www.erdosproblems.com/948) (Erdős 1977; Erdős–Galvin [ErGa91], Problem 4.2): is there a function `f(n)` and a `k` such that in any `k`-colouring of the integers there is a sequence `a_1 < a_2 < ⋯` with `a_n < f(n)` for infinitely many `n` whose set of finite subset sums does not contain all colours? The answer is no (GPT Pro, prompted by Liam Price, June 2026, confirmed on the problem page): for every `f` there is a colouring of the positive integers with countably many colours such that every such sequence has finite subset sums of every colour, and reducing the colour modulo `k` gives the same for every `k ≥ 1`.

## Statement and proof

[Erdos948Colouring/Main.lean](Erdos948Colouring/Main.lean) proves

```lean
theorem erdos_948_nat (f : ℕ → ℕ) :
    ∃ c : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → SmallInfinitelyOften f a →
      ∀ j : ℕ, ∃ m ∈ FiniteSums a, c m = j
theorem erdos_948 (f : ℕ → ℕ) (k : ℕ) (hk : 0 < k) :
    ∃ c : ℕ → Fin k, ∀ a : ℕ → ℕ, StrictMono a → SmallInfinitelyOften f a →
      ∀ j : Fin k, ∃ m ∈ FiniteSums a, c m = j
theorem erdos_948_closed :
    ¬ ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧ ∀ c : ℕ → Fin k, ∃ a : ℕ → ℕ, StrictMono a ∧
      SmallInfinitelyOften f a ∧ ∃ j : Fin k, ∀ m ∈ FiniteSums a, c m ≠ j
```

where, in [Erdos948Colouring/Definitions.lean](Erdos948Colouring/Definitions.lean), `FiniteSums a` is the set of sums `∑_{i ∈ S} a i` over nonempty finite `S ⊆ ℕ` and `SmallInfinitelyOften f a` says `∀ N, ∃ n ≥ N, a n < f n`, i.e. `a n < f n` for infinitely many `n`. A colouring with `k` colours is a function `ℕ → Fin k`; the sequence is any strictly increasing `a : ℕ → ℕ`. Sequences are indexed from `0` rather than `1`, and colourings are defined on all of `ℕ` rather than on the positive integers; neither changes the question (a colouring of `ℕ` restricts to one of the positive integers, and a strictly increasing sequence of naturals is a sequence of positive integers from its second term on, so a colouring defeating every sequence on `ℕ` defeats every sequence of positive integers). `FiniteSums` takes the stronger reading that the finite index set is nonempty (with the empty sum allowed, the value `0` would always be present, and no such degenerate hit is used); this makes the positive theorems harder and the negation stronger. The third theorem is the literal negation of the question as asked; the first two are the positive statements it follows from, the first being the countable-colour strengthening recorded on the problem page. [Audit.lean](Audit.lean) restates all three as typed `example`s.

The colouring is the greedy-window colouring of the problem page sketch. Fix `G : ℕ → ℕ` and, for `n ≥ 1`, let `v` be the position of the lowest set binary digit of `n`; clear the digits of `n` in the window `[v, v + G v]` and repeat on what is left. `greedy G n` is the number of windows used and the colour of `n` is `greedy G n − 1`. The proof that every sparse sequence hits every colour is elementary:

1. [Greedy.lean](Erdos948Colouring/Greedy.lean): `greedy_add` shows that if `0 < m < 2^(k + G k + 1)` is divisible by `2^k` and `r` is divisible by `2^(k + G k + G (k + G k) + 1)`, then `greedy G (m + r) = 1 + greedy G r` (the first window of `m + r` is exactly the window of `m`). Iterating, `greedy_sum_blocks` gives `greedy G (m_1 + ⋯ + m_j) = j` for `j` such "blocks" `m_i` whose windows are separated in this sense.
2. [Blocks.lean](Erdos948Colouring/Blocks.lean): `exists_block` finds, beyond any index `N` and for any lower bound `K`, an interval `[s, t)` of indices whose block `m = ∑_{i ∈ [s,t)} a i` satisfies `0 < m`, `2^k ∣ m` and `m < 2^(k + G_f k + 1)` for some `k ≥ K`. Take an index `n` with `a n < f n` far beyond `N`, let `2^k ≤ n − N < 2^(k+1)`; by the pigeonhole principle two of the `n − N + 1` partial sums `∑_{i ∈ [N, i')} a i` agree modulo `2^k` (in the code `N` is first replaced by `N + 1`, so that every term in play is positive), and their difference is a block bounded by `(n − N) · a n < 2^(k+1) f n`; the window function `G_f k = ⌊log₂(2^(k+1) · env_f(2^(k+2)))⌋ + 1`, with `env_f` the monotone envelope `∑_{i ≤ n} f i`, is chosen exactly so that this block fits in `[k, k + G_f k]`.
3. [Assembly.lean](Erdos948Colouring/Assembly.lean): `exists_finiteSum_greedy` builds `j + 1` pairwise disjoint such blocks with separated windows, by induction using step 2 with `N` and `K` taken from the previous block, so that the union of their index sets is a nonempty finite `S` with `greedy (G_f) (∑_{i ∈ S} a i) = j + 1`.
4. [Main.lean](Erdos948Colouring/Main.lean): the colour `j` is therefore attained by a finite sum, for every `j`; reducing the colouring modulo `k` gives the `k`-colour theorem, and the closed form follows.

No numerical certificate or decision procedure is used.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness.

[Audit.lean](Audit.lean) prints the axioms of the three theorems and of the main lemmas. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the package. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (https://www.hejustinsun.com/prize/rules, v1.0, retrieved 16 September 2026; the rules are not part of this repository) require in their sections 4 and 6 an offline axiom audit by the designated verifiers and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official process.

## Attribution and submission status

The negative answer and the greedy-window colouring are due to GPT Pro prompted by Liam Price (June 2026), peer-reviewed by Stijn Cambie and summarized by Thomas Bloom on the problem page; the argument formalized here is that sketch (pigeonhole on partial sums modulo `2^k`, then disjoint blocks with separated windows), written for this package from the problem page alone with its own choice of window function. Liam Price reports a Lean formalization of the argument produced with Aristotle, and a Lean formalization also exists in the repository plby/lean-proofs (file `src/latest/ErdosProblems/Erdos948.lean` at commit `8822f7dd`, whose header a coverage screen of that repository read to identify the problem; its proof text was not opened). Neither carries a license grant we could rely on: Price's share names no license, and the plby repository has no root LICENSE while its notice `src/latest/LICENSE` covers only externally sourced files. The plby file is also registered as existing Lean evidence for this catalog entry in upstream [issue #19](https://github.com/TheJustinSunPrize/awards/issues/19) and [PR #40](https://github.com/TheJustinSunPrize/awards/pull/40) (third-party replay reports and a catalog-status correction, which redistribute or point to that file but submit no proof of their own). The present package is an independent formalization written from the mathematical argument on the problem page without consulting or reusing either proof text; it is offered as a license-clean, first-party kernel-checked proof of the catalog question, and it does not dispute the credit or priority recorded in those registrations. It was prepared with Claude Code (Claude Fable 5.1 planning, Claude Opus implementation) assistance. The contribution sought is a reusable kernel-checked formalization of the exact catalog question; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed.

Proposed formalizer: `RECIPIENT-jsp-000788-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
