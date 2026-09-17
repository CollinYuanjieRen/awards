# JSP-000731 (Erdős #880): must the distinct-element sumset of an additive basis have bounded gaps?

Catalog entry: [JSP-000731](../../problems/catalog-0701-0800.md#JSP-000731). Problem page:
<https://www.erdosproblems.com/880>.

## The question and its complete answer

Erdős (1998), for Burr and himself: call an infinite set `A` of integers an *asymptotic basis of order `k`*
if every sufficiently large integer is the sum of `k` or fewer elements of `A`. Let `b₁ < b₂ < ⋯` be the
integers that are sums of `k` or fewer **pairwise distinct** elements of `A`. Is `b_{i+1} − b_i` bounded?

Hegyvári, Hennecart and Plagne (*Answer to a question by Burr and Erdős on restricted addition, and related
results*, Combin. Probab. Comput. 16 (2007) 747–756, Theorem 1) answered: **yes for `k = 2`** (the gaps are
eventually at most 2) and **no for every `k ≥ 3`**. Everything below is proved in Lean 4 / Mathlib for every
`k`, with only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

| face | statement | theorem |
|---|---|---|
| (i) | order 2: for every `A`, eventually every window `[n, n+1]` contains a sum of ≤ 2 distinct elements, so the gaps are bounded | `Erdos880.order_two_gap_le_two`, `Erdos880.order_two_bounded_gaps` |
| (ii) | every `k ≥ 3`: an explicit infinite set of positive integers which is an asymptotic basis of order **exactly** `k` (not of any order `j < k`) whose (infinite) set of sums of ≤ k distinct elements has unbounded gaps | `Erdos880.counterexample` |
| (iii) | the literal enumeration form with `bᵢ = Nat.nth (· ∈ distinctSums A k) i`: bounded consecutive differences for order 2; unbounded consecutive differences for the order-`k` example, `k ≥ 3` | `Erdos880.erdos_880_enumeration` |
| (iv) | the "exactly `k` summands" reading used by the paper (`hA`, `h × A`, with `0 ∈ A` allowed): both halves | `Erdos880.erdos_880_exact` |

Faces (i) and (ii) are bundled in `Erdos880.erdos_880` in [Jsp731/Main.lean](Jsp731/Main.lean). The
definitions ([Jsp731/Defs.lean](Jsp731/Defs.lean)) are the literal ones: `IsSumOfAtMost A k n` is the
existence of a multiset of at most `k` members of `A` with sum `n`; `distinctSums A k` is the set of sums of a
finset of at most `k` members of `A`; `IsAsymptoticBasis A k` is `∀ᶠ n in atTop, IsSumOfAtMost A k n` (Erdős's
definition, no minimality clause — minimality is *proved* for the counterexample, so the stricter definition
of the paper is covered too); `HasBoundedGaps B` says some window length `C` works eventually, and
[Jsp731/Enumeration.lean](Jsp731/Enumeration.lean) proves that for infinite `B` this is equivalent to the
boundedness of `b_{i+1} − b_i`. The frozen faces are stated once more, with `sorry`, in
[Target.lean](Target.lean), which nothing imports; it serves as the challenge file for statement comparison
(its definitions are byte-identical to `Defs.lean`, and `erdos_880`/`erdos_880_enumeration` discharge its
statements verbatim).

## Proof structure

* [OrderTwo.lean](Jsp731/OrderTwo.lean): `k = 2` — every large odd integer that is a sum of ≤ 2 elements is
  a sum of ≤ 2 *distinct* elements (`a + a` is even), so every window `[n, n+1]` eventually meets the restricted
  sumset. Also the zero-padding lemmas relating "at most `k`" and "exactly `k`".
* [Construction.lean](Jsp731/Construction.lean): the paper's set for `h ≥ 3`, without the element 0: with
  `c = 3·2^{h−2} − 1`, `x₀ = h`, `x_{n+1} = c·x_n² + h·x_n`, block `n` is `[x_n, x_n + x_n²) ∪ {x_n + 2^j x_n² : j < h−1}`
  and `A = ⋃ₙ block n`; growth of the scales, ordering of the blocks, classification of the elements below `x_{n+1}`.
* [PowTwo.lean](Jsp731/PowTwo.lean): binary-expansion arithmetic — `∑_{j∈F} 2^j ≥ 2^{|F|} − 1`, the bound
  `∑_{j∈J} 2^j ≤ 2^N − 2^{N−|J|}` for `J ⊆ [0,N)`, its multiset version (repeated exponents allowed), and
  expansions with few bits.
* [Coverage.lean](Jsp731/Coverage.lean): every `m ∈ [x_n, x_{n+1})` is a sum of ≤ h elements of block `n`
  (`m = h·x_n + q·x_n² + r`, with `q` written as at most `h − 1` spikes), so `A` is an asymptotic basis of order `h`.
* [ExactOrder.lean](Jsp731/ExactOrder.lean): `2^{h−1} x_n² − 1` is not a sum of ≤ h−1 elements (the paper's
  pigeonhole on powers of two, stated for multisets so that repeated summands are handled), so `A` has no
  order `j < h`.
* [UnboundedGaps.lean](Jsp731/UnboundedGaps.lean): no sum of ≤ h *distinct* elements lies in
  `(2^{h−1} x_n² + h x_n, x_{n+1})`, an interval of length `≥ x_n² → ∞`.
* [Enumeration.lean](Jsp731/Enumeration.lean): windows ⇔ consecutive differences of `Nat.nth`.
* [Infinite.lean](Jsp731/Infinite.lean): the exact-count restricted sumset of the example is infinite.
* [Main.lean](Jsp731/Main.lean): assembly.

Deviations from the paper: the element `0` is omitted from `A` (irrelevant under "k or fewer", and it makes
every element positive); the exact-order argument is carried out for multisets (the paper's real parameter
`ρ` is replaced by the count of small summands); the unbounded-gap bound uses the subset bound on
`∑ 2^j` instead of the paper's `max(l × A_n)` computation.

No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs anywhere outside the
challenge file `Target.lean`.

## Reproduce

```bash
cd submissions/jsp-000731-cyr
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.
`Audit.lean` prints the axioms of the twelve root theorems (expected output in `verification.txt`).

## Attribution and submission status

The mathematics is due to Norbert Hegyvári, François Hennecart and Alain Plagne (2007); the problem is due to
Burr and Erdős. The author's copy of the paper (<https://www.cmls.polytechnique.fr/perso/plagne.alain/Erdos-Burr.pdf>,
SHA-256 `2012568bc0c255ec0c234cc5cbf8eb7081022987a52cef80eccb192a0f954a02`) was the only mathematical source.
The Lean formalization was written from scratch by Collin Yuanjie Ren (@CollinYuanjieRen) with Claude Code
assistance (design and review by Claude Fable 5.1, Lean implementation by Claude Opus subagents); no Lean code
from any other project was consulted or reused. An earlier, independent Lean proof of the same resolution exists
publicly (plby/lean-proofs, module `Erdos880`); no first-formalization priority or entitlement to an award is
claimed. An independent adversarial audit (statement alignment against the original question and the paper,
axiom census, numerical checks of the construction) was performed before submission; no organizer-supplied or
third-party authoritative Lean statement of this problem exists (erdosproblems.com: "Formalised statement: No";
formal-conjectures has no `ErdosProblems/880.lean`), so no official comparator run is claimed. This is a self-submission with a direct interest in the review outcome.
Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
