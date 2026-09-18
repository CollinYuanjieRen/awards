# JSP-000799 (Erdős #960): many ordinary lines do not force an all-ordinary subset — `f_{r,k}(n) ≥ n²/12 − 10n/3`

Catalog entry: [JSP-000799](../../problems/catalog-0701-0800.md#JSP-000799). Problem page:
<https://www.erdosproblems.com/960>.

## The question and its complete answer

Erdős [Er84, p. 102]: let `r, k ≥ 2` be fixed and let `A ⊂ ℝ²` be a set of `n` points with no `k` on a line.
Determine the threshold `f_{r,k}(n)` such that whenever `A` determines at least `f_{r,k}(n)` ordinary lines (lines
containing exactly two points of `A`) there is an `r`-point subset of `A` all of whose joining lines are ordinary.
Is `f_{r,k}(n) = o(n²)`, or even `≪ n`?

Resolution (Alexeev, Putterman, Sawhney, Sellke, Valiant with an internal OpenAI model, *Short proofs in
combinatorics, probability and number theory II*, arXiv:2604.06609, Theorem 2.1): **no** — for every `r ≥ 3`, `k ≥ 4`
and `n ≥ 72`, `f_{r,k}(n) ≥ n²/12 − 10n/3`, so the threshold is neither `o(n²)` nor `O(n)`. (For `k ≤ 3` or `r = 2`
the threshold is trivially `O(1)`.) Everything below is proved in Lean 4 / Mathlib with only the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`):

| face | statement | theorem |
|---|---|---|
| (i) | `r ≥ 3`, `k ≥ 4`, `n ≥ 72`: `n²/12 − 10n/3 ≤ f_{r,k}(n)` | `Erdos960.f_ge` |
| (ii) | `r ≥ 3`, `k ≥ 4`: `f_{r,k}` is not `o(n²)` | `Erdos960.f_not_isLittleO` |
| (iii) | `r ≥ 3`, `k ≥ 4`: `f_{r,k}` is not `O(n)` | `Erdos960.f_not_isBigO_linear` |
| (iv) | degenerate ranges: `f_{r,k}(n) = 0` for `k ≤ 2` (`n ≥ 2`) and for `k = 3` (`n ≥ r`); `f_{2,k}(n) ≤ 1` | `Erdos960.f_eq_zero_of_k_le_two`, `f_eq_zero_of_k_eq_three`, `f_two_le_one` |

Faces (i)–(iii) are bundled in `Erdos960.erdos_960` in [Jsp799/Main.lean](Jsp799/Main.lean). The definitions
([Jsp799/Defs.lean](Jsp799/Defs.lean)) are the literal ones on `ℝ × ℝ` with Mathlib's affine `Collinear ℝ`: an
ordinary pair is a pair of distinct points of `A` with no third point of `A` on their line; `ordCount A` counts the
unordered ordinary pairs (= ordinary lines); `NoKCollinear A k`; `HasOrdinaryClique A r`; `Forces r k n t`; and
`f r k n` is the least forcing threshold (`sInf`, over a nonempty set). The frozen statement is restated once more,
with `sorry`, in [Target.lean](Target.lean), which nothing imports (its definitions and statement are byte-identical
to the proved ones).

## Proof structure (an elementary realization of the paper's construction)

The paper takes a cyclic subgroup of order `7m` of a real elliptic curve and keeps the six nonzero cosets modulo 7;
here the same combinatorics is realized on the real nodal cubic `y² = x²(x − 1)`, whose smooth points are
parametrized by `t ↦ (t² + 1, t(t² + 1))` and satisfy the classical collinearity law: three distinct parameters
`a, b, c` are collinear iff `ab + bc + ca = 1`. With `t = cot(iπ/M)` this becomes `M ∣ i + j + k`.

* [Cubic.lean](Jsp799/Cubic.lean): the parametrization, `Collinear ℝ {p, q, r} ↔ det = 0`, the factorization
  `det = (b−a)(c−b)(c−a)(ab+bc+ca−1)`, no four curve points collinear.
* [Trig.lean](Jsp799/Trig.lean): `sin(a+b+c) = sin a sin b sin c (cot a cot b + cot b cot c + cot c cot a − 1)`,
  injectivity of `cot` on the angles `iπ/M`, and the criterion `… = 1 ↔ M ∣ i + j + k`.
* [Indices.lean](Jsp799/Indices.lean): the index set (`0 < i < 7m`, `7 ∤ i`, plus `s ≤ 5` extra multiples of 7),
  `|Idx| = 6m + s`; index-level ordinary pairs; no three pairwise ordinary indices (residues `{1,2,4}` versus
  `{3,5,6}` mod 7 make the ordinary graph bipartite; extra points create no cross edges and no triangle among
  themselves); at least `2(3m² − 3ms)` ordered ordinary pairs.
* [Assembly.lean](Jsp799/Assembly.lean): the point configuration, the transfer between point-level and
  index-level ordinary pairs, `|A| = n`, no four collinear, no all-ordinary triple, `ordCount ≥ 3m² − 3ms`.
* [Degenerate.lean](Jsp799/Degenerate.lean): the `k ≤ 3` and `r = 2` ranges.
* [Main.lean](Jsp799/Main.lean): the threshold bound and the asymptotic disproofs.

No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs anywhere outside the challenge file `Target.lean`.

## Reproduce

```bash
cd submissions/jsp-000799-cyr
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.
`Audit.lean` prints the axioms of the eleven audited theorems (expected output in `verification.txt`).

## Attribution and submission status

The problem is due to Erdős [Er84]; the resolution and the construction are due to Alexeev, Putterman, Sawhney,
Sellke and Valiant with an internal OpenAI model (arXiv:2604.06609, Section 2; the paper's elliptic-curve cyclic
subgroup is replaced here by the cotangent parametrization of a nodal cubic, a standard elementary realization of
the same group structure). The Lean formalization was written from scratch by Collin Yuanjie Ren (@CollinYuanjieRen)
with Claude Code assistance (design and review by Claude Fable 5.1, Lean implementation by Claude Opus subagents);
no Lean code from any other project was consulted or reused. An earlier, independent Lean proof of the same resolution
exists publicly (plby/lean-proofs, module `Erdos960`); no first-formalization priority or entitlement to an award is
claimed. An independent adversarial audit (statement alignment against the problem text and the paper, axiom census,
numerical checks of the construction) was performed before submission; no organizer-supplied or third-party
authoritative Lean statement of this problem exists (erdosproblems.com: "Formalised statement: No"; formal-conjectures
has no `ErdosProblems/960.lean`), so no official comparator run is claimed. This is a self-submission with a direct
interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and
[content license](../../LICENSE-CONTENT).
