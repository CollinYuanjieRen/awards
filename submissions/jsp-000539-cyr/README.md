# JSP-000539 (Erdős #664): no uniformly bounded transversal for linear set systems of size `> c√n`

Catalog entry: [JSP-000539](../../problems/catalog-0501-0600.md#JSP-000539). Problem page:
<https://www.erdosproblems.com/664>.

## The question and its complete answer

Erdős [Er81, Er97f]: let `c < 1` be a constant and let `A_1, …, A_m ⊆ {1, …, n}` satisfy `|A_i| > c√n` for all `i` and
`|A_i ∩ A_j| ≤ 1` for all `i ≠ j`. Must there exist a set `B` such that `B ∩ A_i ≠ ∅` and `|B ∩ A_i| ≪_c 1` for all `i`?

Resolution (N. Alon, *Blocking partial designs and block-compatible sequences*, Theorem 2.1): **no** — random halves of the
lines of a projective plane give `|A_i| > 0.4√n`, `|A_i ∩ A_j| ≤ 1`, and every `B` meeting all `A_i` meets some `A_i` in
`≥ 0.1 log n` points. Everything below is proved in Lean 4 / Mathlib with only the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`):

| face | statement | theorem |
|---|---|---|
| (i) | for every `c < 1` and every `K`, a family with `|A_i| > c√n`, `|A_i ∩ A_j| ≤ 1` such that every `B` meeting all `A_i` has `|B ∩ A_i| > K` for some `i` | `Erdos664.counterexample` |
| (ii) | for every `c < 1`, no constant `K` is a uniform transversal bound | `Erdos664.erdos_664` |
| (iii) | the instance `c = 2/5` in the form of the public comparator challenge | `Erdos664.not_erdos_664` |

The definitions ([Jsp539/Defs.lean](Jsp539/Defs.lean)) are those of the public comparator challenge for this problem
(plby/lean-proofs, `ComparatorChallenges/ErdosProblems/Erdos664.lean`, identical up to line wrapping): `LinearFamily A`
(pairwise intersections of size `≤ 1`), `HitsAll A B` (`B` meets every member), and `HasUniformTransversalBound c K`
(every family `A : Fin m → Finset (Fin n)` with `c·√n < |A_i|` and pairwise intersections `≤ 1` admits `B` with
`0 < |B ∩ A_i| ≤ K` for all `i`). Face (ii) refutes the question for *every* constant `c < 1`, which is stronger than
the page's `c = 2/5`. The frozen statement is restated once more, with `sorry`, in [Target.lean](Target.lean), which
nothing imports.

## Proof structure (an elementary realization of Alon's argument, no measure theory)

* [Plane.lean](Jsp539/Plane.lean): the affine plane over `ZMod p` (`p` prime): points `(x, y)`, the `p²` non-vertical lines
  `y = ax + b`, each with `p` points; two distinct lines share at most one point; each point lies on exactly `p` lines;
  hence `∑_ℓ |B ∩ L_ℓ| = |B|·p`.
* [Sample.lean](Jsp539/Sample.lean): the sample space `Ω = Line → ZMod p → Fin M` (uniform counting; a point of a line is
  *kept* iff its value is nonzero, i.e. with probability `1 − 1/M`), the product factorisation `∑_ω ∏_ℓ w_ℓ(ω ℓ) = ∏_ℓ ∑_g w_ℓ(g)`,
  the exponential tail bound for the number of kept coordinates in any coordinate set `S`
  (`#{ω : X_S(ω) ≤ K} ≤ |Ω|·2^{|S|}·M^{K}/M^{|S|}`), and the block bound
  `#{ω : ∀ ℓ, ∃ x ∈ T_ℓ, ω ℓ x ≠ 0} ≤ |Ω|·(1 − M^{−t})^{#light lines}`.
* [Events.lean](Jsp539/Events.lean): the three bad events — a line keeps too few points, a point has too small degree, a
  set `B` of size `≤ 2p(K+1)` meets every kept set — with their counting bounds, and the existence of a sample avoiding all
  three once the sum of the bounds is `< 1`.
* [Asymptotics.lean](Jsp539/Asymptotics.lean): the choice of `M` (`M ≥ 5`, `M^{1−c} > 2`) and the real-analysis fact that the
  sum of the three bounds is `< 1` for all large `p` (geometric decay beats `p²`; `(p²+1)^{2p(K+1)}(1 − M^{−t})^{p²/2} → 0`).
* [Main.lean](Jsp539/Main.lean): for a prime `p` large enough, the kept sets form the required family on `n = m = p²`
  (`√n = p`); a set `B` meeting all kept sets has `|B| > 2p(K+1)`, so by double counting with the degree bound some kept set
  contains more than `K` points of `B`.

No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs anywhere outside the statement-only file `Target.lean`.

## Reproduce

```bash
cd submissions/jsp-000539-cyr
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.
`Audit.lean` prints the axioms of the audited theorems (expected output in `verification.txt`).

## Attribution and submission status

The problem is due to Erdős [Er81]; the resolution and the random-half-lines construction are due to Noga Alon (Theorem 2.1 of
the cited note; the projective plane and sampling probability `1/2` are replaced here by the affine plane over a prime field and
sampling probability `1 − 1/M`, which yields the negative answer for every `c < 1`). The Lean formalization was written from
scratch by Collin Yuanjie Ren (@CollinYuanjieRen) with Claude Code assistance (design and review by Claude Fable 5.1, Lean
implementation by Claude Opus subagents); no Lean code from any other project was consulted or reused, apart from the three
definitions of the public comparator challenge, which are adopted verbatim so that the challenge statement is discharged
literally. An earlier, independent Lean proof of the same resolution exists publicly (plby/lean-proofs, module `Erdos664`,
by Codex / GPT-5.6 Sol, August 2026); no first-formalization priority or entitlement to an award is claimed. An independent
adversarial audit (statement alignment against the problem text and the note, axiom census) and an independent
original-target scope review were performed before submission; no organizer-supplied authoritative Lean statement of this
problem exists (erdosproblems.com: "Formalised statement: No"; formal-conjectures has no `ErdosProblems/664.lean`), so no
official comparator run is claimed. Erdős's 1981 block-design variant (pairwise balanced designs) remains open and is not
claimed. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the
repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
