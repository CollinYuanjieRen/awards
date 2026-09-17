# JSP-000490 (Erdős #603): how many colours avoid a monochromatic member of a family of countably infinite sets whose pairwise intersections never have size two?

Catalog entry: [JSP-000490](../../problems/catalog-0401-0500.md#JSP-000490). Problem page:
<https://www.erdosproblems.com/603>.

## The question and its complete answer

Komjáth (Erdős 1987): let `(A_i)` be a family of countably infinite sets with `|A_i ∩ A_j| ≠ 2` for all `i ≠ j`.
Find the smallest cardinal `C` such that `⋃ A_i` can always be coloured with at most `C` colours so that no
`A_i` is monochromatic.

Answer (recorded on the problem page; proof contributors GPT-5.4 Pro, prompted by P. Chojecki): **no cardinal
`C` suffices**, so there is no smallest one. For every `C` the family of edge sets of countably infinite cliques
of a complete graph on `(2^λ)⁺` vertices, `λ = C + ℵ₀`, has all the required properties, and by the Erdős–Rado
theorem every colouring of its edges with at most `C` colours contains a monochromatic countably infinite clique.
Everything below is proved in Lean 4 / Mathlib with only the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`):

| face | statement | theorem |
|---|---|---|
| (i) | for every cardinal `C`: a family `𝒜` of countably infinite sets, pairwise never meeting in exactly two elements, covering its ground set `X`, such that every colouring `X → Y` with `#Y ≤ C` is constant on some member of `𝒜` | `Erdos603.erdos_603` |
| (ii) | for every `C`, "`C` colours always suffice" (`AlwaysColourable C`, colourings of `⋃ 𝒜` with no monochromatic member) is false | `Erdos603.not_alwaysColourable` |
| (iii) | there is no smallest sufficient cardinal | `Erdos603.no_least_cardinal` |
| (iv) | reading-gap corollaries: colourings with colour type in any universe (`erdos_603_anyUniverse`); the literal indexed-family form `(A_i)`, `i ≠ j`, `⋃ A_i = X` (`erdos_603_indexed`); the statement forces a nonempty family on an infinite ground set for every `C` (`witness_nontrivial`) | `Jsp490/Corollaries.lean` |
| (v) | Erdős–Rado, countable-homogeneous form: `ℵ₀ ≤ λ`, `#Y ≤ λ`, `#V ≥ (2^λ)⁺`, `c : V → V → Y` symmetric ⇒ a countably infinite `S ⊆ V` on which all pairs of distinct elements get one colour | `Erdos603.erdos_rado_countable` |

The definitions are the literal ones ([Jsp490/Defs.lean](Jsp490/Defs.lean), [Jsp490/Family.lean](Jsp490/Family.lean)):
"`|A ∩ B| ≠ 2`" is `(A ∩ B).encard ≠ 2` with `encard : ℕ∞` (infinite intersections allowed); "countably infinite"
is `Countable ∧ Infinite`; "coloured with at most `C` colours" is a map into a type of cardinality `≤ C`; the family
is the set of edge sets of countably infinite cliques, `cliqueEdges S = {pairs of distinct vertices inside S}` on the
vertex set `{e : Sym2 V // ¬ e.IsDiag}`. The frozen statements are restated once more, with `sorry`, in
[Target.lean](Target.lean), which nothing imports (its definition and statements are byte-identical to the proved ones).

## Proof structure

* [Recursion.lean](Jsp490/Recursion.lean): the end-homogeneous sequence of the Erdős–Rado proof, for an arbitrary
  well-ordered index type `W`: for each vertex `y`, `seq y : W → V` picks at each stage the least unused vertex
  coloured against all earlier terms exactly as `y` is. If `y` never appears, `seq y` is injective and
  end-homogeneous; if every `y` appears, `y ↦ (first appearance, colour pattern below it)` is injective.
* [Counting.lean](Jsp490/Counting.lean): with `W = (λ⁺).ord.ToType`, the codes `Σ β, (Iio β → Y)` number at most
  `λ⁺ · λ^λ = 2^λ`; pigeonhole for an infinite fibre of `W → Y`; countably infinite subsets of infinite sets.
* [ErdosRado.lean](Jsp490/ErdosRado.lean): assembly — since `#V ≥ (2^λ)⁺ > 2^λ`, some `y` never appears; an infinite
  fibre of its pattern gives the homogeneous countable set.
* [Family.lean](Jsp490/Family.lean): edge sets of cliques are countable/infinite with the clique, intersect in the
  edge set of the intersection, never have exactly two elements (two distinct edges always spawn a third edge of the
  clique they span), cover every edge (the vertex set is infinite), and a homogeneous clique has a monochromatic edge set.
* [Main.lean](Jsp490/Main.lean): the family, `erdos_603`, and the two corollaries.
* [Corollaries.lean](Jsp490/Corollaries.lean): the any-universe, indexed-family and anti-vacuity forms.

Deviation from the page: for finite `C` the page's `κ = (2^C)^+` is read with `λ = C + ℵ₀` in place of `C`
(Erdős–Rado needs an infinite exponent); the Erdős–Rado theorem itself is proved here from scratch in the weak form
needed (a countably infinite homogeneous set), following the classical end-homogeneous-sequence proof
(Erdős–Rado 1956; Jech, *Set Theory*, Thm 9.6).

No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs anywhere outside the challenge file `Target.lean`.

## Reproduce

```bash
cd submissions/jsp-000490-cyr
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.
`Audit.lean` prints the axioms of the fourteen audited theorems (expected output in `verification.txt`).

## Attribution and submission status

The problem is due to Komjáth (via Erdős 1987); the resolution recorded on erdosproblems.com/603 is credited there to
GPT-5.4 Pro prompted by Przemysław Chojecki (the catalog lists no publication); the Erdős–Rado theorem is due to Erdős
and Rado (1956). The Lean formalization was written from scratch by Collin Yuanjie Ren (@CollinYuanjieRen) with Claude
Code assistance (design and review by Claude Fable 5.1, Lean implementation by Claude Opus subagents); no Lean code from
any other project was consulted or reused. An earlier, independent Lean proof of the same resolution exists publicly
(plby/lean-proofs, module `Erdos603`); no first-formalization priority or entitlement to an award is claimed. An
independent adversarial audit (statement alignment against the problem text, axiom census, construction checks) was
performed before submission; no organizer-supplied or third-party authoritative Lean statement of this problem exists
(erdosproblems.com: "Formalised statement: No"; formal-conjectures has no `ErdosProblems/603.lean`), so no official
comparator run is claimed. This is a self-submission with a direct interest in the review outcome. Code and documentation
follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
