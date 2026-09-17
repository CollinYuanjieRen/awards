# JSP-000183: an infinite small-step walk in ℤ³ with no three collinear points (Erdős #193)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000183](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000183), which is [Erdős Problem #193](https://www.erdosproblems.com/193) (Gerver–Ramsey, catalog reference [GeRa79]): must an infinite walk in three-dimensional space whose steps come from a finite set of vectors visit three collinear points? The answer is no: Cambie and Kalviainen (arXiv:2609.01766, 2026, catalog reference [CaKa26]) construct an infinite walk in ℤ³ with steps from a fixed set of sixteen vectors and no three collinear vertices.

## Statement and proof

[Erdos193Walk/Main.lean](Erdos193Walk/Main.lean) proves

```lean
theorem erdos_193 :
    False ↔ ∀ S : Set (Fin 3 → ℤ), S.Finite →
      ∀ a : ℕ → Fin 3 → ℤ, IsSWalk S a → (range a).Infinite →
      HasCollinearTriple ℚ (range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ))
```

where `IsSWalk S a` means that every difference `a (n+1) - a n` lies in `S` and `HasCollinearTriple ℚ A` means that `A` contains three distinct points that are collinear over `ℚ`. These two definitions and the right-hand side of the equivalence are copied verbatim from the statement of the problem in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/193.lean) (file `ErdosProblems/193.lean`, `theorem erdos_193 : answer(sorry) ↔ …`); the only change is that the placeholder `answer(sorry)` is replaced by the answer `False`. The same file proves the positive form `exists_walk_no_collinear_triple`: there are a finite `S ⊆ ℤ³` and an infinite `S`-walk with no three collinear points. [Audit.lean](Audit.lean) restates both as typed `example`s, the second with every auxiliary definition unfolded.

The walk is the one of Cambie and Kalviainen, and the proof follows their two-page argument.

1. [Definitions.lean](Erdos193Walk/Definitions.lean): with `α n` the binary digit sum of `n` modulo 4, `u n = i ^ α n` is a Gaussian unit and `z n = Σ_{r < n} u r` a nearest-neighbour walk in the Gaussian integers; the four corners `c k ∈ {0, i, −1 + i, −1}` of a unit square tag the four states; `w n = 2 z n + c (α n)`, `h n = 4 n + α n`, and the walk is `P n = (Re w n, Im w n, h n)`. The step set is the image of the sixteen tag pairs `(j, k) ↦ (2 i^j + c k − c j, 4 + k − j)`; only its finiteness is used (the package does not prove that exactly sixteen steps occur or the bound `{−2,…,2}² × {1,…,7}` of the paper).
2. [Walk.lean](Erdos193Walk/Walk.lean): the binary recursions `u (2n+ε) = i^ε u n`, `z (2n+ε) = (1+i) z n + ε u n`, and identity (2) of the paper: if `m < n` and `u m = u n`, then `|z n − z m|²` is nonzero with 2-adic valuation `ν₂(n − m)`.
3. [Chords.lean](Erdos193Walk/Chords.lean): identity (4): for `m < n`, `ν₂ |w n − w m|² = ν₂ (h n − h m)`, by the three cases on the tags; every step `P (n+1) − P n` lies in the step set; `h` is strictly increasing, so the walk is injective (the infinitude of its range is then drawn in `Main.lean`).
4. [Collinear.lean](Erdos193Walk/Collinear.lean): if `P a, P b, P d` with `a < b < d` were collinear over ℚ, the chords `X = w b − w a`, `Y = w d − w b` and heights `A = h b − h a`, `B = h d − h b` would satisfy `(A+B)² |X|² = A² |X+Y|²` and `B² |X|² = A² |Y|²`; identity (4) turns this into `ν₂ A = ν₂ B = ν₂ (A+B)`, which is impossible. Hence no three points of the walk are collinear.

No numerical certificate or external computation is used; apart from kernel `decide` on a single Gaussian-integer norm and small case splits on the four tags, the argument is the 2-adic valuation bookkeeping of the paper.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness.

[Audit.lean](Audit.lean) prints the axioms of both roots and of the main lemmas. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the package. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (https://www.hejustinsun.com/prize/rules, v1.0, retrieved 16 September 2026; the rules are not part of this repository) require in their section 6 an offline axiom audit by the designated verifiers, list in section 7 the failure to detect placeholder or unreviewed axioms as a ground for revocation, and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The construction and proof are due to Stijn Cambie and Erik Kalviainen (arXiv:2609.01766, September 2026), who also published their own Lean formalization at github.com/ekalvi/erdos-193 alongside the paper; the present package is an independent formalization written from the paper (no code from that repository was consulted or reused) and is not the first formalization of the result. The statement is taken from google-deepmind/formal-conjectures (Apache License 2.0). This package was prepared with Claude Code (Claude Fable 5.1 planning, Claude Opus implementation) assistance. The contribution sought is a kernel-checked formalization of the exact catalog question in the official statement shape; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed.

Proposed formalizer: `RECIPIENT-jsp-000183-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
