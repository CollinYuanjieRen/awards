# Erdős 318: reciprocal squares excluding one

This package proves that every nontrivial partition of the natural square denominators greater than one admits equal nonempty finite reciprocal sums in its two colors. It also proves the canonical signed formulation `Erdos318.erdos_318.parts.ii`: every nonconstant assignment of signs to those reciprocals has a nonempty finite zero-sum subset.

The solution has no additional hypotheses, custom axioms, admitted proofs or native-evaluation shortcuts. The exact transitive foundational axiom set of both endpoints is `propext`, `Classical.choice`, `Quot.sound`.

## Statement and attribution

- Problem: [Erdős 318](https://www.erdosproblems.com/318), catalog JSP-000264.
- Mathematical source: Daniel Larsen, [Erdős problem 318](https://github.com/Larsen-Daniel/Erdos-318/tree/39139e2b16b65b478da842365196fa3cc68539dd), the square-specific weighted Fourier construction. The Lean implementation makes the prefix, prime subset products, divisibility and finite frequency estimates explicit. This is a formalization of an existing mathematical result, not a claim of a new mathematical discovery.
- Canonical statement: [Formal Conjectures 318](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/318.lean). The `P₁` definition is copied verbatim with its Apache 2.0 copyright notice. `answer(True)` elaborates to `True` with metadata, removed by the pinned comparator exporter.
- Formalization prepared with OpenAI Codex.

The arithmetic-progression and positive-density-counterexample parts have prior formalizations by [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos318.lean). They have now also been reproduced, adapted to the canonical predicate names, and accepted by an actual matching-version comparator with Lean kernel replay. See [full catalog coverage](FULL_SCOPE.md) and the separate [reuse reproduction bundle](reuse/README.md). They remain credited prior work; this package supplies the formerly missing squares-excluding-one result. The negative statement for squares including one is a different proposition.

## Reproduction

Lean: `leanprover/lean4:v4.34.0-rc1`. Mathlib: `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. The included Lake manifest pins all dependencies.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The library root imports the canonical endpoint and its full local proof dependencies. `source-hashes.json` records the submitted Lean source bytes. The source uses standard Mathlib definitions of squareness, finite sums, real numbers and rational numbers.

## Verification status

The development workspace compiled the canonical endpoint successfully (8801 build jobs), and printed exactly the three standard foundational axioms above for both endpoints. Independent statement and proof-source audits checked the original premises, domain excluding 0 and 1, and the conversion between rational reciprocal equality and real signed zero sum.

The actual pinned native comparator passes declaration/dependency comparison, the three-axiom check and Lean kernel replay. A fresh checker compiled the complete submitted source set; its aggregate build and Audit.lean also pass. See [comparison evidence](verification/README.md) for logs, immutable pins, reference extraction and reproducible commands. This is explicitly an unsandboxed macOS development run, against a reviewed source port of Formal Conjectures from Lean 4.33.1 to the pinned 4.34.0-rc1 environment. Production Linux sandboxing, nanoda and prize acceptance are not claimed. Public prize rules require axiom and independent-checker review but do not explicitly publish a named allowlist for these three axioms; the standard example configuration of Lean's comparator permits them. Formal Conjectures is the statement collection used for this comparison; it is not represented as a prize-organizer-mandated checker or an unported original environment. Repository metadata CI does not certify this proof.

New Lean proof sources are licensed under Apache 2.0; retained third-party notices govern copied definitions. See [LICENSE](LICENSE).
