# JSP-000464: Turán numbers of an odd and an even cycle of adjacent lengths (Erdős #574)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000464](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000464), which is [Erdős Problem #574](https://www.erdosproblems.com/574) ([ErSi82]): is it true that, for `k ≥ 2`, `ex(n; {C_{2k−1}, C_{2k}}) = (1 + o(1)) (n/2)^{1 + 1/k}`? The answer is no. Lazebnik, Ustimenko and Woldar [LUW94b] constructed, for `k = 3` and `k = 5`, bipartite `C_{2k}`-free graphs with `((k−1)/k^{1+1/k} + o(1)) n^{1+1/k}` edges, and Füredi, Naor and Verstraëte [FNV06] gave another disproof for `k = 3`.

## Statement and proof

[Erdos574Cycles/Main.lean](Erdos574Cycles/Main.lean) proves

```lean
theorem not_claim_three : ¬ Claim 3
theorem erdos_574 : ¬ ∀ k : ℕ, 2 ≤ k → Claim k
```

where ([Erdos574Cycles/Definitions.lean](Erdos574Cycles/Definitions.lean)) `exOddEven n k` is the largest number of edges of a simple graph on `Fin n` that contains neither `C_{2k−1}` nor `C_{2k}` as a subgraph (Mathlib's `cycleGraph` and `Free`, defined exactly as Mathlib's `SimpleGraph.extremalNumber` but with two forbidden graphs), and `Claim k` is the statement `ex(n; {C_{2k−1}, C_{2k}}) / (n/2)^{1+1/k} → 1` as `n → ∞` (Mathlib's `Tendsto … atTop (𝓝 1)`), i.e. the displayed `(1 + o(1))` asymptotic. The theorem `erdos_574` is the literal negation of the question; `not_claim_three` identifies the failing case `k = 3`, and `exOddEven_lower` ([Erdos574Cycles/Count.lean](Erdos574Cycles/Count.lean)) gives the explicit bound `ex(3q³; {C₅, C₆}) ≥ 2q⁴` for every prime `q`. [Audit.lean](Audit.lean) restates these as typed `example`s.

The construction is the incidence graph `D(3, q)` of Lazebnik and Ustimenko, with its line set doubled:

1. [Definitions.lean](Erdos574Cycles/Definitions.lean): over a field `F`, a point `(p₁, p₁₁, p₁₂)` and a line `[l₁, l₁₁, l₁₂]` are incident when `l₁₁ = p₁₁ + l₁ p₁` and `l₁₂ = p₁₂ + l₁₁ p₁`. The doubled graph has the points and two copies of the lines as vertices, each point being adjacent to both copies of every line through it.
2. [Girth.lean](Erdos574Cycles/Girth.lean): `D(3, q)` has no `4`-cycle and no `6`-cycle. Two points on a common line with the same first coordinate coincide, and likewise two lines through a common point; a `4`-cycle gives `(l₁ − l₁')(p₁' − p₁) = 0`, and a `6`-cycle `p₁ l₁ p₂ l₂ p₃ l₃` gives, after eliminating the second and third coordinates, `(a₂ − a₁)(a₃ − a₂)(x₂ − x₁) = 0` for the first coordinates `aᵢ` of the points and `xᵢ` of the lines, each factor being nonzero.
3. [Free.lean](Erdos574Cycles/Free.lean): the doubled graph is bipartite (points against lines), so it contains no `C₅`; a `C₆` in it would give either a `6`-cycle of `D(3, q)` (three distinct underlying lines) or a `4`-cycle (two of the underlying lines coincide across the copies).
4. [Count.lean](Erdos574Cycles/Count.lean): the doubled graph has `3q³` vertices and `2q⁴` edges (points have degree `2q`, lines have degree `q`); transporting it to `Fin (3q³)` gives `exOddEven (3q³) 3 ≥ 2q⁴` for `F = ℤ/qℤ`, `q` prime.
5. [Main.lean](Erdos574Cycles/Main.lean): along `n = 3q³` the ratio is at least `2q⁴ / (3q³/2)^{4/3} = 2 (2/3)^{4/3} > 8/7`, and there are infinitely many primes, so the ratio does not tend to `1`.

Only the instance `k = 3` is refuted, which is exactly what the negative answer requires; the full Lazebnik–Ustimenko–Woldar bound for `k = 5`, the value of `ex(n; C₆)` and the general growth of `ex(n; {C_{2k−1}, C_{2k}})` are not formalized and not claimed. No numerical certificate, `decide` or `native_decide` is used.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness.

[Audit.lean](Audit.lean) prints the axioms of the theorems and of the main lemmas. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the package. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (https://www.hejustinsun.com/prize/rules, v1.0, retrieved 16 September 2026; the rules are not part of this repository) require in their section 6 an offline axiom audit by the designated verifiers, list in section 7 the failure to detect placeholder or unreviewed axioms as a ground for revocation, and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official process.

## Attribution and submission status

The disproof is due to Lazebnik, Ustimenko and Woldar (Properties of certain families of 2k-cycle-free graphs, J. Combin. Theory Ser. B 60 (1994), 293–298), using the graphs `D(k, q)` of Lazebnik and Ustimenko; the doubling of the line set, which yields the constant `2/3^{4/3}`, appears to be the `m × 2m` bipartite construction of Füredi, Naor and Verstraëte (On the Turán number for the hexagon, Adv. Math. 200 (2006), 476–496), as described on the problem page; their paper was not consulted. The definition of `D(3, q)` was taken from Lazebnik–Ustimenko–Woldar, A new series of dense graphs of high girth (arXiv:math/9501231), and the absence of `4`-cycles and `6`-cycles in its incidence relation, i.e. the girth-8 property, was re-proved for this package by direct algebra on the incidence equations (the original girth proof was not consulted). A Lean formalization of this problem exists in the repository plby/lean-proofs (file `src/latest/ErdosProblems/Erdos574.lean` at commit `8822f7dd`, whose header a coverage screen of that repository read to identify the problem; its proof text was not opened); that repository has no root LICENSE and its notice `src/latest/LICENSE` covers only externally sourced files, so no license grant applies to it. The present package is an independent formalization written from the published construction without consulting or reusing that proof text; it is offered as a license-clean, first-party kernel-checked proof of the catalog question and does not dispute the credit of that earlier formalization. It was prepared with Claude Code (Claude Fable 5.1 planning, Claude Opus implementation) assistance. The contribution sought is a reusable kernel-checked formalization of the exact catalog question; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed.

Proposed formalizer: `RECIPIENT-jsp-000464-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
