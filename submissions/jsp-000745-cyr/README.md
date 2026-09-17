# JSP-000745: finite colourings avoiding lacunary differences (Erdős #894)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000745](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000745), which is [Erdős Problem #894](https://www.erdosproblems.com/894): if `n₁ < n₂ < ⋯` is a lacunary sequence of positive integers (there is `ε > 0` with `n_{k+1} ≥ (1 + ε) n_k` for all `k`), must there be a finite colouring of the positive integers with no monochromatic solution to `a − b = n_k`? The answer is yes: Katznelson (Combinatorica 21 (2001), catalog reference [Ka01]) observed that it follows from a Diophantine-approximation result on lacunary sequences, and Peres and Schlag (Bull. Lond. Math. Soc. 42 (2010), catalog reference [PeSc10]) gave the best known bound on the number of colours.

## Statement and proof

[Erdos894Colouring/Main.lean](Erdos894Colouring/Main.lean) proves

```lean
theorem erdos_894 (n : ℕ → ℕ) (hn : IsLacunary n) : HasAvoidingColouring n
theorem erdos_894_nat (n : ℕ → ℕ) (hn : IsLacunary n) :
    ∃ (r : ℕ) (c : ℕ → Fin r), ∀ a b : ℕ, c a = c b → ∀ k, a ≠ b + n k
```

with ([Erdos894Colouring/Definitions.lean](Erdos894Colouring/Definitions.lean))

```lean
def IsLacunary (n : ℕ → ℕ) : Prop :=
  (∀ k, 0 < n k) ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ k, (1 + ε) * (n k : ℝ) ≤ n (k + 1)
def HasAvoidingColouring (n : ℕ → ℕ) : Prop :=
  ∃ (r : ℕ) (c : ℤ → Fin r), ∀ a b : ℤ, c a = c b → ∀ k, a - b ≠ (n k : ℤ)
```

The same file also states the closed form `erdos_894_closed : ¬ ∃ n, IsLacunary n ∧ ¬ HasAvoidingColouring n`. `IsLacunary` is the problem's own hypothesis: the terms are positive and grow by a fixed factor `1 + ε > 1`. `HasAvoidingColouring` asks for a colouring of all the integers with finitely many colours such that no two integers of the same colour differ by a term of the sequence; this is the Cayley-graph formulation mentioned on the problem page and implies the colouring of the positive integers asked for there, which is `erdos_894_nat`. No hypothesis beyond lacunarity is used, and the number of colours is not bounded by the statement (the proof produces `8^r` colours where `(1 + ε)^r ≥ 4`). [Audit.lean](Audit.lean) restates both results with the two definitions unfolded.

The proof is the classical rotation argument (recalled at the end of Section 1 of Peres–Schlag, equation (1.3), where it is credited to Katznelson, to Weiss, and to Ruzsa, Tuza and Voigt); it uses no Diophantine input:

1. [Split.lean](Erdos894Colouring/Split.lean): by Bernoulli's inequality there is `r ≥ 1` with `(1 + ε)^r ≥ 4`, so each of the `r` subsequences `i ↦ n (j + r i)`, `j < r`, grows by a factor at least `4`.
2. [Nested.lean](Erdos894Colouring/Nested.lean): a sequence `m` with `4 m_i ≤ m_{i+1}` admits a real `θ` with every `θ m_i` having fractional part in `[1/4, 3/4]`, obtained as the supremum of the left endpoints of nested intervals `[(t_i + 1/4)/m_i, (t_i + 3/4)/m_i]` with integer `t_i`.
3. [Colouring.lean](Erdos894Colouring/Colouring.lean): with rotations `θ_j` for the `r` subsequences, colour an integer `a` by the vector of cells `⌊8 · frac(θ_j a)⌋`, `j < r`. Two integers with the same colour have fractional parts `frac(θ_j a)`, `frac(θ_j b)` within `1/8` for every `j`, whereas `a − b = n_k` with `k ≡ j (mod r)` forces them to be at distance at least `1/4`.

No numerical certificate or decision procedure is used.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness.

[Audit.lean](Audit.lean) prints the axioms of the roots (including the closed form) and of the three lemmas. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the package. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (https://www.hejustinsun.com/prize/rules, v1.0, retrieved 16 September 2026; the rules are not part of this repository) require in their section 6 an offline axiom audit by the designated verifiers, list in section 7 the failure to detect placeholder or unreviewed axioms as a ground for revocation, and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The theorem is Katznelson's (2001); the elementary rotation argument formalized here is the one recalled by Peres and Schlag (2010), who attribute it to Katznelson, Weiss, and Ruzsa–Tuza–Voigt, and whose own contribution is the sharper bound on the number of colours (not formalized here). A Lean formalization of this problem exists in the repository plby/lean-proofs (file `ErdosProblems/Erdos894.lean`, formal authors Codex and GPT-5.6 Sol); that file carries no license grant, and the present package is an independent formalization written from the published mathematical argument without reusing or consulting its proof text. It was prepared with Claude Code (Claude Fable 5.1 planning, Claude Opus implementation) assistance. The contribution sought is a reusable kernel-checked formalization of the exact catalog question; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed.

Proposed formalizer: `RECIPIENT-jsp-000745-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
