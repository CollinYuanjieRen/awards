# JSP-000358: monochromatic sums that are perfect powers (Erdős #439)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000358](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000358), which is [Erdős Problem #439](https://www.erdosproblems.com/439): must every finite colouring of the positive integers contain two distinct integers of the same colour whose sum is a perfect square, and more generally a perfect k-th power? The answer is yes; the theorem is due to Khalfalah and Szemerédi (catalog reference [KhSz06]), who proved it for the values of any nonconstant integer polynomial that takes an even value.

## Statement and proof

[Erdos439Power/Goal.lean](Erdos439Power/Goal.lean) proves `Erdos439Power.full_resolution : FullStatement` and `Erdos439Power.integer_resolution : IntegerStatement`, where ([Erdos439Power/Statement.lean](Erdos439Power/Statement.lean))

```lean
def PowerSumStatement (k : ℕ) : Prop :=
  ∀ r : ℕ, ∀ colour : ℕ → Fin r,
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ colour x = colour y ∧ x + y = z ^ k

def FullStatement : Prop := ∀ k : ℕ, 2 ≤ k → PowerSumStatement k

def IntegerStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ r : ℕ, ∀ colour : ℤ → Fin r,
    ∃ x y z : ℤ, x ≠ y ∧ colour x = colour y ∧ x + y = z ^ k
```

A colouring with finitely many colours is a map into `Fin r`; the conclusion asks for two distinct positive integers `x ≠ y` of the same colour whose sum is literally `z ^ k`. `FullStatement` quantifies over every exponent `k ≥ 2`, so it contains the square case and every higher fixed power. `IntegerStatement` is the integer-domain wording of the problem page; it follows from the positive-integer statement by restricting a colouring of `ℤ` to `ℕ`. No hypothesis beyond the finite colouring is used. The same file also states both results with every quantifier exposed as a binder (`full_resolution_explicit`, `integer_resolution_explicit`, with the exponent written `k + 2`), and [Audit.lean](Audit.lean) restates both propositions as typed `example`s closed by the theorems.

The proof follows the circle-method strategy of Khalfalah–Szemerédi as presented by Li and Pan (arXiv:0710.5344, §2), specialised from prime weights to ordinary integer weights:

1. **Combinatorial reduction** (pinned upstream code, see below). `Erdos439.powerResolution_of_normalizedPowerFourierDecay` reduces the colouring statement for exponent `k` to an analytic predicate `HasNormalizedPowerFourierDecay k`. Write `W = k·2^{k−1}·L` and let `P_L` be the integer polynomial with `powerStep · P_L(n) + 2^k = (W·n + 2)^k` (so the k-th powers `(W·n + 2)^k` at the even base point `2` are read through `P_L`); the predicate says: for every `ε > 0` and every bound `B` there are a dilation `L` and a length `N` with `P_L(N) > B` such that the gap-weighted measure on the values `P_L(n)`, `n < N`, has every nonzero Fourier coefficient modulo `P_L(N)` of modulus at most `ε`. The arbitrarily large modulus `P_L(N) > B` is what lets the upstream reduction find the monochromatic pair.
2. **Complete rational sums** ([SmallPrimeCancellation.lean](Erdos439Power/SmallPrimeCancellation.lean), [CyclicWeyl.lean](Erdos439Power/CyclicWeyl.lean), [PrimeResidueCount.lean](Erdos439Power/PrimeResidueCount.lean), [PolynomialPrime.lean](Erdos439Power/PolynomialPrime.lean), [PolynomialPhase.lean](Erdos439Power/PolynomialPhase.lean), [CyclicPolynomialBound.lean](Erdos439Power/CyclicPolynomialBound.lean), [NormalizedPolynomial.lean](Erdos439Power/NormalizedPolynomial.lean), [CompleteRationalSums.lean](Erdos439Power/CompleteRationalSums.lean)). With `L` the factorial of a large `w`, a complete sum `q⁻¹ Σ_r e(a·P_L(r)/q)` with `gcd(a, q) = 1` vanishes when `q` shares a prime `p` with `L` (translation of the residue sum by `q/p`), and otherwise is bounded by `((k−1)/w)^{1/2^{k−1}}`: `k − 1` rounds of cyclic Weyl differencing and character orthogonality leave the probability that a single prime `p ∣ q` divides one of the `k − 1` shifts, which is at most `(k−1)/p`. The proved bound for `q > 1` needs no coprimality hypothesis; the two cases are split inside the proof.
3. **Major arcs** ([MajorArcBasics.lean](Erdos439Power/MajorArcBasics.lean), [WeightedVariation.lean](Erdos439Power/WeightedVariation.lean), [RealPhase.lean](Erdos439Power/RealPhase.lean), [PeriodicMainTerm.lean](Erdos439Power/PeriodicMainTerm.lean), [MeshQuadrature.lean](Erdos439Power/MeshQuadrature.lean), [RationalPhaseBridge.lean](Erdos439Power/RationalPhaseBridge.lean), [MajorArcCore.lean](Erdos439Power/MajorArcCore.lean), [MeshNormalization.lean](Erdos439Power/MeshNormalization.lean), [PowerGrowth.lean](Erdos439Power/PowerGrowth.lean), [MajorScalar.lean](Erdos439Power/MajorScalar.lean), [MajorArcs.lean](Erdos439Power/MajorArcs.lean)). Near a rational `a/q` the weighted exponential sum is the complete-sum mean times a weighted real-phase sum, up to a periodic error controlled by finite Abel summation and the bounded variation of the weights; at denominator one the geometric sum over the value grid `0 ≤ s < P_L(N)` vanishes exactly for a nonzero frequency, with a mesh-quadrature error. With `N = M⁴` and Dirichlet cutoff `M^{4k−1}` the normalised error is `O(M⁻³)`.
4. **Minor arcs** ([MinorScalar.lean](Erdos439Power/MinorScalar.lean), [MinorEnvelope.lean](Erdos439Power/MinorEnvelope.lean), [MinorArcs.lean](Erdos439Power/MinorArcs.lean)). When the Dirichlet denominator of the leading phase coefficient exceeds `M`, the finite Weyl inequality of the pinned upstream code bounds every prefix sum `m ≤ N`, and weighted summation by parts turns this into a bound on the Fourier coefficient that tends to zero uniformly in the frequency.
5. **Assembly** ([RationalReduction.lean](Erdos439Power/RationalReduction.lean), [FourierDecay.lean](Erdos439Power/FourierDecay.lean), [Goal.lean](Erdos439Power/Goal.lean)): for given `ε` choose `L`, then the minor-arc threshold and the major-arc threshold, then `M`; every nonzero frequency is on a major or a minor arc, which proves `HasNormalizedPowerFourierDecay k` for every `k ≥ 2` and hence both statements.

## Pinned upstream sources (not redistributed)

The combinatorial reduction, the finite Weyl inequality and the finite Fourier transform used here are taken unchanged from [plby/lean-proofs](https://github.com/plby/lean-proofs) at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` (nine files under `src/latest/ErdosProblems/`: `Erdos439/PowerSums.lean`, `Erdos438/Fourier.lean`, `Erdos387/{FiniteWeylInequality,InverseWeylDifferencing,KloostermanOrthogonality,AdditiveCharacterOrthogonality}.lean`, `Erdos443.lean`, `Erdos444/{Basic,Moment}.lean`). The two `Erdos444` files carry Apache License 2.0 headers (copyright The Formal Conjectures Authors); the other seven files and the repository carry no license notice, so none of their text is copied into this submission. [fetch_vendor.py](fetch_vendor.py) downloads each file, verifies its SHA-256 against the pinned value, and rewrites only its `import` lines into `Erdos439Power/Vendor/`. The upstream file `PowerSums.lean` itself proves the reduction from `HasNormalizedPowerFourierDecay` and states that predicate; it contains no `sorry` and no axiom, and the axiom audit below covers it.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
python3 fetch_vendor.py
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness.

[Audit.lean](Audit.lean) prints the axioms of both roots and of the main components. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the dependency cone. [verification.txt](verification.txt) records the local fetch, build and audit of this exported package. The published prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit by the designated verifiers and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The theorem is due to Khalfalah and Szemerédi (Combin. Probab. Comput. 15 (2006), 213–227); the proof strategy formalized here follows the exposition of Li and Pan (arXiv:0710.5344) with the prime-weighted inputs replaced by classical polynomial Weyl estimates. The combinatorial reduction and the finite Weyl inequality are the pinned upstream Lean code credited above; where those files name their authors the credit is theirs (`Erdos443.lean` credits Aristotle and Boris Alexeev, the `Erdos444` files the Formal Conjectures Authors; the remaining files carry no author header). The complete-sum, major-arc and minor-arc modules and the assembly were prepared with Codex (GPT) and Claude Code (Claude Fable 5.1 and Claude Opus) assistance. The contribution sought is formalization of the exact problem statement; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed.

Proposed formalizer: `RECIPIENT-jsp-000358-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT); the pinned upstream files are fetched at build time under their own terms and are not part of this contribution.
