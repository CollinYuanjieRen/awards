# JSP-000355: Λ(2,2) = 9 — runs of two consecutive quadratic residues (Erdős #436, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000355](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000355) / [Erdős Problem #436](https://www.erdosproblems.com/436): for a prime `p` and `k, m ≥ 2`, let `r(k,m,p)` be the least `r` such that `r, r+1, …, r+m−1` are all `k`th power residues modulo `p`, and `Λ(k,m) = limsup_{p→∞} r(k,m,p)`; the problem asks whether `Λ(k,2)` and `Λ(k,3)` are finite and how large they are. The component formalized here is the value recorded on the problem page and due to D. H. Lehmer and E. Lehmer (1962): **`Λ(2,2) = 9`**. Hildebrand's finiteness of `Λ(k,2)` for all `k`, the finiteness of `Λ(k,3)` for odd `k ≥ 5` (open), the growth of these functions and the other exact values (`Λ(3,2) = 77`, …) are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos436`, [Proof/Defs.lean](Proof/Defs.lean)):

```lean
def IsQR (p r : ℕ) : Prop := (r : ZMod p) ≠ 0 ∧ IsSquare (r : ZMod p)   -- quadratic residue

def IsRunStart (p r : ℕ) : Prop := 0 < r ∧ IsQR p r ∧ IsQR p (r + 1)

noncomputable def runStart (p : ℕ) : ℕ := sInf {r : ℕ | IsRunStart p r}    -- r(2,2,p)

noncomputable def Lambda22 : ℕ := limsup runStart (atTop ⊓ 𝓟 {p : ℕ | p.Prime})   -- Λ(2,2)
```

[Proof/Main.lean](Proof/Main.lean), [Proof/Upper.lean](Proof/Upper.lean) and [Proof/Lower.lean](Proof/Lower.lean) prove:

```lean
theorem lambda22_eq_nine : Lambda22 = 9

theorem runStart_le_nine (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : runStart p ≤ 9

theorem exists_prime_gt_runStart_eq_nine (N : ℕ) : ∃ p > N, p.Prime ∧ runStart p = 9
```

The first theorem is Lehmer–Lehmer's value; the other two are its halves: every prime `p ≥ 11` has `r(2,2,p) ≤ 9` (the bound `11 ≤ p` only guarantees that `1, …, 10` are nonzero modulo `p`), and there are arbitrarily large primes with `r(2,2,p) = 9`. `Λ(2,2)` is the `limsup` of `runStart` along the filter of large primes, taken in `ℕ`; the proof establishes both an eventual upper bound and a frequent lower bound, so no junk value of `limsup` or `sInf` is used. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline (Lehmer–Lehmer 1962, as on the problem page)

Upper bound: `1, 4, 9` are residues. If `2` is a residue, `(1, 2)` is a run; otherwise, if `5` is a residue, `(4, 5)` is a run; otherwise `2` and `5` are both non-residues, so `10 = 2·5` is a residue (the quadratic character is multiplicative) and `(9, 10)` is a run. Lower bound: by Dirichlet's theorem there are arbitrarily large primes `p ≡ 43 (mod 840)`; for such `p`, `p ≡ 3 (mod 8)` makes `2` a non-residue, and quadratic reciprocity with `p ≡ 3 (mod 4)`, `p ≡ 1 (mod 3)`, `p ≡ 3 (mod 5)`, `p ≡ 1 (mod 7)` makes `3`, `5`, `7` non-residues; hence among `1, …, 10` the residues are exactly `1, 4, 6, 9, 10`, no `r ≤ 8` starts a run, and `9` does. Combining the eventual bound and the frequent equality gives `limsup = 9`.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all three theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems; the small finite-field facts use the kernel-checked `decide`. Dirichlet's theorem on primes in arithmetic progressions and quadratic reciprocity are used from Mathlib. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's; the value `Λ(2,2) = 9` and the argument are due to D. H. Lehmer and E. Lehmer, *On runs of residues*, Proc. Amer. Math. Soc. 13 (1962), 102–106 ([open access](https://doi.org/10.1090/S0002-9939-1962-0138582-6)). The later results on `Λ(k,m)` (Dunton, Bierstedt–Mills, Lehmer–Lehmer–Mills, Brillhart–Lehmer–Lehmer, Graham, Hildebrand) are not formalized. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the open questions. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000355-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
