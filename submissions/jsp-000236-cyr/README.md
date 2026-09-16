# JSP-000236: a Lucas sequence of composite numbers with no common divisor (Erdős #276, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000236](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000236) / [Erdős Problem #276](https://www.erdosproblems.com/276): is there an infinite Lucas sequence `a₀, a₁, …` with `a_{n+2} = a_{n+1} + a_n` such that all `a_k` are composite, and yet no integer has a common factor with every term? The component formalized here is the existence result recorded on the problem page, **Graham's theorem (1964): such a sequence exists**, certified with the smallest known initial pair, due to Vsemirnov (2004), `a₀ = 106276436867`, `a₁ = 35256392432`, and a covering system of 17 primes. The page's remaining question, whether every composite Lucas sequence must come from an underlying system of covering congruences (Ismailescu–Son's conjectural example), is **not** claimed. This is the known existence half and is labelled as such.

## Statements

All definitions are our own (namespace `Erdos276`, [Proof/Main.lean](Proof/Main.lean)):

```lean
def IsLucasSequence (a : ℕ → ℕ) : Prop := ∀ n, a (n + 2) = a (n + 1) + a n

def lucasPair (x y : ℕ) : ℕ → ℕ × ℕ
  | 0 => (x, y)
  | n + 1 => ((lucasPair x y n).2, (lucasPair x y n).1 + (lucasPair x y n).2)

def lucas (x y : ℕ) (n : ℕ) : ℕ := (lucasPair x y n).1

def vsemirnov : ℕ → ℕ := lucas 106276436867 35256392432

theorem exists_composite_lucasSequence :
    ∃ a : ℕ → ℕ, IsLucasSequence a ∧ (∀ k, 1 < a k ∧ ¬ (a k).Prime) ∧
      (∀ d, 2 ≤ d → ∃ k, ¬ d ∣ a k)

theorem vsemirnov_exists_proper_factor : ∀ k, ∃ p, 1 < p ∧ p < vsemirnov k ∧ p ∣ vsemirnov k

theorem vsemirnov_coprime_succ : ∀ k, Nat.Coprime (vsemirnov k) (vsemirnov (k + 1))
```

`lucas x y` is the Lucas sequence with initial terms `x, y`, computed by iterating the pair `(a n, a (n+1))` so that the kernel evaluates it in linear time; `vsemirnov` is the witness sequence. The first theorem is Graham's theorem in the page's wording: composite is rendered as `1 < a k ∧ ¬ (a k).Prime`, and "no integer has a common factor with every term" as "no `d ≥ 2` divides every term". The second theorem exhibits an explicit proper factor of every term of the witness, which is how compositeness is proved; the third is the stronger form of the coprimality clause (consecutive terms are coprime, as in Vsemirnov's Theorem 1). There are no hypotheses, no custom axioms and no unproved inputs.

Note on the third-party statement in the formal-conjectures repository (file `ErdosProblems/276.lean`, not used here): its coprimality clause `∀ n > 1, ∃ k, Nat.gcd n (a k) = 1` is false for every covering-based sequence (take `n` to be the product of the covering primes), so it cannot be what the problem intends; our statement follows the page's wording instead.

## Proof outline

Graham's method as refined by Knuth and Vsemirnov, with the certificate recomputed locally. Let `a = vsemirnov`. (1) Every term is at least `min (a 0) (a 1) = 35256392432` (two-step induction). (2) For any Lucas sequence and any `p`, if `(a per, a (per+1)) ≡ (a 0, a 1) (mod p)` then `a (n + per) ≡ a n (mod p)` for all `n`, so `a n mod p` depends only on `n mod per`. (3) For each of the 17 primes `p ∈ {2, 3, 5, 7, 11, 17, 19, 23, 31, 41, 47, 61, 107, 181, 541, 1103, 2521}` the period `per_p` (all dividing `1440`) and the residues `r < per_p` with `p ∣ a r` are listed in the certificate table of `Proof/Main.lean` (34 residue classes); the periodicity conditions, the divisibilities `p ∣ a r` and the covering of every residue class modulo `1440` are checked by kernel `decide` (no `native_decide`). Hence every `a n` is divisible by one of the 17 primes, each smaller than `35256392432 ≤ a n`, so `a n` is composite. (4) `gcd (a (n+1)) (a (n+2)) = gcd (a (n+1)) (a n)`, so `gcd (a n) (a (n+1)) = gcd (a 0) (a 1) = 1` for all `n`; in particular no `d ≥ 2` divides both `a 0` and `a 1`.

The pair printed on the problem page (`1786772701928802632268715130455793`, `1059683225053915111058165141686995`) is not used: in our computation it admits no covering by primes below `6000` with periods dividing `34560`, whereas Vsemirnov's pair (and Graham's and Knuth's pairs as printed by Knuth) do; Vsemirnov's pair has the smallest certificate.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut (the finite certificate is checked by the kernel's `decide`), and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is due to Erdős and Graham (ErGr80, p. 27). The existence theorem is due to R. L. Graham, *A Fibonacci-like sequence of composite numbers*, Math. Mag. 37 (1964), 322–324; the method was refined by D. E. Knuth, *A Fibonacci-like sequence of composite numbers*, Math. Mag. 63 (1990), 21–25, and the initial pair used here is from M. Vsemirnov, *A new Fibonacci-like sequence of composite numbers*, J. Integer Seq. 7 (2004), Article 04.3.7 (Theorem 1). The covering certificate was recomputed independently for this package. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the open question about covering systems. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000236-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
