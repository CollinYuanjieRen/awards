# JSP-000495: the Erdős–Graham odd-cycle-free colouring of K_{2^n} and the trivial bound on f(n) (Erdős #609, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000495](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000495) / [Erdős Problem #609](https://www.erdosproblems.com/609): let `f(n)` be the least `m` such that every `n`-colouring of the edges of `K_{2^n+1}` contains a monochromatic odd cycle of length at most `m`; estimate `f(n)`. The component formalized here consists of the construction recorded on the problem page, **the edges of `K_{2^n}` can be `n`-coloured to avoid odd cycles of any length** (Erdős–Graham 1975), and the pigeonhole converse, **every `n`-colouring of `K_{2^n+1}` has a monochromatic odd cycle**, from which `f(n)` is a genuine minimum and satisfies the page's trivial bound `f(n) ≤ 2^n + 1` (and `f(n) ≥ 3` for `n ≥ 1`). The growth of `f(n)` (Chung's question, the Day–Johnson lower bound, the Girão–Hunter and Janzer–Yip upper bounds) and the page's question are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos609`, [Proof/Defs609.lean](Proof/Defs609.lean)). An edge colouring of the complete graph on `V` with `n` colours is a function `c : Sym2 V → Fin n`:

```lean
def colourClass {V : Type*} {n : ℕ} (c : Sym2 V → Fin n) (i : Fin n) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => c s(u, v) = i)

def HasOddCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ Odd p.length

def HasOddCycleLe {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ Odd p.length ∧ p.length ≤ m

noncomputable def oddCycleThreshold (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ c : Sym2 (Fin (2 ^ n + 1)) → Fin n, ∃ i, HasOddCycleLe (colourClass c i) m}
```

[Proof/Construction.lean](Proof/Construction.lean) and [Proof/Main.lean](Proof/Main.lean) prove:

```lean
theorem exists_colouring_no_oddCycle (n : ℕ) :
    ∃ c : Sym2 (Fin (2 ^ (n + 1))) → Fin (n + 1), ∀ i, ¬ HasOddCycle (colourClass c i)

theorem exists_mono_oddCycle (n : ℕ) (c : Sym2 (Fin (2 ^ n + 1)) → Fin n) :
    ∃ i, HasOddCycle (colourClass c i)

theorem oddCycleThreshold_le (n : ℕ) : oddCycleThreshold n ≤ 2 ^ n + 1

theorem oddCycleThreshold_mem (n : ℕ) :
    ∀ c : Sym2 (Fin (2 ^ n + 1)) → Fin n, ∃ i, HasOddCycleLe (colourClass c i) (oddCycleThreshold n)
```

`oddCycleThreshold n` is the page's `f(n)`. The first theorem is the Erdős–Graham construction, stated with `n + 1` colours on `2^{n+1}` vertices so that it holds for every `n` (with no colours there is no edge colouring at all); the second is the pigeonhole converse; the third the page's trivial bound; the fourth says the infimum defining `f(n)` is attained. `three_le_oddCycleThreshold` (`f(n) ≥ 3` for `n ≥ 1`) is proved in the same file. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Construction: colour the edge `{x, y}` of `K_{2^{n+1}}` (vertices `0, …, 2^{n+1} − 1`, `x ≠ y`) by the least binary digit in which `x` and `y` differ, which is below `n + 1`. In colour class `i` the two ends of every edge have different `i`-th digits, so the `i`-th digit is a proper `2`-colouring of the class; along a walk in a properly `2`-coloured graph the colour alternates, so every closed walk has even length and there is no odd cycle. Converse: if every class of an `n`-colouring of `K_{2^n+1}` had no odd cycle, every class would be `2`-colourable (a graph with no odd closed walk is `2`-colourable and a shortest odd closed walk is a cycle; this is the odd-cycle module of our JSP-000841 package, reused in [Proof/OddCycle.lean](Proof/OddCycle.lean)), and the map sending a vertex to the vector of its `n` class-colours would be injective (two distinct vertices are adjacent in the class of their edge), which is impossible from `2^n + 1` vertices into `2^n` vectors. The odd cycle so obtained has length at most `2^n + 1` (its vertices are distinct), so `2^n + 1` belongs to the set defining `f(n)`; hence the infimum is attained and `f(n) ≤ 2^n + 1`; every cycle has length at least `3`.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's (Erdős–Graham). The construction is due to P. Erdős and R. L. Graham, *On partition theorems for finite graphs*, Colloq. Math. Soc. János Bolyai 10 (1975), cited on the problem page; the colouring by the first differing binary digit is the standard one, and the converse is the standard pigeonhole argument. The Lean development is our own; the odd-cycle module is reused from our JSP-000841 package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000495-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
