# JSP-000668: a balanced 6-colouring of K_{13^k} with no rainbow K₄ (scoped component of Erdős #811)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000668](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000668) (Erdős Problem [#811](https://www.erdosproblems.com/811), Erdős–Pyber–Tuza): "Suppose `n ≡ 1 (mod m)`. We say that an edge-colouring of `K_n` using `m` colours is balanced if every vertex sees exactly `⌊n/m⌋` many edges of each colour. For which graphs `G` is it true that, if `m = e(G)`, for all large `n ≡ 1 (mod m)`, every balanced edge-colouring of `K_n` with `m` colours contains a rainbow copy of `G`?"

**The general characterisation is open and is not claimed here** (in particular nothing is claimed about `C_6`, about the quantitative `d_G(n)`, or about the Axenovich–Clemen infinite families). The problem page records that "Clemen and Wagner [ClWa23] proved that `K_4` does lack this property". This package formalizes exactly that published result: F. C. Clemen and A. Z. Wagner, *Balanced edge-colorings avoiding rainbow cliques of size four*, Electron. J. Combin. 30(3) (2023), #P3.17, Theorem 2: for every `k ≥ 1` there is a balanced edge-colouring of `K_{13^k}` with 6 colours and no rainbow `K_4`.

## Statement and proof

`Jsp668/Defs.lean` models a 6-colouring of the complete graph on a finite vertex type `V` as a symmetric function `c : V → V → Fin 6` (`IsSymm c`; the diagonal is irrelevant) and defines, verbatim from the problem page with `m = 6`,

```lean
def BalancedWith (c : V → V → Fin 6) (t : ℕ) : Prop :=
  ∀ v : V, ∀ col : Fin 6, (Finset.univ.filter (fun w => w ≠ v ∧ c v w = col)).card = t
def Balanced (c : V → V → Fin 6) : Prop := BalancedWith c (Fintype.card V / 6)
def IsRainbowK4 (c : V → V → Fin 6) (a b d e : V) : Prop :=
  a ≠ b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e ∧
    [c a b, c a d, c a e, c b d, c b e, c d e].Nodup
def HasRainbowK4 (c : V → V → Fin 6) : Prop := ∃ a b d e, IsRainbowK4 c a b d e
```

The main theorems (`Jsp668/Main.lean`) are

```lean
theorem exists_balanced_no_rainbowK4 (k : ℕ) :
    ∃ c : Fin (13 ^ k) → Fin (13 ^ k) → Fin 6, IsSymm c ∧ Balanced c ∧ ¬ HasRainbowK4 c
theorem K4_not_forced :
    ¬ ∃ N : ℕ, ∀ n, N ≤ n → n % 6 = 1 →
      ∀ c : Fin n → Fin n → Fin 6, IsSymm c → Balanced c → HasRainbowK4 c
```

The first is Clemen–Wagner's Theorem 2 (stated for all `k`, the case `k = 0` being trivial); the second is the negative answer to the problem's question for `G = K_4`, `m = e(K_4) = 6`, in the form "it is not the case that for all large `n ≡ 1 (mod 6)` every balanced 6-colouring of `K_n` contains a rainbow `K_4`", since `13^k ≡ 1 (mod 6)` is unbounded.

The proof is the paper's. `Jsp668/Base.lean` contains the paper's 13-vertex colouring (Figure 1(a), the symmetric 13×13 matrix, colours 1–6 shifted to `Fin 6`) and verifies by kernel reduction (`decide +kernel`; no `native_decide`, no compiled evaluation) that it is symmetric, that every vertex sees every colour exactly twice (`base_balanced : BalancedWith base 2`), and that none of the four-vertex sets is rainbow (`base_noRainbow`). `Jsp668/Lift.lean` proves the Axenovich–Clemen product lemma (Lemma 2.2 of arXiv:2209.13867, Lemma 3 of the paper) in the one-step form used inductively: for colourings `c₁` on `A` and `c₂` on `V`, colour `{(a, x), (b, y)}` by `c₁ a b` when `a ≠ b` and by `c₂ x y` when `a = b`; then `BalancedWith c₁ t₁ → BalancedWith c₂ t₂ → BalancedWith (lift c₁ c₂) (t₁·|V| + t₂)`, and, for symmetric `c₁`, a rainbow `K_4` in the lift yields one in `c₁` (all first coordinates distinct), one in `c₂` (all equal), or two edges of the same colour `c₁ aᵢ a_l` (otherwise; symmetry of `c₁` is genuinely needed here, and `Lift.lean` records a `decide`-checked counterexample without it). `Jsp668/Main.lean` iterates: the `k`-fold product `Fin 13 × ⋯ × Fin 13` has `13^k` vertices, the iterated lift sees each colour `(13^k − 1)/6 = ⌊13^k/6⌋` times at every vertex, and the colouring is transported to `Fin (13^k)` along `Fintype.equivFin`.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definitions and the two targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/811, retrieved 2026-09-16) is recorded verbatim in `sources/erdos811-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of the main theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` declarations occur in the built library (`Jsp668/`, `Jsp668.lean`, `Audit.lean`); the only `sorry`s in the package are the two statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package. Local verification used arm64 macOS and cached upstream dependencies; authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The mathematics is Clemen–Wagner's (2023; base colouring found by their computer search, reproduced here from Figure 1(a) of the CC BY-ND paper) and Axenovich–Clemen's (the lifting lemma); the contribution sought is the formalization of this published component, following the fleet convention for scoped components of open problems. The formalization was prepared with Claude (Anthropic) assistance (design and hints by Claude Fable 5.1, Lean implementation by Claude Opus subagents) and locally checked. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000668-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
