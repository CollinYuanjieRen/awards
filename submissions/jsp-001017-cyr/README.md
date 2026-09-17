# JSP-001017: Erdős #1212, Stewart's path `(p_k, p_{k+1}) → (p_{k+1}, p_{k+2})`

This package submits, for intake and eligibility review, a Lean formalization of the argument recounted on the page of [JSP-001017](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-1001-1022.md#JSP-001017) / [Erdős Problem #1212](https://www.erdosproblems.com/1212): in the graph `G` on the visible lattice points `(x, y)` (`gcd(x, y) = 1`), adjacent when they differ by `±1` in one coordinate, is there an infinite path all of whose vertices have `min(x, y) > 1` and a composite coordinate?

**Scope statement.** The current question is open and is not addressed. The page recounts that Erdős originally asked only for `min(x, y) > 1`, and that "Stewart gave the simple proof: `(p_k, p_{k+1})` can be joined to `(p_{k+1}, p_{k+2})`" by the path `(p_k, p_{k+1}) → (p_k, p_{k+1}+1) → ⋯ → (p_k, p_{k+2}) → (p_k+1, p_{k+2}) → ⋯ → (p_{k+1}, p_{k+2})`, "permissible provided `[p_{k+1}, p_{k+2}]` contains no multiple of `p_k`, which is true provided `p_{k+2} < 2p_k`". This package proves Stewart's step under exactly that proviso, for any primes `a < b < c` with `c < 2a` and hence for `p_k, p_{k+1}, p_{k+2}` whenever `p_{k+2} < 2p_k`. The adjacency `Adj` is copied verbatim from the formal-conjectures rendering of #1212; "joined" is the reflexive-transitive closure of adjacency restricted to visible vertices with both coordinates `> 1`. The page's claim that the proviso holds for all `k ≥ 4`, the resulting infinite path, and the composite-coordinate question are not claimed.

## Statement and proof

[Erdos1212Stewart/Main.lean](Erdos1212Stewart/Main.lean) defines `Adj` (formal-conjectures), `Visible p := 1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1` and `VisiblyJoined p q := Relation.ReflTransGen (fun u v => Visible u ∧ Visible v ∧ Adj u v) p q`, and proves

```lean
theorem stewart_joined (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) (h2 : c < 2 * a) : VisiblyJoined (a, b) (b, c)

theorem erdos_1212_stewart (k : ℕ) (h : Nat.nth Nat.Prime (k + 2) < 2 * Nat.nth Nat.Prime k) :
    VisiblyJoined (Nat.nth Nat.Prime k, Nat.nth Nat.Prime (k + 1))
      (Nat.nth Nat.Prime (k + 1), Nat.nth Nat.Prime (k + 2))
```

(primes indexed from `0`), together with the closed form `erdos_1212_stewart_closed`.

Proof. Along the vertical leg `(a, y)`, `b ≤ y ≤ c`, we have `a < y < 2a`, so `a ∤ y` and `gcd(a, y) = 1`; along the horizontal leg `(x, c)`, `a ≤ x ≤ b`, we have `1 < x < c` with `c` prime, so `gcd(x, c) = 1`. Consecutive vertices of each leg are adjacent, giving the path.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks that `Adj` is the formal-conjectures adjacency, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
